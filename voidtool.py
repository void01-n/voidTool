"""
voidTool -- a single consolidated MCP server merging what used to be four
separate connectors (shell, browser-automation/puppeteer, sqlite-database,
and the "ant.dir.ant.anthropic.filesystem" extension) into one process/one
name, so there's a single "Always Allow" toggle instead of four.

NOTE ON SCOPE OF THAT TOGGLE: enabling Always Allow for this server grants
blanket, no-prompt access to: arbitrary shell/PowerShell execution, killing
ANY process on the machine by pid, full read/write/delete access to every
path under ALLOWED_DIRS below (currently C:/, D:/@/, D:/@home/), arbitrary
SQL against the database, and full control of a real browser (including
whatever it's logged into). That's a lot of privilege behind one switch.

Sub-systems:
  SHELL       -- run_cmd, run_pwr, run_process, find_pid, close_pid
                 (ported directly from the old shell.py)
  FILESYSTEM  -- read_file, read_text_file, read_media_file,
                 read_multiple_files, write_file, edit_file,
                 create_directory, list_directory, list_directory_with_sizes,
                 directory_tree, move_file, search_files, get_file_info,
                 list_allowed_directories -- reimplemented natively in
                 Python (stdlib), matching the tool names/behavior of the
                 real "ant.dir.ant.anthropic.filesystem" extension
                 (dist/index.js), launched with roots C:/, D:/@/, D:/@home/
  SQLITE      -- list_tables, describe_table, create_table, read_query,
                 write_query, append_insight -- reimplemented with the
                 stdlib sqlite3 module against the same db file the old
                 mcp-server-sqlite connector used
  BROWSER     -- puppeteer_navigate/click/fill/hover/select/evaluate/
                 screenshot -- reimplemented with Playwright (Python)
                 instead of the old Node-based Puppeteer server
  GITHUB      -- github_login/logout/whoami/auth_status plus repo, issue,
                 pull-request, workflow, and code-search tools against the
                 GitHub REST API (stdlib urllib, no extra HTTP dependency).
                 The personal access token is encrypted at rest with
                 AES-256-GCM; the AES key is generated randomly and wrapped
                 with Windows DPAPI (CryptProtectData), tied to this
                 Windows user account, so github_login only needs to be
                 called once per machine/user.

Requirements (pip install -r requirements.txt / uv sync):
  mcp
  playwright   (+ `playwright install chromium` once, to fetch the browser)
  cryptography (already present as a sub-dependency of mcp's auth support)
"""

import asyncio
import base64
import csv
import ctypes
import difflib
import io
import json
import os
import platform
import random
import re
import shlex
import shutil
import sqlite3
import subprocess
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from ctypes import wintypes
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from mcp.server.mcpserver import Context, MCPServer

mcp = MCPServer("voidTool")

__version__ = "0.1.1"

# =========================================================
# SHARED CONFIG
# =========================================================
DB_PATH = r"C:\Users\H4CKRR.DESKTOP-0H6OPCA\claude-agent.db"

# Matches the real filesystem extension's launch args:
#   node .../index.js C:/ D:\@\ D:\@home\
ALLOWED_DIRS = [
    Path("C:/"),
    Path("D:/@/"),
    Path("D:/@home/"),
]

# Every subprocess this server spawns (run_cmd, run_powershell, run_process,
# and the Windows-side wsl.exe launcher for vm()/vm_show()) starts here
# instead of inheriting whatever cwd this server process happens to have
# (observed to be C:\Windows\System32 when launched via some MCP client
# configs). "~" is always the default working directory.
DEFAULT_CWD = Path.home()


def _check_allowed(path: str) -> Path:
    p = Path(path)
    resolved = p.resolve()
    ok = any(
        str(resolved).lower() == str(a.resolve()).lower()
        or str(resolved).lower().startswith(str(a.resolve()).lower().rstrip("\\/") + "\\")
        for a in ALLOWED_DIRS
        if a.exists()
    )
    if not ok:
        raise PermissionError(f"{resolved} is outside allowed directories: {[str(a) for a in ALLOWED_DIRS]}")
    return resolved


# =========================================================
# SHELL  (ported from the old shell.py)
# =========================================================
_running: dict[int, dict] = {}


def _startupinfo_and_flags(hidden: bool):
    creationflags = 0
    startupinfo = None
    if hidden:
        startupinfo = subprocess.STARTUPINFO()
        startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        startupinfo.wShowWindow = subprocess.SW_HIDE
        creationflags = subprocess.CREATE_NO_WINDOW
    return startupinfo, creationflags


def _cmd_argv(command: str) -> list[str]:
    return ["cmd.exe", "/c", command]


_POWERSHELL_GUARD_MSG = "run_cmd doesnt support powershell! use run_pwr!"
_CMD_GUARD_MSG = "run_pwr doesnt support cmd! use run_cmd!"
_POWERSHELL_TOKENS = ("powershell", "powershell.exe", "pwsh", "pwsh.exe")
_CMD_TOKENS = ("cmd", "cmd.exe")


def _first_word_tokens(command: str) -> list[str]:
    tokens = []
    for segment in re.split(r"&&", command):
        first_word = segment.strip().split(None, 1)
        if not first_word:
            continue
        tokens.append(first_word[0].strip('"').strip("'").lower())
    return tokens


def _invokes_powershell(command: str) -> bool:
    return any(t in _POWERSHELL_TOKENS for t in _first_word_tokens(command))


def _invokes_cmd(command: str) -> bool:
    return any(t in _CMD_TOKENS for t in _first_word_tokens(command))


def _powershell_argv(command: str) -> list[str]:
    return [
        "powershell.exe",
        "-NoProfile",
        "-NonInteractive",
        "-ExecutionPolicy", "Bypass",
        "-Command",
        f"$OutputEncoding = [System.Text.Encoding]::UTF8; "
        f"[Console]::OutputEncoding = [System.Text.Encoding]::UTF8; {command}",
    ]


async def _stream_lines(stream, ctx: Optional[Context], prefix: str, collected: list[str]):
    """
    Stream a process's stdout/stderr incrementally. Reads raw chunks
    (instead of stream.readline()-style line iteration) and splits on
    EITHER \n or \r, so \r-only progress-bar output (nix, pip, npm,
    docker pulls, etc.) streams live instead of sitting fully buffered
    until the process exits or a real newline shows up -- previously
    that made long-running commands look frozen/flaky even though they
    were making progress. Any trailing partial line with no terminator
    (common right before EOF, or if a timeout cuts a command off
    mid-line) is still flushed at the end instead of silently dropped.
    """
    if stream is None:
        return
    line_no = 0
    buf = b""

    def _emit(raw: bytes):
        nonlocal line_no
        line_no += 1
        line = raw.decode("utf-8", errors="replace")
        collected.append(line)
        return line_no, line

    while True:
        chunk = await stream.read(4096)
        if not chunk:
            break
        buf += chunk
        while True:
            idx_n = buf.find(b"\n")
            idx_r = buf.find(b"\r")
            candidates = [i for i in (idx_n, idx_r) if i != -1]
            if not candidates:
                break
            idx = min(candidates)
            raw_line, rest = buf[:idx], buf[idx + 1:]
            # collapse a \r\n pair into one terminator instead of emitting
            # a spurious blank line for the \n half of it
            if buf[idx:idx + 1] == b"\r" and rest[:1] == b"\n":
                rest = rest[1:]
            buf = rest
            n, line = _emit(raw_line)
            if ctx is not None:
                await ctx.report_progress(n, None, f"{prefix}{line}")
    if buf:
        n, line = _emit(buf)
        if ctx is not None:
            await ctx.report_progress(n, None, f"{prefix}{line}")


async def _run(argv: list[str], hidden: bool, timeout_ms: int, kind: str,
                background: bool, ctx: Optional[Context], command: str) -> str:
    startupinfo, creationflags = _startupinfo_and_flags(hidden)
    proc = await asyncio.create_subprocess_exec(
        *argv,
        stdin=asyncio.subprocess.DEVNULL,  # never let a child block waiting on stdin it'll never get
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
        cwd=str(DEFAULT_CWD),
        startupinfo=startupinfo,
        creationflags=creationflags,
    )
    _running[proc.pid] = {"proc": proc, "kind": kind, "command": command}

    if background:
        return f"[started, pid={proc.pid}] -- running in background; use find_pid to see it and close_pid({proc.pid}) to stop it."

    out_lines: list[str] = []
    err_lines: list[str] = []
    try:
        await asyncio.wait_for(
            asyncio.gather(
                _stream_lines(proc.stdout, ctx, "", out_lines),
                _stream_lines(proc.stderr, ctx, "[stderr] ", err_lines),
                proc.wait(),
            ),
            timeout=timeout_ms / 1000,
        )
    except asyncio.TimeoutError:
        proc.kill()
        _running.pop(proc.pid, None)
        return f"[timed out after {timeout_ms}ms, process killed]\n" + "\n".join(out_lines + err_lines)

    _running.pop(proc.pid, None)
    parts = []
    if out_lines:
        parts.append("\n".join(out_lines))
    if err_lines:
        parts.append("[stderr]\n" + "\n".join(err_lines))
    parts.append(f"[exit code: {proc.returncode}]")
    return "\n".join(parts)


@mcp.tool()
async def run_cmd(command: str, hidden: bool = True, background: bool = False,
                   timeout_ms: int = 30_000, ctx: Optional[Context] = None) -> str:
    """Run a command through cmd.exe. Streams output live. Hidden window by default."""
    if _invokes_powershell(command):
        return _POWERSHELL_GUARD_MSG
    ok, reason = validate_shell_command(command)
    if not ok:
        return reason
    return await _run(_cmd_argv(command), hidden, timeout_ms, "cmd", background, ctx, command)


@mcp.tool()
async def run_pwr(command: str, hidden: bool = True, background: bool = False,
                   timeout_ms: int = 30_000, ctx: Optional[Context] = None) -> str:
    """Run a command through PowerShell. Streams output live, chunk-by-chunk (splits on \\n or \\r so progress-bar style output isn't buffered). Hidden window by default."""
    if _invokes_cmd(command):
        return _CMD_GUARD_MSG
    ok, reason = validate_shell_command(command)
    if not ok:
        return reason
    return await _run(_powershell_argv(command), hidden, timeout_ms, "powershell", background, ctx, command)


@mcp.tool()
def run_process(path: str, args: Optional[list[str]] = None) -> str:
    """Launch a GUI application directly (not a shell command). Stop later with close_pid(pid)."""
    argv = [path] + (args or [])
    try:
        proc = subprocess.Popen(argv, close_fds=True, cwd=str(DEFAULT_CWD))
    except OSError as e:
        return f"Failed to launch {path}: {e}"
    _running[proc.pid] = {"proc": proc, "kind": "process", "command": " ".join(argv)}
    return f"Launched: {' '.join(argv)} (pid={proc.pid})"


@mcp.tool()
def find_pid(name: Optional[str] = None) -> str:
    """List processes on the machine (via tasklist), optionally filtered by image-name substring."""
    try:
        raw = subprocess.check_output(["tasklist", "/FO", "CSV", "/NH"], text=True,
                                       encoding="utf-8", errors="replace")
    except Exception as e:
        return f"Failed to list processes: {e}"
    rows = list(csv.reader(io.StringIO(raw)))
    lines = []
    for row in rows:
        if len(row) < 2:
            continue
        image_name, pid_str = row[0], row[1]
        if name is not None and name.lower() not in image_name.lower():
            continue
        try:
            pid = int(pid_str)
        except ValueError:
            continue
        entry = _running.get(pid)
        suffix = f" [started here: kind={entry['kind']} command={entry['command']!r}]" if entry else ""
        lines.append(f"pid={pid} name={image_name}{suffix}")
    if not lines:
        return "No processes found" + (f" matching name={name!r}." if name else ".")
    return "\n".join(lines)


@mcp.tool()
def close_pid(pid: int) -> str:
    """
    Stop ANY process on the machine by pid (via taskkill /F), not just ones
    started by this server. Use find_pid first if you need to look up a pid.

    Ask the user for permission TWICE (two separate explicit confirmations)
    before closing a process that was NOT started via this MCP server.
    """
    entry = _running.pop(pid, None)
    result = subprocess.run(["taskkill", "/PID", str(pid), "/F"], capture_output=True,
                             text=True, encoding="utf-8", errors="replace")
    output = (result.stdout + result.stderr).strip()
    tracked_note = f" (was tracked here: kind={entry['kind']})" if entry else ""
    if result.returncode == 0:
        return f"Stopped pid={pid}{tracked_note}.\n{output}"
    return f"Failed to stop pid={pid}{tracked_note}: {output}"


# =========================================================
# FILESYSTEM
# (matches ant.dir.ant.anthropic.filesystem's dist/index.js tool set,
#  launched with roots C:/, D:/@/, D:/@home/)
# =========================================================
# =========================================================
# SHELL COMMAND VALIDATOR
# Blocks host filesystem modification attempts via shell.
# Hooks into run_cmd, run_pwr, and run_cmd_resilient.
# =========================================================

# Redirect operators that write to the filesystem.
# Allows: > NUL, >NUL, 2>&1, 2>NUL, 1>NUL  (null-device redirects only)
_REDIR_RE = re.compile(
    r'(?<![\w&])'           # not preceded by & (so 2>&1 is fine)
    r'>{1,2}'               # > or >>
    r'(?!\s*(?:NUL|/dev/null|&[012]))',  # not pointing at null device
    re.IGNORECASE,
)

# Destructive / modifier tokens for CMD and PowerShell
_BLACKLIST_TOKENS: list[tuple[re.Pattern, str]] = [
    # CMD destructive
    (re.compile(r'\bdel\b',        re.IGNORECASE), 'del'),
    (re.compile(r'\berase\b',      re.IGNORECASE), 'erase'),
    (re.compile(r'\bcopy\b',       re.IGNORECASE), 'copy'),
    (re.compile(r'\bmove\b',       re.IGNORECASE), 'move'),
    (re.compile(r'\bmkdir\b',      re.IGNORECASE), 'mkdir'),
    (re.compile(r'\bmd\b',         re.IGNORECASE), 'md'),
    (re.compile(r'\brmdir\b',      re.IGNORECASE), 'rmdir'),
    (re.compile(r'\brd\b',         re.IGNORECASE), 'rd'),
    (re.compile(r'\brename\b',     re.IGNORECASE), 'rename'),
    (re.compile(r'\bren\b',        re.IGNORECASE), 'ren'),
    (re.compile(r'\bxcopy\b',      re.IGNORECASE), 'xcopy'),
    (re.compile(r'\brobocopy\b',   re.IGNORECASE), 'robocopy'),
    (re.compile(r'\becho\b.*>',    re.IGNORECASE), 'echo >'),
    # PowerShell filesystem cmdlets
    (re.compile(r'\bSet-Content\b',    re.IGNORECASE), 'Set-Content'),
    (re.compile(r'\bAdd-Content\b',    re.IGNORECASE), 'Add-Content'),
    (re.compile(r'\bOut-File\b',       re.IGNORECASE), 'Out-File'),
    (re.compile(r'\bNew-Item\b',       re.IGNORECASE), 'New-Item'),
    (re.compile(r'\bRemove-Item\b',    re.IGNORECASE), 'Remove-Item'),
    (re.compile(r'\bSet-Item\b',       re.IGNORECASE), 'Set-Item'),
    (re.compile(r'\bMove-Item\b',      re.IGNORECASE), 'Move-Item'),
    (re.compile(r'\bCopy-Item\b',      re.IGNORECASE), 'Copy-Item'),
    (re.compile(r'\bRename-Item\b',    re.IGNORECASE), 'Rename-Item'),
    (re.compile(r'\bClear-Content\b',  re.IGNORECASE), 'Clear-Content'),
    (re.compile(r'\bExport-Csv\b',     re.IGNORECASE), 'Export-Csv'),
    (re.compile(r'\bExport-Clixml\b',  re.IGNORECASE), 'Export-Clixml'),
    # Network / download shortcuts (binary drop vectors)
    (re.compile(r'\bInvoke-WebRequest\b', re.IGNORECASE), 'Invoke-WebRequest'),
    (re.compile(r'\biwr\b',              re.IGNORECASE), 'iwr'),
    (re.compile(r'\bInvoke-RestMethod\b', re.IGNORECASE), 'Invoke-RestMethod'),
    (re.compile(r'\birm\b',              re.IGNORECASE), 'irm'),
    (re.compile(r'\bStart-BitsTransfer\b',re.IGNORECASE), 'Start-BitsTransfer'),
    (re.compile(r'\bcurl\b',             re.IGNORECASE), 'curl'),
    (re.compile(r'\bwget\b',             re.IGNORECASE), 'wget'),
    (re.compile(r'\bcertutil\b',         re.IGNORECASE), 'certutil'),
    (re.compile(r'\bbitsadmin\b',        re.IGNORECASE), 'bitsadmin'),
]

_BLOCKED_MSG = (
    "BLOCKED: Host modification via shell is prohibited. "
    "Use 'vm_import' to deploy file payloads directly into an isolated WSL sandbox distro."
)


def validate_shell_command(command: str) -> tuple[bool, str]:
    """
    Validate a shell command against the host-modification blacklist.
    Returns (True, "") if the command is allowed.
    Returns (False, reason) if it should be blocked.
    Checks:
      1. Output redirections that target real files (not NUL / &1 / &2).
      2. Destructive CMD tokens (del, copy, move, mkdir, rmdir, ...).
      3. PowerShell filesystem write cmdlets (Set-Content, Out-File, ...).
      4. Network/download shortcuts (curl, wget, iwr, certutil, ...).
    """
    if _REDIR_RE.search(command):
        return False, _BLOCKED_MSG
    for pattern, token in _BLACKLIST_TOKENS:
        if pattern.search(command):
            return False, _BLOCKED_MSG
    return True, ""


@mcp.tool()
def create_directory(path: str) -> str:
    """Create a directory (and any nested parents). Succeeds silently if it already exists."""
    p = _check_allowed(path)
    p.mkdir(parents=True, exist_ok=True)
    return f"Successfully created directory {path}"


@mcp.tool()
def list_directory(path: str) -> str:
    """List files/directories in a path, prefixed with [FILE]/[DIR]. Only works within allowed directories."""
    p = _check_allowed(path)
    entries = [f"{'[DIR]' if e.is_dir() else '[FILE]'} {e.name}" for e in p.iterdir()]
    return "\n".join(entries)


@mcp.tool()
def list_directory_with_sizes(path: str, sortBy: str = "name") -> str:
    """
    List files/directories in a path with sizes, sorted by 'name' (default)
    or 'size'. Includes a summary of total files, directories, and combined
    size. Only works within allowed directories.
    """
    p = _check_allowed(path)
    detailed = []
    for e in p.iterdir():
        try:
            st = e.stat()
            detailed.append({"name": e.name, "is_dir": e.is_dir(), "size": 0 if e.is_dir() else st.st_size})
        except OSError:
            detailed.append({"name": e.name, "is_dir": e.is_dir(), "size": 0})

    if sortBy == "size":
        detailed.sort(key=lambda x: -x["size"])
    else:
        detailed.sort(key=lambda x: x["name"].lower())

    def fmt_size(n: int) -> str:
        for unit in ["B", "KB", "MB", "GB", "TB"]:
            if n < 1024:
                return f"{n:.0f}{unit}" if unit == "B" else f"{n:.1f}{unit}"
            n /= 1024
        return f"{n:.1f}PB"

    lines = [
        f"{'[DIR]' if d['is_dir'] else '[FILE]'} {d['name']:<30} {'' if d['is_dir'] else fmt_size(d['size']).rjust(10)}"
        for d in detailed
    ]
    total_files = sum(1 for d in detailed if not d["is_dir"])
    total_dirs = sum(1 for d in detailed if d["is_dir"])
    total_size = sum(d["size"] for d in detailed if not d["is_dir"])
    lines += ["", f"Total: {total_files} files, {total_dirs} directories", f"Combined size: {fmt_size(total_size)}"]
    return "\n".join(lines)


@mcp.tool()
def directory_tree(path: str, excludePatterns: Optional[list[str]] = None) -> str:
    """
    Recursive tree view of files/directories as JSON. Each entry has
    'name', 'type' (file/directory), and directories have a 'children'
    array. Supports glob-style excludePatterns. Only works within allowed
    directories.
    """
    import fnmatch
    exclude = excludePatterns or []
    root = _check_allowed(path)

    def excluded(rel: str) -> bool:
        return any(fnmatch.fnmatch(rel, pat) or fnmatch.fnmatch(rel, f"*/{pat}") or fnmatch.fnmatch(rel, f"*/{pat}/*")
                   for pat in exclude)

    def build(cur: Path):
        result = []
        for e in sorted(cur.iterdir()):
            rel = str(e.relative_to(root))
            if excluded(rel):
                continue
            node = {"name": e.name, "type": "directory" if e.is_dir() else "file"}
            if e.is_dir():
                node["children"] = build(e)
            result.append(node)
        return result

    return json.dumps(build(root), indent=2)


@mcp.tool()
def move_file(source: str, destination: str) -> str:
    """
    Move or rename a file/directory. Fails if the destination already
    exists. Both paths must be within allowed directories.
    """
    s = _check_allowed(source)
    d = _check_allowed(destination)
    if d.exists():
        raise FileExistsError(f"Destination already exists: {destination}")
    s.rename(d)
    return f"Successfully moved {source} to {destination}"


@mcp.tool()
def search_files(path: str, pattern: str, excludePatterns: Optional[list[str]] = None) -> str:
    """
    Recursively search a directory for files/dirs matching a glob pattern
    (e.g. '*.py', '**/*.log'), skipping any matching excludePatterns. Only
    searches within allowed directories.
    """
    import fnmatch
    exclude = excludePatterns or []
    root = _check_allowed(path)
    matches = []
    for m in root.rglob(pattern):
        rel = str(m.relative_to(root))
        if any(fnmatch.fnmatch(rel, pat) for pat in exclude):
            continue
        matches.append(str(m))
    return "\n".join(matches) if matches else "No matches found"


@mcp.tool()
def get_file_info(path: str) -> str:
    """Get metadata (size, timestamps, type) about a file or directory. Only works within allowed directories."""
    p = _check_allowed(path)
    st = p.stat()
    import datetime
    info = {
        "size": st.st_size,
        "created": datetime.datetime.fromtimestamp(st.st_ctime).isoformat(),
        "modified": datetime.datetime.fromtimestamp(st.st_mtime).isoformat(),
        "accessed": datetime.datetime.fromtimestamp(st.st_atime).isoformat(),
        "isDirectory": p.is_dir(),
        "isFile": p.is_file(),
        "permissions": oct(st.st_mode)[-3:],
    }
    return "\n".join(f"{k}: {v}" for k, v in info.items())


@mcp.tool()
def list_allowed_directories() -> str:
    """Returns the list of directories this server is allowed to access (subdirectories included)."""
    return "Allowed directories:\n" + "\n".join(str(a) for a in ALLOWED_DIRS)


# =========================================================
# SQLITE  (new native implementation, same db file as before)
# =========================================================
_insights: list[str] = []


def _db():
    return sqlite3.connect(DB_PATH)


@mcp.tool()
def list_tables() -> str:
    """List all tables in the SQLite database."""
    with _db() as conn:
        rows = conn.execute("SELECT name FROM sqlite_master WHERE type='table'").fetchall()
    return "\n".join(r[0] for r in rows) if rows else "(no tables)"


@mcp.tool()
def describe_table(table_name: str) -> str:
    """Get schema info for a specific table."""
    with _db() as conn:
        rows = conn.execute(f"PRAGMA table_info({table_name})").fetchall()
    return "\n".join(str(r) for r in rows) if rows else "(no such table)"


@mcp.tool()
def create_table(query: str) -> str:
    """Run a CREATE TABLE statement."""
    with _db() as conn:
        conn.execute(query)
        conn.commit()
    return "Table created."


@mcp.tool()
def read_query(query: str) -> str:
    """Execute a SELECT query."""
    with _db() as conn:
        rows = conn.execute(query).fetchall()
    return "\n".join(str(r) for r in rows) if rows else "(no rows)"


@mcp.tool()
def write_query(query: str) -> str:
    """Execute an INSERT, UPDATE, or DELETE query."""
    with _db() as conn:
        cur = conn.execute(query)
        conn.commit()
    return f"{cur.rowcount} row(s) affected."


@mcp.tool()
def append_insight(insight: str) -> str:
    """Add a business insight to the in-memory memo for this session."""
    _insights.append(insight)
    return f"Recorded. ({len(_insights)} insight(s) so far)"


# =========================================================
# GITHUB AUTOMATION
# The GitHub personal access token is encrypted at rest with AES-256-GCM.
# The AES-256 key is generated randomly on first use and is itself wrapped
# with Windows DPAPI (CryptProtectData), which ties decryption to this
# specific Windows user account -- so copying the key file or the db to
# another machine/account does not expose the token. The key never touches
# disk unwrapped; the token is only ever decrypted in memory, per call, and
# is never echoed back to the caller.
# =========================================================
class _DATA_BLOB(ctypes.Structure):
    _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]


_crypt32 = ctypes.windll.crypt32
_kernel32 = ctypes.windll.kernel32
_crypt32.CryptProtectData.argtypes = [
    ctypes.POINTER(_DATA_BLOB), wintypes.LPCWSTR, ctypes.POINTER(_DATA_BLOB),
    ctypes.c_void_p, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(_DATA_BLOB),
]
_crypt32.CryptProtectData.restype = wintypes.BOOL
_crypt32.CryptUnprotectData.argtypes = [
    ctypes.POINTER(_DATA_BLOB), ctypes.POINTER(wintypes.LPWSTR), ctypes.POINTER(_DATA_BLOB),
    ctypes.c_void_p, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(_DATA_BLOB),
]
_crypt32.CryptUnprotectData.restype = wintypes.BOOL
_kernel32.LocalFree.argtypes = [ctypes.c_void_p]
_kernel32.LocalFree.restype = ctypes.c_void_p

_CRYPTPROTECT_UI_FORBIDDEN = 0x01


def _make_blob(data: bytes):
    buf = ctypes.create_string_buffer(data, len(data))
    blob = _DATA_BLOB(cbData=len(data), pbData=ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
    return blob, buf  # keep buf alive for the duration of the call


def _dpapi_protect(data: bytes, entropy: bytes) -> bytes:
    in_blob, _in_buf = _make_blob(data)
    ent_blob, _ent_buf = _make_blob(entropy)
    out_blob = _DATA_BLOB()
    ok = _crypt32.CryptProtectData(
        ctypes.byref(in_blob), None, ctypes.byref(ent_blob), None, None,
        _CRYPTPROTECT_UI_FORBIDDEN, ctypes.byref(out_blob),
    )
    if not ok:
        raise OSError(f"CryptProtectData failed: WinError {ctypes.get_last_error()}")
    try:
        return ctypes.string_at(out_blob.pbData, out_blob.cbData)
    finally:
        _kernel32.LocalFree(out_blob.pbData)


def _dpapi_unprotect(blob_bytes: bytes, entropy: bytes) -> bytes:
    in_blob, _in_buf = _make_blob(blob_bytes)
    ent_blob, _ent_buf = _make_blob(entropy)
    out_blob = _DATA_BLOB()
    ok = _crypt32.CryptUnprotectData(
        ctypes.byref(in_blob), None, ctypes.byref(ent_blob), None, None,
        _CRYPTPROTECT_UI_FORBIDDEN, ctypes.byref(out_blob),
    )
    if not ok:
        raise OSError(f"CryptUnprotectData failed: WinError {ctypes.get_last_error()}")
    try:
        return ctypes.string_at(out_blob.pbData, out_blob.cbData)
    finally:
        _kernel32.LocalFree(out_blob.pbData)


_MASTER_KEY_ENTROPY = b"voidTool-secrets-master-key-v1"
_MASTER_KEY_PATH = Path(os.environ.get("LOCALAPPDATA") or str(Path.home())) / "voidTool" / "master.key"


def _get_master_key() -> bytes:
    """Return the 32-byte AES-256 master key, generating + DPAPI-wrapping it on first use."""
    _MASTER_KEY_PATH.parent.mkdir(parents=True, exist_ok=True)
    if _MASTER_KEY_PATH.exists():
        return _dpapi_unprotect(_MASTER_KEY_PATH.read_bytes(), _MASTER_KEY_ENTROPY)
    key = os.urandom(32)
    _MASTER_KEY_PATH.write_bytes(_dpapi_protect(key, _MASTER_KEY_ENTROPY))
    return key


def _init_secrets_table():
    with _db() as conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS voidtool_secrets (
                key TEXT PRIMARY KEY,
                nonce BLOB NOT NULL,
                ciphertext BLOB NOT NULL,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
        """)
        conn.commit()


_init_secrets_table()


def _save_secret(key: str, plaintext: str) -> None:
    aesgcm = AESGCM(_get_master_key())
    nonce = os.urandom(12)
    ciphertext = aesgcm.encrypt(nonce, plaintext.encode("utf-8"), None)
    now = datetime.now(timezone.utc).isoformat()
    with _db() as conn:
        row = conn.execute("SELECT created_at FROM voidtool_secrets WHERE key=?", (key,)).fetchone()
        created_at = row[0] if row else now
        conn.execute(
            "INSERT INTO voidtool_secrets (key, nonce, ciphertext, created_at, updated_at) VALUES (?,?,?,?,?) "
            "ON CONFLICT(key) DO UPDATE SET nonce=excluded.nonce, ciphertext=excluded.ciphertext, updated_at=excluded.updated_at",
            (key, nonce, ciphertext, created_at, now),
        )
        conn.commit()


def _load_secret(key: str) -> Optional[str]:
    with _db() as conn:
        row = conn.execute("SELECT nonce, ciphertext FROM voidtool_secrets WHERE key=?", (key,)).fetchone()
    if not row:
        return None
    nonce, ciphertext = row
    aesgcm = AESGCM(_get_master_key())
    return aesgcm.decrypt(bytes(nonce), bytes(ciphertext), None).decode("utf-8")


def _delete_secret(key: str) -> bool:
    with _db() as conn:
        cur = conn.execute("DELETE FROM voidtool_secrets WHERE key=?", (key,))
        conn.commit()
    return cur.rowcount > 0


_GITHUB_API = "https://api.github.com"


def _github_request(method: str, path: str, params: Optional[dict] = None, body: Optional[dict] = None):
    token = _load_secret("github_token")
    if not token:
        raise PermissionError("Not logged in to GitHub. Call github_login(token=...) first.")
    url = _GITHUB_API + path
    if params:
        url += "?" + urllib.parse.urlencode({k: v for k, v in params.items() if v is not None})
    data = json.dumps(body).encode("utf-8") if body is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    req.add_header("Authorization", f"Bearer {token}")
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("X-GitHub-Api-Version", "2022-11-28")
    req.add_header("User-Agent", "voidTool")
    if data is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            raw = resp.read()
            return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"GitHub API error {e.code}: {err_body}") from e


@mcp.tool()
def github_login(token: str) -> str:
    """
    Save a GitHub personal access token, encrypted at rest with AES-256-GCM
    (the AES key is Windows-DPAPI-wrapped, tied to this Windows user
    account). Call this once; every other github_* tool reuses the saved
    token afterward without asking again. The raw token is never echoed
    back, logged, or returned by any tool.
    """
    token = token.strip()
    if not token:
        return "FAIL: empty token."
    _save_secret("github_token", token)
    try:
        me = _github_request("GET", "/user")
        return f"Saved and verified. Authenticated as {me.get('login', 'unknown')}."
    except Exception as e:
        return f"Token saved, but a verification call to GitHub failed: {e}"


@mcp.tool()
def github_logout() -> str:
    """Delete the saved GitHub token from encrypted storage."""
    return "Removed saved GitHub token." if _delete_secret("github_token") else "No GitHub token was saved."


@mcp.tool()
def github_auth_status() -> str:
    """Report whether a GitHub token is currently saved (never reveals the token itself)."""
    with _db() as conn:
        row = conn.execute("SELECT updated_at FROM voidtool_secrets WHERE key='github_token'").fetchone()
    return f"Authenticated (token saved, last updated {row[0]})." if row else "Not authenticated. Call github_login(token=...)."


@mcp.tool()
def github_whoami() -> str:
    """Return the currently authenticated GitHub username, without exposing the token."""
    me = _github_request("GET", "/user")
    return f"login={me.get('login')} name={me.get('name')} id={me.get('id')}"


@mcp.tool()
def github_list_repos(visibility: str = "all", per_page: int = 30) -> str:
    """List repositories for the authenticated user (visibility: all/public/private)."""
    repos = _github_request("GET", "/user/repos", params={"visibility": visibility, "per_page": per_page, "sort": "updated"})
    return "\n".join(f"{r['full_name']}  ({'private' if r['private'] else 'public'})  {r.get('html_url', '')}" for r in repos) or "(no repos)"


@mcp.tool()
def github_get_repo(owner: str, repo: str) -> str:
    """Get details for a specific repository."""
    r = _github_request("GET", f"/repos/{owner}/{repo}")
    keys = ("full_name", "description", "private", "default_branch", "stargazers_count", "open_issues_count", "html_url")
    return json.dumps({k: r.get(k) for k in keys}, indent=2)


@mcp.tool()
def github_list_issues(owner: str, repo: str, state: str = "open", per_page: int = 30) -> str:
    """List issues in a repository (state: open/closed/all). Pull requests are excluded."""
    issues = _github_request("GET", f"/repos/{owner}/{repo}/issues", params={"state": state, "per_page": per_page})
    lines = [f"#{i['number']} [{i['state']}] {i['title']}" for i in issues if "pull_request" not in i]
    return "\n".join(lines) or "(no issues)"


@mcp.tool()
def github_create_issue(owner: str, repo: str, title: str, body: str = "") -> str:
    """Create a new issue in a repository."""
    i = _github_request("POST", f"/repos/{owner}/{repo}/issues", body={"title": title, "body": body})
    return f"Created issue #{i['number']}: {i['html_url']}"


@mcp.tool()
def github_comment_issue(owner: str, repo: str, issue_number: int, body: str) -> str:
    """Add a comment to an issue or pull request."""
    c = _github_request("POST", f"/repos/{owner}/{repo}/issues/{issue_number}/comments", body={"body": body})
    return f"Comment added: {c['html_url']}"


@mcp.tool()
def github_list_pull_requests(owner: str, repo: str, state: str = "open", per_page: int = 30) -> str:
    """List pull requests in a repository (state: open/closed/all)."""
    prs = _github_request("GET", f"/repos/{owner}/{repo}/pulls", params={"state": state, "per_page": per_page})
    return "\n".join(f"#{p['number']} [{p['state']}] {p['title']} ({p['head']['ref']} -> {p['base']['ref']})" for p in prs) or "(no pull requests)"


@mcp.tool()
def github_get_pull_request(owner: str, repo: str, pr_number: int) -> str:
    """Get details for a specific pull request."""
    p = _github_request("GET", f"/repos/{owner}/{repo}/pulls/{pr_number}")
    keys = ("number", "title", "state", "mergeable", "html_url", "additions", "deletions", "changed_files")
    return json.dumps({k: p.get(k) for k in keys}, indent=2)


@mcp.tool()
def github_list_workflow_runs(owner: str, repo: str, per_page: int = 10) -> str:
    """List recent GitHub Actions workflow runs for a repository."""
    data = _github_request("GET", f"/repos/{owner}/{repo}/actions/runs", params={"per_page": per_page})
    runs = data.get("workflow_runs", [])
    return "\n".join(f"#{r['run_number']} {r['name']} [{r['status']}/{r['conclusion']}] {r['html_url']}" for r in runs) or "(no runs)"


@mcp.tool()
def github_trigger_workflow(owner: str, repo: str, workflow_id: str, ref: str = "main", inputs: Optional[dict] = None) -> str:
    """Trigger a workflow_dispatch run. workflow_id can be the filename (e.g. 'ci.yml') or its numeric id."""
    _github_request("POST", f"/repos/{owner}/{repo}/actions/workflows/{workflow_id}/dispatches",
                     body={"ref": ref, "inputs": inputs or {}})
    return f"Dispatched workflow {workflow_id!r} on ref {ref!r}."


@mcp.tool()
def github_get_file(owner: str, repo: str, path: str, ref: Optional[str] = None) -> str:
    """Get a file's contents from a repository (or list a directory's contents)."""
    data = _github_request("GET", f"/repos/{owner}/{repo}/contents/{path}", params={"ref": ref} if ref else None)
    if isinstance(data, list):
        return "\n".join(f"{'[DIR]' if e['type'] == 'dir' else '[FILE]'} {e['name']}" for e in data)
    return base64.b64decode(data["content"]).decode("utf-8", errors="replace")


@mcp.tool()
def github_search_repos(query: str, per_page: int = 10) -> str:
    """Search GitHub repositories."""
    data = _github_request("GET", "/search/repositories", params={"q": query, "per_page": per_page})
    return "\n".join(f"{r['full_name']}  \u2605{r['stargazers_count']}  {r['html_url']}" for r in data.get("items", [])) or "(no results)"


@mcp.tool()
def github_search_code(query: str, per_page: int = 10) -> str:
    """Search code across GitHub (supports GitHub code-search qualifiers, e.g. 'repo:owner/name filename:x.py')."""
    data = _github_request("GET", "/search/code", params={"q": query, "per_page": per_page})
    return "\n".join(f"{i['repository']['full_name']}: {i['path']}" for i in data.get("items", [])) or "(no results)"


@mcp.tool()
def github_create_repo(name: str, private: bool = False, description: str = "",
                        auto_init: bool = True, org: Optional[str] = None) -> str:
    """
    Create a new GitHub repository under the authenticated user (or under
    `org` if given). auto_init=True creates an initial commit (README) so
    the repo isn't empty. Requires the token to have 'repo' scope.
    """
    body = {"name": name, "private": private, "description": description, "auto_init": auto_init}
    path = f"/orgs/{org}/repos" if org else "/user/repos"
    r = _github_request("POST", path, body=body)
    return f"Created {r['full_name']}: {r['html_url']} (clone: {r['clone_url']})"


@mcp.tool()
def github_update_repo(owner: str, repo: str, description: Optional[str] = None,
                        private: Optional[bool] = None, default_branch: Optional[str] = None,
                        archived: Optional[bool] = None) -> str:
    """Update settings on an existing repository. Only pass the fields you want changed."""
    body = {k: v for k, v in {
        "description": description, "private": private,
        "default_branch": default_branch, "archived": archived,
    }.items() if v is not None}
    if not body:
        return "Nothing to update -- pass at least one field."
    r = _github_request("PATCH", f"/repos/{owner}/{repo}", body=body)
    return f"Updated {r['full_name']}: {r['html_url']}"


@mcp.tool()
def github_delete_repo(owner: str, repo: str, confirm: bool = False) -> str:
    """
    PERMANENTLY delete a repository. Irreversible. Requires the token to
    have 'delete_repo' scope. Refuses to run unless confirm=True is passed
    explicitly -- always get an explicit, separate go-ahead from the user
    before setting confirm=True, especially for a repo that wasn't just
    created in this same session.
    """
    if not confirm:
        return f"Refusing: call again with confirm=True to permanently delete {owner}/{repo}."
    _github_request("DELETE", f"/repos/{owner}/{repo}")
    return f"Deleted {owner}/{repo}."


@mcp.tool()
def github_api(method: str, path: str, params: Optional[dict] = None, body: Optional[dict] = None) -> str:
    """
    Generic escape hatch to ANY GitHub REST API endpoint -- covers
    everything the other github_* tools do plus anything they don't
    (releases, branch protection, teams, gists, webhooks, org/user admin,
    etc.), limited only by what scopes the saved token actually has.
    `method` is GET/POST/PATCH/PUT/DELETE. `path` is the API path after
    the host, e.g. '/repos/{owner}/{repo}/releases'. `params` become the
    query string; `body` is sent as JSON. Uses the same saved, encrypted
    token as every other github_* tool -- call github_login first if not
    yet authenticated. Because this can do destructive/irreversible things
    (DELETE calls, force-pushes to protected settings, etc.) that the
    narrower tools guard against, treat any DELETE or destructive-looking
    PATCH/PUT through this tool with the same caution as
    github_delete_repo: confirm with the user first.
    """
    result = _github_request(method.upper(), path, params=params, body=body)
    return json.dumps(result, indent=2) if result else "(empty response)"


# =========================================================
# BROWSER AUTOMATION  (Playwright, replacing Node/Puppeteer)
# =========================================================
_playwright = None
_browser = None
_page = None


def _ensure_page():
    global _playwright, _browser, _page
    if _page is not None:
        return _page
    from playwright.sync_api import sync_playwright
    _playwright = sync_playwright().start()
    _browser = _playwright.chromium.launch(headless=False)
    _page = _browser.new_page()
    return _page


@mcp.tool()
def puppeteer_navigate(url: str) -> str:
    """Navigate to a URL."""
    _ensure_page().goto(url)
    return f"Navigated to {url}"


@mcp.tool()
def puppeteer_click(selector: str) -> str:
    """Click an element on the page."""
    _ensure_page().click(selector)
    return f"Clicked {selector}"


@mcp.tool()
def puppeteer_fill(selector: str, value: str) -> str:
    """Fill out an input field."""
    _ensure_page().fill(selector, value)
    return f"Filled {selector} with {value!r}"


@mcp.tool()
def puppeteer_hover(selector: str) -> str:
    """Hover an element on the page."""
    _ensure_page().hover(selector)
    return f"Hovered {selector}"


@mcp.tool()
def puppeteer_select(selector: str, value: str) -> str:
    """Select an option in a <select> element."""
    _ensure_page().select_option(selector, value)
    return f"Selected {value!r} in {selector}"


@mcp.tool()
def puppeteer_evaluate(script: str) -> str:
    """Execute JavaScript in the browser console."""
    result = _ensure_page().evaluate(script)
    return json.dumps(result) if result is not None else "undefined"


@mcp.tool()
def puppeteer_screenshot(path: str = "") -> str:
    """Take a screenshot of the current page."""
    out = _check_allowed(path) if path else Path(r"D:\@\voidTool_screenshot.png")
    out.parent.mkdir(parents=True, exist_ok=True)
    _ensure_page().screenshot(path=str(out))
    return f"Saved screenshot to {out}"


# =========================================================
# SEQUENTIAL THINKING
# =========================================================
_thought_sessions: dict[str, list[dict]] = {}


@mcp.tool()
def sequential_thinking(
    thought: str,
    thought_number: int,
    total_thoughts: int,
    next_thought_needed: bool,
    session_id: str = "default",
    is_revision: bool = False,
    revises_thought: Optional[int] = None,
    branch_from_thought: Optional[int] = None,
    branch_id: Optional[str] = None,
    needs_more_thoughts: bool = False,
) -> str:
    """
    Record one step of a multi-step reasoning chain and get back the
    running thought history. Call this repeatedly -- one call per thought
    -- to plan or debug complex, multi-step tasks before acting: break the
    problem down, revise earlier thoughts as understanding grows
    (is_revision + revises_thought), branch to explore alternatives
    (branch_from_thought + branch_id), and adjust total_thoughts up or
    down as you go. Set next_thought_needed=False on the final thought.
    State is kept per session_id so unrelated tasks don't interleave.
    """
    session = _thought_sessions.setdefault(session_id, [])
    entry = {
        "thought": thought,
        "thought_number": thought_number,
        "total_thoughts": total_thoughts,
        "next_thought_needed": next_thought_needed,
        "is_revision": is_revision,
        "revises_thought": revises_thought,
        "branch_from_thought": branch_from_thought,
        "branch_id": branch_id,
        "needs_more_thoughts": needs_more_thoughts,
        "ts": datetime.now(timezone.utc).isoformat(),
    }
    session.append(entry)

    lines = [f"Session {session_id!r} -- {len(session)} thought(s) recorded so far:"]
    for e in session:
        tag = ""
        if e["is_revision"]:
            tag = f" [revision of #{e['revises_thought']}]"
        elif e["branch_from_thought"]:
            tag = f" [branch {e['branch_id']!r} from #{e['branch_from_thought']}]"
        lines.append(f"  #{e['thought_number']}/{e['total_thoughts']}{tag}: {e['thought']}")
    status = "more thoughts needed" if next_thought_needed else "chain complete"
    lines.append(f"-- {status} --")
    return "\n".join(lines)


@mcp.tool()
def get_thinking_session(session_id: str = "default") -> str:
    """Return the full recorded thought chain for a sequential_thinking session."""
    session = _thought_sessions.get(session_id)
    if not session:
        return f"No thoughts recorded for session {session_id!r}."
    return json.dumps(session, indent=2)


@mcp.tool()
def clear_thinking_session(session_id: str = "default") -> str:
    """Clear a sequential_thinking session's recorded thoughts."""
    existed = _thought_sessions.pop(session_id, None) is not None
    return f"Cleared session {session_id!r}." if existed else f"Session {session_id!r} was already empty."


# =========================================================
# AGENTIC MEMORY & TASK CHECKPOINTING
# (persisted in the same SQLite db as the SQLITE subsystem)
# =========================================================
def _init_agent_tables():
    with _db() as conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS agent_memory (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL,
                category TEXT DEFAULT 'general',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS task_checkpoints (
                checkpoint_id TEXT PRIMARY KEY,
                task_id TEXT NOT NULL,
                description TEXT,
                state_json TEXT NOT NULL,
                created_at TEXT NOT NULL
            )
        """)
        conn.commit()


_init_agent_tables()


@mcp.tool()
def memory_save(key: str, value: str, category: str = "general") -> str:
    """
    Save a fact/preference/note to durable cross-session memory, keyed by
    `key`. Overwrites if the key already exists. Use short stable keys
    (e.g. 'user.editor', 'project.voidTool.style_guide') so future
    sessions can look them up with memory_recall or memory_search.
    """
    now = datetime.now(timezone.utc).isoformat()
    with _db() as conn:
        row = conn.execute("SELECT created_at FROM agent_memory WHERE key=?", (key,)).fetchone()
        created_at = row[0] if row else now
        conn.execute(
            "INSERT INTO agent_memory (key, value, category, created_at, updated_at) VALUES (?,?,?,?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value, category=excluded.category, updated_at=excluded.updated_at",
            (key, value, category, created_at, now),
        )
        conn.commit()
    return f"Saved memory {key!r} (category={category!r})."


@mcp.tool()
def memory_recall(key: str) -> str:
    """Retrieve one durable memory by exact key. Returns 'not found' if it doesn't exist."""
    with _db() as conn:
        row = conn.execute("SELECT value, category, updated_at FROM agent_memory WHERE key=?", (key,)).fetchone()
    if not row:
        return f"No memory found for key {key!r}."
    value, category, updated_at = row
    return f"[{category}] {key} (updated {updated_at}):\n{value}"


@mcp.tool()
def memory_search(query: str, category: Optional[str] = None) -> str:
    """Search durable memory by substring match against key and value, optionally filtered by category."""
    like = f"%{query}%"
    with _db() as conn:
        if category:
            rows = conn.execute(
                "SELECT key, value, category, updated_at FROM agent_memory "
                "WHERE (key LIKE ? OR value LIKE ?) AND category=? ORDER BY updated_at DESC",
                (like, like, category),
            ).fetchall()
        else:
            rows = conn.execute(
                "SELECT key, value, category, updated_at FROM agent_memory "
                "WHERE key LIKE ? OR value LIKE ? ORDER BY updated_at DESC",
                (like, like),
            ).fetchall()
    if not rows:
        return f"No memories matching {query!r}."
    return "\n".join(f"[{c}] {k} (updated {u}): {v}" for k, v, c, u in rows)


@mcp.tool()
def memory_list(category: Optional[str] = None) -> str:
    """List all durable memory keys, optionally filtered by category."""
    with _db() as conn:
        if category:
            rows = conn.execute(
                "SELECT key, category, updated_at FROM agent_memory WHERE category=? ORDER BY updated_at DESC",
                (category,),
            ).fetchall()
        else:
            rows = conn.execute("SELECT key, category, updated_at FROM agent_memory ORDER BY updated_at DESC").fetchall()
    if not rows:
        return "(no memories stored)"
    return "\n".join(f"[{c}] {k} (updated {u})" for k, c, u in rows)


@mcp.tool()
def memory_delete(key: str) -> str:
    """Delete one durable memory by key."""
    with _db() as conn:
        cur = conn.execute("DELETE FROM agent_memory WHERE key=?", (key,))
        conn.commit()
    return f"Deleted {key!r}." if cur.rowcount else f"No memory found for key {key!r}."


@mcp.tool()
def checkpoint_save(task_id: str, state_json: str, description: str = "") -> str:
    """
    Save a named checkpoint of task progress (arbitrary JSON state string:
    e.g. completed steps, key decisions, file paths touched) so a long
    multi-step task can be resumed after an interruption or failure.
    Returns a checkpoint_id to pass to checkpoint_restore.
    """
    try:
        json.loads(state_json)
    except json.JSONDecodeError as e:
        return f"FAIL: state_json is not valid JSON: {e}"
    checkpoint_id = f"{task_id}-{uuid.uuid4().hex[:8]}"
    now = datetime.now(timezone.utc).isoformat()
    with _db() as conn:
        conn.execute(
            "INSERT INTO task_checkpoints (checkpoint_id, task_id, description, state_json, created_at) VALUES (?,?,?,?,?)",
            (checkpoint_id, task_id, description, state_json, now),
        )
        conn.commit()
    return f"Checkpoint saved: {checkpoint_id}"


@mcp.tool()
def checkpoint_list(task_id: Optional[str] = None) -> str:
    """List saved checkpoints, optionally filtered to one task_id, newest first."""
    with _db() as conn:
        if task_id:
            rows = conn.execute(
                "SELECT checkpoint_id, description, created_at FROM task_checkpoints WHERE task_id=? ORDER BY created_at DESC",
                (task_id,),
            ).fetchall()
            return "\n".join(f"{cid}  {created}  {desc}" for cid, desc, created in rows) if rows else "(no checkpoints for this task_id)"
        rows = conn.execute(
            "SELECT checkpoint_id, task_id, description, created_at FROM task_checkpoints ORDER BY created_at DESC"
        ).fetchall()
    return "\n".join(f"{cid}  task={tid}  {created}  {desc}" for cid, tid, desc, created in rows) if rows else "(no checkpoints saved)"


@mcp.tool()
def checkpoint_restore(checkpoint_id: str) -> str:
    """Restore and return the saved state_json for a checkpoint_id, to resume a task where it left off."""
    with _db() as conn:
        row = conn.execute(
            "SELECT task_id, description, state_json, created_at FROM task_checkpoints WHERE checkpoint_id=?",
            (checkpoint_id,),
        ).fetchone()
    if not row:
        return f"FAIL: no checkpoint {checkpoint_id!r} found."
    task_id, description, state_json, created_at = row
    return f"task_id={task_id}\ndescription={description}\ncreated_at={created_at}\nstate:\n{state_json}"


@mcp.tool()
def checkpoint_delete(checkpoint_id: str) -> str:
    """Delete a saved checkpoint."""
    with _db() as conn:
        cur = conn.execute("DELETE FROM task_checkpoints WHERE checkpoint_id=?", (checkpoint_id,))
        conn.commit()
    return f"Deleted {checkpoint_id}." if cur.rowcount else f"No checkpoint {checkpoint_id!r} found."


# =========================================================
# SELF-VERIFICATION
# =========================================================
@mcp.tool()
def verify_file_contains(path: str, expected_substring: str, case_sensitive: bool = True) -> str:
    """
    Self-check: confirm a file actually contains an expected substring
    after an edit/write, instead of assuming the operation worked. Returns
    PASS/FAIL plus a snippet of surrounding context.
    """
    try:
        p = _check_allowed(path)
        content = p.read_text(encoding="utf-8", errors="replace")
    except Exception as e:
        return f"FAIL: could not read {path}: {e}"
    haystack = content if case_sensitive else content.lower()
    needle = expected_substring if case_sensitive else expected_substring.lower()
    if needle in haystack:
        idx = haystack.find(needle)
        snippet = content[max(0, idx - 40):idx + len(expected_substring) + 40]
        return f"PASS: found in {path}.\n...{snippet}..."
    return f"FAIL: {expected_substring!r} not found in {path}."


@mcp.tool()
def verify_file_absent(path: str) -> str:
    """Self-check: confirm a file/path does NOT exist (e.g. after a delete/move)."""
    return f"PASS: {path} does not exist." if not Path(path).exists() else f"FAIL: {path} still exists."


@mcp.tool()
def verify_command_output(output: str, expected_pattern: str, use_regex: bool = True) -> str:
    """
    Self-check: verify that captured command output matches an expected
    pattern (regex by default, or a plain substring if use_regex=False)
    before treating a command as having succeeded.
    """
    try:
        matched = bool(re.search(expected_pattern, output)) if use_regex else (expected_pattern in output)
    except re.error as e:
        return f"FAIL: bad regex {expected_pattern!r}: {e}"
    return "PASS: pattern found in output." if matched else f"FAIL: pattern {expected_pattern!r} not found in output."


@mcp.tool()
def verify_no_error_markers(output: str, extra_markers: Optional[list[str]] = None) -> str:
    """
    Self-check: scan command/log output for common failure markers
    (Traceback, Exception, permission denied, non-zero exit code, etc.)
    so success isn't assumed just because a command returned some text.
    """
    markers = ["traceback (most recent call last)", "exception", "fatal error", "syntax error",
               "permission denied", "command not found", "modulenotfounderror"]
    markers += [m.lower() for m in (extra_markers or [])]
    lower = output.lower()
    hits = [m for m in markers if m in lower]
    m = re.search(r"\[exit code:\s*(-?\d+)\]", output)
    if m and m.group(1) != "0":
        hits.append(f"non-zero exit code ({m.group(1)})")
    return f"FAIL: found error markers: {hits}" if hits else "PASS: no known error markers found."


# =========================================================
# FAILURE RECOVERY
# =========================================================
@mcp.tool()
async def run_cmd_resilient(command: str, hidden: bool = True, timeout_ms: int = 30_000,
                             max_retries: int = 2, backoff_ms: int = 1000,
                             retry_on_patterns: Optional[list[str]] = None,
                             ctx: Optional[Context] = None) -> str:
    """
    Like run_cmd, but automatically retries on failure (non-zero exit,
    timeout, or any of retry_on_patterns found in output) with exponential
    backoff, up to max_retries attempts. Returns the last attempt's output
    plus a retry-attempt summary. Use this instead of plain run_cmd for
    flaky operations (network calls, file locks, transient services).
    """
    if _invokes_powershell(command):
        return _POWERSHELL_GUARD_MSG
    ok, reason = validate_shell_command(command)
    if not ok:
        return reason
    patterns = [p.lower() for p in (retry_on_patterns or [])]
    attempts_log = []
    delay = backoff_ms
    result = ""
    for attempt in range(1, max_retries + 2):
        result = await _run(_cmd_argv(command), hidden, timeout_ms, "cmd", False, ctx, command)
        failed = "[exit code: 0]" not in result or any(p in result.lower() for p in patterns)
        attempts_log.append(f"attempt {attempt}: {'FAILED' if failed else 'OK'}")
        if not failed:
            break
        if attempt <= max_retries:
            await asyncio.sleep(delay / 1000)
            delay *= 2
    summary = "\n".join(attempts_log)
    return f"[retry log]\n{summary}\n\n[final output]\n{result}"


# =========================================================
# TOOL SELECTION INTELLIGENCE
# =========================================================
_TOOL_REGISTRY = {
    "run_cmd": "run a one-off Windows cmd.exe command",
    "run_pwr": "run a PowerShell command or script",
    "run_cmd_resilient": "run a cmd.exe command with automatic retry/backoff for flaky operations",
    "run_process": "launch a GUI application directly, not a shell command",
    "find_pid": "look up running processes by name",
    "close_pid": "force-kill a process by pid",
    "validate_shell_command": "validate a shell command against the host-modification blacklist before execution",
    "create_directory": "create a directory tree",
    "list_directory": "list files and folders in a path",
    "list_directory_with_sizes": "list files/folders with sizes and totals",
    "directory_tree": "recursive JSON tree of a folder",
    "move_file": "move or rename a file or directory",
    "search_files": "recursively glob-search a directory for matching files",
    "get_file_info": "get size/timestamp/type metadata for a path",
    "list_allowed_directories": "see which directories this server can touch",
    "vm_import": "push a Windows file/directory into a WSL sandbox distro (Windows -> WSL), with CRLF->LF sanitization",
    "vm_export": "pull a file/directory from a WSL sandbox back to Windows, then trash the source in the VM (WSL -> Windows)",
    "vm_exec": "run a shell command inside an open WSL sandbox VM session by vm_id, mirrored into the shared session log with vm_show",
    "vm_show": "open a visible console window into an already-open vm() session",
    "list_vms": "list all currently open VM sessions",
    "vm": "open a new WSL sandbox VM session on an installed distro",
    "close_vm": "close a VM session and drop its tracking table",
    "list_tables": "list SQLite tables",
    "describe_table": "get a SQLite table's schema",
    "create_table": "run a CREATE TABLE statement",
    "read_query": "run a SQLite SELECT query",
    "write_query": "run a SQLite INSERT, UPDATE, or DELETE",
    "read_vm_query": "run a SQLite SELECT query against vm.db (the VM sessions database) instead of the main db",
    "append_insight": "jot a business insight to the session memo",
    "puppeteer_navigate": "open a URL in the automated browser",
    "puppeteer_click": "click an element in the automated browser",
    "puppeteer_fill": "fill a form field in the automated browser",
    "puppeteer_hover": "hover an element in the automated browser",
    "puppeteer_select": "choose a dropdown option in the automated browser",
    "puppeteer_evaluate": "run JavaScript in the automated browser and get the result",
    "puppeteer_screenshot": "screenshot the current automated browser page",
    "sequential_thinking": "record one step of a multi-step reasoning or planning chain",
    "get_thinking_session": "review a sequential_thinking session's full chain",
    "clear_thinking_session": "reset a sequential_thinking session",
    "memory_save": "store a durable fact or preference across sessions",
    "memory_recall": "look up one durable memory by exact key",
    "memory_search": "search durable memories by substring",
    "memory_list": "list all durable memory keys",
    "memory_delete": "delete a durable memory",
    "checkpoint_save": "save task progress state so it can be resumed later",
    "checkpoint_list": "list saved task checkpoints",
    "checkpoint_restore": "load a saved checkpoint's state back",
    "checkpoint_delete": "delete a saved checkpoint",
    "verify_file_contains": "self-check that a file contains expected text after editing it",
    "verify_file_absent": "self-check that a path no longer exists after deleting or moving it",
    "verify_command_output": "self-check that command output matches an expected pattern",
    "verify_no_error_markers": "scan output for common failure or error markers",
    "get_environment_info": "inspect the current OS, host, runtime, and allowed-directory context",
    "get_metadata": "structured JSON of user/machine/session/paths/runtime/voidTool config",
    "get_git_status": "check git branch and status for a repo path, if any",
    "github_login": "save a GitHub personal access token, encrypted at rest",
    "github_logout": "delete the saved GitHub token",
    "github_auth_status": "check whether a GitHub token is currently saved",
    "github_whoami": "show the currently authenticated GitHub user",
    "github_list_repos": "list the authenticated user's GitHub repositories",
    "github_get_repo": "get details for a specific GitHub repository",
    "github_list_issues": "list issues in a GitHub repository",
    "github_create_issue": "create a new issue in a GitHub repository",
    "github_comment_issue": "comment on a GitHub issue or pull request",
    "github_list_pull_requests": "list pull requests in a GitHub repository",
    "github_get_pull_request": "get details for a specific GitHub pull request",
    "github_list_workflow_runs": "list recent GitHub Actions workflow runs",
    "github_trigger_workflow": "trigger a GitHub Actions workflow_dispatch run",
    "github_get_file": "read a file's contents from a GitHub repository",
    "github_search_repos": "search GitHub repositories",
    "github_search_code": "search code across GitHub",
    "github_create_repo": "create a new GitHub repository",
    "github_update_repo": "update settings on an existing GitHub repository",
    "github_delete_repo": "permanently delete a GitHub repository (requires confirm=True)",
    "github_api": "call any GitHub REST API endpoint directly -- full API surface, limited only by token scopes",
    "github_push": "push local commits to GitHub using the saved token for auth",
    "github_pull": "pull from GitHub using the saved token for auth",
    "git_commit": "stage and commit changes in a local git repo (no shell-quoting issues)",
}


@mcp.tool()
def suggest_tool(task_description: str, top_n: int = 5) -> str:
    """
    Given a plain-English description of what you're trying to do, rank
    this server's own tools by keyword relevance so you pick the right
    one instead of guessing or defaulting to a shell command for
    everything. Not a substitute for reading a tool's own docstring once
    you've picked it.
    """
    words = set(re.findall(r"[a-z0-9]+", task_description.lower()))
    scored = []
    for name, desc in _TOOL_REGISTRY.items():
        desc_words = set(re.findall(r"[a-z0-9]+", (name + " " + desc).lower()))
        overlap = words & desc_words
        if overlap:
            scored.append((len(overlap), name, desc))
    scored.sort(key=lambda t: -t[0])
    if not scored:
        return ("No strong keyword match. Consider: get_environment_info (to orient) or "
                "sequential_thinking (to plan), then browse the tool list directly.")
    return "\n".join(f"{name} (score {score}): {desc}" for score, name, desc in scored[:top_n])


# =========================================================
# ENVIRONMENT AWARENESS
# =========================================================
@mcp.tool()
def get_environment_info() -> str:
    """
    Report the current runtime context: OS/platform, Python version,
    hostname, cwd, allowed directories, DB path, disk space on each
    allowed drive, and current UTC/local time. Call this at the start of
    a task when you're unsure what machine/environment you're operating
    in, or before making assumptions about paths.
    """
    info = {
        "os": platform.platform(),
        "python_version": platform.python_version(),
        "hostname": platform.node(),
        "cwd": str(Path.cwd()),
        "allowed_directories": [str(a) for a in ALLOWED_DIRS],
        "db_path": DB_PATH,
        "utc_time": datetime.now(timezone.utc).isoformat(),
        "local_time": datetime.now().isoformat(),
        "tracked_processes": len(_running),
    }
    disk = {}
    for a in ALLOWED_DIRS:
        try:
            if a.exists():
                total, used, free = shutil.disk_usage(str(a))
                disk[str(a)] = f"{free // (1024**3)}GB free / {total // (1024**3)}GB total"
        except OSError:
            continue
    info["disk_space"] = disk
    return json.dumps(info, indent=2)


@mcp.tool()
def get_metadata() -> str:
    """
    Report structured metadata about the current user, machine, session,
    and runtime -- plus voidTool's own config -- so the model doesn't have
    to guess paths or environment details. Complements get_environment_info
    (OS/runtime/disk diagnostics); this is user/session/paths/runtime/
    voidTool-specific context. Never dumps raw environment variables and
    never exposes values that look like secrets, tokens, or credentials --
    only specific known-safe path variables are read.
    """

    def _safe_run(argv: list[str], timeout: float = 3.0) -> Optional[str]:
        try:
            startupinfo, creationflags = _startupinfo_and_flags(True)
            result = subprocess.run(
                argv, capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=timeout, startupinfo=startupinfo, creationflags=creationflags,
            )
            out = (result.stdout or "").strip() or (result.stderr or "").strip()
            return out.splitlines()[0].strip() if out else None
        except (OSError, subprocess.TimeoutExpired, FileNotFoundError):
            return None

    userprofile = os.environ.get("USERPROFILE")

    def _subdir(name: str) -> Optional[str]:
        if not userprofile:
            return None
        p = Path(userprofile) / name
        return str(p) if p.exists() else f"{p} (not found)"

    user = {
        "username": os.environ.get("USERNAME"),
        "user_profile_directory": userprofile,
        "home_directory": str(Path.home()),
    }

    machine = {
        "hostname": platform.node(),
        "computer_name": os.environ.get("COMPUTERNAME"),
        "operating_system": platform.system(),
        "os_version": platform.version(),
        "architecture": platform.machine(),
    }

    session = {
        "current_working_directory": str(Path.cwd()),
        "temp_directory": os.environ.get("TEMP") or os.environ.get("TMP"),
        "local_app_data": os.environ.get("LOCALAPPDATA"),
        "app_data": os.environ.get("APPDATA"),
        "program_data": os.environ.get("PROGRAMDATA"),
        "desktop_directory": _subdir("Desktop"),
        "documents_directory": _subdir("Documents"),
        "downloads_directory": _subdir("Downloads"),
    }

    cmd_available = shutil.which("cmd.exe") is not None or Path(r"C:\Windows\System32\cmd.exe").exists()

    runtime = {
        "python_version": platform.python_version(),
        "java_version": _safe_run(["java", "-version"]) or "not found",
        "git_version": _safe_run(["git", "--version"]) or "not found",
        "powershell_version": _safe_run([
            "powershell.exe", "-NoProfile", "-NonInteractive", "-Command",
            "$PSVersionTable.PSVersion.ToString()",
        ]) or "not found",
        "cmd_available": cmd_available,
    }

    try:
        github_authenticated = _load_secret("github_token") is not None
    except Exception:
        github_authenticated = False

    voidtool_info = {
        "voidtool_version": __version__,
        "database_path": DB_PATH,
        "allowed_directories": [
            (str(a) if a.exists() else f"{a} (not found)") for a in ALLOWED_DIRS
        ],
        "tracked_processes": len(_running),
        "github_authenticated": github_authenticated,
        "server_name": "voidTool",
    }

    return json.dumps({
        "user": user,
        "machine": machine,
        "session": session,
        "runtime": runtime,
        "voidtool": voidtool_info,
    }, indent=2)


@mcp.tool()
def get_git_status(path: str) -> str:
    """
    If `path` is inside a git repo, report the current branch, whether the
    working tree is dirty, and a short list of changed files. Returns a
    clear message if it's not a git repo. Useful for orienting before
    making file edits.
    """
    p = _check_allowed(path)
    try:
        branch = subprocess.check_output(
            ["git", "-C", str(p), "rev-parse", "--abbrev-ref", "HEAD"],
            text=True, encoding="utf-8", errors="replace", stderr=subprocess.STDOUT,
        ).strip()
    except subprocess.CalledProcessError as e:
        return f"Not a git repo (or git error) at {path}: {e.output.strip()}"
    except FileNotFoundError:
        return "git executable not found on PATH."
    status = subprocess.check_output(
        ["git", "-C", str(p), "status", "--porcelain"],
        text=True, encoding="utf-8", errors="replace",
    ).strip()
    lines = [f"branch: {branch}"]
    if status:
        changed = status.splitlines()
        lines.append(f"dirty: {len(changed)} changed file(s)")
        lines.extend(f"  {c}" for c in changed[:20])
        if len(changed) > 20:
            lines.append(f"  ... and {len(changed) - 20} more")
    else:
        lines.append("clean working tree")
    return "\n".join(lines)


def _authenticated_remote_url(path: Path, remote: str) -> tuple[str, str]:
    """Return (original_url, token_embedded_url) for `remote` in the repo at `path`."""
    original = subprocess.check_output(
        ["git", "-C", str(path), "remote", "get-url", remote],
        text=True, encoding="utf-8", errors="replace",
    ).strip()
    token = _load_secret("github_token")
    if not token:
        raise PermissionError("Not logged in to GitHub. Call github_login(token=...) first.")
    m = re.match(r"^https://(?:[^@]+@)?github\.com/(.+)$", original)
    if not m:
        raise ValueError(f"Remote {remote!r} ({original}) is not a plain https://github.com/... URL -- "
                         f"can't safely inject a token. Set it up manually or use github_api instead.")
    authed = f"https://x-access-token:{token}@github.com/{m.group(1)}"
    return original, authed


@mcp.tool()
def github_push(path: str, remote: str = "origin", branch: Optional[str] = None, set_upstream: bool = False) -> str:
    """
    Push local commits to GitHub using the saved token for auth (no need
    for a separately configured git credential helper). Temporarily
    rewrites the remote's URL to embed the token for just this push, then
    restores the original URL afterward -- the token is never left sitting
    in .git/config. `branch` defaults to the current branch. Set
    set_upstream=True on a branch's first push to set tracking.
    """
    p = _check_allowed(path)
    if branch is None:
        branch = subprocess.check_output(
            ["git", "-C", str(p), "rev-parse", "--abbrev-ref", "HEAD"],
            text=True, encoding="utf-8", errors="replace",
        ).strip()
    original, authed = _authenticated_remote_url(p, remote)
    try:
        subprocess.check_call(["git", "-C", str(p), "remote", "set-url", remote, authed])
        argv = ["git", "-C", str(p), "push", remote, branch]
        if set_upstream:
            argv.insert(4, "-u")
        result = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8", errors="replace")
        output = (result.stdout + result.stderr).strip()
        if result.returncode != 0:
            return f"FAIL (exit {result.returncode}):\n{output}"
        return f"Pushed {branch} -> {remote}.\n{output}"
    finally:
        subprocess.check_call(["git", "-C", str(p), "remote", "set-url", remote, original])


@mcp.tool()
def github_pull(path: str, remote: str = "origin", branch: Optional[str] = None) -> str:
    """
    Pull from GitHub using the saved token for auth, same temporary-URL-
    swap approach as github_push (token is never left in .git/config).
    `branch` defaults to the current branch.
    """
    p = _check_allowed(path)
    if branch is None:
        branch = subprocess.check_output(
            ["git", "-C", str(p), "rev-parse", "--abbrev-ref", "HEAD"],
            text=True, encoding="utf-8", errors="replace",
        ).strip()
    original, authed = _authenticated_remote_url(p, remote)
    try:
        subprocess.check_call(["git", "-C", str(p), "remote", "set-url", remote, authed])
        result = subprocess.run(["git", "-C", str(p), "pull", remote, branch],
                                 capture_output=True, text=True, encoding="utf-8", errors="replace")
        output = (result.stdout + result.stderr).strip()
        if result.returncode != 0:
            return f"FAIL (exit {result.returncode}):\n{output}"
        return f"Pulled {branch} <- {remote}.\n{output}"
    finally:
        subprocess.check_call(["git", "-C", str(p), "remote", "set-url", remote, original])


@mcp.tool()
def git_commit(path: str, message: str, add_all: bool = True, files: Optional[list[str]] = None) -> str:
    """
    Stage and commit changes in a local git repo. By default (add_all=True)
    stages everything (git add -A); pass files=[...] to stage only specific
    paths instead. Runs with argv (no shell string parsing), so the commit
    message is passed through exactly as given -- no quoting issues.
    Author identity defaults to whatever git already has configured
    (user.name/user.email) for that repo; falls back to void01-n's
    noreply address if none is set.
    """
    p = _check_allowed(path)

    has_identity = subprocess.run(
        ["git", "-C", str(p), "config", "user.email"],
        capture_output=True, text=True,
    ).stdout.strip()

    if add_all:
        add_argv = ["git", "-C", str(p), "add", "-A"]
    else:
        add_argv = ["git", "-C", str(p), "add", "--"] + (files or [])
        if not files:
            return "FAIL: add_all=False but no files given."
    add_result = subprocess.run(add_argv, capture_output=True, text=True, encoding="utf-8", errors="replace")
    if add_result.returncode != 0:
        return f"FAIL (git add, exit {add_result.returncode}):\n{(add_result.stdout + add_result.stderr).strip()}"

    commit_argv = ["git", "-C", str(p)]
    if not has_identity:
        commit_argv += ["-c", "user.email=void01-n@users.noreply.github.com", "-c", "user.name=void01-n"]
    commit_argv += ["commit", "-m", message]

    commit_result = subprocess.run(commit_argv, capture_output=True, text=True, encoding="utf-8", errors="replace")
    output = (commit_result.stdout + commit_result.stderr).strip()
    if commit_result.returncode != 0:
        return f"FAIL (git commit, exit {commit_result.returncode}):\n{output}"
    return output


# =========================================================
# VM SESSIONS
# (one global vm()/close_vm() pair backed by the installed WSL distros.
#  Uses its OWN SQLite db -- vm.db, a sibling of the SQLITE subsystem's
#  db file -- kept separate from agent_memory/task_checkpoints/etc.
#  Each open session gets its own table (vm_session_<id>); vm() creates
#  it, close_vm() drops it. "Distro in USE!" is checked by scanning the
#  existing vm_session_* tables for that wsl_distro.)
# =========================================================
VM_DB_PATH = str(Path(DB_PATH).with_name("vm.db"))

_VM_DISTRO_ALIASES = {
    "arch": "archlinux", "archlinux": "archlinux",
    "debian": "Debian",
    "ubuntu": "Ubuntu",
    "fedora": "FedoraLinux-44",
    "opensuse": "openSUSE-Tumbleweed", "suse": "openSUSE-Tumbleweed", "tumbleweed": "openSUSE-Tumbleweed",
    "kali": "kali-linux",
    "alpine": "Alpine",
    "rocky": "Rocky", "rockylinux": "Rocky",
    "nixos": "NixOS", "nix": "NixOS",
    "pop": "Pop-OS", "popos": "Pop-OS", "pop_os": "Pop-OS",
}


def _vm_db():
    return sqlite3.connect(VM_DB_PATH)


def _disable_wsl_automount(wsl_distro: str) -> None:
    """
    Write /etc/wsl.conf inside `wsl_distro` with automount disabled, so
    Windows drives (C:, D:, or any other fixed drive) are NEVER mounted
    under /mnt/* for any VM opened via vm() -- there's no per-drive
    granularity in WSL's automount feature, so "enabled = false" is what
    covers both "Windows is never mounted" and "D:/ isn't automounted"
    in one setting. Also disables interop's appendWindowsPath, since with
    automount off it would otherwise try (and fail, noisily) to translate
    every Windows PATH entry into the Linux $PATH on each shell launch.
    wsl.conf is only read at instance boot, so this terminates the
    distro (if running) before writing, then terminates it again
    afterward so the NEXT `wsl.exe -d <distro>` boots fresh with the new
    config applied.
    """
    subprocess.run(["wsl.exe", "--terminate", wsl_distro], capture_output=True, text=True)
    conf = (
        "[automount]\n"
        "enabled = false\n"
        "mountFsTab = false\n"
        "\n"
        "[interop]\n"
        "appendWindowsPath = false\n"
    )
    write_cmd = "mkdir -p /etc && printf '%s' " + shlex.quote(conf) + " > /etc/wsl.conf"
    subprocess.run(
        ["wsl.exe", "-d", wsl_distro, "-u", "root", "--", "sh", "-c", write_cmd],
        capture_output=True, text=True,
    )
    subprocess.run(["wsl.exe", "--terminate", wsl_distro], capture_output=True, text=True)


def _vm_table_name(vm_id: str) -> str:
    # vm_id is validated as exactly 2 digits by every caller before this
    # is used to build a table name (table/column names can't be bound
    # as SQL parameters, so this check is what keeps it injection-safe).
    if not re.fullmatch(r"\d{2}", vm_id):
        raise ValueError(f"invalid vm_id {vm_id!r}: must be exactly 2 digits")
    return f"vm_session_{vm_id}"


def _list_vm_tables(conn) -> list[str]:
    rows = conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name LIKE 'vm\\_session\\___' ESCAPE '\\'"
    ).fetchall()
    return [r[0] for r in rows]


def _normalize_vm_distro(distro: str) -> Optional[str]:
    key = re.sub(r"[\s\-_]", "", distro.strip().lower())
    normalized = {re.sub(r"[\s\-_]", "", k): v for k, v in _VM_DISTRO_ALIASES.items()}
    return normalized.get(key)


def _next_vm_id(conn) -> Optional[str]:
    """
    Pick a free 2-digit vm_id (00-99) at random from whatever's not
    currently in use, rather than always handing out the lowest free
    slot -- so ids aren't a predictable/ordered sequence.
    """
    used = {t.replace("vm_session_", "") for t in _list_vm_tables(conn)}
    free = [f"{i:02d}" for i in range(100) if f"{i:02d}" not in used]
    if not free:
        return None
    return random.choice(free)


@mcp.tool()
def vm(name: str, distro: str) -> str:
    """
    Open a new VM session on an installed WSL distro. `name` is a label
    you choose for this session (what you're using/making it for);
    `distro` picks which WSL distribution backs it -- arch, debian,
    ubuntu, fedora, opensuse, kali, alpine, rocky, nixos, or pop
    (case/format insensitive). Only one open VM session per distro is
    allowed at a time (WSL runs one live instance of a given distro);
    if that distro already has an open session this refuses with "Distro in USE!"
    instead of opening a second one. On success returns a 2-digit vm_id
    (00-99) -- pass that to close_vm to shut it down later. Creates a
    dedicated table (vm_session_<id>) for this session in vm.db, a
    SQLite db kept separate from the SQLITE subsystem's own db file.

    Before launching, disables WSL automount for this distro (writes
    /etc/wsl.conf with [automount] enabled=false and restarts the
    distro) -- Windows drives (C:, D:, etc.) are never mounted under
    /mnt/* inside any VM opened this way. The session's shell also
    always starts in the Linux home directory (~), regardless of this
    server's own working directory.
    """
    wsl_distro = _normalize_vm_distro(distro)
    if wsl_distro is None:
        return f"FAIL: unknown distro {distro!r}. Known: " + ", ".join(sorted(set(_VM_DISTRO_ALIASES.values())))

    with _vm_db() as conn:
        for t in _list_vm_tables(conn):
            row = conn.execute(f"SELECT vm_id, name FROM {t} WHERE wsl_distro=?", (wsl_distro,)).fetchone()
            if row:
                return f"Distro in USE! ({wsl_distro} is already open as vm_id={row[0]}, name={row[1]!r})"

        vm_id = _next_vm_id(conn)
        if vm_id is None:
            return "FAIL: all 100 vm_id slots (00-99) are currently in use."
        table = _vm_table_name(vm_id)

        _disable_wsl_automount(wsl_distro)

        startupinfo, creationflags = _startupinfo_and_flags(True)
        proc = subprocess.Popen(
            ["wsl.exe", "-d", wsl_distro, "--cd", "~"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            cwd=str(DEFAULT_CWD),
            startupinfo=startupinfo, creationflags=creationflags,
        )
        _running[proc.pid] = {"proc": proc, "kind": "vm", "command": f"wsl -d {wsl_distro} --cd ~"}

        now = datetime.now(timezone.utc).isoformat()
        conn.execute(f"""
            CREATE TABLE {table} (
                vm_id TEXT, name TEXT, distro_input TEXT, wsl_distro TEXT,
                pid INTEGER, created_at TEXT
            )
        """)
        conn.execute(f"INSERT INTO {table} VALUES (?,?,?,?,?,?)",
                     (vm_id, name, distro, wsl_distro, proc.pid, now))
        conn.commit()

    return f"Opened vm_id={vm_id} name={name!r} distro={wsl_distro} (pid={proc.pid}). Use close_vm('{vm_id}') when done."


@mcp.tool()
def close_vm(vm_id: str) -> str:
    """
    Close a VM session by its 2-digit vm_id (as returned by vm()).
    Terminates the backing process and the WSL distro instance itself
    (wsl --terminate), then DROPS that session's table (vm_session_<id>)
    from vm.db entirely -- freeing that distro and that vm_id for reuse.
    """
    vm_id = vm_id.strip().zfill(2)
    if not re.fullmatch(r"\d{2}", vm_id):
        return f"FAIL: vm_id must be 2 digits, got {vm_id!r}."
    table = _vm_table_name(vm_id)

    with _vm_db() as conn:
        exists = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name=?", (table,)
        ).fetchone()
        if not exists:
            return f"FAIL: no open VM with vm_id={vm_id!r}."

        name, wsl_distro, pid = conn.execute(f"SELECT name, wsl_distro, pid FROM {table}").fetchone()

        entry = _running.pop(pid, None)
        if entry is not None:
            try:
                entry["proc"].terminate()
            except OSError:
                pass

        subprocess.run(["wsl.exe", "--terminate", wsl_distro], capture_output=True, text=True)

        conn.execute(f"DROP TABLE {table}")
        conn.commit()

    return f"Closed vm_id={vm_id} name={name!r} distro={wsl_distro}. (table {table} dropped)"


@mcp.tool()
def list_vms() -> str:
    """List all currently OPEN VM sessions (one row per vm_session_<id> table in vm.db)."""
    with _vm_db() as conn:
        tables = _list_vm_tables(conn)
        if not tables:
            return "(no open VM sessions)"
        lines = []
        for t in tables:
            v, n, d, c = conn.execute(f"SELECT vm_id, name, wsl_distro, created_at FROM {t}").fetchone()
            lines.append(f"vm_id={v} name={n!r} distro={d} opened={c}")
    return "\n".join(lines)


# Tokens that indicate a mount attempt inside vm_exec.
# Checked against the full command string (lowercased) before execution.
_VM_EXEC_MOUNT_PATTERNS: list[re.Pattern] = [
    re.compile(r'\bmount\b'),           # mount, umount, mountpoint
    re.compile(r'\bumount\b'),
    re.compile(r'\bmountpoint\b'),
    re.compile(r'\bdrvfs\b'),           # explicit DrvFs filesystem type
    re.compile(r'\b9p\b'),              # 9P / Plan 9 filesystem (WSL's P9NP)
    re.compile(r'\bvirtiofs\b'),        # virtio-fs (WSL2 alt transport)
    re.compile(r'\bfuse\b'),            # FUSE mounts
    re.compile(r'\bfusermount\b'),
    re.compile(r'\bsshfs\b'),
    re.compile(r'\bnfs\b'),
    re.compile(r'\bcifs\b'),
    re.compile(r'\bsmb\b'),
    re.compile(r'/proc/mounts'),        # reading mount table
    re.compile(r'/etc/fstab'),          # editing fstab = deferred mount
    re.compile(r'\bsystemctl\b.*mount', re.IGNORECASE),
    re.compile(r'\bautomount\b'),
    re.compile(r'\bauto[-_]?mount\b'),
    re.compile(r'--bind'),              # bind mounts
    re.compile(r'--rbind'),
    re.compile(r'-o\s+bind'),
    re.compile(r'\boverlay\b'),         # overlayfs (container-style mounts)
    re.compile(r'\btmpfs\b'),           # tmpfs mounts
    re.compile(r'\bdevtmpfs\b'),
    re.compile(r'\bsysfs\b'),
    re.compile(r'\bprocfs\b'),
    re.compile(r'\bcgroupfs\b'),
    re.compile(r'\bcgroup\b'),
    re.compile(r'\bnsenter\b'),         # namespace entry (can expose host mounts)
    re.compile(r'\bunshare\b'),         # mount namespace manipulation
    re.compile(r'\bchroot\b'),          # chroot with bind-mount tricks
    re.compile(r'\bpivot_root\b'),
    re.compile(r'wsl\.conf'),           # prevent re-enabling automount via wsl.conf edit
    re.compile(r'\bwslpath\b'),         # wslpath translates Windows paths (mount-adjacent)
]

_VM_EXEC_MOUNT_BLOCKED = (
    "BLOCKED: mount operations are not permitted inside vm_exec. "
    "Use vm_import/vm_export to move files between Windows and the VM."
)


def _vm_exec_check_mount(command: str) -> tuple[bool, str]:
    """Return (allowed, reason). Blocks any command that attempts a mount operation."""
    lower = command.lower()
    for pat in _VM_EXEC_MOUNT_PATTERNS:
        if pat.search(lower):
            return False, _VM_EXEC_MOUNT_BLOCKED
    return True, ""


@mcp.tool()
def vm_exec(vm_id: str, command: str, timeout_ms: int = 30_000, cwd: Optional[str] = None) -> str:
    """
    Run a shell command inside an open WSL sandbox VM session, identified
    by its 2-digit vm_id (as returned by vm()). Executes non-interactively
    as root via a direct sh invocation -- this is a one-shot exec against
    the distro (like vm_import/vm_export use internally), NOT the same
    live shell/pid that vm() opened, so a "cd" in a previous vm_exec call
    doesn't persist between calls; pass cwd to run this specific command
    from a given directory instead. Use list_vms() to see which vm_id's
    are currently open.

    By default this now mirrors: the command and its combined output are
    appended to a shared per-session log file inside the distro, the
    same log a vm_show() window for this vm_id writes its own activity
    into -- so a command run from either side becomes visible to the
    other via that shared history.

    Filesystem remount, bind, and namespace-escape attempts of any kind
    are rejected before the command reaches the distro (see the guard
    list defined just above this function). Use vm_import and vm_export
    to move files between Windows and the VM instead.

    Args:
        vm_id:      The 2-digit id of the open VM session (from vm()).
        command:    Shell command (sh syntax) to run inside the distro.
        timeout_ms: Kill the command and return if it hasn't finished
                    within this many milliseconds (default 30000).
        cwd:        Optional directory inside the distro to run the
                    command from (defaults to wherever sh -c lands,
                    normally the invoking user's home).

    Returns combined stdout, then stderr (if any) under a [stderr]
    marker, then an [exit code: N] line.
    """
    allowed, reason = _vm_exec_check_mount(command)
    if not allowed:
        return reason

    wsl_distro = _resolve_vm_distro(vm_id)
    log_path = _vm_session_log_path(vm_id)
    inner = command if cwd is None else f"cd {shlex.quote(cwd)} && {command}"
    marker_line = f"$ {command}"
    sh = (
        "{ printf '%s\n' " + repr(marker_line).replace("'", "'\''") + "; "
        + inner + "; } 2>&1 | tee -a " + repr(log_path).replace("'", "'\''")
    )
    timeout_s = max(1, timeout_ms // 1000)
    try:
        rc, out, err = _wsl_run(wsl_distro, sh, timeout=timeout_s)
    except subprocess.TimeoutExpired:
        return f"[timed out after {timeout_ms}ms]"
    parts = []
    if out:
        parts.append(out)
    if err:
        parts.append("[stderr]\n" + err)
    parts.append(f"[exit code: {rc}]")
    return "\n".join(parts)



def _vm_session_log_path(vm_id: str) -> str:
    """Shared session log path inside the distro for a given vm_id. vm_exec
    appends every command and its output here, and vm_show's window tees
    everything IT runs here too, so both surfaces build one shared history
    instead of being two disconnected views into the same distro."""
    return f"~/.voidtool_session_log_{vm_id}"


@mcp.tool()
def vm_show(pid: int) -> str:
    """
    Open a new, VISIBLE console window into an already-open vm() session,
    identified by that session's pid (as returned by vm() or list_vms --
    note list_vms doesn't print pid directly, use vm()'s own return value
    or check vm.db). The original hidden session keeps running untouched;
    this just spawns a second, visible `wsl -d <distro>` window onto the
    SAME distro so you can see/interact with it directly. Only works for
    a pid that's actually tracked as an open VM session in vm.db -- this
    won't open a window for an arbitrary/unrelated pid.
    """
    with _vm_db() as conn:
        match = None
        for t in _list_vm_tables(conn):
            row = conn.execute(f"SELECT vm_id, name, wsl_distro, pid FROM {t} WHERE pid=?", (pid,)).fetchone()
            if row:
                match = row
                break
    if match is None:
        return f"FAIL: pid {pid} is not tracked as an open VM session (check list_vms/vm.db)."
    vm_id, name, wsl_distro, tracked_pid = match

    log_path = _vm_session_log_path(vm_id)
    tee_wrapper = f"exec > >(tee -a {shlex.quote(log_path)}) 2>&1; exec bash -i"
    try:
        proc = subprocess.Popen(
            ["wsl.exe", "-d", wsl_distro, "--cd", "~", "--", "bash", "-c", tee_wrapper],
            cwd=str(DEFAULT_CWD),
            creationflags=subprocess.CREATE_NEW_CONSOLE,
        )
    except OSError as e:
        return f"FAIL: could not open a window for {wsl_distro}: {e}"

    return (f"Opened a visible window for vm_id={vm_id} name={name!r} distro={wsl_distro} "
            f"(session pid={tracked_pid}, window pid={proc.pid}).")


@mcp.tool()
def read_vm_query(query: str) -> str:
    """
    Execute a SELECT query against vm.db (VM_DB_PATH) -- the VM sessions
    database used by vm()/close_vm()/list_vms(), kept separate from the
    main SQLITE subsystem's db (DB_PATH/claude-agent.db). Use this
    instead of read_query to inspect vm_session_<id> tables directly
    (e.g. after vm() opens a session) -- read_query only ever sees the
    main db and will report "no such table" for anything vm-session-
    related.
    """
    with _vm_db() as conn:
        rows = conn.execute(query).fetchall()
    return "\n".join(str(r) for r in rows) if rows else "(no rows)"


# =========================================================
# VM PAYLOAD TRANSFER  (Windows <-> WSL sandbox)
# =========================================================
_VM_TRASH_DIR = "~/.voidtool_trash"
_VM_TRASH_MAX_DAYS = 30


def _wsl_zip_export(wsl_distro: str, vm_path: str, win_dest: Path, timeout: int = 120) -> tuple[bool, str]:
    """
    Export `vm_path` from WSL to Windows.
    - Single file: raw cat over stdout, no archive overhead.
    - Directory: tar (no compression, --stored) piped over stdout, extracted with stdlib tarfile.
    No Windows network (UNC) path is ever touched.
    """
    src_name = Path(vm_path).name
    parent = vm_path.rsplit("/", 1)[0] or "/"
    startupinfo, creationflags = _startupinfo_and_flags(True)

    # Check whether source is a file or directory
    rc_type, out_type, _ = _wsl_run(wsl_distro, f"test -f {shlex.quote(vm_path)} && echo file || echo dir", timeout=15)
    is_file = out_type.strip() == "file"

    if is_file:
        # Fast path: raw bytes over stdout, no archive at all
        pull = subprocess.run(
            ["wsl.exe", "-d", wsl_distro, "-u", "root", "--", "cat", vm_path],
            capture_output=True, timeout=timeout, cwd=str(DEFAULT_CWD),
            startupinfo=startupinfo, creationflags=creationflags,
        )
        if pull.returncode != 0:
            return False, pull.stderr.decode("utf-8", errors="replace").strip()
        win_dest.mkdir(parents=True, exist_ok=True)
        (win_dest / src_name).write_bytes(pull.stdout)
    else:
        # Directory: tar with no compression piped over stdout
        pull = subprocess.run(
            ["wsl.exe", "-d", wsl_distro, "-u", "root", "--", "sh", "-c",
             f"tar -C {shlex.quote(parent)} --no-auto-compress -cf - {shlex.quote(src_name)}"],
            capture_output=True, timeout=timeout, cwd=str(DEFAULT_CWD),
            startupinfo=startupinfo, creationflags=creationflags,
        )
        if pull.returncode != 0:
            return False, pull.stderr.decode("utf-8", errors="replace").strip()
        win_dest.mkdir(parents=True, exist_ok=True)
        import tarfile, io
        with tarfile.open(fileobj=io.BytesIO(pull.stdout), mode="r:") as tf:
            tf.extractall(str(win_dest))
    return True, ""


def _wsl_run(wsl_distro: str, sh: str, timeout: int = 60) -> tuple[int, str, str]:
    """Run a sh -c command inside a WSL distro as root. Returns (returncode, stdout, stderr)."""
    startupinfo, creationflags = _startupinfo_and_flags(True)
    r = subprocess.run(
        ["wsl.exe", "-d", wsl_distro, "-u", "root", "--", "sh", "-c", sh],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        timeout=timeout, cwd=str(DEFAULT_CWD),
        startupinfo=startupinfo, creationflags=creationflags,
    )
    return r.returncode, r.stdout.strip(), r.stderr.strip()


def _wsl_trash_sweep(wsl_distro: str) -> None:
    """
    Lazily sweep ~/.voidtool_trash inside `wsl_distro`, deleting anything
    older than _VM_TRASH_MAX_DAYS days. Called at the start of every
    vm_export / vm_import so there is no cron/systemd dependency.
    """
    sweep = (
        f"mkdir -p {_VM_TRASH_DIR} && "
        f"find {_VM_TRASH_DIR} -maxdepth 1 -mindepth 1 "
        f"-mtime +{_VM_TRASH_MAX_DAYS} -exec rm -rf {{}} \\;"
    )
    try:
        _wsl_run(wsl_distro, sweep, timeout=30)
    except Exception:
        pass  # sweep failure is non-fatal


def _resolve_vm_distro(vm_id: str) -> str:
    """Look up the wsl_distro for an open vm_id. Raises ValueError if not found."""
    vm_id = vm_id.strip().zfill(2)
    if not re.fullmatch(r"\d{2}", vm_id):
        raise ValueError(f"vm_id must be 2 digits, got {vm_id!r}")
    table = _vm_table_name(vm_id)
    with _vm_db() as conn:
        exists = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name=?", (table,)
        ).fetchone()
        if not exists:
            raise ValueError(f"No open VM with vm_id={vm_id!r}. Use list_vms() to see open sessions.")
        row = conn.execute(f"SELECT wsl_distro FROM {table}").fetchone()
    return row[0]


def _wsl_zip_import(wsl_distro: str, src: Path, vm_dest_dir: str, timeout: int = 120) -> tuple[bool, str]:
    """
    Import `src` (file or directory) from Windows into WSL.
    - Single file: raw cat over stdin, no archive overhead.
    - Directory: tar (no compression) piped over stdin, extracted inside the distro.
    No Windows network (UNC) path is ever touched.
    """
    startupinfo, creationflags = _startupinfo_and_flags(True)

    if src.is_file():
        # Fast path: pipe raw bytes straight into the destination file
        file_bytes = src.read_bytes()
        dest_file = vm_dest_dir.rstrip("/") + "/" + src.name
        push = subprocess.run(
            ["wsl.exe", "-d", wsl_distro, "-u", "root", "--", "sh", "-c",
             f"mkdir -p {shlex.quote(vm_dest_dir)} && cat > {shlex.quote(dest_file)}"],
            input=file_bytes, capture_output=True, timeout=timeout, cwd=str(DEFAULT_CWD),
            startupinfo=startupinfo, creationflags=creationflags,
        )
        if push.returncode != 0:
            return False, push.stderr.decode("utf-8", errors="replace").strip()
    else:
        # Directory: build an uncompressed tar locally, pipe it into tar -x inside WSL
        import tarfile, io
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:") as tf:
            tf.add(str(src), arcname=src.name)
        tar_bytes = buf.getvalue()

        push = subprocess.run(
            ["wsl.exe", "-d", wsl_distro, "-u", "root", "--", "sh", "-c",
             f"mkdir -p {shlex.quote(vm_dest_dir)} && tar -C {shlex.quote(vm_dest_dir)} -xf -"],
            input=tar_bytes, capture_output=True, timeout=timeout, cwd=str(DEFAULT_CWD),
            startupinfo=startupinfo, creationflags=creationflags,
        )
        if push.returncode != 0:
            return False, push.stderr.decode("utf-8", errors="replace").strip()
    return True, ""


@mcp.tool()
def vm_import(vm_id: str, windows_path: str, vm_dest_dir: str,
              sanitize_line_endings: bool = True) -> str:
    """
    Push a file or directory from Windows into an open WSL sandbox distro
    (Windows -> WSL). No archive staging and no compression: a single file
    is piped straight into the distro via wsl.exe's stdin (cat > dest), and
    a directory is packed with an uncompressed tar and piped in the same
    way (tar -xf - inside the distro) -- one mechanism, streamed directly,
    no intermediate zip file written to disk. No Windows network (UNC)
    path is touched, avoiding the automount dependency (automount is
    disabled for all vm() sessions).

    Args:
        vm_id:                  The 2-digit id of the open VM session (from vm()).
        windows_path:           Absolute Windows path to the source file or directory.
        vm_dest_dir:            Destination directory path inside the WSL distro
                                (e.g. "/home/user/payloads"). Created if it doesn't exist.
        sanitize_line_endings:  If True (default), convert \\r\\n -> \\n in all text
                                files after transfer. Binary files are left untouched.

    """
    wsl_distro = _resolve_vm_distro(vm_id)
    _wsl_trash_sweep(wsl_distro)

    src = Path(windows_path)
    if not src.exists():
        return f"FAIL: source path does not exist: {windows_path}"

    ok, err = _wsl_zip_import(wsl_distro, src, vm_dest_dir)
    if not ok:
        return f"FAIL: copy to [{wsl_distro}]:{vm_dest_dir} failed: {err}"

    result_lines = [f"Imported {windows_path} -> [{wsl_distro}]:{vm_dest_dir}/{src.name}"]

    if sanitize_line_endings:
        target = vm_dest_dir.rstrip("/") + "/" + src.name
        if src.is_dir():
            sanitize_sh = (
                f"find {shlex.quote(target)} -type f | while IFS= read -r f; do "
                f"  ft=$(file -b --mime-encoding \"$f\"); "
                f"  case \"$ft\" in us-ascii|utf-8|iso-8859*|unknown-8bit) sed -i 's/\\r$//' \"$f\";; esac; "
                f"done"
            )
        else:
            sanitize_sh = (
                f"ft=$(file -b --mime-encoding {shlex.quote(target)}); "
                f"case \"$ft\" in us-ascii|utf-8|iso-8859*|unknown-8bit) "
                f"sed -i 's/\\r$//' {shlex.quote(target)};; esac"
            )
        rc2, _, err2 = _wsl_run(wsl_distro, sanitize_sh, timeout=60)
        if rc2 == 0:
            result_lines.append("Line endings sanitized (CRLF -> LF).")
        else:
            result_lines.append(f"Warning: line-ending sanitization failed: {err2}")

    return "\n".join(result_lines)


@mcp.tool()
def vm_export(vm_id: str, vm_path: str, windows_dest_dir: str) -> str:
    """
    Pull a file or directory from an open WSL sandbox back to Windows,
    then move the source into the VM's trash bin (~/.voidtool_trash) for
    automatic 30-day cleanup (WSL -> Windows + self-clean). No archive
    staging and no compression: a single file is piped straight out over
    wsl.exe's stdout (cat) and written to disk as-is; a directory is
    packed with an uncompressed tar inside the distro and streamed out the
    same way, extracted locally with stdlib tarfile -- one mechanism, no
    intermediate zip file. No Windows network (UNC) path is ever touched.

    Args:
        vm_id:            The 2-digit id of the open VM session (from vm()).
        vm_path:          Absolute path to the file or directory inside the
                          WSL distro (e.g. "/home/user/output/result.tar").
        windows_dest_dir: Destination directory on Windows (must be within
                          ALLOWED_DIRS). Created if it doesn't exist.

    The source is NOT permanently deleted -- it is moved into
    ~/.voidtool_trash/<timestamp>-<name> inside the VM. Anything in that
    trash folder older than 30 days is swept on the next vm_export or
    vm_import call (lazy, no cron/systemd needed).
    """
    wsl_distro = _resolve_vm_distro(vm_id)
    _wsl_trash_sweep(wsl_distro)

    win_dest = _check_allowed(windows_dest_dir)
    win_dest.mkdir(parents=True, exist_ok=True)

    src_name = Path(vm_path).name

    rc_exists, out_exists, _ = _wsl_run(wsl_distro, f"test -e {shlex.quote(vm_path)} && echo yes || echo no", timeout=15)
    if out_exists.strip() != "yes":
        return f"FAIL: {vm_path} does not exist inside [{wsl_distro}]."

    ok, err = _wsl_zip_export(wsl_distro, vm_path, win_dest)
    if not ok:
        return f"FAIL: copy from [{wsl_distro}]:{vm_path} failed: {err}"

    # Move source to trash inside the VM (30-day auto-clear)
    ts = datetime.now(timezone.utc).strftime("%Y%m%d%H%M%S")
    trash_target = f"{_VM_TRASH_DIR}/{ts}-{src_name}"
    sh_trash = (
        f"mkdir -p {_VM_TRASH_DIR} && "
        f"mv {shlex.quote(vm_path)} {shlex.quote(trash_target)}"
    )
    rc2, _, err2 = _wsl_run(wsl_distro, sh_trash, timeout=30)
    trash_note = (
        f"Source moved to [{wsl_distro}]:{trash_target} (auto-deleted after {_VM_TRASH_MAX_DAYS} days)."
        if rc2 == 0 else
        f"Warning: could not move source to trash: {err2}"
    )

    return (
        f"Exported [{wsl_distro}]:{vm_path} -> {win_dest / src_name}\n"
        + trash_note
    )


# =========================================================
# VM FILESYSTEM HTTP BRIDGE  (127.0.0.1:8888)
#
# Bypasses AtlasOS's stripped network provider stack entirely:
#   - No P9NP / 9P filesystem driver
#   - No SMB routing or UNC path resolution (\\wsl$, \\wsl.localhost)
#   - No DrvFs automounts (/mnt/c/ etc. -- disabled in wsl.conf by vm())
#
# Instead, streams raw binary over the wsl.exe process stdin/stdout
# pipeline directly into the Hyper-V socket layer, which survives even
# with every Windows Network Provider stripped out.  All data moves
# through a single 64 MB buffer per chunk -- no zip, no tar, no
# intermediate files on disk.
#
# Endpoints:
#   PUT /vm/{vm_id}/push?path=/abs/linux/path
#       Request body  = raw file bytes, streamed in 64 MB chunks.
#       Writes to `path` inside the distro backing vm_id.
#
#   GET /vm/{vm_id}/pull?path=/abs/linux/path
#       Response body = raw file bytes, streamed in 64 MB chunks.
#       Reads `path` from inside the distro backing vm_id.
#
#   GET /vms
#       JSON list of all open vm sessions (vm_id, name, distro).
#
# Routing is fully dynamic: vm_id resolves to whatever distro is
# currently open under that id via vm.db -- no static config needed.
#
# Security: binds ONLY on 127.0.0.1 (loopback).  A random 32-byte
# bearer token is generated at startup and stored in the DB under
# the key 'vm_bridge_token'; every request must supply it as
#   Authorization: Bearer <token>
# Any request missing or mismatching the token gets 401.
# =========================================================

_BRIDGE_CHUNK = 64 * 1024 * 1024   # 64 MB -- single read/write unit per pipe call
_BRIDGE_HOST  = "127.0.0.1"
_BRIDGE_PORT  = 8888
_BRIDGE_TOKEN_KEY = "vm_bridge_token"


def _bridge_token() -> str:
    """Return the bearer token for the HTTP bridge, generating it once on first call."""
    existing = _load_secret(_BRIDGE_TOKEN_KEY)
    if existing:
        return existing
    token = base64.urlsafe_b64encode(os.urandom(32)).decode()
    _save_secret(_BRIDGE_TOKEN_KEY, token)
    return token


def _bridge_resolve(vm_id: str) -> str:
    """Resolve vm_id -> wsl_distro, raising ValueError if not open."""
    return _resolve_vm_distro(vm_id)


async def _bridge_push(wsl_distro: str, vm_path: str, reader: asyncio.StreamReader) -> None:
    """
    Stream raw bytes from `reader` into `vm_path` inside `wsl_distro`.
    Uses wsl.exe stdin pipeline with _BRIDGE_CHUNK-sized reads.
    Path is passed as a positional argument (no shell interpolation).
    """
    startupinfo, creationflags = _startupinfo_and_flags(True)
    # Parent dir creation runs first as a separate, safe one-shot call.
    parent = vm_path.rsplit("/", 1)[0] or "/"
    _wsl_run(wsl_distro, f"mkdir -p {shlex.quote(parent)}", timeout=15)

    loop = asyncio.get_running_loop()
    proc = await loop.run_in_executor(None, lambda: subprocess.Popen(
        ["wsl.exe", "-d", wsl_distro, "-u", "root", "--", "bash", "-c",
         f"cat > {shlex.quote(vm_path)}"],
        stdin=subprocess.PIPE,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        cwd=str(DEFAULT_CWD),
        startupinfo=startupinfo,
        creationflags=creationflags,
    ))
    try:
        while True:
            chunk = await reader.read(_BRIDGE_CHUNK)
            if not chunk:
                break
            await loop.run_in_executor(None, proc.stdin.write, chunk)
        await loop.run_in_executor(None, proc.stdin.close)
        rc = await loop.run_in_executor(None, proc.wait)
        if rc != 0:
            err = proc.stderr.read().decode("utf-8", errors="replace").strip()
            raise RuntimeError(f"wsl write failed (exit {rc}): {err}")
    except Exception:
        proc.kill()
        raise


async def _bridge_pull(wsl_distro: str, vm_path: str, writer: asyncio.StreamWriter) -> None:
    """
    Stream raw bytes from `vm_path` inside `wsl_distro` into `writer`.
    Uses wsl.exe stdout pipeline with _BRIDGE_CHUNK-sized reads.
    """
    startupinfo, creationflags = _startupinfo_and_flags(True)
    loop = asyncio.get_running_loop()
    proc = await loop.run_in_executor(None, lambda: subprocess.Popen(
        ["wsl.exe", "-d", wsl_distro, "-u", "root", "--", "cat", vm_path],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=str(DEFAULT_CWD),
        startupinfo=startupinfo,
        creationflags=creationflags,
    ))
    try:
        while True:
            chunk = await loop.run_in_executor(None, proc.stdout.read, _BRIDGE_CHUNK)
            if not chunk:
                break
            writer.write(chunk)
            await writer.drain()
        rc = await loop.run_in_executor(None, proc.wait)
        if rc != 0:
            err = proc.stderr.read().decode("utf-8", errors="replace").strip()
            raise RuntimeError(f"wsl read failed (exit {rc}): {err}")
    except Exception:
        proc.kill()
        raise


def _parse_http_request(raw: bytes) -> tuple[str, str, dict, bytes]:
    """
    Minimal HTTP/1.1 request parser.
    Returns (method, path_with_query, headers_dict, body_bytes_so_far).
    Headers are lowercased.  body_bytes_so_far is whatever arrived after
    the blank line in the first read; the caller streams the rest.
    """
    sep = raw.find(b"\r\n\r\n")
    if sep == -1:
        raise ValueError("incomplete HTTP headers")
    header_block = raw[:sep].decode("utf-8", errors="replace")
    body_start   = raw[sep + 4:]
    lines = header_block.split("\r\n")
    req_line = lines[0].split(" ", 2)
    method = req_line[0].upper()
    path   = req_line[1] if len(req_line) > 1 else "/"
    headers = {}
    for line in lines[1:]:
        if ":" in line:
            k, _, v = line.partition(":")
            headers[k.strip().lower()] = v.strip()
    return method, path, headers, body_start


def _http_response(
    status: str,
    body: bytes = b"",
    content_type: str = "application/octet-stream",
    extra_headers: Optional[dict] = None,
) -> bytes:
    hdrs = [
        f"HTTP/1.1 {status}",
        f"Content-Length: {len(body)}",
        f"Content-Type: {content_type}",
        "Connection: close",
    ]
    for k, v in (extra_headers or {}).items():
        hdrs.append(f"{k}: {v}")
    return ("\r\n".join(hdrs) + "\r\n\r\n").encode() + body


def _http_stream_header(
    status: str = "200 OK",
    content_type: str = "application/octet-stream",
) -> bytes:
    """Return just the HTTP header for a chunked/streaming response (no Content-Length)."""
    return (
        f"HTTP/1.1 {status}\r\n"
        f"Content-Type: {content_type}\r\n"
        f"Connection: close\r\n"
        f"\r\n"
    ).encode()


async def _bridge_handle(reader: asyncio.StreamReader, writer: asyncio.StreamWriter) -> None:
    """
    Handle one incoming connection to the VM bridge server.
    Parses a minimal HTTP/1.1 request, checks the bearer token,
    dispatches to push/pull/list, then closes.
    """
    token = _bridge_token()
    try:
        raw = await asyncio.wait_for(reader.read(65536), timeout=10.0)
        if not raw:
            return

        try:
            method, path_qs, headers, body_initial = _parse_http_request(raw)
        except ValueError as e:
            writer.write(_http_response("400 Bad Request", str(e).encode()))
            await writer.drain()
            return

        # Auth check
        auth = headers.get("authorization", "")
        supplied = auth.removeprefix("Bearer ").strip()
        if supplied != token:
            writer.write(_http_response("401 Unauthorized", b"bad or missing token"))
            await writer.drain()
            return

        # Parse path and query string
        if "?" in path_qs:
            path_part, qs = path_qs.split("?", 1)
        else:
            path_part, qs = path_qs, ""
        params = dict(urllib.parse.parse_qsl(qs))

        # Route: GET /vms
        if method == "GET" and path_part.rstrip("/") == "/vms":
            with _vm_db() as conn:
                tables = _list_vm_tables(conn)
                sessions = []
                for t in tables:
                    row = conn.execute(
                        f"SELECT vm_id, name, wsl_distro FROM {t}"
                    ).fetchone()
                    if row:
                        sessions.append({"vm_id": row[0], "name": row[1], "distro": row[2]})
            body = json.dumps(sessions).encode()
            writer.write(_http_response("200 OK", body, "application/json"))
            await writer.drain()
            return

        # Route: /vm/{vm_id}/push  or  /vm/{vm_id}/pull
        m = re.fullmatch(r"/vm/([0-9]{1,2})/(push|pull)", path_part)
        if not m:
            writer.write(_http_response("404 Not Found", b"unknown endpoint"))
            await writer.drain()
            return

        vm_id   = m.group(1).zfill(2)
        action  = m.group(2)
        vm_path = params.get("path", "").strip()

        if not vm_path or not vm_path.startswith("/"):
            writer.write(_http_response("400 Bad Request", b"?path must be an absolute Linux path"))
            await writer.drain()
            return

        try:
            wsl_distro = _bridge_resolve(vm_id)
        except ValueError as e:
            writer.write(_http_response("404 Not Found", str(e).encode()))
            await writer.drain()
            return

        if action == "push" and method == "PUT":
            # Re-wrap reader: prepend body_initial bytes already consumed
            class _PrependedReader:
                def __init__(self, prefix: bytes, r: asyncio.StreamReader):
                    self._prefix = prefix
                    self._r = r
                async def read(self, n: int) -> bytes:
                    if self._prefix:
                        out, self._prefix = self._prefix[:n], self._prefix[n:]
                        return out
                    return await self._r.read(n)

            try:
                await _bridge_push(wsl_distro, vm_path, _PrependedReader(body_initial, reader))
                writer.write(_http_response("200 OK", b"ok", "text/plain"))
            except Exception as e:
                writer.write(_http_response("500 Internal Server Error", str(e).encode()))

        elif action == "pull" and method == "GET":
            writer.write(_http_stream_header())
            await writer.drain()
            try:
                await _bridge_pull(wsl_distro, vm_path, writer)
            except Exception as e:
                # Best-effort: stream has already started, just close
                pass

        else:
            writer.write(_http_response("405 Method Not Allowed", b"wrong method for action"))

        await writer.drain()

    except Exception:
        pass
    finally:
        try:
            writer.close()
            await writer.wait_closed()
        except Exception:
            pass


async def _bridge_serve() -> None:
    """Start the VM bridge HTTP server and run forever."""
    server = await asyncio.start_server(
        _bridge_handle,
        host=_BRIDGE_HOST,
        port=_BRIDGE_PORT,
        reuse_address=True,
    )
    token = _bridge_token()
    print(
        f"[vm-bridge] listening on http://{_BRIDGE_HOST}:{_BRIDGE_PORT}  "
        f"chunk={_BRIDGE_CHUNK // (1024*1024)}MB  "
        f"token={token[:8]}...  (full token in DB key '{_BRIDGE_TOKEN_KEY}')",
        flush=True,
    )
    async with server:
        await server.serve_forever()


@mcp.tool()
def vm_bridge_token() -> str:
    """
    Return the current bearer token for the VM filesystem bridge
    (http://127.0.0.1:8888).  Include it in every request as:
        Authorization: Bearer <token>
    The token is stored encrypted in the DB (same AES-256-GCM/DPAPI
    scheme as the GitHub token) and persists across restarts.
    To rotate: call vm_bridge_rotate_token().
    """
    return _bridge_token()


@mcp.tool()
def vm_bridge_rotate_token() -> str:
    """
    Generate and save a new random bearer token for the VM bridge,
    invalidating the old one immediately.  Any client holding the
    old token will start getting 401 on its next request.
    """
    new_token = base64.urlsafe_b64encode(os.urandom(32)).decode()
    _save_secret(_BRIDGE_TOKEN_KEY, new_token)
    return f"Rotated. New token starts with: {new_token[:8]}...  (full token in DB key '{_BRIDGE_TOKEN_KEY}')"


# =========================================================
# ENTRYPOINT
# =========================================================
if __name__ == "__main__":
    import threading

    def _run_bridge():
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        loop.run_until_complete(_bridge_serve())

    t = threading.Thread(target=_run_bridge, daemon=True, name="vm-bridge")
    t.start()

    mcp.run()