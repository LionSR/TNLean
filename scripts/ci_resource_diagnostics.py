#!/usr/bin/env python3
"""Bounded Linux resource samples, never build output or process arguments.

The sampler exits on parent death or cancellation without shell PID signalling.
A watchdog covers initialization, polling, sampling and close. Only closed,
owned output is eligible for the separate artifact publication step.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import signal
import stat
import tempfile
from pathlib import Path
import time

INTERVAL = 30
MAX_SAMPLES = 720
MAX_BYTES = 4 * 1024 * 1024
MAX_PROCESSES = 16
SNAPSHOT_SECONDS = 2
PROCESS_NAMES = frozenset({"lake", "lean", "leanc", "clang", "clang++", "cc", "cc1", "ld", "lld"})
MEMORY_KEYS = frozenset({"MemTotal", "MemAvailable", "SwapTotal", "SwapFree", "Dirty"})
EVENT_KEYS = frozenset({"low", "high", "max", "oom", "oom_kill", "oom_group_kill"})
CPU_KEYS = frozenset({"usage_usec", "user_usec", "system_usec", "nr_periods", "nr_throttled", "throttled_usec"})


def read_small(path: Path) -> str:
    with path.open(encoding="ascii") as stream:
        return stream.read(65536)


def numbers(path: Path, keys: frozenset[str]) -> dict[str, int] | None:
    try:
        result = {}
        for line in read_small(path).splitlines():
            fields = line.replace(":", "").split()
            if len(fields) >= 2 and fields[0] in keys:
                result[fields[0]] = int(fields[1])
        return result
    except (OSError, ValueError, UnicodeError):
        return None


def scalar(path: Path) -> int | str | None:
    try:
        text = read_small(path).strip()
        return "max" if text == "max" else int(text)
    except (OSError, ValueError, UnicodeError):
        return None


def process(path: Path) -> dict | None:
    """Read only /proc/PID/stat; never cmdline, environ, cwd or open files."""
    try:
        raw = read_small(path / "stat")
        opening, closing = raw.index("("), raw.rindex(")")
        fields = raw[closing + 2:].split()
        return {"pid": int(path.name), "name": raw[opening + 1:closing],
                "state": fields[0], "start_ticks": int(fields[19]),
                "cpu_ticks": int(fields[11]) + int(fields[12]),
                "rss_pages": int(fields[21])}
    except (OSError, ValueError, UnicodeError, IndexError):
        return None


def parent_alive(proc: Path, pid: int, start: int) -> bool:
    p = process(proc / str(pid))
    return p is not None and p["start_ticks"] == start and p["state"] not in {"Z", "X"}


def cgroup_dir(proc: Path, pid: int, root: Path) -> Path | None:
    """Find this process's v2 cgroup without recording its name/path."""
    try:
        for line in read_small(proc / str(pid) / "cgroup").splitlines():
            if line.startswith("0::/"):
                candidate = (root / line[4:]).resolve()
                if candidate.is_relative_to(root.resolve()):
                    return candidate
    except (OSError, ValueError, UnicodeError):
        pass
    return None


def sample(proc: Path, cgroup: Path | None, workspace: Path) -> dict:
    row = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
           "memory_kib": numbers(proc / "meminfo", MEMORY_KEYS)}
    try:
        fields = read_small(proc / "stat").splitlines()[0].split()
        row["cpu_ticks"] = dict(zip(
            ("user", "nice", "system", "idle", "iowait", "irq", "softirq", "steal"),
            [int(value) for value in fields[1:9]], strict=True))
    except (OSError, ValueError, UnicodeError, IndexError):
        row["cpu_ticks"] = None
    try:
        fields = read_small(proc / "loadavg").split()
        row["loadavg"] = [float(value) for value in fields[:3]]
    except (OSError, ValueError, UnicodeError):
        row["loadavg"] = None
    try:
        disk = os.statvfs(workspace)
        row["disk"] = {"total_bytes": disk.f_blocks * disk.f_frsize,
                       "available_bytes": disk.f_bavail * disk.f_frsize,
                       "available_inodes": disk.f_favail}
    except OSError:
        row["disk"] = None
    row["cgroup_v2"] = None if cgroup is None else {
        "memory_current_bytes": scalar(cgroup / "memory.current"),
        "memory_max_bytes": scalar(cgroup / "memory.max"),
        "memory_events": numbers(cgroup / "memory.events", EVENT_KEYS),
        "cpu_stat": numbers(cgroup / "cpu.stat", CPU_KEYS),
        "pids_current": scalar(cgroup / "pids.current"),
    }
    processes = []
    try:
        uptime = float(read_small(proc / "uptime").split()[0])
        ticks = os.sysconf("SC_CLK_TCK")
        pages = os.sysconf("SC_PAGE_SIZE")
        # Bound work even if a broken job creates many thousands of processes.
        with os.scandir(proc) as entries:
            for index, entry in enumerate(entries):
                if index >= 4096:
                    break
                if not entry.name.isdecimal():
                    continue
                p = process(proc / entry.name)
                if p is None or p["name"] not in PROCESS_NAMES:
                    continue
                processes.append({"pid": p["pid"], "name": p["name"],
                                  "start_ticks": p["start_ticks"],
                                  "cpu_seconds": round(p["cpu_ticks"] / ticks, 2),
                                  "elapsed_seconds": round(max(0, uptime - p["start_ticks"] / ticks), 2),
                                  "rss_bytes": max(0, p["rss_pages"] * pages)})
        row["observed_build_processes"] = len(processes)
        row["observed_build_rss_bytes"] = sum(p["rss_bytes"] for p in processes)
        # Fixed-size details: cumulative CPU leaders, with RSS breaking ties.
        row["processes"] = sorted(processes, key=lambda p: (p["cpu_seconds"], p["rss_bytes"]),
                                  reverse=True)[:MAX_PROCESSES]
    except (OSError, ValueError, UnicodeError, IndexError):
        row["observed_build_processes"] = None
        row["observed_build_rss_bytes"] = None
        row["processes"] = None
    return row


def notice(message: str) -> None:
    try:
        print(message, flush=True)
    except OSError:
        pass


def _monitor(output: Path, pid: int, proc: Path = Path("/proc"),
            cgroup_root: Path = Path("/sys/fs/cgroup"), workspace: Path = Path("."),
            interval: float = INTERVAL, max_samples: int = MAX_SAMPLES,
            max_bytes: int = MAX_BYTES, stop_requested=lambda: False) -> None:
    parent = process(proc / str(pid))
    if parent is None or parent["state"] in {"Z", "X"}:
        return
    cgroup = cgroup_dir(proc, pid, cgroup_root)
    # Exclusive creation: do not follow or overwrite a pre-existing artifact.
    with output.open("x", encoding="ascii") as stream:
        identity = os.fstat(stream.fileno())
        digest = hashlib.sha256()
        written = 0
        next_sample = time.monotonic()
        count = 0

        def write_sample(phase: str) -> bool:
            nonlocal written, count
            if count >= max_samples:
                return False
            # A blocked diagnostic read/write (including console output) must
            # not leave an orphan after parent death. SIGALRM's default action
            # terminates only this sampler, never the build process.
            signal.alarm(SNAPSHOT_SECONDS)
            try:
                row = sample(proc, cgroup, workspace)
                row["phase"] = phase
                encoded = json.dumps(row, ensure_ascii=True, allow_nan=False, separators=(",", ":")) + "\n"
                if written + len(encoded) > max_bytes:
                    return False
                stream.write(encoded)
                stream.flush()
                digest.update(encoded.encode("ascii"))
                written += len(encoded)
                count += 1
                notice(f"Resource sample {count} ({phase}): utc={row['utc']} "
                       f"load1={(row['loadavg'] or [None])[0]} "
                       f"mem_available_kib={(row['memory_kib'] or {}).get('MemAvailable')} "
                       f"disk_available_bytes={(row['disk'] or {}).get('available_bytes')} "
                       f"build_processes={row['observed_build_processes']}")
                return True
            finally:
                signal.alarm(SNAPSHOT_SECONDS)

        while True:
            # Reset before polling too: a blocked /proc read must not orphan us.
            signal.alarm(SNAPSHOT_SECONDS)
            if stop_requested() or not parent_alive(proc, pid, parent["start_ticks"]):
                write_sample("final")
                break
            now = time.monotonic()
            if now >= next_sample:
                if not write_sample("periodic") or count >= max_samples:
                    break
                next_sample = now + interval
            time.sleep(min(1, max(0, next_sample - time.monotonic())))
        signal.alarm(SNAPSHOT_SECONDS)
    # This receipt is created only after our exclusively created stream closes.
    # Rejected pre-existing output, failed writes/close and watchdog termination
    # cannot leave an upload-eligible file. Never overwrite an existing receipt.
    receipt = {"version": 1, "device": identity.st_dev, "inode": identity.st_ino,
               "bytes": written, "sha256": digest.hexdigest()}
    with (output.parent / "closed.json").open("x", encoding="ascii") as stream:
        json.dump(receipt, stream)


def monitor(*args, **kwargs) -> None:
    # Armed before the first parent/cgroup read and kept armed through close.
    # SIGALRM terminates only this process; no handler turns it into success.
    signal.alarm(SNAPSHOT_SECONDS)
    try:
        _monitor(*args, **kwargs)
    finally:
        signal.alarm(0)


def owned_file(directory_fd: int, name: str, limit: int) -> tuple[bytes, os.stat_result]:
    fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory_fd)
    with os.fdopen(fd, "rb") as stream:
        info = os.fstat(stream.fileno())
        if (not stat.S_ISREG(info.st_mode) or info.st_nlink != 1 or
                info.st_uid != os.getuid() or info.st_size > limit):
            raise ValueError("not a bounded owned regular file")
        data = stream.read(limit + 1)
        if len(data) > limit:
            raise ValueError("file exceeds limit")
        return data, info


def publish(directory: Path, temp_root: Path, github_output: Path) -> Path | None:
    """Validate a closed sample, then publish a new copy, never the input path."""
    signal.alarm(5)
    try:
        fd = os.open(directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            info = os.fstat(fd)
            if info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) != 0o700:
                return None
            # The build shell never waits for the sidecar. Allow its normal
            # parent-death detection/final snapshot to finish, with a hard cap.
            deadline = time.monotonic() + 3
            while True:
                try:
                    receipt_data, _ = owned_file(fd, "closed.json", 2048)
                    break
                except FileNotFoundError:
                    if time.monotonic() >= deadline:
                        return None
                    time.sleep(0.1)
            receipt = json.loads(receipt_data)
            data, sample_stat = owned_file(fd, "samples.jsonl", MAX_BYTES)
            expected = {"version": 1, "device": sample_stat.st_dev, "inode": sample_stat.st_ino,
                        "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
            if receipt != expected or not data:
                return None
            # Upload a closed snapshot in another exclusive directory, so a
            # change to the original sample after validation cannot be uploaded.
            destination = Path(tempfile.mkdtemp(prefix="lean-resources-upload-", dir=temp_root)) / "samples.jsonl"
            with destination.open("xb") as stream:
                stream.write(data)
            with github_output.open("a", encoding="utf-8") as stream:
                stream.write(f"artifact_path={destination}\n")
            return destination
        finally:
            os.close(fd)
    finally:
        signal.alarm(0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    sampler = commands.add_parser("sample")
    sampler.add_argument("--output", type=Path, required=True)
    sampler.add_argument("--parent-pid", type=int, required=True)
    publisher = commands.add_parser("publish")
    publisher.add_argument("--directory", type=Path, required=True)
    publisher.add_argument("--temp-root", type=Path, required=True)
    publisher.add_argument("--github-output", type=Path, required=True)
    args = parser.parse_args()
    stopping = False

    def stop(signum, frame):
        nonlocal stopping
        stopping = True

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        if args.command == "sample":
            monitor(args.output, args.parent_pid, stop_requested=lambda: stopping)
        else:
            publish(args.directory, args.temp_root, args.github_output)
    except Exception:
        # Do not print exceptions: they may contain paths or arbitrary file text.
        signal.alarm(SNAPSHOT_SECONDS)
        notice("Resource diagnostics unavailable; build checks are unchanged.")
        signal.alarm(0)


if __name__ == "__main__":
    main()
