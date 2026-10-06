#!/usr/bin/env python3
"""Export a bounded, source-verified QIC prerequisite set after a successful Lean build.

Only the explicit module allowlist and its compiled Lean companions are copied.
No repository metadata, credentials, environment variables, or unrelated cache
contents are included. The consumer must verify the manifest before reuse.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ilean")
MAX_BYTES = 30 * 1024 * 1024
MODULE = re.compile(r"QICLean(?:\.[A-Za-z_][A-Za-z_0-9]*)+\Z")
PACKAGE = re.compile(r"[A-Za-z_][A-Za-z_0-9.-]*\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(repo), *args])


def prerequisite_modules(root: Path) -> list[str]:
    entries = json.loads((root / "scripts/coherent_qic_prerequisites.json").read_text())["modules"]
    if not entries or len(entries) != len(set(entries)) or not all(MODULE.fullmatch(m) for m in entries):
        raise ValueError("invalid or duplicate QIC prerequisite module")
    return entries


def build_prerequisites(root: Path) -> None:
    """Build the allowlisted module facets once; the later root build reuses them."""
    before = prepare(root)
    targets = [f"@qiclean/+{module}:olean" for module in before[0]]
    subprocess.run(["lake", "build", *targets], cwd=root, check=True)
    if prepare(root) != before:
        raise ValueError("source state changed during the prerequisite build")


def prepare(root: Path) -> tuple[list[str], Path, dict]:
    """Verify recorded dependency pins and their complete Lean/config source state."""
    root = root.resolve()
    entries = prerequisite_modules(root)
    manifest_bytes = (root / "lake-manifest.json").read_bytes()
    packages = json.loads(manifest_bytes)["packages"]
    pins = {}
    for package in packages:
        name, rev = package["name"], package["rev"]
        if not PACKAGE.fullmatch(name) or not COMMIT.fullmatch(rev) or name in pins:
            raise ValueError("invalid or duplicate dependency name or revision")
        checkout = root / ".lake/packages" / name
        if git(checkout, "rev-parse", "HEAD").decode().strip() != rev:
            raise ValueError(f"dependency checkout differs from its pin: {name}")
        if git(checkout, "status", "--porcelain", "--untracked-files=all", "--",
               "*.lean", "lean-toolchain", "lake-manifest.json", "lakefile.*").strip():
            raise ValueError(f"dependency Lean/config sources are dirty: {name}")
        pins[name] = rev
    pin = pins["qiclean"]
    qic = (root / ".lake/packages/qiclean").resolve()
    toolchain = (root / "lean-toolchain").read_bytes()
    if (qic / "lean-toolchain").read_bytes() != toolchain:
        raise ValueError("QIC and TNLean toolchains differ")
    manifest = {
        "format_version": 1,
        "qic_commit": pin,
        "lean_toolchain": toolchain.decode().strip(),
        "lean_toolchain_sha256": digest(toolchain),
        "root_manifest_sha256": digest(manifest_bytes),
        "dependency_pins": pins,
        "dependency_lean_config_sources_clean": True,
        "modules": {},
    }
    for module in entries:
        relative = Path(*module.split("."))
        source_path = relative.with_suffix(".lean")
        source_file = qic / source_path
        if source_file.is_symlink() or not source_file.resolve().is_relative_to(qic):
            raise ValueError(f"source is outside the pinned checkout: {module}")
        source = source_file.read_bytes()
        if git(qic, "show", f"{pin}:{source_path.as_posix()}") != source:
            raise ValueError(f"source differs from the QIC pin: {module}")
        manifest["modules"][module] = {"source_sha256": digest(source), "artifacts": {}}
    return entries, qic, manifest


def export(root: Path, output: Path) -> dict:
    if output.exists():
        raise ValueError("the export destination must not already exist")
    entries, qic, manifest = prepare(root)
    files = []
    total = 0
    for module in entries:
        relative = Path(*module.split("."))
        base = qic / ".lake/build/lib/lean" / relative
        if not Path(str(base) + ".olean").is_file():
            raise ValueError(f"compiled module missing: {module}")
        artifact_info = {}
        for suffix in SUFFIXES:
            artifact = Path(str(base) + suffix)
            if not artifact.is_file():
                continue
            if artifact.is_symlink() or not artifact.resolve().is_relative_to(qic):
                raise ValueError(f"artifact is outside the pinned checkout: {module}")
            if total + artifact.stat().st_size > MAX_BYTES:
                raise ValueError("the bounded prerequisite export exceeds 30 MiB")
            data = artifact.read_bytes()
            total += len(data)
            if total > MAX_BYTES:
                raise ValueError("the bounded prerequisite export exceeds 30 MiB")
            target = Path(str(relative) + suffix)
            artifact_info[target.as_posix()] = {"sha256": digest(data), "bytes": len(data)}
            files.append((data, target))
        manifest["modules"][module]["artifacts"] = artifact_info
    manifest["total_artifact_bytes"] = total
    manifest_data = (json.dumps(manifest, indent=2) + "\n").encode()
    if total + len(manifest_data) > MAX_BYTES:
        raise ValueError("the bounded prerequisite export including provenance exceeds 30 MiB")
    output.mkdir(parents=True)
    for data, target in files:
        destination = output / target
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    (output / "manifest.json").write_bytes(manifest_data)
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--build", action="store_true",
                        help="build only the allowlisted QIC module prerequisites first")
    args = parser.parse_args()
    if args.build:
        build_prerequisites(args.root)
    result = export(args.root, args.output)
    print(f"Exported {len(result['modules'])} QIC modules, {result['total_artifact_bytes']} bytes.")


if __name__ == "__main__":
    main()
