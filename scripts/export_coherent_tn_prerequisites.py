#!/usr/bin/env python3
"""Export only explicitly listed, unchanged TN prerequisites and exact provenance.

The selected source closure must equal both HEAD and the recorded baseline.
Every dependency checkout must match its pin and have clean Lean/config sources.
No environment variables, credentials, repository metadata or unrelated cache are copied.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

from export_coherent_qic_prerequisites import MAX_BYTES, SUFFIXES, digest, git
from lean_import_syntax import MODULE_NAME, strip_lean_comments

MODULE = re.compile(r"TNLean(?:\.[A-Za-z_][A-Za-z_0-9]*)+\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")
PACKAGE = re.compile(r"[A-Za-z_][A-Za-z_0-9.-]*\Z")
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(.+)\Z")


def header_imports(source: str) -> list[str]:
    clean, error = strip_lean_comments(source)
    if error:
        raise ValueError(error)
    result = []
    for line in clean.splitlines():
        line = line.strip()
        if not line or line in {"module", "prelude"}:
            continue
        match = IMPORT.fullmatch(line)
        if not match:
            break
        names = match[1].split()
        if not names or not all(re.fullmatch(MODULE_NAME, name) for name in names):
            raise ValueError("unsupported import header")
        result.extend(names)
    return result


def prepare(root: Path) -> tuple[list[str], dict]:
    spec = json.loads((root / "scripts/coherent_tn_prerequisites.json").read_text())
    modules, baseline = spec["modules"], spec["baseline_commit"]
    if not modules or len(modules) != len(set(modules)) or not all(MODULE.fullmatch(m) for m in modules):
        raise ValueError("invalid or duplicate TN prerequisite module")
    if not COMMIT.fullmatch(baseline):
        raise ValueError("invalid source baseline")
    head = git(root, "rev-parse", "HEAD").decode().strip()
    if not COMMIT.fullmatch(head):
        raise ValueError("invalid source commit")
    toolchain = (root / "lean-toolchain").read_bytes()
    manifest_bytes = (root / "lake-manifest.json").read_bytes()
    config = (root / "lakefile.toml").read_bytes()
    for path, data in (("lean-toolchain", toolchain), ("lake-manifest.json", manifest_bytes),
                       ("lakefile.toml", config)):
        for commit in (head, baseline):
            if git(root, "show", f"{commit}:{path}") != data:
                raise ValueError(f"{path} differs from the recorded source configuration")
    packages = json.loads(manifest_bytes)["packages"]
    pins = {}
    for package in packages:
        name, rev = package["name"], package["rev"]
        if not PACKAGE.fullmatch(name) or not COMMIT.fullmatch(rev):
            raise ValueError("invalid dependency name or revision")
        checkout = root / ".lake/packages" / name
        if git(checkout, "rev-parse", "HEAD").decode().strip() != rev:
            raise ValueError(f"dependency checkout differs from its pin: {name}")
        if git(checkout, "status", "--porcelain", "--untracked-files=all", "--",
               "*.lean", "lean-toolchain", "lake-manifest.json", "lakefile.*").strip():
            raise ValueError(f"dependency Lean/config sources are dirty: {name}")
        pins[name] = rev
    sources = {}
    pending = list(modules)
    while pending:
        module = pending.pop()
        if module in sources:
            continue
        if not MODULE.fullmatch(module):
            raise ValueError("invalid TN dependency module")
        path = Path(*module.split(".")).with_suffix(".lean")
        source_file = root / path
        if source_file.is_symlink() or not source_file.resolve().is_relative_to(root):
            raise ValueError(f"source is outside the checkout: {module}")
        source = source_file.read_bytes()
        for commit in (head, baseline):
            if git(root, "show", f"{commit}:{path.as_posix()}") != source:
                raise ValueError(f"source differs from the recorded commit: {module}")
        imports = header_imports(source.decode())
        sources[module] = {"sha256": digest(source), "imports": imports}
        pending.extend(m for m in imports if m.startswith("TNLean."))
    return modules, {
        "format_version": 1,
        "source_commit": head,
        "baseline_commit": baseline,
        "lean_toolchain": toolchain.decode().strip(),
        "lean_toolchain_sha256": digest(toolchain),
        "root_manifest_sha256": digest(manifest_bytes),
        "root_config_sha256": digest(config),
        "dependency_pins": pins,
        "dependency_lean_config_sources_clean": True,
        "tn_source_closure": sources,
        "modules": {},
    }


def export(root: Path, output: Path, build: bool = False) -> dict:
    root = root.resolve()
    if output.exists():
        raise ValueError("the export destination must not already exist")
    modules, manifest = prepare(root)
    if build:
        subprocess.run(["lake", "build", *(f"@/+{m}:olean" for m in modules)], cwd=root, check=True)
        # The build is not permitted to change the verified source/dependency state.
        if prepare(root) != (modules, manifest):
            raise ValueError("source state changed during the prerequisite build")
    files, total = [], 0
    for module in modules:
        relative = Path(*module.split("."))
        base = root / ".lake/build/lib/lean" / relative
        if not Path(str(base) + ".olean").is_file():
            raise ValueError(f"compiled module missing: {module}")
        artifacts = {}
        for suffix in SUFFIXES:
            artifact = Path(str(base) + suffix)
            if not artifact.is_file():
                continue
            if artifact.is_symlink() or not artifact.resolve().is_relative_to(root):
                raise ValueError(f"artifact is outside the checkout: {module}")
            if total + artifact.stat().st_size > MAX_BYTES:
                raise ValueError("the bounded TN export exceeds 30 MiB")
            data = artifact.read_bytes()
            total += len(data)
            if total > MAX_BYTES:
                raise ValueError("the bounded TN export exceeds 30 MiB")
            target = Path(str(relative) + suffix)
            artifacts[target.as_posix()] = {"sha256": digest(data), "bytes": len(data)}
            files.append((target, data))
        manifest["modules"][module] = {"artifacts": artifacts}
    manifest["total_artifact_bytes"] = total
    manifest_data = (json.dumps(manifest, indent=2) + "\n").encode()
    if total + len(manifest_data) > MAX_BYTES:
        raise ValueError("the bounded TN export including provenance exceeds 30 MiB")
    output.mkdir(parents=True)
    for target, data in files:
        path = output / target
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    (output / "manifest.json").write_bytes(manifest_data)
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    result = export(args.root, args.output, args.build)
    print(f"Exported {len(result['modules'])} TN modules, {result['total_artifact_bytes']} bytes.")


if __name__ == "__main__":
    main()
