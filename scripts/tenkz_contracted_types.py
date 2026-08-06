#!/usr/bin/env python3
"""Report the type of every contracted index in the tenkz RMP corpus.

The kernel strokes a connected wire the same way whether its two ends are
physical or virtual ports, so a mistyped contracted index leaves the drawing
untouched and no render comparison can find it.  The record stream does carry
the type, and this script reads it: for each target it compiles the case and
reports how many of its contracted indices are physical and how many virtual,
with the origin of each contraction.

Both picture languages are covered.  In the kernel a contracted index is a
``wire`` record with both ``from`` and ``to`` resolved; it carries
``port-type=physical`` when the kernel typed both of its ports physical, and
carries no type field when the contraction is virtual.  In the older grid
dialect the type is fixed by the grammar rather than declared, so the record
kind names it: ``pairleg``, ``pairtrace`` and ``phtrace`` are site
contractions, while ``bond``, ``cup`` and ``trace`` run along the network.

Usage::

    python3 scripts/tenkz_contracted_types.py --all
    python3 scripts/tenkz_contracted_types.py --id rmp-ii-ortho-left
    python3 scripts/tenkz_contracted_types.py --all --physical-only
    python3 scripts/tenkz_contracted_types.py --all --build-dir DIR

``--build-dir`` reuses (and populates) a directory of compiled targets instead
of a temporary one, which makes a repeated audit cheap.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import os
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from tenkz_rmp import (  # noqa: E402
    DEFAULT_MANIFEST,
    RMPError,
    load_manifest,
    standalone_wrapper,
    tex_environment,
)

ROOT = Path(__file__).resolve().parents[1]

# Grid-dialect record kinds that are contractions.  The dialect has no declared
# port type: a ket-bra site pairing and a physical trace are physical because
# the grammar that emits them says so, and a bond, a cup and a virtual trace
# run along the network.
DIALECT_PHYSICAL = frozenset({"pairleg", "pairtrace", "phtrace"})
DIALECT_VIRTUAL = frozenset({"bond", "cup", "trace"})


@dataclass
class Contraction:
    """One contracted index, with the type and the construct that made it."""

    picture: str
    lang: str
    kind: str
    origin: str
    type: str


@dataclass
class TargetReport:
    id: str
    languages: list[str] = field(default_factory=list)
    contractions: list[Contraction] = field(default_factory=list)
    error: str | None = None

    @property
    def physical(self) -> list[Contraction]:
        return [item for item in self.contractions if item.type == "physical"]

    @property
    def virtual(self) -> list[Contraction]:
        return [item for item in self.contractions if item.type == "virtual"]


def record_fields(line: str) -> tuple[str, dict[str, str]]:
    parts = line.strip().split("|")
    attrs: dict[str, str] = {}
    for part in parts[1:]:
        key, separator, value = part.partition("=")
        if separator:
            attrs[key] = value
    return parts[0], attrs


def read_stream(text: str) -> tuple[list[str], list[Contraction]]:
    """Classify every contracted index in one event stream."""
    languages: list[str] = []
    picture = "?"
    lang = "unknown"
    contractions: list[Contraction] = []
    for line in text.splitlines():
        kind, attrs = record_fields(line)
        if kind == "picture":
            picture = attrs.get("id", "?")
            lang = attrs.get("lang", "unknown").split("|")[0]
            if lang not in languages:
                languages.append(lang)
            continue
        if kind == "wire":
            if "from" not in attrs or "to" not in attrs:
                continue
            contractions.append(
                Contraction(
                    picture=picture,
                    lang=lang,
                    kind="wire",
                    origin=attrs.get("origin", "tnwire"),
                    # The kernel stamps port-type only on a physical index;
                    # an untyped contraction is virtual by default.
                    type=attrs.get("port-type", "virtual"),
                )
            )
            continue
        if kind in DIALECT_PHYSICAL or kind in DIALECT_VIRTUAL:
            contractions.append(
                Contraction(
                    picture=attrs.get("picture", picture),
                    lang=lang,
                    kind=kind,
                    origin=kind,
                    type="physical" if kind in DIALECT_PHYSICAL else "virtual",
                )
            )
    return languages, contractions


def compile_target(target, work_root: Path, env: dict[str, str]) -> TargetReport:
    work = work_root / target.id
    work.mkdir(parents=True, exist_ok=True)
    wrapper = work / f"{target.id}-standalone.tex"
    wrapper.write_text(standalone_wrapper(target), encoding="utf-8")
    stream = wrapper.with_suffix(".tnlog")
    if not (stream.is_file() and stream.stat().st_size):
        try:
            subprocess.run(
                ["xelatex", "-interaction=nonstopmode", "-halt-on-error", wrapper.name],
                cwd=work,
                env=env,
                capture_output=True,
                text=True,
                timeout=180,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return TargetReport(id=target.id, error=str(exc))
        if not (stream.is_file() and stream.stat().st_size):
            return TargetReport(id=target.id, error="produced no nonempty .tnlog")
    languages, contractions = read_stream(stream.read_text(encoding="utf-8"))
    return TargetReport(id=target.id, languages=languages, contractions=contractions)


def describe(report: TargetReport) -> str:
    if report.error is not None:
        return f"{report.id}\tERROR: {report.error}"
    origins = Counter(item.origin for item in report.physical)
    detail = ", ".join(f"{origin}={count}" for origin, count in sorted(origins.items()))
    return (
        f"{report.id}\t"
        f"lang={'+'.join(report.languages) or 'none'}\t"
        f"physical={len(report.physical)}\t"
        f"virtual={len(report.virtual)}"
        + (f"\tvia {detail}" if detail else "")
    )


def run(targets, work_root: Path, jobs: int) -> list[TargetReport]:
    env = tex_environment(work_root)
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        return list(pool.map(lambda t: compile_target(t, work_root, env), targets))


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    selection = result.add_mutually_exclusive_group(required=True)
    selection.add_argument("--all", action="store_true")
    selection.add_argument("--id", dest="target_id", metavar="TARGET")
    result.add_argument(
        "--build-dir",
        type=Path,
        help="reuse this directory of compiled targets instead of a temporary one",
    )
    result.add_argument(
        "--physical-only",
        action="store_true",
        help="list only the targets that record a contracted physical index",
    )
    return result


def main() -> int:
    args = parser().parse_args()
    manifest = Path(os.environ.get("TENKZ_RMP_MANIFEST", DEFAULT_MANIFEST))
    try:
        targets = load_manifest(manifest)
    except RMPError as exc:
        print(f"FAIL: {exc}")
        return 1
    if args.target_id is not None:
        targets = [target for target in targets if target.id == args.target_id]
        if not targets:
            print(f"FAIL: unknown target id: {args.target_id}")
            return 1
    jobs = max(1, os.cpu_count() or 1)

    if args.build_dir is not None:
        args.build_dir.mkdir(parents=True, exist_ok=True)
        reports = run(targets, args.build_dir.resolve(), jobs)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz-contracted-") as temporary:
            reports = run(targets, Path(temporary), jobs)

    failures = [report for report in reports if report.error is not None]
    shown = [report for report in reports if not args.physical_only or report.physical]
    for report in shown:
        print(describe(report))

    physical_targets = [report for report in reports if report.physical]
    mixed = [report for report in physical_targets if report.virtual]
    print(
        f"\n{len(reports)} targets; "
        f"{len(physical_targets)} record a contracted physical index, "
        f"{len(mixed)} contract both types; "
        f"{sum(len(report.physical) for report in reports)} physical and "
        f"{sum(len(report.virtual) for report in reports)} virtual contractions."
    )
    if failures:
        for report in failures:
            print(f"FAIL: {report.id}: {report.error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
