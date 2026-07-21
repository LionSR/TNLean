#!/usr/bin/env python3
"""Render a compiled tenkz corpus into a deterministic PNG baseline tree."""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path


DPI = 200
MARKER_NAME = ".tenkz-corpus-render"
MARKER_CONTENT = "tenkz-corpus-render-v1\n"


class RenderError(RuntimeError):
    """A render precondition or tool invocation failed."""


def resolved(path: Path) -> Path:
    return path.expanduser().resolve(strict=False)


def has_valid_ownership_marker(output_dir: Path) -> bool:
    marker = output_dir / MARKER_NAME
    try:
        marker_status = marker.lstat()
    except OSError:
        return False
    if not stat.S_ISREG(marker_status.st_mode):
        return False
    try:
        return marker.read_text(encoding="utf-8") == MARKER_CONTENT
    except OSError:
        return False


def validate_paths(input_dir: Path, output_dir: Path, protected: list[Path]) -> None:
    if not input_dir.is_dir():
        raise RenderError(f"input directory does not exist: {input_dir}")
    if output_dir == Path(output_dir.anchor):
        raise RenderError(f"refusing to replace filesystem root: {output_dir}")
    paths_overlap = (
        output_dir == input_dir
        or output_dir in input_dir.parents
        or input_dir in output_dir.parents
    )
    if paths_overlap:
        raise RenderError("input and output directories must not contain one another")
    if output_dir in protected:
        raise RenderError(f"refusing to replace protected directory: {output_dir}")
    if output_dir.is_symlink():
        raise RenderError(f"output directory must not be a symlink: {output_dir}")
    if output_dir.exists() and not output_dir.is_dir():
        raise RenderError(f"output path exists and is not a directory: {output_dir}")
    if (
        output_dir.exists()
        and any(output_dir.iterdir())
        and not has_valid_ownership_marker(output_dir)
    ):
        raise RenderError(
            f"refusing to replace nonempty directory without a valid regular "
            f"{MARKER_NAME}: {output_dir}"
        )


def require_tool(name: str) -> str:
    executable = shutil.which(name)
    if executable is None:
        raise RenderError(f"tenkz corpus rendering requires {name}")
    return executable


def compiled_pdfs(input_dir: Path) -> list[Path]:
    sources = sorted(input_dir.glob("*.tex"), key=lambda path: path.name)
    if not sources:
        raise RenderError(f"no corpus sources found in {input_dir}")

    expected = {source.with_suffix(".pdf") for source in sources}
    missing = sorted(path.name for path in expected if not path.is_file())
    if missing:
        raise RenderError("compiled corpus PDFs are missing: " + ", ".join(missing))

    actual = {path for path in input_dir.glob("*.pdf") if path.is_file()}
    extras = sorted(path.name for path in actual - expected)
    if extras:
        raise RenderError("unexpected PDFs in compiled corpus: " + ", ".join(extras))
    return sorted(expected, key=lambda path: path.name)


def pdf_page_count(pdf: Path, pdfinfo: str) -> int:
    try:
        result = subprocess.run(
            [pdfinfo, str(pdf)],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
        )
    except subprocess.TimeoutExpired as exc:
        raise RenderError(f"pdfinfo timed out for {pdf.name}") from exc
    if result.returncode:
        detail = result.stderr.strip() or f"exit status {result.returncode}"
        raise RenderError(f"pdfinfo failed for {pdf.name}: {detail}")
    match = re.search(r"^Pages:\s+([1-9][0-9]*)\s*$", result.stdout, re.MULTILINE)
    if match is None:
        raise RenderError(f"pdfinfo reported no positive page count for {pdf.name}")
    return int(match.group(1))


def render_page(pdf: Path, page: int, destination: Path, pdftocairo: str) -> None:
    prefix = destination.with_suffix("")
    try:
        result = subprocess.run(
            [
                pdftocairo,
                "-png",
                "-r",
                str(DPI),
                "-f",
                str(page),
                "-l",
                str(page),
                "-singlefile",
                str(pdf),
                str(prefix),
            ],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        raise RenderError(f"pdftocairo timed out for {pdf.name} page {page}") from exc
    if result.returncode:
        detail = result.stderr.strip() or f"exit status {result.returncode}"
        raise RenderError(f"pdftocairo failed for {pdf.name} page {page}: {detail}")
    if not destination.is_file() or destination.stat().st_size == 0:
        raise RenderError(f"pdftocairo produced no PNG for {pdf.name} page {page}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_manifests(stage: Path, census: list[tuple[str, int]], pngs: list[Path]) -> None:
    (stage / MARKER_NAME).write_text(MARKER_CONTENT, encoding="utf-8")
    census_lines = ["source_file\tpages", *(f"{source}\t{pages}" for source, pages in census)]
    (stage / "CENSUS.tsv").write_text("\n".join(census_lines) + "\n", encoding="utf-8")

    checksum_lines = [
        f"{sha256(path)}  {path.relative_to(stage).as_posix()}"
        for path in sorted(pngs, key=lambda item: item.relative_to(stage).as_posix())
    ]
    (stage / "SHA256SUMS").write_text("\n".join(checksum_lines) + "\n", encoding="utf-8")


def install_stage(stage: Path, output_dir: Path) -> None:
    backup = output_dir.parent / f".{output_dir.name}.previous.{os.getpid()}"
    if backup.exists():
        raise RenderError(f"stale render backup blocks installation: {backup}")

    moved_old = output_dir.exists()
    if moved_old:
        try:
            output_dir.rename(backup)
        except OSError as exc:
            raise RenderError(f"cannot stage prior baseline at {backup}: {exc}") from exc

    try:
        stage.rename(output_dir)
    except OSError as exc:
        if moved_old:
            try:
                backup.rename(output_dir)
            except OSError as restore_exc:
                raise RenderError(
                    f"cannot install render baseline at {output_dir}; restoring untouched "
                    f"backup {backup} also failed: {restore_exc}"
                ) from exc
        raise RenderError(f"cannot install render baseline at {output_dir}: {exc}") from exc

    if moved_old:
        try:
            shutil.rmtree(backup)
        except OSError as exc:
            print(
                f"WARNING: installed complete render baseline at {output_dir}, but could not "
                f"remove prior baseline backup {backup}: {exc}",
                file=sys.stderr,
            )


def render_corpus(input_dir: Path, output_dir: Path, protected: list[Path]) -> tuple[int, int]:
    input_dir = resolved(input_dir)
    if output_dir.expanduser().is_symlink():
        raise RenderError(f"output directory must not be a symlink: {output_dir}")
    output_dir = resolved(output_dir)
    protected = [resolved(path) for path in protected]
    validate_paths(input_dir, output_dir, protected)

    pdfinfo = require_tool("pdfinfo")
    pdftocairo = require_tool("pdftocairo")
    pdfs = compiled_pdfs(input_dir)
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(
        tempfile.mkdtemp(prefix=f".{output_dir.name}.staging.", dir=output_dir.parent)
    )

    census: list[tuple[str, int]] = []
    pngs: list[Path] = []
    try:
        for pdf in pdfs:
            pages = pdf_page_count(pdf, pdfinfo)
            census.append((pdf.with_suffix(".tex").name, pages))
            fixture_dir = stage / pdf.stem
            fixture_dir.mkdir()
            for page in range(1, pages + 1):
                destination = fixture_dir / f"page-{page:03d}.png"
                render_page(pdf, page, destination, pdftocairo)
                pngs.append(destination)
        write_manifests(stage, census, pngs)
        install_stage(stage, output_dir)
    except Exception:
        if stage.exists():
            shutil.rmtree(stage)
        raise
    return len(pdfs), len(pngs)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--protect", action="append", default=[], type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        pdf_count, page_count = render_corpus(args.input_dir, args.output_dir, args.protect)
    except (OSError, RenderError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    output_dir = resolved(args.output_dir)
    print(
        f"PASS: rendered {pdf_count} corpus PDFs ({page_count} pages) at {DPI} dpi "
        f"in {output_dir}"
    )
    print(f"Checksums: {output_dir / 'SHA256SUMS'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
