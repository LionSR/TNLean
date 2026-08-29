#!/usr/bin/env python3
"""Recover and verify the external paper sources pinned by TNLean."""

from __future__ import annotations

import argparse
import hashlib
import io
import os
import re
import tarfile
import tempfile
import tomllib
import urllib.error
import urllib.request
from pathlib import Path, PurePosixPath
from typing import Any, Callable

REPO = Path(__file__).resolve().parents[1]
MANIFEST = REPO / "Papers" / "external_sources.toml"
SHA256_RE = re.compile(r"[0-9a-f]{64}")
ARXIV_ID_RE = re.compile(
    r"(?P<base>[0-9]{4}\.[0-9]{5})v(?P<version>[1-9][0-9]*)"
)
WINDOWS_DRIVE_RE = re.compile(r"[A-Za-z]:")
RANGE_RE = re.compile(r"([1-9][0-9]*)(?:-([1-9][0-9]*))?")
RANGE_TOKEN = r"[1-9][0-9]*(?:-[1-9][0-9]*)?"
SOURCE_ANCHOR_TAG = "TNLEAN_EXTERNAL_SOURCE_RANGES:"
SOURCE_ANCHOR_RE = re.compile(
    rf"(?P<source>[0-9]{{4}}\.[0-9]{{5}}v[1-9][0-9]*)\s+"
    rf"(?P<ranges>{RANGE_TOKEN}(?:\s*,\s*{RANGE_TOKEN})*)"
)
PRESERVATION_MODES = {"download-only", "vendored"}
PRESERVATION_ROOTS = {
    "download-only": ("build", "paper-sources"),
    "vendored": ("Papers",),
}
LICENSE_POLICIES = {
    "arXiv non-exclusive distribution license 1.0": (
        "https://arxiv.org/licenses/nonexclusive-distrib/1.0/",
        "download-only",
    ),
    "Creative Commons Attribution 4.0 International": (
        "https://creativecommons.org/licenses/by/4.0/",
        "vendored",
    ),
}
ANCHOR_DOCUMENT_ROOTS = (("docs", "audits"), ("docs", "paper-gaps"))


class VerificationError(Exception):
    """Raised when a pinned source artifact does not match its manifest."""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require_string(table: dict[str, Any], field: str, source_id: str) -> str:
    value = table.get(field)
    if not isinstance(value, str) or not value:
        raise VerificationError(f"{source_id}: {field} must be a nonempty string")
    return value


def lexical_relative_path(value: str, source_id: str, field: str) -> PurePosixPath:
    """Parse a manifest path without permitting platform-dependent escapes."""
    if "\\" in value:
        raise VerificationError(f"{source_id}: {field} must use forward slashes")
    if "\x00" in value:
        raise VerificationError(f"{source_id}: {field} contains a NUL byte")
    if value.startswith("/") or WINDOWS_DRIVE_RE.match(value):
        raise VerificationError(f"{source_id}: {field} must be repository-relative")
    parts = value.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise VerificationError(
            f"{source_id}: {field} contains an empty, dot, or parent component"
        )
    return PurePosixPath(*parts)


def checked_repo_path(
    repo: Path, relative: PurePosixPath, source_id: str, field: str
) -> Path:
    """Return a repository path after rejecting every existing symlink component."""
    try:
        root = repo.resolve(strict=True)
    except OSError as error:
        raise VerificationError(f"repository root is unavailable: {error}") from error
    current = root
    for index, component in enumerate(relative.parts):
        current /= component
        if current.is_symlink():
            raise VerificationError(
                f"{source_id}: {field} traverses symlink component {component!r}"
            )
        if current.exists() and index + 1 < len(relative.parts) and not current.is_dir():
            raise VerificationError(
                f"{source_id}: {field} traverses non-directory component {component!r}"
            )
    return current


def source_filename(source: dict[str, Any]) -> str:
    source_id = source["arxiv_id"]
    filename = require_string(source, "source_filename", source_id)
    relative = lexical_relative_path(filename, source_id, "source_filename")
    if len(relative.parts) != 1:
        raise VerificationError(
            f"{source_id}: source_filename must name one top-level archive member"
        )
    return filename


def canonical_local_relative(source: dict[str, Any]) -> PurePosixPath:
    """Validate and return the only output path allowed for a source record."""
    source_id = source["arxiv_id"]
    match = ARXIV_ID_RE.fullmatch(source_id)
    if match is None:
        raise VerificationError(f"invalid versioned arXiv ID {source_id!r}")
    preservation = source["preservation"]
    try:
        root_parts = PRESERVATION_ROOTS[preservation]
    except KeyError as error:
        raise VerificationError(
            f"{source_id}: preservation must be one of {sorted(PRESERVATION_MODES)}"
        ) from error
    local_path = require_string(source, "local_path", source_id)
    relative = lexical_relative_path(local_path, source_id, "local_path")
    expected = PurePosixPath(
        *root_parts, match.group("base"), source_filename(source)
    )
    if relative != expected:
        raise VerificationError(
            f"{source_id}: local_path must be the canonical path {expected.as_posix()}"
        )
    return relative


def local_path_for_source(repo: Path, source: dict[str, Any]) -> Path:
    source_id = source["arxiv_id"]
    return checked_repo_path(
        repo, canonical_local_relative(source), source_id, "local_path"
    )


def document_relative_path(value: str, source_id: str) -> PurePosixPath:
    relative = lexical_relative_path(value, source_id, "citation document")
    if not any(
        relative.parts[: len(root)] == root for root in ANCHOR_DOCUMENT_ROOTS
    ):
        raise VerificationError(
            f"{source_id}: citation document must be under docs/audits or docs/paper-gaps"
        )
    if relative.suffix not in {".md", ".tex"}:
        raise VerificationError(
            f"{source_id}: citation document must be Markdown or LaTeX"
        )
    return relative


def parse_range(value: str, source_id: str) -> tuple[int, int]:
    match = RANGE_RE.fullmatch(value)
    if match is None:
        raise VerificationError(f"{source_id}: invalid cited range {value!r}")
    first = int(match.group(1))
    last = int(match.group(2) or match.group(1))
    if last < first:
        raise VerificationError(f"{source_id}: reversed cited range {value!r}")
    return first, last


def validate_ranges(values: Any, source_id: str, context: str) -> tuple[str, ...]:
    if not isinstance(values, list) or not values or not all(
        isinstance(value, str) for value in values
    ):
        raise VerificationError(f"{source_id}: {context} has no valid ranges")
    parsed = [parse_range(value, source_id) for value in values]
    if len(set(values)) != len(values):
        raise VerificationError(f"{source_id}: {context} repeats a range")
    if parsed != sorted(parsed):
        raise VerificationError(f"{source_id}: {context} ranges are not sorted")
    return tuple(values)


def range_is_written(document: str, first: int, last: int) -> bool:
    if first == last:
        pattern = rf"(?<![0-9-]){first}(?![0-9-])"
    else:
        pattern = rf"(?<![0-9-]){first}--{last}(?![0-9-])"
    return re.search(pattern, document) is not None


def parse_document_anchor(
    line: str, document: str, line_number: int
) -> tuple[str, tuple[str, ...]]:
    stripped = line.strip()
    if document.endswith(".md"):
        nonrendered = stripped.startswith("<!--") and stripped.endswith("-->")
    else:
        nonrendered = stripped.startswith("%")
    if not nonrendered:
        raise VerificationError(
            f"{document}:{line_number}: external-source anchor must be non-rendered"
        )
    payload = line.split(SOURCE_ANCHOR_TAG, 1)[1].strip()
    if payload.endswith("-->"):
        payload = payload[:-3].rstrip()
    match = SOURCE_ANCHOR_RE.fullmatch(payload)
    if match is None:
        raise VerificationError(
            f"{document}:{line_number}: malformed external-source anchor"
        )
    source_id = match.group("source")
    values = [value.strip() for value in match.group("ranges").split(",")]
    return source_id, validate_ranges(values, source_id, document)


def collect_document_anchors(repo: Path) -> dict[tuple[str, str], tuple[str, ...]]:
    """Read every source-associated anchor from the audited document trees."""
    root = repo.resolve(strict=True)
    anchors: dict[tuple[str, str], tuple[str, ...]] = {}
    for root_parts in ANCHOR_DOCUMENT_ROOTS:
        document_root = root.joinpath(*root_parts)
        if not document_root.is_dir():
            continue
        for path in sorted(document_root.rglob("*")):
            if path.suffix not in {".md", ".tex"} or not path.is_file():
                continue
            relative = PurePosixPath(path.relative_to(root).as_posix())
            checked = checked_repo_path(root, relative, "anchor audit", "document")
            text = checked.read_text(encoding="utf-8")
            rendered_lines = []
            document_keys: list[tuple[str, str]] = []
            for line_number, line in enumerate(text.splitlines(), start=1):
                if SOURCE_ANCHOR_TAG not in line:
                    rendered_lines.append(line)
                    continue
                rendered_lines.append("")
                source_id, ranges = parse_document_anchor(
                    line, relative.as_posix(), line_number
                )
                key = (relative.as_posix(), source_id)
                if key in anchors:
                    raise VerificationError(
                        f"{relative}: duplicate anchor for {source_id}"
                    )
                anchors[key] = ranges
                document_keys.append(key)
            rendered_text = "\n".join(rendered_lines)
            for document, source_id in document_keys:
                for value in anchors[(document, source_id)]:
                    first, last = parse_range(value, source_id)
                    if not range_is_written(rendered_text, first, last):
                        raise VerificationError(
                            f"{source_id}: anchored range {value} is not written in {document}"
                        )
    return anchors


def validate_citation_anchors(
    repo: Path,
    sources: list[dict[str, Any]],
    expected_range_count: int,
) -> None:
    """Compare the manifest and audited documents in both directions."""
    manifest_anchors: dict[tuple[str, str], tuple[str, ...]] = {}
    for source in sources:
        source_id = source["arxiv_id"]
        citations = source.get("citation")
        if not isinstance(citations, list) or not citations:
            raise VerificationError(
                f"{source_id}: at least one [[source.citation]] is required"
            )
        for citation in citations:
            if not isinstance(citation, dict):
                raise VerificationError(f"{source_id}: citation must be a table")
            document = require_string(citation, "document", source_id)
            relative = document_relative_path(document, source_id)
            document_path = checked_repo_path(
                repo, relative, source_id, "citation document"
            )
            if not document_path.is_file():
                raise VerificationError(
                    f"{source_id}: cited document is missing: {document}"
                )
            ranges = validate_ranges(citation.get("ranges"), source_id, document)
            key = (relative.as_posix(), source_id)
            if key in manifest_anchors:
                raise VerificationError(
                    f"{source_id}: duplicate citation table for {document}"
                )
            manifest_anchors[key] = ranges

    document_anchors = collect_document_anchors(repo)
    if manifest_anchors.keys() != document_anchors.keys():
        absent = sorted(document_anchors.keys() - manifest_anchors.keys())
        stale = sorted(manifest_anchors.keys() - document_anchors.keys())
        raise VerificationError(
            "external-source anchor association mismatch; "
            f"absent from manifest={absent}, absent from documents={stale}"
        )
    for key, ranges in manifest_anchors.items():
        if document_anchors[key] != ranges:
            raise VerificationError(
                f"external-source ranges differ for {key}: "
                f"manifest={ranges}, document={document_anchors[key]}"
            )
    manifest_count = sum(len(ranges) for ranges in manifest_anchors.values())
    document_count = sum(len(ranges) for ranges in document_anchors.values())
    if manifest_count != expected_range_count or document_count != expected_range_count:
        raise VerificationError(
            f"external-source range count is manifest={manifest_count}, "
            f"documents={document_count}, expected={expected_range_count}"
        )


def validate_source_metadata(source: dict[str, Any]) -> PurePosixPath:
    source_id = require_string(source, "arxiv_id", "unknown source")
    if ARXIV_ID_RE.fullmatch(source_id) is None:
        raise VerificationError(f"invalid versioned arXiv ID {source_id!r}")
    for field in (
        "title",
        "eprint_url",
        "archive_filename",
        "archive_sha256",
        "source_filename",
        "source_sha256",
        "license",
        "license_url",
        "preservation",
        "local_path",
    ):
        require_string(source, field, source_id)
    expected_url = f"https://arxiv.org/e-print/{source_id}"
    if source["eprint_url"] != expected_url:
        raise VerificationError(
            f"{source_id}: eprint_url must be the official versioned arXiv endpoint"
        )
    expected_archive = f"arXiv-{source_id}.tar.gz"
    if source["archive_filename"] != expected_archive:
        raise VerificationError(
            f"{source_id}: archive_filename must be {expected_archive}"
        )
    source_filename(source)
    for field in ("archive_sha256", "source_sha256"):
        if SHA256_RE.fullmatch(source[field]) is None:
            raise VerificationError(f"{source_id}: {field} is not a SHA-256 digest")
    authors = source.get("authors")
    if not isinstance(authors, list) or not authors or not all(
        isinstance(author, str) and author for author in authors
    ):
        raise VerificationError(f"{source_id}: authors must be a nonempty string list")
    source_lines = source.get("source_lines")
    if not isinstance(source_lines, int) or source_lines <= 0:
        raise VerificationError(f"{source_id}: source_lines must be positive")

    preservation = source["preservation"]
    if preservation not in PRESERVATION_MODES:
        raise VerificationError(
            f"{source_id}: preservation must be one of {sorted(PRESERVATION_MODES)}"
        )
    license_name = source["license"]
    if license_name not in LICENSE_POLICIES:
        raise VerificationError(f"{source_id}: unsupported license {license_name!r}")
    expected_license_url, expected_preservation = LICENSE_POLICIES[license_name]
    if source["license_url"] != expected_license_url:
        raise VerificationError(
            f"{source_id}: license_url does not match the recorded license"
        )
    if preservation != expected_preservation:
        raise VerificationError(
            f"{source_id}: {license_name} requires {expected_preservation} preservation"
        )
    return canonical_local_relative(source)


def validate_local_path_collisions(sources: list[dict[str, Any]]) -> None:
    seen: dict[PurePosixPath, str] = {}
    for source in sources:
        source_id = source["arxiv_id"]
        relative = canonical_local_relative(source)
        if relative in seen:
            raise VerificationError(
                f"{source_id}: local_path collides with {seen[relative]} at {relative}"
            )
        seen[relative] = source_id


def load_manifest(
    manifest: Path = MANIFEST, repo: Path = REPO
) -> list[dict[str, Any]]:
    data = tomllib.loads(manifest.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1:
        raise VerificationError("unsupported external-source manifest schema")
    if data.get("generated_root") != "build/paper-sources":
        raise VerificationError("generated_root must be build/paper-sources")
    expected_range_count = data.get("cited_range_count")
    if not isinstance(expected_range_count, int) or expected_range_count <= 0:
        raise VerificationError("cited_range_count must be positive")
    sources = data.get("source")
    if not isinstance(sources, list) or not sources:
        raise VerificationError("external-source manifest has no [[source]] entries")

    seen_ids: set[str] = set()
    for source in sources:
        if not isinstance(source, dict):
            raise VerificationError("every [[source]] entry must be a table")
        relative = validate_source_metadata(source)
        source_id = source["arxiv_id"]
        if source_id in seen_ids:
            raise VerificationError(f"duplicate source {source_id}")
        seen_ids.add(source_id)
        checked_repo_path(repo, relative, source_id, "local_path")
    validate_local_path_collisions(sources)
    validate_citation_anchors(repo, sources, expected_range_count)
    return sources


def download_archive(
    source: dict[str, Any], opener: Callable[..., Any] | None = None
) -> bytes:
    source_id = source["arxiv_id"]
    request = urllib.request.Request(
        source["eprint_url"], headers={"User-Agent": "TNLean-source-verifier/1.0"}
    )
    open_url = opener or urllib.request.urlopen
    try:
        with open_url(request, timeout=60) as response:
            reported_name = response.headers.get_filename()
            if reported_name != source["archive_filename"]:
                raise VerificationError(
                    f"{source_id}: server reported archive filename {reported_name!r}, "
                    f"expected {source['archive_filename']!r}"
                )
            archive = response.read()
    except urllib.error.URLError as error:
        raise VerificationError(f"{source_id}: source download failed: {error}") from error
    actual = sha256(archive)
    if actual != source["archive_sha256"]:
        raise VerificationError(
            f"{source_id}: archive SHA-256 {actual} does not match "
            f"{source['archive_sha256']}"
        )
    return archive


def read_source_member(source: dict[str, Any], archive: bytes) -> bytes:
    source_id = source["arxiv_id"]
    filename = source_filename(source)
    try:
        with tarfile.open(fileobj=io.BytesIO(archive), mode="r:*") as source_archive:
            matches = [
                member for member in source_archive.getmembers() if member.name == filename
            ]
            if len(matches) != 1:
                raise VerificationError(
                    f"{source_id}: expected one exact archive member named {filename}"
                )
            member = matches[0]
            if not member.isfile() or member.name != filename:
                raise VerificationError(
                    f"{source_id}: {filename} is not an exact regular-file archive member"
                )
            extracted = source_archive.extractfile(member)
            if extracted is None:
                raise VerificationError(
                    f"{source_id}: could not read archive member {filename}"
                )
            return extracted.read()
    except (KeyError, tarfile.TarError) as error:
        raise VerificationError(f"{source_id}: cannot read {filename}: {error}") from error


def prepare_generated_parent(repo: Path, source: dict[str, Any]) -> Path:
    source_id = source["arxiv_id"]
    relative = canonical_local_relative(source)
    root = repo.resolve(strict=True)
    current = root
    for component in relative.parts[:-1]:
        current /= component
        if current.is_symlink():
            raise VerificationError(
                f"{source_id}: local_path traverses symlink component {component!r}"
            )
        try:
            current.mkdir()
        except FileExistsError:
            pass
        if current.is_symlink() or not current.is_dir():
            raise VerificationError(
                f"{source_id}: local_path parent {component!r} is not a safe directory"
            )
    target = checked_repo_path(repo, relative, source_id, "local_path")
    if target.exists() and not target.is_file():
        raise VerificationError(f"{source_id}: generated target is not a regular file")
    return target


def write_generated(repo: Path, source: dict[str, Any], data: bytes) -> Path:
    """Atomically replace one canonical generated file and clean failed temporaries."""
    source_id = source["arxiv_id"]
    relative = canonical_local_relative(source)
    path = prepare_generated_parent(repo, source)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            dir=path.parent,
            prefix=".tnlean-source-",
            suffix=".tmp",
            delete=False,
        ) as output:
            temporary = Path(output.name)
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.chmod(temporary, 0o644)
        checked = checked_repo_path(repo, relative, source_id, "local_path")
        if checked != path or path.parent.is_symlink() or path.is_symlink():
            raise VerificationError(f"{source_id}: generated target changed during write")
        os.replace(temporary, path)
        temporary = None
        return path
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def verify_source(source: dict[str, Any], data: bytes) -> tuple[int, int]:
    source_id = source["arxiv_id"]
    actual = sha256(data)
    if actual != source["source_sha256"]:
        raise VerificationError(
            f"{source_id}: source SHA-256 {actual} does not match "
            f"{source['source_sha256']}"
        )
    line_count = len(data.splitlines())
    if line_count != source["source_lines"]:
        raise VerificationError(
            f"{source_id}: source has {line_count} lines, "
            f"expected {source['source_lines']}"
        )
    ranges = [
        value for citation in source["citation"] for value in citation["ranges"]
    ]
    for value in ranges:
        _, last = parse_range(value, source_id)
        if last > line_count:
            raise VerificationError(
                f"{source_id}: cited range {value} exceeds the {line_count}-line source"
            )
    return line_count, len(ranges)


def process_source(
    source: dict[str, Any],
    *,
    fetch: bool,
    repo: Path = REPO,
    downloader: Callable[[dict[str, Any]], bytes] | None = None,
) -> None:
    source_id = source["arxiv_id"]
    path = local_path_for_source(repo, source)
    if not fetch:
        if not path.is_file():
            raise VerificationError(
                f"{source_id}: {source['local_path']} is missing; rerun with --fetch"
            )
        data = path.read_bytes()
        line_count, range_count = verify_source(source, data)
    else:
        get_archive = downloader or download_archive
        data = read_source_member(source, get_archive(source))
        line_count, range_count = verify_source(source, data)
        if source["preservation"] == "vendored":
            if not path.is_file():
                raise VerificationError(
                    f"{source_id}: vendored file is missing: {source['local_path']}"
                )
            if path.read_bytes() != data:
                raise VerificationError(
                    f"{source_id}: vendored file differs from the official archive member"
                )
        else:
            write_generated(repo, source, data)
    print(
        f"verified {source_id}: {source['source_filename']} "
        f"({line_count} lines; {range_count} cited ranges)"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "sources",
        nargs="*",
        metavar="ARXIV_ID",
        help="source IDs to verify (default: every manifest entry)",
    )
    parser.add_argument(
        "--fetch",
        action="store_true",
        help="download and verify official archives before checking source files",
    )
    args = parser.parse_args()

    try:
        sources = load_manifest()
        available = {source["arxiv_id"]: source for source in sources}
        requested = args.sources or list(available)
        unknown = [source_id for source_id in requested if source_id not in available]
        if unknown:
            raise VerificationError(f"unknown source IDs: {', '.join(unknown)}")
        for source_id in requested:
            process_source(available[source_id], fetch=args.fetch)
    except VerificationError as error:
        parser.exit(1, f"error: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
