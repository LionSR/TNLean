#!/usr/bin/env python3
"""Adversarial tests for the external-paper-source verifier."""

from __future__ import annotations

import copy
import hashlib
import io
import os
import subprocess
import sys
import tarfile
import tempfile
import tomllib
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_external_paper_sources as verifier  # noqa: E402


class FakeHeaders:
    """The small part of an HTTP header mapping used by the verifier."""

    def __init__(self, filename: str):
        self.filename = filename

    def get_filename(self) -> str:
        return self.filename


class FakeResponse(io.BytesIO):
    """A context-managed in-memory response with a Content-Disposition name."""

    def __init__(self, data: bytes, filename: str):
        super().__init__(data)
        self.headers = FakeHeaders(filename)

    def __enter__(self) -> FakeResponse:
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()


def source_record(
    *,
    source_id: str = "1111.11111v1",
    filename: str = "source.tex",
    preservation: str = "download-only",
    source_data: bytes = b"source\n",
) -> dict[str, object]:
    """Return a minimal internally consistent source record for unit tests."""
    base = source_id.split("v", 1)[0]
    root = "Papers" if preservation == "vendored" else "build/paper-sources"
    return {
        "arxiv_id": source_id,
        "eprint_url": f"https://arxiv.org/e-print/{source_id}",
        "archive_filename": f"arXiv-{source_id}.tar.gz",
        "archive_sha256": "0" * 64,
        "source_filename": filename,
        "source_sha256": hashlib.sha256(source_data).hexdigest(),
        "source_lines": len(source_data.splitlines()),
        "preservation": preservation,
        "local_path": f"{root}/{base}/{filename}",
        "citation": [],
    }


def regular_archive(filename: str, data: bytes) -> bytes:
    """Build an in-memory tar archive containing one regular member."""
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w") as archive:
        member = tarfile.TarInfo(filename)
        member.size = len(data)
        archive.addfile(member, io.BytesIO(data))
    return buffer.getvalue()


def special_archive(filename: str, member_type: bytes) -> bytes:
    """Build an archive whose named source member is not a regular file."""
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w") as archive:
        member = tarfile.TarInfo(filename)
        member.type = member_type
        member.linkname = "elsewhere"
        archive.addfile(member)
    return buffer.getvalue()


class PathSafetyTests(unittest.TestCase):
    def test_lexical_path_rejects_platform_and_traversal_escapes(self) -> None:
        rejected = (
            "",
            "/absolute",
            "//server/share",
            "../escape",
            "safe/../escape",
            "./relative",
            "safe//file",
            "C:/drive",
            r"C:\drive",
            r"\\server\share",
            r"safe\file",
        )
        for path in rejected:
            with self.subTest(path=path), self.assertRaises(verifier.VerificationError):
                verifier.lexical_relative_path(path, "test", "local_path")

    def test_local_path_must_be_the_mode_specific_canonical_path(self) -> None:
        for preservation, path in (
            ("vendored", "Papers/NOTICE.md"),
            ("vendored", "build/paper-sources/1111.11111/source.tex"),
            ("download-only", "Papers/1111.11111/source.tex"),
            ("download-only", "build/paper-sources/other/source.tex"),
        ):
            source = source_record(preservation=preservation)
            source["local_path"] = path
            with self.subTest(path=path), self.assertRaises(verifier.VerificationError):
                verifier.canonical_local_relative(source)

    def test_two_versions_cannot_share_an_output(self) -> None:
        first = source_record(source_id="1111.11111v1")
        second = source_record(source_id="1111.11111v2")
        with self.assertRaisesRegex(verifier.VerificationError, "collides"):
            verifier.validate_local_path_collisions([first, second])

    def test_traversal_cannot_overwrite_an_existing_repository_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            notice = repo / "Papers" / "NOTICE.md"
            notice.parent.mkdir()
            notice.write_bytes(b"do not replace\n")
            source = source_record(filename="NOTICE.md", preservation="vendored")
            source["local_path"] = "Papers/../Papers/NOTICE.md"
            with self.assertRaises(verifier.VerificationError):
                verifier.write_generated(repo, source, b"replacement\n")
            self.assertEqual(notice.read_bytes(), b"do not replace\n")

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks are unavailable")
    def test_symlink_parent_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory) / "repo"
            outside = Path(directory) / "outside"
            (repo / "build").mkdir(parents=True)
            outside.mkdir()
            (repo / "build" / "paper-sources").symlink_to(
                outside, target_is_directory=True
            )
            source = source_record()
            with self.assertRaisesRegex(verifier.VerificationError, "symlink"):
                verifier.write_generated(repo, source, b"replacement\n")
            self.assertEqual(list(outside.iterdir()), [])

    def test_failed_atomic_replace_removes_the_temporary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            source = source_record()
            target = repo / str(source["local_path"])
            target.parent.mkdir(parents=True)
            target.write_bytes(b"original\n")
            with mock.patch.object(verifier.os, "replace", side_effect=OSError("stop")):
                with self.assertRaises(OSError):
                    verifier.write_generated(repo, source, b"replacement\n")
            self.assertEqual(target.read_bytes(), b"original\n")
            self.assertEqual(list(target.parent.glob(".tnlean-source-*.tmp")), [])


class ArchiveSafetyTests(unittest.TestCase):
    def test_named_special_members_are_rejected(self) -> None:
        source = source_record()
        for member_type in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.CHRTYPE):
            with self.subTest(member_type=member_type):
                archive = special_archive(str(source["source_filename"]), member_type)
                with self.assertRaisesRegex(
                    verifier.VerificationError, "regular-file"
                ):
                    verifier.read_source_member(source, archive)

    def test_duplicate_named_members_are_rejected(self) -> None:
        source = source_record()
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w") as archive:
            for data in (b"first\n", b"second\n"):
                member = tarfile.TarInfo(str(source["source_filename"]))
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))
        with self.assertRaisesRegex(verifier.VerificationError, "expected one exact"):
            verifier.read_source_member(source, buffer.getvalue())

    def test_special_member_failure_does_not_write(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            source = source_record()
            target = repo / str(source["local_path"])
            target.parent.mkdir(parents=True)
            target.write_bytes(b"original\n")
            archive = special_archive(
                str(source["source_filename"]), tarfile.SYMTYPE
            )
            with self.assertRaisesRegex(verifier.VerificationError, "regular-file"):
                verifier.process_source(
                    source,
                    fetch=True,
                    repo=repo,
                    downloader=lambda _source: archive,
                )
            self.assertEqual(target.read_bytes(), b"original\n")

    def test_archive_digest_failure_does_not_write(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            source = source_record()
            target = repo / str(source["local_path"])
            target.parent.mkdir(parents=True)
            target.write_bytes(b"original\n")
            archive = regular_archive(
                str(source["source_filename"]), b"source\n"
            )

            def opener(*_args: object, **_kwargs: object) -> FakeResponse:
                return FakeResponse(archive, str(source["archive_filename"]))

            def downloader(item: dict[str, object]) -> bytes:
                return verifier.download_archive(item, opener=opener)

            with self.assertRaisesRegex(verifier.VerificationError, "archive SHA-256"):
                verifier.process_source(
                    source, fetch=True, repo=repo, downloader=downloader
                )
            self.assertEqual(target.read_bytes(), b"original\n")

    def test_extracted_digest_failure_does_not_write(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            source = source_record(source_data=b"expected\n")
            target = repo / str(source["local_path"])
            target.parent.mkdir(parents=True)
            target.write_bytes(b"original\n")
            archive = regular_archive(
                str(source["source_filename"]), b"different\n"
            )
            with self.assertRaisesRegex(verifier.VerificationError, "source SHA-256"):
                verifier.process_source(
                    source,
                    fetch=True,
                    repo=repo,
                    downloader=lambda _source: archive,
                )
            self.assertEqual(target.read_bytes(), b"original\n")


class CitationAssociationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self.temporary.name)
        document = self.repo / "docs" / "audits" / "sources.md"
        document.parent.mkdir(parents=True)
        document.write_text(
            """# Source audit

Source one is used at lines 10--12 and 15.
<!-- TNLEAN_EXTERNAL_SOURCE_RANGES: 1111.11111v1 10-12, 15 -->

Source two is used at lines 20--21.
<!-- TNLEAN_EXTERNAL_SOURCE_RANGES: 2222.22222v1 20-21 -->
""",
            encoding="utf-8",
        )
        self.sources = [
            {
                "arxiv_id": "1111.11111v1",
                "citation": [
                    {
                        "document": "docs/audits/sources.md",
                        "ranges": ["10-12", "15"],
                    }
                ],
            },
            {
                "arxiv_id": "2222.22222v1",
                "citation": [
                    {
                        "document": "docs/audits/sources.md",
                        "ranges": ["20-21"],
                    }
                ],
            },
        ]

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_bidirectional_association_accepts_complete_inventory(self) -> None:
        verifier.validate_citation_anchors(self.repo, self.sources, 3)

    def test_cross_source_reassignment_fails(self) -> None:
        reassigned = copy.deepcopy(self.sources)
        reassigned[0]["citation"][0]["ranges"] = ["20-21"]
        reassigned[1]["citation"][0]["ranges"] = ["10-12", "15"]
        with self.assertRaisesRegex(verifier.VerificationError, "ranges differ"):
            verifier.validate_citation_anchors(self.repo, reassigned, 3)

    def test_omitted_manifest_range_fails_the_reverse_audit(self) -> None:
        omitted = copy.deepcopy(self.sources)
        omitted[0]["citation"][0]["ranges"] = ["10-12"]
        with self.assertRaisesRegex(verifier.VerificationError, "ranges differ"):
            verifier.validate_citation_anchors(self.repo, omitted, 2)

    def test_omitted_manifest_source_fails_the_reverse_audit(self) -> None:
        with self.assertRaisesRegex(verifier.VerificationError, "association mismatch"):
            verifier.validate_citation_anchors(self.repo, self.sources[:1], 2)

    def test_anchor_range_must_also_appear_in_reader_facing_prose(self) -> None:
        document = self.repo / "docs" / "audits" / "sources.md"
        document.write_text(
            """# Source audit

The source is cited without coordinates.
<!-- TNLEAN_EXTERNAL_SOURCE_RANGES: 1111.11111v1 10-12 -->
""",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(verifier.VerificationError, "is not written"):
            verifier.validate_citation_anchors(self.repo, self.sources[:1], 1)

    def test_reader_facing_machine_anchor_is_rejected(self) -> None:
        document = self.repo / "docs" / "audits" / "sources.md"
        document.write_text(
            """# Source audit

Lines 10--12 are used.
TNLEAN_EXTERNAL_SOURCE_RANGES: 1111.11111v1 10-12
""",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(verifier.VerificationError, "non-rendered"):
            verifier.validate_citation_anchors(self.repo, self.sources[:1], 1)


class GitAttributeTests(unittest.TestCase):
    def test_hostile_autocrlf_checkout_preserves_vendored_bytes(self) -> None:
        repository = Path(__file__).resolve().parents[1]
        paths = (
            Path("Papers/2203.12563/REsubmission.tex"),
            Path("Papers/2405.00439/MPU-DW.tex"),
        )
        manifest = tomllib.loads(
            (repository / "Papers" / "external_sources.toml").read_text(
                encoding="utf-8"
            )
        )
        pinned_hashes = {
            Path(source["local_path"]): source["source_sha256"]
            for source in manifest["source"]
            if source["preservation"] == "vendored"
        }
        self.assertEqual(set(paths), set(pinned_hashes))
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            (checkout / ".gitattributes").write_bytes(
                (repository / ".gitattributes").read_bytes()
            )
            for relative in paths:
                target = checkout / relative
                target.parent.mkdir(parents=True)
                target.write_bytes((repository / relative).read_bytes())
                self.assertEqual(
                    verifier.sha256(target.read_bytes()), pinned_hashes[relative]
                )
            subprocess.run(["git", "init", "-q"], cwd=checkout, check=True)
            subprocess.run(
                ["git", "-c", "core.autocrlf=false", "add", "."],
                cwd=checkout,
                check=True,
            )
            for relative in paths:
                (checkout / relative).unlink()
            subprocess.run(
                ["git", "-c", "core.autocrlf=true", "checkout", "--", *paths],
                cwd=checkout,
                check=True,
            )
            for relative in paths:
                self.assertEqual(
                    verifier.sha256((checkout / relative).read_bytes()),
                    pinned_hashes[relative],
                )
            attributes = subprocess.check_output(
                ["git", "check-attr", "text", "whitespace", "--", *paths],
                cwd=checkout,
                text=True,
            )
            for relative in paths:
                self.assertIn(f"{relative}: text: unset", attributes)
                self.assertIn(f"{relative}: whitespace: unset", attributes)


if __name__ == "__main__":
    unittest.main()
