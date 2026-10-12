#!/usr/bin/env python3
"""Regression tests for the docbuild manifest checker on synthetic manifests."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_docbuild_manifest as checker  # noqa: E402

LAKEFILE = """\
name = "docbuild"
packagesDir = "../.lake/packages"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "v1.0.0"

[[require]]
name = "TNLean"
path = "../"
"""


def package(name: str, rev: str, input_rev: str | None = None) -> dict:
    entry = {"name": name, "rev": rev, "type": "git"}
    if input_rev is not None:
        entry["inputRev"] = input_rev
    return entry


class DocbuildManifestTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root / "docbuild").mkdir()
        (self.root / "docbuild" / "lakefile.toml").write_text(LAKEFILE, encoding="utf-8")
        self.root_packages = [package("mathlib", "aaa"), package("QICLean", "bbb")]
        self.docs_packages = [
            package("mathlib", "aaa"),
            package("QICLean", "bbb"),
            package("«doc-gen4»", "ccc", "v1.0.0"),
        ]

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write(self, relative: str, packages: list[dict]) -> None:
        path = self.root / relative
        path.write_text(json.dumps({"version": "1.1.0", "packages": packages}), encoding="utf-8")

    def run_check(self) -> tuple[int, str]:
        self.write("lake-manifest.json", self.root_packages)
        self.write("docbuild/lake-manifest.json", self.docs_packages)
        output = io.StringIO()
        argv = ["check_docbuild_manifest.py", "--root", str(self.root)]
        with mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(output):
            status = checker.main()
        return status, output.getvalue()

    def test_agreeing_manifests_pass(self) -> None:
        status, output = self.run_check()
        self.assertEqual(status, 0, output)
        self.assertIn("agrees with TNLean on 2 packages", output)

    def test_package_missing_from_docbuild_fails(self) -> None:
        self.docs_packages = [p for p in self.docs_packages if p["name"] != "QICLean"]
        status, output = self.run_check()
        self.assertEqual(status, 1)
        self.assertIn("QICLean: pinned at bbb by TNLean, missing from docbuild", output)

    def test_stale_rev_fails(self) -> None:
        self.docs_packages[0] = package("mathlib", "old")
        status, output = self.run_check()
        self.assertEqual(status, 1)
        self.assertIn("mathlib: TNLean pins aaa, docbuild pins old", output)

    def test_stale_input_rev_fails(self) -> None:
        self.docs_packages[2] = package("«doc-gen4»", "ccc", "v0.9.0")
        status, output = self.run_check()
        self.assertEqual(status, 1)
        self.assertIn("doc-gen4: docbuild/lakefile.toml requires v1.0.0, its manifest records v0.9.0", output)

    def test_rev_pinned_requirement_missing_from_manifest_fails(self) -> None:
        self.docs_packages = self.docs_packages[:2]
        status, output = self.run_check()
        self.assertEqual(status, 1)
        self.assertIn("doc-gen4: required at v1.0.0 by docbuild/lakefile.toml, missing from its manifest", output)


if __name__ == "__main__":
    unittest.main()
