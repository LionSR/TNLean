#!/usr/bin/env python3
"""Check that the diagnostic QIC export is bounded and source-specific."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import export_coherent_qic_prerequisites as exporter


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "scripts").mkdir()
        self.qic = self.root / ".lake/packages/qiclean"
        self.qic.mkdir(parents=True)
        self.source = b"theorem example_true : True := True.intro\n"
        (self.qic / "QICLean/Analysis").mkdir(parents=True)
        (self.qic / "QICLean/Analysis/Example.lean").write_bytes(self.source)
        self.build = self.qic / ".lake/build/lib/lean/QICLean/Analysis"
        self.build.mkdir(parents=True)
        (self.build / "Example.olean").write_bytes(b"test compiled bytes")
        (self.build / "secret.txt").write_text("must not be exported")
        for p in (self.root, self.qic):
            (p / "lean-toolchain").write_text("leanprover/lean4:v-test\n")
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": n, "rev": n + "-pin"} for n in ("qiclean", "mathlib", "Gametheory")
        ]}))
        self.allowlist = self.root / "scripts/coherent_qic_prerequisites.json"
        self.allowlist.write_text(json.dumps({"modules": ["QICLean.Analysis.Example"]}))
        self.output = self.root / "export"

    def git(self, repo, *args):
        return b"qiclean-pin\n" if args == ("rev-parse", "HEAD") else self.source

    def test_only_allowlisted_companions_and_manifest(self):
        with patch.object(exporter, "git", self.git):
            manifest = exporter.export(self.root, self.output)
        self.assertEqual(sorted(p.relative_to(self.output).as_posix() for p in self.output.rglob("*")
                                if p.is_file()), ["QICLean/Analysis/Example.olean", "manifest.json"])
        self.assertEqual(manifest["qic_commit"], "qiclean-pin")
        self.assertEqual(manifest["modules"]["QICLean.Analysis.Example"]["source_sha256"],
                         exporter.digest(self.source))

    def test_build_targets_are_only_validated_qic_modules(self):
        with patch.object(exporter.subprocess, "run") as run:
            exporter.build_prerequisites(self.root)
        run.assert_called_once_with(
            ["lake", "build", "@qiclean/+QICLean.Analysis.Example:olean"],
            cwd=self.root, check=True,
        )
        self.allowlist.write_text(json.dumps({"modules": ["--arbitrary-target"]}))
        with patch.object(exporter.subprocess, "run") as run, self.assertRaises(ValueError):
            exporter.build_prerequisites(self.root)
        run.assert_not_called()

    def test_rejects_traversal_and_duplicate_names(self):
        for entries in (["QICLean...secret"], ["QICLean.Analysis.Example"] * 2):
            self.allowlist.write_text(json.dumps({"modules": entries}))
            with self.assertRaises(ValueError):
                exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_rejects_mismatched_source(self):
        def wrong_git(repo, *args):
            return b"qiclean-pin\n" if args == ("rev-parse", "HEAD") else b"other source"
        with patch.object(exporter, "git", wrong_git), self.assertRaises(ValueError):
            exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_size_limit_is_checked_before_copying(self):
        with patch.object(exporter, "git", self.git), patch.object(exporter, "MAX_BYTES", 1):
            with self.assertRaises(ValueError):
                exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_rejects_symlinked_artifacts(self):
        artifact = self.build / "Example.olean"
        artifact.unlink()
        artifact.symlink_to(self.build / "secret.txt")
        with patch.object(exporter, "git", self.git), self.assertRaises(ValueError):
            exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_existing_output_is_not_modified(self):
        self.output.mkdir()
        marker = self.output / "keep.txt"
        marker.write_text("keep")
        with patch.object(exporter, "git", self.git), self.assertRaises(ValueError):
            exporter.export(self.root, self.output)
        self.assertEqual(marker.read_text(), "keep")


if __name__ == "__main__":
    unittest.main()
