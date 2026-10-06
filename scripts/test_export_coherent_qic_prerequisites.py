#!/usr/bin/env python3
"""Check that the diagnostic QIC export is bounded and source-specific."""
import json
from pathlib import Path
import subprocess
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
        self.pins = {n: str(i) * 40 for i, n in enumerate(
            ("qiclean", "mathlib", "Gametheory", "batteries"), start=1)}
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": n, "rev": rev} for n, rev in self.pins.items()
        ]}))
        self.allowlist = self.root / "scripts/coherent_qic_prerequisites.json"
        self.allowlist.write_text(json.dumps({"modules": ["QICLean.Analysis.Example"]}))
        self.output = self.root / "export"

    def git(self, repo, *args):
        if args == ("rev-parse", "HEAD"):
            return (self.pins[repo.name] + "\n").encode()
        if args[0] == "status":
            self.assertEqual(args, ("status", "--porcelain", "--untracked-files=all", "--",
                                    "*.lean", "lean-toolchain", "lake-manifest.json", "lakefile.*"))
            return b""
        self.assertEqual(args[0], "show")
        return self.source

    def test_only_allowlisted_companions_and_manifest(self):
        with patch.object(exporter, "git", self.git):
            manifest = exporter.export(self.root, self.output)
        self.assertEqual(sorted(p.relative_to(self.output).as_posix() for p in self.output.rglob("*")
                                if p.is_file()), ["QICLean/Analysis/Example.olean", "manifest.json"])
        self.assertEqual(manifest["qic_commit"], self.pins["qiclean"])
        self.assertEqual(manifest["dependency_pins"], self.pins)
        self.assertTrue(manifest["dependency_lean_config_sources_clean"])
        self.assertEqual(manifest["modules"]["QICLean.Analysis.Example"]["source_sha256"],
                         exporter.digest(self.source))

    def test_build_targets_are_only_validated_qic_modules(self):
        with patch.object(exporter, "git", self.git), patch.object(exporter.subprocess, "run") as run:
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
            return b"other source" if args[0] == "show" else self.git(repo, *args)
        with patch.object(exporter, "git", wrong_git), self.assertRaises(ValueError):
            exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_rejects_every_recorded_dependency_at_another_revision(self):
        for name in self.pins:
            with self.subTest(dependency=name):
                def wrong_git(repo, *args):
                    if repo.name == name and args == ("rev-parse", "HEAD"):
                        return b"wrong-pin\n"
                    return self.git(repo, *args)
                with patch.object(exporter, "git", wrong_git), self.assertRaisesRegex(
                        ValueError, f"checkout differs from its pin: {name}"):
                    exporter.export(self.root, self.output)
                self.assertFalse(self.output.exists())

    def test_rejects_dirty_transitive_qic_source_before_build(self):
        def dirty_git(repo, *args):
            if repo.name == "qiclean" and args[0] == "status":
                return b" M QICLean/Analysis/UnlistedDependency.lean\n"
            return self.git(repo, *args)
        with patch.object(exporter, "git", dirty_git), \
                patch.object(exporter.subprocess, "run") as run, self.assertRaisesRegex(
                    ValueError, "Lean/config sources are dirty: qiclean"):
            exporter.build_prerequisites(self.root)
        run.assert_not_called()
        self.assertFalse(self.output.exists())

    def test_rejects_dirty_dependency_config_or_untracked_source(self):
        for name in self.pins:
            for status in (b" M lakefile.lean\n", b"?? Nested/Untracked.lean\n"):
                with self.subTest(dependency=name, status=status):
                    def dirty_git(repo, *args):
                        if repo.name == name and args[0] == "status":
                            return status
                        return self.git(repo, *args)
                    with patch.object(exporter, "git", dirty_git), self.assertRaisesRegex(
                            ValueError, f"Lean/config sources are dirty: {name}"):
                        exporter.export(self.root, self.output)
                    self.assertFalse(self.output.exists())

    def test_rechecks_dependency_state_after_build(self):
        built = False

        def run(*_args, **_kwargs):
            nonlocal built
            built = True

        def dirty_git(repo, *args):
            if built and repo.name == "qiclean" and args[0] == "status":
                return b" M QICLean/Analysis/UnlistedDependency.lean\n"
            return self.git(repo, *args)
        with patch.object(exporter, "git", dirty_git), \
                patch.object(exporter.subprocess, "run", run), self.assertRaisesRegex(
                    ValueError, "Lean/config sources are dirty: qiclean"):
            exporter.build_prerequisites(self.root)
        self.assertTrue(built)
        self.assertFalse(self.output.exists())

    def test_rejects_invalid_or_duplicate_dependency_metadata(self):
        for packages in ([{"name": "../outside", "rev": "a" * 40}],
                         [{"name": "qiclean", "rev": "not-a-commit"}],
                         [{"name": "qiclean", "rev": "1" * 40}] * 2):
            (self.root / "lake-manifest.json").write_text(json.dumps({"packages": packages}))
            with patch.object(exporter, "git", self.git), self.assertRaisesRegex(
                    ValueError, "invalid or duplicate dependency"):
                exporter.export(self.root, self.output)
            self.assertFalse(self.output.exists())

    def test_real_git_rejects_dirty_transitive_source_and_dependency_config(self):
        for name in self.pins:
            repo = self.root / ".lake/packages" / name
            repo.mkdir(parents=True, exist_ok=True)
            (repo / ".gitignore").write_text(".lake/\n")
            (repo / "lakefile.toml").write_text('name = "fixture"\n')
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
            subprocess.run(["git", "-C", str(repo), "-c", "user.name=Fixture",
                            "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture"],
                           check=True)
            self.pins[name] = exporter.git(repo, "rev-parse", "HEAD").decode().strip()
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": n, "rev": rev} for n, rev in self.pins.items()
        ]}))
        exporter.export(self.root, self.output)
        unlisted = self.qic / "QICLean/Analysis/UnlistedDependency.lean"
        unlisted.write_text("-- untracked transitive source\n")
        with self.assertRaisesRegex(ValueError, "sources are dirty: qiclean"):
            exporter.export(self.root, self.root / "dirty-qic")
        unlisted.unlink()
        (self.root / ".lake/packages/mathlib/lakefile.toml").write_text('name = "changed"\n')
        with self.assertRaisesRegex(ValueError, "sources are dirty: mathlib"):
            exporter.export(self.root, self.root / "dirty-mathlib")
        self.assertFalse((self.root / "dirty-qic").exists())
        self.assertFalse((self.root / "dirty-mathlib").exists())

    def test_size_limit_is_checked_before_copying(self):
        with patch.object(exporter, "git", self.git), patch.object(exporter, "MAX_BYTES", 1):
            with self.assertRaises(ValueError):
                exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_manifest_is_included_in_size_limit_before_creating_output(self):
        artifact_bytes = (self.build / "Example.olean").stat().st_size
        with patch.object(exporter, "git", self.git), \
                patch.object(exporter, "MAX_BYTES", artifact_bytes), self.assertRaisesRegex(
                    ValueError, "including provenance exceeds"):
            exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_manifest_inclusive_size_boundary(self):
        with patch.object(exporter, "git", self.git):
            exporter.export(self.root, self.output)
        total = sum(p.stat().st_size for p in self.output.rglob("*") if p.is_file())
        fits, too_small = self.root / "fits", self.root / "too-small"
        with patch.object(exporter, "git", self.git), patch.object(exporter, "MAX_BYTES", total):
            exporter.export(self.root, fits)
        with patch.object(exporter, "git", self.git), patch.object(exporter, "MAX_BYTES", total - 1):
            with self.assertRaisesRegex(ValueError, "including provenance exceeds"):
                exporter.export(self.root, too_small)
        self.assertFalse(too_small.exists())

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
