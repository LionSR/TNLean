#!/usr/bin/env python3
"""Test bounded unchanged-source TN prerequisite export without running Lean."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import export_coherent_tn_prerequisites as exporter


class TNExportTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.baseline, self.head, self.pin = "a" * 40, "b" * 40, "c" * 40
        self.sources = {
            "TNLean/Example.lean": b"/- import TNLean.Secret -/\nimport TNLean.Dependency\nexample : True := .intro\n",
            "TNLean/Dependency.lean": b"import Mathlib.Data.Nat.Basic\nexample : True := .intro\n",
            "lean-toolchain": b"leanprover/lean4:v-test\n",
            "lakefile.toml": b'name = "TNLean"\n',
            "lake-manifest.json": json.dumps({"packages": [{"name": "qiclean", "rev": self.pin}]}).encode(),
        }
        for name, content in self.sources.items():
            p = self.root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(content)
        (self.root / "scripts").mkdir()
        self.allowlist = self.root / "scripts/coherent_tn_prerequisites.json"
        self.allowlist.write_text(json.dumps({"baseline_commit": self.baseline, "modules": ["TNLean.Example"]}))
        self.checkout = self.root / ".lake/packages/qiclean"
        self.checkout.mkdir(parents=True)
        self.build = self.root / ".lake/build/lib/lean/TNLean"
        self.build.mkdir(parents=True)
        (self.build / "Example.olean").write_bytes(b"fixture compiled bytes")
        (self.build / "Example.ilean").write_bytes(b"fixture metadata bytes")
        (self.build / "unrelated.txt").write_text("must not be exported")
        self.output = self.root / "export"

    def git(self, repo, *args):
        if args == ("rev-parse", "HEAD"):
            return ((self.head if repo == self.root else self.pin) + "\n").encode()
        if args[0] == "status":
            return b""
        if args[0] == "show":
            return self.sources[args[1].split(":", 1)[1]]
        raise AssertionError(args)

    def test_only_allowlisted_artifacts_and_full_tn_source_closure(self):
        with patch.object(exporter, "git", self.git):
            manifest = exporter.export(self.root, self.output)
        self.assertEqual(set(manifest["tn_source_closure"]), {"TNLean.Example", "TNLean.Dependency"})
        self.assertEqual(manifest["source_commit"], self.head)
        self.assertEqual(manifest["baseline_commit"], self.baseline)
        self.assertEqual(manifest["dependency_pins"], {"qiclean": self.pin})
        self.assertEqual(sorted(p.relative_to(self.output).as_posix() for p in self.output.rglob("*")
                                if p.is_file()), ["TNLean/Example.ilean", "TNLean/Example.olean", "manifest.json"])

    def test_header_parser_ignores_comments_and_collects_public_multiple_imports(self):
        self.assertEqual(exporter.header_imports(
            "/- import TNLean.Secret -/\nmodule\npublic import TNLean.A TNLean.B\n"
            "import Mathlib.X -- ignored\nnamespace Foo\nimport TNLean.NotAHeader\n"
        ), ["TNLean.A", "TNLean.B", "Mathlib.X"])

    def test_rejects_traversal_duplicates_and_bad_baseline(self):
        for modules, baseline in [(["TNLean...secret"], self.baseline),
                                  (["TNLean.Example"] * 2, self.baseline),
                                  (["TNLean.Example"], "HEAD:secret")]:
            self.allowlist.write_text(json.dumps({"baseline_commit": baseline, "modules": modules}))
            with patch.object(exporter, "git", self.git), self.assertRaises(ValueError):
                exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_rejects_changed_selected_or_transitive_source(self):
        for name in ("TNLean/Example.lean", "TNLean/Dependency.lean"):
            path = self.root / name
            path.write_bytes(self.sources[name] + b"-- changed\n")
            with patch.object(exporter, "git", self.git), self.assertRaises(ValueError):
                exporter.export(self.root, self.output)
            path.write_bytes(self.sources[name])
        self.assertFalse(self.output.exists())

    def test_rejects_dependency_pin_or_source_drift(self):
        for kind in ("pin", "dirty"):
            def changed_git(repo, *args):
                if repo == self.checkout:
                    if kind == "pin" and args == ("rev-parse", "HEAD"):
                        return b"wrong-pin\n"
                    if kind == "dirty" and args[0] == "status":
                        return b" M QICLean/Changed.lean\n"
                return self.git(repo, *args)
            with patch.object(exporter, "git", changed_git), self.assertRaises(ValueError):
                exporter.export(self.root, self.output)

    def test_rejects_unsafe_dependency_names(self):
        bad = json.dumps({"packages": [{"name": "../secret", "rev": self.pin}]}).encode()
        self.sources["lake-manifest.json"] = bad
        (self.root / "lake-manifest.json").write_bytes(bad)
        with patch.object(exporter, "git", self.git), self.assertRaises(ValueError):
            exporter.export(self.root, self.output)

    def test_workflow_upload_gate_order_and_early_timing_capture(self):
        workflow = (Path(__file__).resolve().parents[1] / ".github/workflows/pr-ci.yml").read_text()
        names = ["Prepare verified coherent TN prerequisites", "Export coherent TN prerequisites",
                 "Check coherent sector conversion targets", "Build Lean project and capture timings"]
        positions = [workflow.index("- name: " + name) for name in names]
        self.assertEqual(positions, sorted(positions))
        upload = workflow[positions[1]:positions[2]]
        self.assertIn("steps.coherent-tn-prerequisites.outcome == 'success'", upload)
        self.assertIn("retention-days: 1", upload)
        target = workflow[positions[2]:positions[3]]
        self.assertNotIn("continue-on-error", target)
        self.assertIn("lake --fail-fast build", target)
        self.assertIn('tee -a "$RUNNER_TEMP/lake-build.log"', target)
        self.assertNotIn('tee "$RUNNER_TEMP/lake-build.log"', workflow)

    def test_rejects_missing_or_symlinked_artifact(self):
        artifact = self.build / "Example.olean"
        artifact.unlink()
        with patch.object(exporter, "git", self.git), self.assertRaises(ValueError):
            exporter.export(self.root, self.output)
        artifact.symlink_to(self.build / "unrelated.txt")
        with patch.object(exporter, "git", self.git), self.assertRaises(ValueError):
            exporter.export(self.root, self.output)

    def test_byte_cap_includes_provenance_and_precedes_writes(self):
        with patch.object(exporter, "git", self.git), patch.object(exporter, "MAX_BYTES", 200):
            with self.assertRaises(ValueError):
                exporter.export(self.root, self.output)
        self.assertFalse(self.output.exists())

    def test_existing_output_is_preserved(self):
        self.output.mkdir()
        marker = self.output / "keep.txt"
        marker.write_text("keep")
        with patch.object(exporter, "git", self.git), self.assertRaises(ValueError):
            exporter.export(self.root, self.output)
        self.assertEqual(marker.read_text(), "keep")

    def test_build_targets_are_scoped_and_failures_prevent_export(self):
        with patch.object(exporter, "git", self.git), patch.object(exporter.subprocess, "run") as run:
            exporter.export(self.root, self.output, build=True)
        run.assert_called_once_with(["lake", "build", "@/+TNLean.Example:olean"], cwd=self.root, check=True)
        other = self.root / "failed"
        with patch.object(exporter, "git", self.git), patch.object(exporter.subprocess, "run", side_effect=OSError):
            with self.assertRaises(OSError):
                exporter.export(self.root, other, build=True)
        self.assertFalse(other.exists())

    def test_build_cannot_change_source_state(self):
        def mutate(*args, **kwargs):
            (self.root / "TNLean/Dependency.lean").write_text("-- changed by build\n")
        with patch.object(exporter, "git", self.git), patch.object(exporter.subprocess, "run", mutate):
            with self.assertRaises(ValueError):
                exporter.export(self.root, self.output, build=True)
        self.assertFalse(self.output.exists())


if __name__ == "__main__":
    unittest.main()
