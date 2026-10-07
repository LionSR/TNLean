"""Validator regressions. Synthetic evidence is test data, never build certification."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_openai_provenance as provenance

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "scripts/fixtures/openai_provenance"
SCHEMA = provenance.read_json(ROOT / "docs/provenance/openai-math.schema.json")
PLAN = provenance.read_json(ROOT / "docs/provenance/openai-math.json")


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.roots = {provenance.REPO: self.root, "openai/math": self.root / "upstream"}
        self.row = deepcopy(PLAN["entries"][0])
        self.row.update(id="fixture-adapted", status="ported")
        self.row["upstream"].update(declaration="OAI.PolynomialPEPS.Vertex", lines=[13, 13])
        self.row["upstream"]["url"] = self.row["upstream"]["url"].split("#")[0] + "#L13-L13"
        self.row["downstream"] = dict(repository=provenance.REPO,
                                      path="TNLean/Example.lean", declaration="Example.Vertex",
                                      name_status="declared")
        self.row["changes"] = ["Changed namespace to Example and natural-number notation to Nat; omitted unrelated declarations and imports."]
        self.text = (FIXTURES / "Adapted.lean.txt").read_text()
        self.source = (FIXTURES / "Source.lean.txt").read_bytes()
        self.write("TNLean/Example.lean", self.text)
        self.write("build.log", "Synthetic validator fixture: no Lean build was run.\n")
        self.write("axioms.log", "Synthetic fixture only.\n'Example.Vertex' does not depend on any axioms\n")
        self.row["verification"] = dict(result="passed", repository=provenance.REPO,
            revision="b" * 40, commands=[dict(kind=kind, command=command, exit_code=0,
                log=log, sha256=self.digest(log)) for kind, command, log in [
                    ("build", "lake build TNLean.Example", "build.log"),
                    ("axioms", "lake env lean Audit.lean", "axioms.log")]])
        self.stored = self.text.encode()
        self.mock_git = patch.object(provenance, "git_bytes", side_effect=self.git_bytes)
        self.mock_git.start()
        self.addCleanup(self.mock_git.stop)

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def digest(self, path):
        return hashlib.sha256((self.root / path).read_bytes()).hexdigest()

    def git_bytes(self, root, revision, path):
        if path.endswith(".tex"):
            return b"\\label{eq:target-error}"
        return self.source if root == self.roots["openai/math"] else self.stored

    def ledger(self, row=None):
        result = deepcopy(PLAN)
        result["entries"] = [self.row if row is None else row]
        return result

    def validate(self, row=None, scan=True):
        return provenance.validate([self.ledger(row)], SCHEMA, self.roots, scan=scan)

    def rejects(self, pattern, row=None):
        with self.assertRaisesRegex(provenance.Invalid, pattern):
            self.validate(row)

    def test_real_source_adaptation_notice(self):
        self.assertEqual(self.validate(), 1)

    def test_four_kinds_schema_fixtures(self):
        for path in sorted(FIXTURES.glob("planned-*.json")):
            with self.subTest(path=path.name):
                self.assertEqual(provenance.validate([provenance.read_json(path)], SCHEMA, {}, scan=False), 1)

    def test_negative_json_fixtures(self):
        for path in sorted(FIXTURES.glob("invalid-*.json")):
            with self.subTest(path=path.name), self.assertRaises(provenance.Invalid):
                provenance.validate([provenance.read_json(path)], SCHEMA, {}, scan=False)

    def test_changed_file_marked_copied(self):
        self.row["reuse_kind"] = "copied"
        self.rejects("changed file marked copied")

    def test_actual_unchanged_copy_and_sidecar(self):
        self.row["reuse_kind"] = "copied"
        self.row["downstream"]["declaration"] = "OAI.PolynomialPEPS.Vertex"
        self.stored = self.source
        self.write("TNLean/Example.lean", self.source.decode())
        sidecar = self.text.replace("Adapted from", "Copied from").replace(
            "Downstream declaration: Example.Vertex", "Downstream declaration: OAI.PolynomialPEPS.Vertex")
        self.write("TNLean/Example.lean.provenance", sidecar)
        self.write("axioms.log", "'OAI.PolynomialPEPS.Vertex' does not depend on any axioms\n")
        self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.assertEqual(self.validate(), 1)

    def test_missing_downstream_declaration(self):
        self.row["downstream"]["declaration"] = "Example.Missing"
        self.rejects("missing downstream declaration")

    def test_comment_does_not_supply_declaration(self):
        self.stored = ("/- " + self.text + " -/").encode()
        self.write("TNLean/Example.lean", self.stored.decode())
        self.rejects("missing downstream declaration")

    def test_string_does_not_supply_declaration(self):
        self.assertNotIn("Example.Vertex", provenance.declarations('def fake := "\nnamespace Example\nabbrev Vertex := Nat\n"'))

    def test_missing_immutable_source(self):
        self.row["upstream"] = None
        self.rejects("schema")

    def test_mutable_url(self):
        self.row["upstream"]["url"] = self.row["upstream"]["url"].replace(provenance.PIN, "main")
        self.rejects("immutable source URL")

    def test_wrong_source_revision(self):
        self.row["upstream"]["commit"] = "a" * 40
        self.rejects("pinned source")

    def test_missing_source_declaration(self):
        self.row["upstream"]["declaration"] = "OAI.Missing"
        self.rejects("missing source declaration")

    def test_reversed_source_lines(self):
        self.row["upstream"]["lines"] = [15, 13]
        self.rejects("reversed source lines")

    def test_wrong_namespace(self):
        self.row["downstream"]["declaration"] = "Other.Vertex"
        self.rejects("missing downstream declaration")

    def test_stale_evidence_revision(self):
        self.write("TNLean/Example.lean", self.text + "\n")
        self.rejects("differs from verified revision")

    def test_missing_evidence_root(self):
        del self.roots["openai/math"]
        self.rejects("repository root required")

    def test_missing_build_evidence(self):
        self.row["verification"]["commands"].pop(0)
        self.rejects("require build and axiom evidence")

    def test_tampered_log(self):
        self.write("build.log", "changed")
        self.rejects("log hash mismatch")

    def test_custom_axiom_rejected(self):
        self.write("axioms.log", "'Example.Vertex' depends on axioms: [propext, sorryAx]\n")
        self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.rejects("unapproved axiom")

    def test_standard_axioms_accepted(self):
        self.write("axioms.log", "'Example.Vertex' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
        self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.assertEqual(self.validate(), 1)

    def test_proposed_cannot_be_completed(self):
        self.row["downstream"]["name_status"] = "proposed"
        self.rejects("schema")

    def test_planned_cannot_claim_passed(self):
        self.row["status"] = "planned"
        self.rejects("schema")

    def test_path_traversal(self):
        for value in ("../escape", "/absolute", "a/../../b", "a\\b", "a/%2e%2e/b"):
            with self.subTest(value=value):
                self.row["upstream"]["path"] = value
                self.rejects("schema")

    def test_symlink_escape(self):
        (self.root / "escape").symlink_to(ROOT, target_is_directory=True)
        with self.assertRaisesRegex(provenance.Invalid, "escapes repository"):
            provenance.safe_file(self.root, "escape/LICENSE")

    def test_duplicate_across_shards(self):
        with self.assertRaisesRegex(provenance.Invalid, "duplicate entry id"):
            provenance.validate([self.ledger(), self.ledger()], SCHEMA, self.roots)

    def test_duplicate_downstream_key(self):
        other = deepcopy(self.row)
        other["id"] = "second"
        with self.assertRaisesRegex(provenance.Invalid, "duplicate downstream"):
            provenance.validate([self.ledger(), self.ledger(other)], SCHEMA, self.roots)

    def test_duplicate_json_key(self):
        self.write("bad.json", '{"entries": [], "entries": []}')
        with self.assertRaisesRegex(provenance.Invalid, "duplicate JSON key"):
            provenance.read_json(self.root / "bad.json")

    def test_orphan_notice(self):
        self.write("TNLean/Orphan.lean", "/-!\nProvenance-ID: orphan\n-/")
        self.rejects("orphan notice")

    def test_missing_change_notice(self):
        self.stored = self.text.replace(self.row["changes"][0], "Unspecified.").encode()
        self.write("TNLean/Example.lean", self.stored.decode())
        self.rejects("concrete change description")

    def test_missing_attribution_notice(self):
        self.row["notices"] = [{"source_path": "NOTICE", "text": "Third-party attribution"}]
        self.rejects("notice absent from claimed source")

    def test_original_no_upstream_mapping(self):
        self.row.update(reuse_kind="original", upstream=None, no_upstream_proof_text_reused=True)
        self.text = self.text.replace("Adapted from OpenAI's openai/math repository (Apache-2.0).",
            "Source: September 24, 2026, eq:target-error; independently formalized;\nno upstream Lean proof text reused.")
        self.stored = self.text.encode()
        self.write("TNLean/Example.lean", self.text)
        self.assertEqual(self.validate(), 1)

    def test_completed_replacement(self):
        self.row.update(status="replaced", reuse_kind="existing_library", upstream=None)
        self.row["library"] = dict(repository=provenance.REPO, commit="b" * 40,
            path="TNLean/Example.lean", declaration="Example.Vertex", lines=[14, 15],
            url=f"https://github.com/{provenance.REPO}/blob/{'b' * 40}/TNLean/Example.lean#L14-L15")
        # No replacement attribution is added to an existing library module.
        self.stored = b"\n" * 12 + b"namespace Example\nabbrev Vertex := Nat\nend Example\n"
        self.write("TNLean/Example.lean", self.stored.decode())
        self.assertEqual(self.validate(), 1)

    def test_axiom_target_requires_exact_quoted_name(self):
        for output in (
            "'NotExample.Vertex' does not depend on any axioms",
            "'Other.Example.Vertex' does not depend on any axioms",
            "'Example.VertexExtra' does not depend on any axioms",
            "Example.Vertex does not depend on any axioms",
            "prefix 'Example.Vertex' does not depend on any axioms",
        ):
            with self.subTest(output=output):
                self.write("axioms.log", output + "\n")
                self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
                self.rejects("axiom log missing downstream declaration")

    def test_later_bad_axiom_record_is_not_ignored(self):
        self.write("axioms.log", "'Example.Vertex' depends on axioms: [propext]\n"
                   "'Example.Vertex' depends on axioms: [sorryAx]\n")
        self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.rejects("unapproved axiom")

    def test_conflicting_exact_target_records(self):
        self.write("axioms.log", "'Example.Vertex' does not depend on any axioms\n"
                   "'Example.Vertex' depends on axioms: [propext]\n")
        self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.rejects("conflicting exact-target")

    def test_malformed_exact_target_record_is_not_ignored(self):
        self.write("axioms.log", "'Example.Vertex' does not depend on any axioms\n"
                   "'Example.Vertex' depends on axioms: unreadable\n")
        self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.rejects("malformed exact-target")

    def test_multiline_axiom_output_and_unrelated_records(self):
        self.write("axioms.log", "'Other.theorem' depends on axioms: [sorryAx]\n"
                   "'Example.Vertex' depends on axioms:\n[propext,\nClassical.choice, Quot.sound]\n")
        self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.assertEqual(self.validate(), 1)

    def test_same_declaration_different_path_rejected(self):
        first, second = deepcopy(PLAN), deepcopy(PLAN)
        second["entries"][0]["id"] = "other-location"
        second["entries"][0]["downstream"]["path"] = "QICLean/Other.lean"
        with self.assertRaisesRegex(provenance.Invalid, "duplicate downstream"):
            provenance.validate([first, second], SCHEMA, {}, scan=False)

    def test_repository_casing_cannot_bypass_uniqueness(self):
        first, second = deepcopy(PLAN), deepcopy(PLAN)
        second["entries"][0]["id"] = "other-casing"
        second["entries"][0]["downstream"]["repository"] = "lionsr/qiclean"
        with self.assertRaisesRegex(provenance.Invalid, "duplicate downstream"):
            provenance.validate([first, second], SCHEMA, {}, scan=False)

    def test_wrong_manuscript_label(self):
        self.row["paper_sources"][0]["labels"] = ["invented-label"]
        self.rejects("missing manuscript label")

    def test_noncanonical_source_path(self):
        self.row["upstream"]["path"] = "lean//Example.lean"
        self.rejects("schema")

    def test_replacement_wrong_dependency_pin(self):
        self.row.update(status="replaced", reuse_kind="existing_library", upstream=None)
        self.row["library"] = dict(repository="LionSR/QICLean", commit="b" * 40,
            path="QICLean/Example.lean", declaration="Example.Vertex", lines=[14, 15],
            url=f"https://github.com/LionSR/QICLean/blob/{'b' * 40}/QICLean/Example.lean#L14-L15")
        self.row["downstream"].update(repository="LionSR/QICLean", path="QICLean/Example.lean")
        self.roots["LionSR/QICLean"] = self.root / "qic"
        self.write("lake-manifest.json", json.dumps({"packages": [{
            "url": "https://github.com/LionSR/QICLean.git", "rev": "c" * 40}]}))
        self.rejects("differs from the dependency pin")

    def test_duplicate_qualified_name_across_paths(self):
        first = deepcopy(PLAN)
        other = deepcopy(first)
        other["entries"][0]["id"] = "renamed-file"
        other["entries"][0]["downstream"]["path"] = "QICLean/Other.lean"
        with self.assertRaisesRegex(provenance.Invalid, "duplicate downstream"):
            provenance.validate([first, other], SCHEMA, {}, scan=False)

    def test_proposed_declaration_names_are_valid(self):
        for name in ("Example..Vertex", "123", "Example.", ".Example", "Example/Vertex"):
            ledger = deepcopy(PLAN)
            ledger["entries"][0]["downstream"]["declaration"] = name
            with self.subTest(name=name), self.assertRaisesRegex(provenance.Invalid, "schema"):
                provenance.validate([ledger], SCHEMA, {}, scan=False)
        for name in ("vertex", "Example.Vertex'", "Example.δ"):
            ledger = deepcopy(PLAN)
            ledger["entries"][0]["downstream"]["declaration"] = name
            self.assertEqual(provenance.validate([ledger], SCHEMA, {}, scan=False), 1)

    def test_planned_downstream_path_is_canonical(self):
        for path in ("QICLean//Other.lean", "QICLean/./Other.lean"):
            ledger = deepcopy(PLAN)
            ledger["entries"][0]["downstream"]["path"] = path
            with self.subTest(path=path), self.assertRaisesRegex(provenance.Invalid, "schema"):
                provenance.validate([ledger], SCHEMA, {}, scan=False)

    def test_unrecorded_derivative_declaration(self):
        self.stored = (self.text + "\nabbrev Unrecorded := Nat\n").encode()
        self.write("TNLean/Example.lean", self.stored.decode())
        self.rejects("unrecorded declarations.*Unrecorded")

    def test_original_declaration_can_complete_mixed_module_inventory(self):
        original = deepcopy(self.row)
        original.update(id="fixture-original", reuse_kind="original", upstream=None,
                        no_upstream_proof_text_reused=True)
        original["downstream"]["declaration"] = "Original"
        block = ("\n/-!\nProvenance-ID: fixture-original\nDownstream declaration: Original\n"
                 "Source: September 24, 2026, eq:target-error; independently formalized;\n"
                 "no upstream Lean proof text reused.\n-/\nabbrev Original := Nat\n")
        self.stored = (self.text + block).encode()
        self.write("TNLean/Example.lean", self.stored.decode())
        self.write("axioms.log", "'Example.Vertex' does not depend on any axioms\n"
                   "'Original' does not depend on any axioms\n")
        for row in (self.row, original):
            row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.assertEqual(provenance.validate([self.ledger(), self.ledger(original)],
                                            SCHEMA, self.roots), 2)

    def test_axiom_output_requires_exact_name_and_complete_line(self):
        for output in ("'NotExample.Vertex' does not depend on any axioms\n",
                       "'Example.VertexExtra' does not depend on any axioms\n",
                       "prefix Example.Vertex does not depend on any axioms\n",
                       "'Example.Vertex' does not depend on any axioms but this is not output\n",
                       "'NotExample.Vertex' depends on axioms: [propext]\n"):
            with self.subTest(output=output):
                self.write("axioms.log", output)
                self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
                self.rejects("axiom log missing downstream declaration")

    def test_every_exact_target_axiom_record_is_checked(self):
        for first in ("'Example.Vertex' depends on axioms: [propext]\n",
                      "'Example.Vertex' does not depend on any axioms\n"):
            with self.subTest(first=first):
                self.write("axioms.log", first + "'Example.Vertex' depends on axioms: [propext, sorryAx]\n")
                self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
                self.rejects("unapproved axiom")


    def test_axiom_output_accepts_wrapped_standard_list(self):
        self.write("axioms.log", "'Example.Vertex' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n")
        self.row["verification"]["commands"][1]["sha256"] = self.digest("axioms.log")
        self.assertEqual(self.validate(), 1)

    def source_header(self, header):
        self.source = (header + "\n").encode() + (FIXTURES / "Source.lean.txt").read_bytes()
        self.row["upstream"]["lines"] = [14, 14]
        self.row["upstream"]["url"] = self.row["upstream"]["url"].split("#")[0] + "#L14-L14"

    def test_opening_legal_notices_cannot_be_omitted(self):
        for header in ("/- Copyright 2026 Example contributor. -/",
                       "/- Patent notice: certain claims reserved. -/",
                       "/- Trademark: ExampleMark belongs to Example Corp. -/",
                       "/- License: Apache-2.0. -/", "-- Authors: Example contributor"):
            with self.subTest(header=header):
                self.source_header(header)
                self.rejects("opening upstream legal/author notice missing")

    def test_retained_opening_notice_is_accepted(self):
        header = "/- Copyright 2026 Example contributor. -/"
        self.source_header(header)
        self.row["notices"] = [{"source_path": self.row["upstream"]["path"], "text": header}]
        self.stored = (header + "\n" + self.text.replace("#L13-L13", "#L14-L14")).encode()
        self.write("TNLean/Example.lean", self.stored.decode())
        self.assertEqual(self.validate(), 1)
        self.stored = self.text.replace("#L13-L13", "#L14-L14").encode()
        self.write("TNLean/Example.lean", self.stored.decode())
        self.rejects("retained upstream notice missing downstream")

    def test_excluded_does_not_claim_completed_verification(self):
        excluded = deepcopy(self.row)
        excluded["status"] = "excluded"
        self.rejects("schema", excluded)
        excluded["verification"] = {"result": "pending"}
        # Exclusion is a decision, not a live module notice or completed proof.
        self.assertEqual(provenance.validate([self.ledger(excluded)], SCHEMA, {}, scan=False), 1)

    def test_anonymous_noncomputable_section_preserves_namespace(self):
        source = ("namespace Outer\nnoncomputable section\nabbrev before := Nat\nend\n"
                  "abbrev after := Nat\nend Outer\n")
        self.assertEqual(provenance.declarations(source), {"Outer.before": 3, "Outer.after": 5})

    def test_named_sections_and_root_qualified_names(self):
        source = ("namespace Outer\nsection Local\nnamespace Inner\n"
                  "abbrev _root_.global := Nat\nend Inner\nend Local\n"
                  "abbrev after := Nat\nend Outer\n")
        self.assertEqual(provenance.declarations(source), {"global": 4, "Outer.after": 7})

    def test_nested_legal_header_is_preserved_whole(self):
        header = "/- Copyright holder. /- additional attribution -/ License: Apache-2.0. -/"
        self.assertEqual(provenance.leading_legal_notices(header + "\nimport Mathlib\n"),
                         [header[2:-2].strip()])

    def test_declaration_scan_rejects_ambiguous_duplicate(self):
        with self.assertRaisesRegex(provenance.Invalid, "ambiguous declaration"):
            provenance.declarations("abbrev x := Nat\nabbrev x := Nat\n")


    def test_git_reads_recorded_revision_not_worktree(self):
        self.mock_git.stop()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "."], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Fixture", "-c",
                        "user.email=fixture@example.invalid", "commit", "-qm", "fixture"], check=True)
        revision = subprocess.check_output(["git", "-C", str(self.root), "rev-parse", "HEAD"], text=True).strip()
        self.write("TNLean/Example.lean", "changed")
        self.assertEqual(provenance.git_bytes(self.root, revision, "TNLean/Example.lean"), self.text.encode())


if __name__ == "__main__":
    unittest.main()
