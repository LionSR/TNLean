#!/usr/bin/env python3
"""Unit tests for the Lean module naming, file-size, import and pass-through policy checkers."""

from __future__ import annotations

import contextlib
import io
import subprocess
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path

import check_import_layers as layers
import check_numbered_lean_files as numbered
import check_oversized_lean_files as oversized
import check_pass_through_declarations as forwarding


class CapturedCheck(unittest.TestCase):
    def capture(self, function: Callable[..., int], *args: object) -> tuple[int, str]:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = function(*args)
        return status, output.getvalue()


class NumberedLeanFilePolicyTests(CapturedCheck):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def track(self, relative: str, source: str = "def x := 1\n") -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        subprocess.run(["git", "-C", str(self.root), "add", relative], check=True)

    def check(
        self,
        debt: frozenset[str] = frozenset(),
        exceptions: dict[str, str] | None = None,
        base_debt: frozenset[str] | None = None,
    ) -> tuple[int, str]:
        return self.capture(
            numbered.check_numbered_files,
            self.root,
            debt,
            {} if exceptions is None else exceptions,
            base_debt,
        )

    def test_new_numbered_production_file_fails_with_guidance(self) -> None:
        self.track("TNLean/Proof2.lean")
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("new numbered-sequel filename", output)
        self.assertIn("Basic.lean", output)

    def test_existing_debt_is_allowed(self) -> None:
        path = "TNLean/Proof2.lean"
        self.track(path)
        status, output = self.check(frozenset({path}))
        self.assertEqual(status, 0)
        self.assertIn("1 numbered debt", output)

    def test_new_debt_allowlist_entry_fails_against_base(self) -> None:
        path = "TNLean/Proof2.lean"
        self.track(path)
        status, output = self.check(frozenset({path}), base_debt=frozenset())
        self.assertEqual(status, 1)
        self.assertIn("debt allowlist; this set may only shrink", output)

    def test_base_debt_ratchet_rejects_pr_and_multicommit_push_additions(self) -> None:
        old_path = "TNLean/Old2.lean"
        new_path = "TNLean/New3.lean"
        self.track(old_path)
        checker = self.root / "scripts" / "check_numbered_lean_files.py"
        checker.parent.mkdir(parents=True)
        checker.write_text(
            "NUMBERED_DEBT_ALLOWLIST: frozenset[str] = "
            f"frozenset({{{old_path!r}}})\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "-C", str(self.root), "add", checker.relative_to(self.root)],
            check=True,
        )
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "baseline",
            ],
            check=True,
        )
        base_ref = subprocess.run(
            ["git", "-C", str(self.root), "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()

        self.track(new_path)
        checker.write_text(
            "NUMBERED_DEBT_ALLOWLIST: frozenset[str] = "
            f"frozenset({{{old_path!r}, {new_path!r}}})\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "-C", str(self.root), "add", checker.relative_to(self.root)],
            check=True,
        )
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "proposed addition",
            ],
            check=True,
        )

        baseline = numbered._debt_allowlist_at_merge_base(self.root, base_ref)
        status, output = self.check(
            frozenset({old_path, new_path}),
            base_debt=baseline,
        )
        self.assertEqual(status, 1)
        self.assertIn(f"{new_path}: added to the numbered debt allowlist", output)

        self.track("TNLean/Unrelated.lean")
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "later commit in the same push",
            ],
            check=True,
        )

        parent_baseline = numbered._debt_allowlist_at_merge_base(self.root, "HEAD^")
        parent_status, _ = self.check(
            frozenset({old_path, new_path}),
            base_debt=parent_baseline,
        )
        self.assertEqual(parent_status, 0)

        push_baseline = numbered._debt_allowlist_at_merge_base(self.root, base_ref)
        push_status, push_output = self.check(
            frozenset({old_path, new_path}),
            base_debt=push_baseline,
        )
        self.assertEqual(push_status, 1)
        self.assertIn(f"{new_path}: added to the numbered debt allowlist", push_output)

    def test_removing_debt_allowlist_entry_is_allowed(self) -> None:
        path = "TNLean/Proof2.lean"
        self.track(path)
        status, output = self.check(
            frozenset({path}),
            base_debt=frozenset({path, "TNLean/Removed3.lean"}),
        )
        self.assertEqual(status, 0)

    def test_stale_debt_entry_fails_so_allowlist_shrinks(self) -> None:
        status, output = self.check(frozenset({"TNLean/Gone2.lean"}))
        self.assertEqual(status, 1)
        self.assertIn("stale debt allowlist entry", output)

    def test_documented_semantic_exception_is_allowed(self) -> None:
        path = "TNLean/ZMod2.lean"
        self.track(path)
        status, output = self.check(
            exceptions={path: "The numeral is part of the mathematical type name."}
        )
        self.assertEqual(status, 0)
        self.assertIn("1 semantic exceptions", output)

    def test_empty_semantic_explanation_fails(self) -> None:
        path = "TNLean/ZMod2.lean"
        self.track(path)
        status, output = self.check(exceptions={path: "  "})
        self.assertEqual(status, 1)
        self.assertIn("has no explanation", output)

    def test_archive_and_untracked_files_are_out_of_scope(self) -> None:
        self.track("TNLean/Archive/Legacy2.lean")
        untracked = self.root / "TNLean" / "Scratch2.lean"
        untracked.write_text("def scratch := 2\n", encoding="utf-8")
        status, output = self.check()
        self.assertEqual(status, 0)
        self.assertIn("0 numbered debt", output)


class OversizedLeanFilePolicyTests(CapturedCheck):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write(self, relative: str, source: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def test_oversized_module_fails_with_actionable_split_guidance(self) -> None:
        self.write("TNLean/Huge.lean", "def x := 1\n" * (oversized.THRESHOLD + 1))
        status, output = self.capture(oversized.check_files, self.root, set(), set())
        self.assertEqual(status, 1)
        self.assertIn("concept-named modules", output)
        self.assertIn("Foo2.lean", output)

    def test_exact_import_only_aggregator_is_exempt(self) -> None:
        source = "/- generated\n  /- nested comment -/\n-/\n" + (
            "import TNLean.Algebra.Basic -- public import\n" * (oversized.THRESHOLD + 1)
        )
        self.write("TNLean.lean", source)
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"TNLean.lean"}
        )
        self.assertEqual(status, 0)
        self.assertIn("validated 1 of 1 exact aggregator exemption", output)

    def test_import_only_file_is_not_exempt_without_exact_registration(self) -> None:
        self.write(
            "TNLean/All.lean",
            "import TNLean.Basic\n" * (oversized.THRESHOLD + 1),
        )
        status, output = self.capture(oversized.check_files, self.root, set(), set())
        self.assertEqual(status, 1)
        self.assertIn("Oversized Lean file", output)

    def test_aggregator_with_declaration_is_rejected_even_below_limit(self) -> None:
        self.write("TNLean.lean", "import TNLean.Basic\ndef notAnAggregator := 1\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"TNLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("contains non-import Lean code", output)

    def test_aggregator_with_invalid_module_segment_is_rejected(self) -> None:
        self.write("TNLean.lean", "import TNLean.0Invalid\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"TNLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("contains non-import Lean code", output)

    def test_missing_aggregator_exemption_is_rejected(self) -> None:
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"Missing.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("must name an existing, scanned .lean file", output)

    def test_unterminated_comment_rejects_aggregator(self) -> None:
        self.write("TNLean.lean", "import TNLean.Basic\n/- never closed\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"TNLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("unterminated block comment", output)


class ImportLayerPolicyTests(unittest.TestCase):
    def test_layers_are_assigned_from_the_bottom_up(self) -> None:
        self.assertEqual(layers.layer_of("TNLean.Algebra.FinKronecker"), "algebra")
        self.assertEqual(layers.layer_of("TNLean.Circuit.SiteEmbedding"), "sites")
        self.assertEqual(layers.layer_of("TNLean.Circuit.SiteEmbeddingNorm"), "sites")
        self.assertEqual(layers.layer_of("TNLean.Circuit.LiebRobinson.Volterra"), "dynamics")
        self.assertEqual(layers.layer_of("TNLean.Circuit.LocalCircuit"), "circuit")
        self.assertEqual(layers.layer_of("TNLean.Lattice.PartyCircuit.PartyWord"), "party")
        self.assertEqual(layers.layer_of("TNLean.Lattice.LocalHamiltonian"), "hamiltonian")
        self.assertIsNone(layers.layer_of("TNLean.MPS.Defs"))

    def test_upward_and_sideways_imports_are_violations(self) -> None:
        sources = {
            "TNLean.Algebra.A": "import TNLean.Circuit.SiteEmbedding\ntheorem a : True := trivial\n",
            "TNLean.Circuit.SiteEmbedding": "import TNLean.Algebra.A\ndef e := 0\n",
            "TNLean.Circuit.LocalCircuit": (
                "import TNLean.Circuit.SiteEmbedding\nimport TNLean.Lattice.LocalHamiltonian\n"
                "def c := 0\n"
            ),
            "TNLean.Lattice.LocalHamiltonian": "import TNLean.MPS.Defs\ndef h := 0\n",
            "TNLean.MPS.Defs": "import TNLean.Lattice.LocalHamiltonian\ndef t := 0\n",
        }
        self.assertEqual(
            layers.violations(sources),
            {
                "TNLean.Algebra.A -> TNLean.Circuit.SiteEmbedding",
                "TNLean.Circuit.LocalCircuit -> TNLean.Lattice.LocalHamiltonian",
                "TNLean.Lattice.LocalHamiltonian -> TNLean.MPS.Defs",
            },
        )

    def test_import_only_aggregators_are_exempt(self) -> None:
        sources = {
            "TNLean.Lattice": "/- generated -/\nimport TNLean.Lattice.PartyCircuit\n",
            "TNLean.Lattice.PartyCircuit": "import TNLean.Lattice.PartyCircuit.PartyWord\n",
        }
        self.assertEqual(layers.violations(sources), set())

    def test_comments_do_not_hide_or_create_imports(self) -> None:
        sources = {
            "TNLean.Algebra.Hidden": (
                "import TNLean.MPS.Defs -- tensor definition\ntheorem a : True := trivial\n"
            ),
            "TNLean.Algebra.Commented": (
                "/- import TNLean.MPS.Defs\n  /- nested -/ import TNLean.PEPS.Defs -/\n"
                "-- import TNLean.Circuit.LocalCircuit\n"
                "theorem b : True := trivial\n"
            ),
        }
        self.assertEqual(
            layers.violations(sources), {"TNLean.Algebra.Hidden -> TNLean.MPS.Defs"}
        )

    def test_import_modifiers_are_recognized(self) -> None:
        sources = {
            "TNLean.Algebra.A": "public import TNLean.MPS.Defs\ndef a := 0\n",
            "TNLean.Algebra.B": "public meta import TNLean.PEPS.Defs\ndef b := 0\n",
            "TNLean.Algebra.C": "import all TNLean.QCA.LocalAlgebra\ndef c := 0\n",
        }
        self.assertEqual(
            layers.violations(sources),
            {
                "TNLean.Algebra.A -> TNLean.MPS.Defs",
                "TNLean.Algebra.B -> TNLean.PEPS.Defs",
                "TNLean.Algebra.C -> TNLean.QCA.LocalAlgebra",
            },
        )

    def test_imports_are_followed_through_nested_aggregators(self) -> None:
        sources = {
            "TNLean.Circuit.Outer": "import TNLean.Circuit.Inner\n",
            "TNLean.Circuit.Inner": "-- wrapper\nimport TNLean.MPS.Defs\nimport TNLean.Circuit.Geometry\n",
            "TNLean.Circuit.Geometry": "def g := 0\n",
            "TNLean.Circuit.LocalCircuit": "import TNLean.Circuit.Outer\ndef c := 0\n",
            "TNLean.MPS.Defs": "def t := 0\n",
        }
        self.assertEqual(
            layers.violations(sources), {"TNLean.Circuit.LocalCircuit -> TNLean.MPS.Defs"}
        )

    def test_party_layer_may_import_circuits_but_not_hamiltonians(self) -> None:
        sources = {
            "TNLean.Lattice.PartyCircuit.Example": (
                "import TNLean.Circuit.LocalCircuit\nimport TNLean.Lattice.LocalHamiltonian\n"
                "def p := 0\n"
            ),
        }
        self.assertEqual(
            layers.violations(sources),
            {"TNLean.Lattice.PartyCircuit.Example -> TNLean.Lattice.LocalHamiltonian"},
        )

    def test_debt_may_only_shrink_against_the_base(self) -> None:
        entry = "TNLean.Algebra.A -> TNLean.MPS.Defs"
        sources = {"TNLean.Algebra.A": "import TNLean.MPS.Defs\ndef a := 0\n"}
        # Recording a new violation in the same change does not admit it.
        errors = layers.check_layers(sources, frozenset({entry}), frozenset())
        self.assertEqual(errors, [f"Entry added to DEBT; this set may only shrink: {entry}"])
        # The same entry is accepted when it is already recorded at the base.
        self.assertEqual(layers.check_layers(sources, frozenset({entry}), frozenset({entry})), [])
        # Without a base (the checker is being introduced) the recorded set is the baseline.
        self.assertEqual(layers.check_layers(sources, frozenset({entry}), None), [])
        # An unrecorded violation and a stale entry both fail.
        self.assertEqual(len(layers.check_layers(sources, frozenset(), frozenset())), 1)
        self.assertEqual(len(layers.check_layers({}, frozenset({entry}), frozenset({entry}))), 1)

    def test_debt_is_read_from_a_checker_revision(self) -> None:
        source = 'DEBT: frozenset[str] = frozenset(\n    {\n        "A -> B",\n    }\n)\n'
        self.assertEqual(layers.debt_from_source(source), frozenset({"A -> B"}))
        self.assertEqual(layers.debt_from_source("DEBT = frozenset({})\n"), frozenset())
        with self.assertRaises(ValueError):
            layers.debt_from_source("DEBT = compute()\n")

    def test_record_is_read_by_name_and_may_be_absent(self) -> None:
        source = 'DEBT = frozenset({})\nMUTUAL_DIRECTORIES = frozenset({"A <-> B"})\n'
        self.assertEqual(
            layers.record_from_source(source, "MUTUAL_DIRECTORIES"), frozenset({"A <-> B"})
        )
        self.assertIsNone(layers.record_from_source(source, "EXAMPLES_IMPORTS"))
        with self.assertRaises(ValueError):
            layers.record_from_source("EXAMPLES_IMPORTS = compute()\n", "EXAMPLES_IMPORTS")

    def test_recorded_debt_matches_the_tree(self) -> None:
        root = Path(__file__).resolve().parent.parent
        self.assertEqual(layers.check_layers(layers.tracked_sources(root)), [])


class MutualDirectoryPolicyTests(unittest.TestCase):
    SOURCES = {
        "TNLean.MPS.Defs": "def t := 0\n",
        "TNLean.MPS.Core.Basic": "import TNLean.MPS.Defs\ndef c := 0\n",
        "TNLean.MPS.Core.Words.Eval": "import TNLean.MPS.Chain.Open\ndef e := 0\n",
        "TNLean.MPS.Chain.Open": "import TNLean.MPS.Core.Basic\ndef o := 0\n",
        "TNLean.QCA.Index": "import TNLean.MPS.Core.Basic\ndef q := 0\n",
    }

    def test_directories_are_taken_at_depth_two_only_below_the_deep_roots(self) -> None:
        self.assertEqual(layers.directory_of("TNLean.MPS.Core.Words.Eval"), "MPS/Core")
        self.assertEqual(layers.directory_of("TNLean.PEPS.AreaLaw.Geometry.CellFans"), "PEPS/AreaLaw")
        self.assertEqual(layers.directory_of("TNLean.MPS.Defs"), "MPS")
        self.assertEqual(layers.directory_of("TNLean.Circuit.Gates.Givens"), "Circuit")
        self.assertEqual(layers.directory_of("TNLean.Lattice.Sheet.SwapCorrection"), "Lattice")
        self.assertIsNone(layers.directory_of("TNLean.MPS"))

    def test_only_pairs_with_imports_in_both_directions_are_found(self) -> None:
        self.assertEqual(
            layers.mutual_directories(self.SOURCES),
            {
                "MPS/Chain <-> MPS/Core": (
                    "TNLean.MPS.Chain.Open -> TNLean.MPS.Core.Basic",
                    "TNLean.MPS.Core.Words.Eval -> TNLean.MPS.Chain.Open",
                )
            },
        )

    def test_an_import_that_closes_a_cycle_of_two_directories_fails(self) -> None:
        recorded = frozenset({"MPS/Chain <-> MPS/Core"})
        self.assertEqual(layers.check_mutual_directories(self.SOURCES, recorded, recorded), [])
        sources = dict(self.SOURCES)
        sources["TNLean.MPS.Core.Basic"] = (
            "import TNLean.MPS.Defs\nimport TNLean.QCA.Index -- new\ndef c := 0\n"
        )
        self.assertEqual(
            layers.check_mutual_directories(sources, recorded, recorded),
            [
                "Directories import each other: MPS/Core <-> QCA (by "
                "TNLean.MPS.Core.Basic -> TNLean.QCA.Index and "
                "TNLean.QCA.Index -> TNLean.MPS.Core.Basic)"
            ],
        )

    def test_aggregators_are_expanded_as_imports_and_ignored_as_importers(self) -> None:
        sources = {
            "TNLean.QCA": "import TNLean.QCA.Index\nimport TNLean.Spectral.Gap\n",
            "TNLean.QCA.All": "import TNLean.Spectral.Gap\n",
            "TNLean.QCA.Index": "def q := 0\n",
            "TNLean.Spectral.Gap": "def g := 0\n",
            "TNLean.Spectral.Decay": "import TNLean.QCA\ndef d := 0\n",
        }
        # ``QCA/All`` imports ``Spectral`` but has no declarations, and the import
        # of the aggregator ``TNLean.QCA`` counts as its two re-exported modules.
        self.assertEqual(layers.mutual_directories(sources), {})
        sources["TNLean.QCA.Index"] = "import TNLean.Spectral.Gap\ndef q := 0\n"
        self.assertEqual(set(layers.mutual_directories(sources)), {"QCA <-> Spectral"})

    def test_commented_imports_and_modules_outside_directories_do_not_count(self) -> None:
        sources = {
            "TNLean.Root": "import TNLean.QCA.Index\ndef r := 0\n",
            "TNLean.QCA.Index": "import TNLean.Root\n-- import TNLean.Spectral.Gap\ndef q := 0\n",
            "TNLean.Spectral.Gap": "/- import TNLean.QCA.Index -/\nimport TNLean.QCA.Index\n",
        }
        self.assertEqual(layers.mutual_directories(sources), {})

    def test_recorded_pairs_may_only_shrink_against_the_base(self) -> None:
        pair = "MPS/Chain <-> MPS/Core"
        check = layers.check_mutual_directories
        # Recording a new pair in the same change does not admit it.
        self.assertEqual(
            check(self.SOURCES, frozenset({pair}), frozenset()),
            [f"Pair added to MUTUAL_DIRECTORIES; this set may only shrink: {pair}"],
        )
        # Without a base (the record is being introduced) the recorded set is the baseline.
        self.assertEqual(check(self.SOURCES, frozenset({pair}), None), [])
        # A pair that no longer exists must be removed from the record.
        errors = check({}, frozenset({pair}), frozenset({pair}))
        self.assertEqual(len(errors), 1)
        self.assertIn("remove the pair", errors[0])

    def test_recorded_pairs_match_the_tree(self) -> None:
        root = Path(__file__).resolve().parent.parent
        sources = layers.tracked_sources(root)
        self.assertEqual(set(layers.mutual_directories(sources)), layers.MUTUAL_DIRECTORIES)


class ExamplesImportPolicyTests(unittest.TestCase):
    def test_only_library_modules_importing_worked_examples_are_found(self) -> None:
        sources = {
            "TNLean.MPS.Examples.GHZ": "def ghz := 0\n",
            "TNLean.MPS.Examples.AKLT": "import TNLean.MPS.Examples.GHZ\ndef aklt := 0\n",
            "TNLean.MPS.MPU.Examples.Shift": "import TNLean.MPS.Examples.GHZ\ndef s := 0\n",
            "TNLean.MPS.Symmetry.Examples": "import TNLean.MPS.Defs\ndef named := 0\n",
            "TNLean.MPS.Preparation.GHZParent": "import TNLean.MPS.Examples.GHZ\ndef p := 0\n",
            "TNLean.PEPS.Blocking": "import TNLean.MPS.MPU.Examples.Shift\ndef b := 0\n",
            "TNLean.MPS.Defs": "-- import TNLean.MPS.Examples.GHZ\ndef t := 0\n",
        }
        self.assertTrue(layers.in_examples("TNLean.MPS.MPU.Examples.Shift"))
        # A module named ``Examples`` outside an ``Examples`` directory is a library module.
        self.assertFalse(layers.in_examples("TNLean.MPS.Symmetry.Examples"))
        self.assertEqual(
            layers.examples_imports(sources),
            {
                "TNLean.MPS.Preparation.GHZParent -> TNLean.MPS.Examples.GHZ",
                "TNLean.PEPS.Blocking -> TNLean.MPS.MPU.Examples.Shift",
            },
        )

    def test_examples_reached_through_an_aggregator_are_found(self) -> None:
        sources = {
            "TNLean.MPS.Examples": "import TNLean.MPS.Examples.GHZ\n",
            "TNLean.MPS.Examples.GHZ": "def ghz := 0\n",
            "TNLean.MPS": "import TNLean.MPS.Examples\n",
            "TNLean.QCA.Index": "import TNLean.MPS.Examples\ndef q := 0\n",
        }
        self.assertEqual(
            layers.examples_imports(sources), {"TNLean.QCA.Index -> TNLean.MPS.Examples.GHZ"}
        )

    def test_recorded_imports_may_only_shrink_against_the_base(self) -> None:
        entry = "TNLean.QCA.Index -> TNLean.MPS.Examples.GHZ"
        sources = {"TNLean.QCA.Index": "import TNLean.MPS.Examples.GHZ\ndef q := 0\n"}
        check = layers.check_examples_imports
        self.assertEqual(
            check(sources, frozenset(), frozenset()),
            [f"Module outside Examples imports a worked example: {entry}"],
        )
        self.assertEqual(
            check(sources, frozenset({entry}), frozenset()),
            [f"Entry added to EXAMPLES_IMPORTS; this set may only shrink: {entry}"],
        )
        self.assertEqual(check(sources, frozenset({entry}), frozenset({entry})), [])
        self.assertEqual(check(sources, frozenset({entry}), None), [])
        self.assertEqual(len(check({}, frozenset({entry}), frozenset({entry}))), 1)

    def test_recorded_imports_match_the_tree(self) -> None:
        root = Path(__file__).resolve().parent.parent
        sources = layers.tracked_sources(root)
        self.assertEqual(layers.examples_imports(sources), layers.EXAMPLES_IMPORTS)


class PassThroughPolicyTests(unittest.TestCase):
    def found(self, source: str) -> list[str]:
        return list(forwarding.pass_throughs_of_source(source))

    def test_the_four_typical_shapes_are_found(self) -> None:
        source = (
            "namespace MPSTensor\n\n"
            "/-- The blocked dimension. -/\n"
            "noncomputable abbrev blockPhysDim (d L : ℕ) : ℕ := Kraus.blockPhysDim d L\n\n"
            "@[simp] lemma blockPhysDim_eq_pow (d L : ℕ) : blockPhysDim d L = d ^ L :=\n"
            "  Kraus.blockPhysDim_eq_pow d L\n\n"
            "lemma length_wordOfBlock (d L : ℕ) (i : Fin (blockPhysDim d L)) :\n"
            "    (wordOfBlock d L i).length = L := by\n"
            "  exact Kraus.length_wordOfBlock d L i -- forwarded\n\n"
            "protected theorem evalWord_nil {D : ℕ} [NeZero D] (A : MPSTensor d D) :\n"
            "    evalWord A [] = 1 := by simpa using Kraus.evalWord_nil A\n\n"
            "end MPSTensor\n"
        )
        self.assertEqual(
            self.found(source),
            [
                "MPSTensor.blockPhysDim",
                "MPSTensor.blockPhysDim_eq_pow",
                "MPSTensor.length_wordOfBlock",
                "MPSTensor.evalWord_nil",
            ],
        )

    def test_names_follow_namespaces_and_not_sections(self) -> None:
        source = (
            "namespace A.B\nnoncomputable section\nvariable {n : ℕ}\n"
            "theorem f (x : ℕ) : P x := Kraus.f x\n"
            "end\nend A.B\n"
            "namespace C\nsection Named\n"
            "theorem D.g (x : ℕ) : P x := Kraus.D.g x\n"
            "theorem _root_.Other.h (x : ℕ) : P x := Kraus.h x\n"
            "end Named\nend C\n"
            "theorem k (x : ℕ) : P x := Kraus.k x\n"
        )
        self.assertEqual(self.found(source), ["A.B.f", "C.D.g", "Other.h", "k"])

    def test_arguments_must_be_the_explicit_binders_in_order(self) -> None:
        for declaration in (
            "theorem f (a b : ℕ) : P a b := Kraus.f b a",
            "theorem f (a b : ℕ) : P a b := Kraus.f a",
            "theorem f (a b : ℕ) : P a b := Kraus.f a b a",
            "theorem f (a b : ℕ) : P a b := Kraus.f a (b + 0)",
            "theorem f (a b : ℕ) : P a b := Kraus.f (d := d) a b",
            "theorem f (a b : ℕ) : P a b := @Kraus.f a b",
            "theorem f (a b : ℕ) : P a b := (Kraus.f a b).symm",
            "theorem f (a b : ℕ) : P a b := by rw [Kraus.f a b]",
            "theorem f (a b : ℕ) : P a b := by\n  simp\n  exact Kraus.f a b",
            "theorem f (a b : ℕ) : P a b := by simpa [g] using Kraus.f a b",
            "theorem f {a b : ℕ} : P a b := Kraus.f a b",
            "theorem f : P := Kraus.f",
            "theorem f (a : ℕ) (b : ℕ := 0) : P a b := Kraus.f a b",
            "theorem f a b : P a b := Kraus.f a b",
        ):
            with self.subTest(declaration=declaration):
                self.assertEqual(self.found(declaration + "\n"), [])
        # An anonymous instance binder binds no name, so its class may be the namespace.
        self.assertEqual(
            self.found("theorem foo (d : ℕ) [NeZero d] : P d := NeZero.foo d\n"), ["foo"]
        )
        self.assertEqual(
            self.found("theorem foo (d : ℕ) [NeZero : C d] : P d := NeZero.foo d\n"), []
        )
        # The same holds for an anonymous instance bound by a ``variable`` command.
        self.assertEqual(
            self.found(
                "variable {β : Type*} [Fintype β]\n"
                "noncomputable def card (α : Type*) [Fintype α] : ℕ := Fintype.card α\n"
            ),
            ["card"],
        )
        # Implicit and instance binders are not arguments; explicit ones may be split.
        self.assertEqual(
            self.found(
                "theorem f {d : ℕ} [NeZero d] (a : Fin d)\n"
                "    ⦃c : ℕ⦄ (b : Fin d) : P a b := Kraus.f a b\n"
            ),
            ["f"],
        )

    def test_the_applied_name_must_be_the_same_name_in_another_namespace(self) -> None:
        for declaration in (
            # A lemma about a definition, proved by a fact about what it unfolds to.
            "theorem regionSumset_mono (h : s ⊆ t) : S s ⊆ S t := Finset.add_subset_add h",
            # A definition that names an application of another one.
            "def bondRegisterWidth (d D : ℕ) : ℕ := Nat.clog d D",
            # A consequence of a hypothesis, of a variable, or of a local constant.
            "theorem trans (h : P) (k : Q) : R := h.trans k",
            "theorem trans (k : Q) : R := hA.trans k",
            "theorem H.trans (k : Q) : R := H.trans k",
            "theorem trace_evalWord (w : W) : T w := xCompression.trace_evalWord w",
            # No namespace: a recursive call or a private helper, not a second namespace.
            "theorem f (a : ℕ) : P a := f a",
        ):
            with self.subTest(declaration=declaration):
                source = f"variable (hA : A) {{H : B}}\n{declaration}\n"
                self.assertEqual(self.found(source), [])

    def test_other_commands_are_never_reported(self) -> None:
        source = (
            "instance blockFintype (d : ℕ) : Fintype (Block d) := Kraus.blockFintype d\n"
            "example (d : ℕ) : P d := Kraus.f d\n"
            "structure S where\n  f (d : ℕ) : ℕ := Kraus.f d\n"
            "def g (d : ℕ) : ℕ := Kraus.g d\nwhere\n  aux (d : ℕ) : ℕ := Kraus.aux d\n"
            "def r (d : ℕ) : ℕ := Kraus.r d\ntermination_by d\n"
            "/- theorem f (d : ℕ) : P d := Kraus.f d -/\n"
            "-- theorem f (d : ℕ) : P d := Kraus.f d\n"
            "def m : ℕ → ℕ\n  | d => Kraus.m d\n"
        )
        self.assertEqual(self.found(source), [])

    def test_archive_is_out_of_scope(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            for relative in ("TNLean/Archive/Old.lean", "TNLean/MPS/New.lean"):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("theorem f (d : ℕ) : P d := Kraus.f d\n", encoding="utf-8")
                subprocess.run(["git", "-C", str(root), "add", relative], check=True)
            sources = layers.tracked_sources(root)
        self.assertEqual(forwarding.pass_throughs(sources), {"f": "TNLean.MPS.New"})

    def test_recorded_pass_throughs_may_only_shrink_against_the_base(self) -> None:
        sources = {"TNLean.MPS.Core.Blocking": "theorem f (d : ℕ) : P d := Kraus.f d\n"}
        check = forwarding.check_pass_throughs
        self.assertEqual(
            check(sources, frozenset(), frozenset()),
            [
                "Declaration only applies another declaration to its own arguments: "
                "f (TNLean.MPS.Core.Blocking)"
            ],
        )
        self.assertEqual(
            check(sources, frozenset({"f"}), frozenset()),
            ["Entry added to PASS_THROUGH; this set may only shrink: f"],
        )
        self.assertEqual(check(sources, frozenset({"f"}), frozenset({"f"})), [])
        self.assertEqual(check(sources, frozenset({"f"}), None), [])
        self.assertEqual(len(check({}, frozenset({"f"}), frozenset({"f"}))), 1)

    def test_recorded_pass_throughs_match_the_tree(self) -> None:
        root = Path(__file__).resolve().parent.parent
        sources = layers.tracked_sources(root)
        self.assertEqual(set(forwarding.pass_throughs(sources)), forwarding.PASS_THROUGH)


if __name__ == "__main__":
    unittest.main()
