/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SelectedCoefficientDecomposition
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of prescribed selected-coefficient middle decompositions -/

run_cmd do
  let structural := ``TNLean.MPS.AreaLaw.exteriorMiddleEquiv
  let structuralAxioms ← Lean.collectAxioms structural
  let expectedStructural := #[``propext, ``Quot.sound]
  unless structuralAxioms.size == expectedStructural.size &&
      structuralAxioms.all (expectedStructural.contains ·) do
    throwError "Unexpected axioms for {structural}: {structuralAxioms}"
  let decl :=
    ``TNLean.MPS.AreaLaw.exists_physical_twoMarkerCoefficient_prescribed_middle_decomposition
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.size == expected.size && axioms.all (expected.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
