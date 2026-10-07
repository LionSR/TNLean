/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceGateDensity

/-!
# Imported axiom audit for finite source-gate density expansion

This audit checks every explicit public declaration in the four new modules.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.SourceInventory.slotLayout_cons
#print axioms TNLean.PEPS.PairEffect.SourceInventory.slotVector
#print axioms TNLean.PEPS.PairEffect.SourceInventory.slotVector_eq_vector
#print axioms TNLean.PEPS.PairEffect.SourceInventory.eval_prepareSlots_eq_appendIso_symm
#print axioms TNLean.PEPS.PairEffect.SourceInventory.eval_prepareSlots_sum_smul
#print axioms TNLean.PEPS.PairEffect.SourceInventory.eval_prepareSlots_eq_sum_basis
#print axioms TNLean.PEPS.PairEffect.Word.preparedMatrix
#print axioms TNLean.PEPS.PairEffect.Word.preparedMatrix_sum_smul
#print axioms TNLean.PEPS.PairEffect.Word.preparedMatrix_eq_sum_basis
#print axioms TNLean.PEPS.PairEffect.Word.preparedDensityCoefficient
#print axioms TNLean.PEPS.PairEffect.Word.preparedMatrix_density_sum_smul
#print axioms TNLean.PEPS.PairEffect.Word.preparedMatrix_density_eq_sum_basis
#print axioms TNLean.PEPS.PairEffect.Word.preparedMatrix_gate_density_eq_sum_basis
#print axioms TNLean.PEPS.PairEffect.Word.norm_preparedMatrix_le_one
#print axioms TNLean.PEPS.PairEffect.Word.norm_preparedMatrix_tmul_le_one
#print axioms TNLean.PEPS.PairEffect.Word.exists_finite_density_expansion

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-source-gate-density"
  IO.FS.writeFile (directory / "final-verification-20261007" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
