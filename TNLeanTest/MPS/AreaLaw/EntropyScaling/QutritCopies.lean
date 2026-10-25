/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.QutritPolynomialObstruction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the explicit qutrit tensor-power family. -/

open TNLean.MPS.AreaLaw TNLean.MPS.AreaLaw.EntropyScaling

-- The zero vector is a valid bond-zero approximant on the sixteen-site example.
-- The full error is one, so the finite estimate must handle it without normalization.
example : Matrix.rectangularTraceNorm
    (Matrix.euclideanOuterProduct (qutritCopies 2) (qutritCopies 2) -
      Matrix.euclideanOuterProduct
        (0 : EuclideanSpace ℂ (Fin (2 ^ 2 * (2 + 2)) → Fin 3)) 0) = 1 := by
  have hz : Matrix.euclideanOuterProduct
      (0 : EuclideanSpace ℂ (Fin (2 ^ 2 * (2 + 2)) → Fin 3))
      (0 : EuclideanSpace ℂ (Fin (2 ^ 2 * (2 + 2)) → Fin 3)) = 0 := by
    simp [Matrix.euclideanOuterProduct]
  rw [hz, sub_zero, Matrix.rectangularTraceNorm_euclideanOuterProduct_self,
    norm_qutritCopies (by decide), one_pow]

example : IsOpenMPS (2 ^ 2 * (2 + 2)) 3 0 (fun _ ↦ 0) := by
  apply isOpenMPS_of_cutMatrix_rank_le (0 : EuclideanSpace ℂ (Fin (2 ^ 2 * (2 + 2)) → Fin 3))
  intro k
  have hz : cutMatrix (0 : EuclideanSpace ℂ (Fin (2 ^ 2 * (2 + 2)) → Fin 3)) k = 0 := by
    ext a b
    rfl
  rw [hz, Matrix.rank_zero]

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``TNLean.MPS.AreaLaw.EntropyScaling.norm_qutritCopies,
    ``TNLean.MPS.AreaLaw.EntropyScaling.regionEntropy_interval_qutritCopies_le,
    ``TNLean.MPS.AreaLaw.EntropyScaling.normSq_overlap_qutritFamily_le_kyFan,
    ``TNLean.MPS.AreaLaw.EntropyScaling.qutritFamily_scalar_error_lower_bound,
    ``TNLean.MPS.AreaLaw.EntropyScaling.bondDimension_qutritCopies_ge_of_scalar_error_lt_one,
    ``TNLean.MPS.AreaLaw.EntropyScaling.bondDimension_qutritCopies_ge,
    ``TNLean.MPS.AreaLaw.EntropyScaling.eventually_no_polynomial_mps_approximation_qutritCopies]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
