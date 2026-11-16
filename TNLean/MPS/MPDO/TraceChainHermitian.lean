/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TraceChainLinearCombination
import QICLean.Analysis.HermitianPartNorm

/-!
# Hermitian parts of site-dependent matrix product operators

Exchanging the physical indices and conjugating the virtual coefficients gives the actual
adjoint operator, without a spatial reflection. Diagonal blocks then construct the Hermitian
part at twice the bond dimension. This supports the Hermitian approximating Hamiltonian in
ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff` and `t:aisefficient`,
lines 1262–1268 and 1412–1420. No positivity of the approximating operator is asserted.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace MPOTensor

/-- Coefficient conjugation and physical-index exchange represent the actual adjoint of a
site-dependent operator chain. The chain and bond dimensions may vanish. Supporting the
operator algebra in ALVV, arXiv:1602.08828v2, `prop:Cheby-AGSP-eff`, lines 1311–1333. -/
theorem traceChainOperator_conjTranspose {L q D : ℕ}
    (A : Fin L → MPOTensor q D) (C : Matrix (Fin D) (Fin D) ℂ) :
    (traceChainOperator A C)ᴴ =
      traceChainOperator (fun v i j ↦ (A v j i).map (starRingEnd ℂ))
        (C.map (starRingEnd ℂ)) := by
  ext sigma tau
  change (starRingEnd ℂ) (Matrix.trace
      (C * (List.ofFn (fun v ↦ A v (tau v) (sigma v))).prod)) =
    Matrix.trace (C.map (starRingEnd ℂ) *
      (List.ofFn (fun v ↦ (A v (tau v) (sigma v)).map (starRingEnd ℂ))).prod)
  rw [AddMonoidHom.map_trace, Matrix.map_mul]
  have hp := map_list_prod (starRingEnd ℂ).mapMatrix
    (List.ofFn (fun v ↦ A v (tau v) (sigma v)))
  simpa only [List.map_ofFn, Function.comp_def, RingHom.mapMatrix_apply] using
    congrArg (fun M ↦ Matrix.trace (C.map (starRingEnd ℂ) * M)) hp

/-- The Hermitian part of an actual operator chain has actual tensors at twice its bond.
The nonempty-chain condition permits absorption of the scalar closing coefficients.
Supporting ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_traceChainOperator_selfAdjointPart {L q D : ℕ} (hL : 1 ≤ L)
    (A : Fin L → MPOTensor q D) :
    ∃ B : Fin L → MPOTensor q (D * 2),
      (selfAdjointPart ℝ (traceChainOperator A 1) :
          Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) = traceChainOperator B 1 := by
  let F : Fin 2 → Fin L → MPOTensor q D :=
    ![A, fun v i j ↦ (A v j i).map (starRingEnd ℂ)]
  obtain ⟨B, hB⟩ := exists_traceChainOperator_linearCombination hL F (fun _ ↦ (1 / 2 : ℂ))
  refine ⟨B, ?_⟩
  have hAdj : traceChainOperator (fun v i j ↦ (A v j i).map (starRingEnd ℂ)) 1 =
      (traceChainOperator A 1)ᴴ := by
    simpa using (traceChainOperator_conjTranspose A 1).symm
  simpa [F, Fin.sum_univ_two, hAdj, selfAdjointPart_apply_coe, invOf_eq_inv,
    ← Complex.coe_smul, Matrix.star_eq_conjTranspose] using hB

/-- An actual approximation to a Hermitian operator yields a Hermitian approximation with the
same error and twice the bond. The tensors of the approximation are constructed from the
supplied operator tensors, supporting ALVV, arXiv:1602.08828v2, lines 1262–1268 and 1412–1420. -/
theorem exists_hermitian_traceChainOperator_approximation {L q D : ℕ} (hL : 1 ≤ L)
    {H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hH : H.IsHermitian)
    (A : Fin L → MPOTensor q D) {eps : ℝ} (herr : ‖H - traceChainOperator A 1‖ ≤ eps) :
    ∃ B : Fin L → MPOTensor q (D * 2), (traceChainOperator B 1).IsHermitian ∧
      ‖H - traceChainOperator B 1‖ ≤ eps := by
  obtain ⟨B, hB⟩ := exists_traceChainOperator_selfAdjointPart hL A
  refine ⟨B, ?_, ?_⟩
  · rw [← hB]
    exact (selfAdjointPart ℝ (traceChainOperator A 1)).property
  · rw [← hB]
    exact (hH.norm_sub_selfAdjointPart_le _).trans herr

end MPOTensor
