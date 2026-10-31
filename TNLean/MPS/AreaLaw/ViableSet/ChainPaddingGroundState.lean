/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ChainPaddingCoordinates
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The actual padded ground vector and its projector gap

Appending the prescribed basis state leaves the ground energy unchanged and
preserves the projector-gap lower bound capped at one. The ancillary operator
is the actual sum of the appended on-site penalties.

Source: product-ancilla accuracy reduction for LVV13, arXiv:1307.5143v1,
final successive induction, lines 652--678. This is an auxiliary reduction;
no equality of spectral gaps or running-time bound is asserted.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker

namespace TNLean.MPS.AreaLaw

/-- Attach the prescribed ancillary basis configuration to the original vector,
using the same prefix coordinates as the retained viable family. -/
noncomputable def paddedGroundVector {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) : EuclideanSpace ℂ (Fin N → Fin q) :=
  rightBasisExtension
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv hi)) Γ) (fun _ ↦ z)

/-- The padded vector is normalized whenever the original vector is normalized. -/
theorem norm_paddedGroundVector {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖paddedGroundVector hi z Γ‖ = ‖Γ‖ := by
  rw [paddedGroundVector, norm_rightBasisExtension, LinearIsometryEquiv.norm_map]

/-- The original ground vector, extended by the actual ancillary product state,
is a ground vector of the actual padded interaction with projector gap at least
the minimum of the original lower bound and one. -/
theorem isGappedGroundState_paddedInteraction {L N q : ℕ} (hL : 1 ≤ L) (hi : L ≤ N)
    (z : Fin q) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    {E Delta : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ j, h j) E Γ Delta) (hDelta : 0 < Delta) :
    IsGappedGroundState (∑ j, paddedInteraction hi z h j) E
      (paddedGroundVector hi z Γ) (min Delta 1) := by
  classical
  let e := leftConfigOfFinEquiv (q := q) hi
  let H := ∑ j, h j
  let u : Entropy.RegionConfig (fun _ : Fin N ↦ q) (leftBlock N L) → ℂ :=
    (WithLp.ofLp Γ) ∘ e.symm
  let b0 : (v : {v : Fin N // v ∉ leftBlock N L}) → Fin q := fun _ ↦ z
  let β : ((v : {v : Fin N // v ∉ leftBlock N L}) → Fin q) → ℂ :=
    Pi.single b0 (1 : ℂ)
  let A := Matrix.reindex e e H
  let B := QuantumCircuit.productBasisPenalty b0
  have hu : ∑ a, ‖u a‖ ^ 2 = 1 := by
    rw [show (∑ a, ‖u a‖ ^ 2) = ‖Γ‖ ^ 2 from by
      simpa only [u, Function.comp_apply, EuclideanSpace.norm_sq_eq] using
        (Equiv.sum_comp e.symm (fun x ↦ ‖Γ x‖ ^ 2))]
    rw [hgs.1]
    norm_num
  have hβ : ∑ b, ‖β b‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single b0]
    · simp [β]
    · intro b _ hb
      simp [β, hb]
    · simp
  have hA : (A - (E : ℂ) • 1 - ((min Delta 1 : ℝ) : ℂ) •
      (1 - vecMulVec u (star u))).PosSemidef := by
    have hp := (hgs.2.2.gap_mono (by
      simpa only [← EuclideanSpace.norm_sq_eq, hgs.1] using (show (1 : ℝ) ^ 2 = 1 by norm_num))
      (min_le_left Delta 1)).submatrix e.symm
    convert hp using 1
    ext a a'
    simp [A, H, u, reindex_apply, submatrix_apply, one_apply,
      e.symm.injective.eq_iff, vecMulVec_apply]
  have hB : (B - (0 : ℂ) • 1 - ((min Delta 1 : ℝ) : ℂ) •
      (1 - vecMulVec β (star β))).PosSemidef := by
    have hp : (B - (0 : ℂ) • 1 - (1 : ℂ) •
        (1 - vecMulVec β (star β))).PosSemidef := by
      simpa only [zero_smul, sub_zero, one_smul] using
        QuantumCircuit.productBasisPenalty_gap b0
    exact hp.gap_mono hβ (min_le_right Delta 1)
  have hgap := hA.tensorSum_gap hB hu hβ (le_min hDelta.le zero_le_one)
  let c := Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)
  have hpad : Entropy.cutOperator (leftBlock N L) (∑ j, paddedInteraction hi z h j) =
      A ⊗ₖ 1 + 1 ⊗ₖ B := by
    rw [sum_paddedInteraction hL hi z h]
    change Entropy.cutOperator (leftBlock N L) (QuantumCircuit.embedOp (Fin.castLE hi) H) +
      Entropy.cutOperator (leftBlock N L)
        (∑ v : {v : Fin N // v ∉ leftBlock N L},
          QuantumCircuit.siteOp v.val (QuantumCircuit.siteBasisPenalty z)) = _
    rw [cutOperator_embedOp_prefix hi b0 H,
      cutOperator_appended_penalty z (fun _ ↦ z)]
  have hΨ (a : Entropy.RegionConfig (fun _ : Fin N ↦ q) (leftBlock N L))
      (b : (v : {v : Fin N // v ∉ leftBlock N L}) → Fin q) :
      paddedGroundVector hi z Γ (c.symm (a, b)) = u a * β b := by
    change (if (c (c.symm (a, b))).2 = b0 then u (c (c.symm (a, b))).1 else 0) = _
    rw [c.apply_symm_apply]
    by_cases hb : b = b0 <;> simp [β, hb]
  have hAu : A *ᵥ u = (E : ℂ) • u := by
    dsimp only [A, u]
    rw [Matrix.reindex_mulVec]
    rw [show H *ᵥ WithLp.ofLp Γ = (E : ℂ) • WithLp.ofLp Γ from
      (isGappedGroundState_iff.mp hgs).2.1]
    rfl
  have hBβ : B *ᵥ β = 0 := QuantumCircuit.productBasisPenalty_mulVec b0
  have hv : (fun p ↦ u p.1 * β p.2) = Matrix.vec (vecMulVec β u) := by
    funext p
    exact mul_comm _ _
  have heigen : (A ⊗ₖ 1 + 1 ⊗ₖ B) *ᵥ (fun p ↦ u p.1 * β p.2) =
      (E : ℂ) • (fun p ↦ u p.1 * β p.2) := by
    rw [hv, add_mulVec, Matrix.kronecker_mulVec_vec, Matrix.kronecker_mulVec_vec]
    simp only [Matrix.transpose_one, Matrix.mul_one,
      Matrix.vecMulVec_mul, Matrix.vecMul_transpose, Matrix.mul_vecMulVec, hAu, hBβ]
    simp [Matrix.vecMulVec_smul, Matrix.vec_smul]
  have hvec : (WithLp.ofLp (paddedGroundVector hi z Γ)) ∘ c.symm =
      (fun p ↦ u p.1 * β p.2) := by
    funext p
    exact hΨ p.1 p.2
  have heq : (∑ j, paddedInteraction hi z h j) *ᵥ
      WithLp.ofLp (paddedGroundVector hi z Γ) =
      (E : ℂ) • WithLp.ofLp (paddedGroundVector hi z Γ) := by
    rw [← hpad, ← hvec] at heigen
    rw [Matrix.reindex_mulVec] at heigen
    funext σ
    simpa only [c, Function.comp_apply, Pi.smul_apply, Equiv.symm_apply_apply] using
      congrFun heigen (c σ)
  have hback (σ : Fin N → Fin q) : u (c σ).1 * β (c σ).2 =
      paddedGroundVector hi z Γ σ := by
    simpa only [Prod.eta, c.symm_apply_apply] using (hΨ (c σ).1 (c σ).2).symm
  rw [← hpad] at hgap
  apply isGappedGroundState_iff.mpr
  refine ⟨(norm_paddedGroundVector hi z Γ).trans hgs.1, heq, ?_⟩
  convert hgap.submatrix c using 1
  ext σ τ
  simp only [submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply, Pi.star_apply, hback, add_zero, one_apply,
    c.injective.eq_iff, Entropy.cutOperator, reindex_apply]
  simp only [c, Equiv.symm_apply_apply]

end TNLean.MPS.AreaLaw
