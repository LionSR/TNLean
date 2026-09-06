/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.MPS.MPU.DoubleLayerContraction
import TNLean.MPS.MPU.SourceVIsometry
import TNLean.MPS.MPU.SuppliedFixedWitnesses

/-!
# Physical closures of the source Y factors

The two diagrams in arXiv:2502.20257, Corollary `cor:mpu`(b), equation
`eq:MPUnice2` (lines 869--917), leave the physical legs open, not the
source-rank legs. Their common contraction is the canonical one-letter
identity in the proof (lines 1013--1050). We derive that identity with the
recorded canonical boundaries from simplicity, then cancel the source X
factors using the Gram equations of arXiv:1703.09188, Theorem III.8.
No simplicity assumption on the physical adjoint is required.
-/

open scoped Matrix BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

/-- The one-letter diagram with identity left boundary and canonical right
boundary is the physical identity. The order `ρ β α` comes from `Matrix.vec`.

Source: arXiv:2502.20257, proof of Corollary `cor:mpu`(b), lines 1013--1030.
The canonical witness alignment uses arXiv:1703.09188, equations `Erightleft`,
`simple1`, and `simple2`, rather than assuming a supplied boundary identity. -/
theorem IsMPUCanonicalFormII.oneLetter_physical_contraction
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) (p q : Fin d) :
    (∑ x : Fin D, ∑ α : Fin D, ∑ β : Fin D, ∑ z : Fin d,
      star (U z p x α) * U z q x β * hU.ρ β α) =
        if p = q then 1 else 0 := by
  have := hU.neZero_phys
  let Φ : Fin (D * D) → ℂ := fun x ↦
    (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)
  let ρ : Fin (D * D) → ℂ := fun x ↦ hU.ρ.vec (finProdFinEquiv.symm x)
  have h₂ := hU.simple2_recorded_fixed_pair hsimple
  have h₁ := hU.isMPU.simple1_of_simple2_supplied Φ ρ h₂ p q
  have hentry (x : Fin D) :
      (doubleLayerTensor U p q *ᵥ ρ) (finProdFinEquiv (x, x)) =
        ∑ α : Fin D, ∑ β : Fin D, ∑ z : Fin d,
          star (U z p x α) * U z q x β * hU.ρ β α := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [ρ, Matrix.vec, doubleLayerTensor_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.sum_apply, kroneckerMap_apply,
      physicalAdjointTensor_apply, RCLike.star_def]
    simp_rw [Finset.sum_mul]
    rw [Fintype.sum_prod_type]
  rw [dotProduct, ← Equiv.sum_comp finProdFinEquiv] at h₁
  simpa only [Φ, Matrix.vec, Equiv.symm_apply_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, hentry] using h₁

/-- Closing the source-rank and virtual legs of the second source factor,
with the canonical right boundary, gives the identity on its physical legs.
This is a physical Gram closure, not a source-rank identity $Y_2Y_2^\dagger$.

Source: arXiv:2502.20257, Corollary `cor:mpu`(b), the first diagram in
`eq:MPUnice2` (lines 869--917); cancellation of $X_2$ in lines 1030--1050. -/
theorem IsMPUCanonicalFormII.sourceY₂_physical_contraction
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) (p q : Fin d) :
    (∑ l : Fin ℓ[U], ∑ α : Fin D, ∑ β : Fin D,
      star (sourceY₂ U l (p, α)) * sourceY₂ U l (q, β) * hU.ρ β α) =
        if p = q then 1 else 0 := by
  rw [Fintype.sum_reverse_three]
  simp_rw [← Finset.sum_mul, ← sourceY₂_gram_eq_rotated_sourceCutM₂_gram,
    Finset.sum_mul]
  rw [Fintype.sum_last_two_first_four]
  conv_lhs => arg 2; ext x; rw [Fintype.sum_reverse_three]
  exact hU.oneLetter_physical_contraction hsimple p q

/-- Closing the source-rank and virtual legs of the first source factor gives
the physical identity. The weight already lies in $Y_1$; diagonality of the
canonical matrix supplies the symmetry needed to orient that weight.

Source: arXiv:2502.20257, Corollary `cor:mpu`(b), the second diagram in
`eq:MPUnice2` (lines 869--917), and its analogous $X_1$ cancellation at line 1050. -/
theorem IsMPUCanonicalFormII.sourceY₁_physical_contraction
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) (p q : Fin d) :
    (∑ r : Fin r[U], ∑ α : Fin D,
      star (sourceY₁ U hU.ρ hU.ρ_posDef r (α, p)) *
        sourceY₁ U hU.ρ hU.ρ_posDef r (α, q)) =
        if p = q then 1 else 0 := by
  rw [Finset.sum_comm]
  simp_rw [sourceY₁_gram_eq_weighted_sourceCutM₁_gram]
  conv_lhs => arg 2; ext x; rw [Fintype.sum_reverse_three]
  calc
    _ = ∑ x : Fin D, ∑ α : Fin D, ∑ β : Fin D, ∑ z : Fin d,
        star (U z p x α) * U z q x β * hU.ρ β α := by
      refine Finset.sum_congr₂ fun x _ α _ ↦ ?_
      refine Finset.sum_congr₂ fun β _ z _ ↦ ?_
      have hρ : hU.ρ α β = hU.ρ β α :=
        congrArg (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M β α) hU.ρ_isDiag.isSymm.eq
      rw [hρ]
      ring
    _ = _ := hU.oneLetter_physical_contraction hsimple p q

end MPOTensor
