/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BondEmbedding
import TNLean.MPS.Preparation.VaryingBondBlocks

/-!
# Density matrices and pairs on padded virtual bonds

Padding a virtual density matrix is its conjugation by the coordinate isometry. Its
fixed-point pair therefore equals the padding of the fixed-point pair on the actual bond.
This identifies the pairs used by the varying-bond preparation theorem.

## References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS".
-/

open Matrix MPSTensor
open scoped ComplexOrder MatrixOrder

namespace MPSTensor

/-- Zero padding of a virtual-bond matrix is its coordinate-isometry embedding. -/
theorem zeroPad_eq_embeddedBlockState {D a : ℕ} (ha : a ≤ D)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    Matrix.zeroPad D X = embeddedBlockState (Fin.castLE ha) X := by
  ext i j
  by_cases h : i.val < a ∧ j.val < a
  · let x : Fin a := ⟨i.val, h.1⟩
    let y : Fin a := ⟨j.val, h.2⟩
    have hi : i = Fin.castLE ha x := Fin.ext rfl
    have hj : j = Fin.castLE ha y := Fin.ext rfl
    rw [Matrix.zeroPad_apply_of_lt X h.1 h.2]
    conv_rhs => rw [hi, hj, embeddedBlockState,
      coordEmbedding_mul_mul_conjTranspose_apply_self (Fin.castLE_injective ha)]
  · rw [Matrix.zeroPad_apply_eq_zero X h, embeddedBlockState,
      coordEmbedding_mul_mul_conjTranspose_apply_eq_zero]
    rcases not_and_or.mp h with hi | hj
    · left
      rintro ⟨x, hx⟩
      exact hi (by simp [← hx])
    · right
      rintro ⟨y, hy⟩
      exact hj (by simp [← hy])

/-- The padded fixed-point pair is the fixed-point pair of the padded density matrix. -/
theorem padPair_fixedPointPair {D a : ℕ} (ha : a ≤ D)
    {σ : Matrix (Fin a) (Fin a) ℂ} (hσ : σ.PosSemidef) :
    VaryingBondChain.padPair D (fixedPointPair σ) = fixedPointPair (Matrix.zeroPad D σ) := by
  funext p
  change Matrix.zeroPad D (CFC.sqrt σ) p.1 p.2 = (CFC.sqrt (Matrix.zeroPad D σ)) p.1 p.2
  rw [zeroPad_eq_embeddedBlockState ha σ, embeddedBlockState,
    cfc_sqrt_coordEmbedding_mul_mul (Fin.castLE_injective ha) hσ,
    zeroPad_eq_embeddedBlockState ha (CFC.sqrt σ)]
  rfl

end MPSTensor
