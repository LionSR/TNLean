/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.Transfer
import TNLean.Algebra.HermitianHelpers
import Mathlib.Analysis.Matrix.Order

/-!
# Kernel invariance for fixed points of the transfer map

For a positive-semidefinite fixed point `ρ` of the transfer operator
`E_A(X) = ∑ i, A i * X * (A i)ᴴ`, the kernel of `ρ` is invariant under each adjoint
Kraus operator `(A i)ᴴ`. This is the kernel-invariance step in the proof of positive
definiteness of fixed points (Wolf Theorem 6.3, item 2) and in the support-projection
invariance arguments for MPS tensors; it was previously proved separately in
`TNLean.QPF.PosDef` and `TNLean.MPS.Irreducible.FixedPointProjection`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2,
  Theorem 6.3 item 2][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- If `ρ` is PSD and `E_A(ρ) = ρ`, then `ker ρ` is invariant under each adjoint Kraus
operator: `ρ *ᵥ x = 0` implies `ρ *ᵥ ((A i)ᴴ *ᵥ x) = 0`. -/
lemma ker_invariant_under_adjoint
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (x : Fin D → ℂ) (hx : ρ *ᵥ x = 0) :
    ∀ i : Fin d, ρ *ᵥ ((A i)ᴴ *ᵥ x) = 0 := by
  classical
  have hqf : star x ⬝ᵥ (ρ *ᵥ x) = 0 := by simp [hx]
  have hsum : star x ⬝ᵥ (ρ *ᵥ x) =
      ∑ i : Fin d, star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) := by
    conv_lhs =>
      rw [show ρ *ᵥ x = (transferMap (d := d) (D := D) A ρ) *ᵥ x from by rw [hρ_fix]]
    simp only [transferMap_apply, Matrix.sum_mulVec]
    rw [dotProduct_sum]
    congr 1; ext i
    rw [show (A i * ρ * (A i)ᴴ) *ᵥ x = A i *ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) from by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]]
    rw [HermitianHelpers.dotProduct_mulVec_conjTranspose]
  have h_each_zero : ∀ i : Fin d,
      star ((A i)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A i)ᴴ *ᵥ x)) = 0 := by
    intro i
    have h_sum_zero :
        ∑ j, RCLike.re (star ((A j)ᴴ *ᵥ x) ⬝ᵥ (ρ *ᵥ ((A j)ᴴ *ᵥ x))) = 0 := by
      rw [← map_sum, ← hsum, hqf]; simp
    have hre := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hρ_psd.re_dotProduct_nonneg _)).mp
      h_sum_zero i (Finset.mem_univ _)
    exact Complex.ext hre (hρ_psd.isHermitian.im_star_dotProduct_mulVec_self _)
  intro i
  exact (hρ_psd.dotProduct_mulVec_zero_iff _).mp (h_each_zero i)

end MPSTensor
