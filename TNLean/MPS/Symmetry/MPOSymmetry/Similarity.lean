/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Matrix product operator fusion algebras under a physical similarity

If the periodic operators of one family of tensors are obtained from those of another by one
similarity of the physical space at each length, `O_a^L = P_L O'_a^L Q_L` with `Q_L P_L = 1`,
then the first family satisfies every fusion rule the second one does. The similarity may be
the identity, so families with equal periodic operators have the same fusion rules.

## Main results

* `MPOTensor.IsMPOFusionAlgebra.of_mpo_eq_mul_mul`: fusion rules transfer along a physical
  similarity of the periodic operators.
-/

open scoped Matrix

namespace MPOTensor

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- **Fusion rules transfer along a physical similarity.** If `O_a^L = P_L O'_a^L Q_L` for every
label `a` and every positive length `L`, with `Q_L P_L = 1`, and the family `O'` satisfies the
fusion rules `N`, then so does the family `O`. -/
theorem IsMPOFusionAlgebra.of_mpo_eq_mul_mul {χ χ' : ι → ℕ} {O : ∀ a, MPOTensor d (χ a)}
    {O' : ∀ a, MPOTensor d (χ' a)} {N : ι → ι → ι → ℕ} (h : IsMPOFusionAlgebra O' N)
    (P Q : ∀ L : ℕ, Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ)
    (hQP : ∀ L, 0 < L → Q L * P L = 1)
    (hO : ∀ a L, 0 < L → mpo (O a) L = P L * mpo (O' a) L * Q L) :
    IsMPOFusionAlgebra O N := by
  intro a b L hL
  have hmid : P L * mpo (O' a) L * Q L * (P L * mpo (O' b) L * Q L) =
      P L * (mpo (O' a) L * mpo (O' b) L) * Q L := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Q L) (P L), hQP L hL, Matrix.one_mul]
  rw [hO a L hL, hO b L hL, hmid, h a b L hL, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hO c L hL, Matrix.mul_smul, Matrix.smul_mul]

end MPOTensor
