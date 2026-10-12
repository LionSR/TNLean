/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceSlotBasis

/-! # Slot-basis coordinates of the joint source vector

The joint source vector of a source inventory expands in the recorded slot
basis with the product of its original source coefficients, and its
coordinates are read off from that expansion.
Source: polynomial-PEPS, `04-compression.tex`, lines 253–267 and 279–355.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 253–267, 279–355 and 565–588.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- The fixed source vector expands in its actual endpoint basis with the
product of its original source coefficients.
Source: polynomial-PEPS 04-compression.tex, lines 253–267 and 279–355. -/
theorem slotVector_eq_sum_slotBasis (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (η : ∀ i, U i ⊗[ℂ] V i) :
    slotVector R U V η = ∑ a : ∀ i, A i × B i,
      (∏ i, ((bU i).tensorProduct (bV i)).repr (η i) (a i)) •
        slotBasis R U V bU bV a := by
  classical
  have h : η = fun i => ∑ a, ((bU i).tensorProduct (bV i)).repr (η i) a •
      (bU i a.1 ⊗ₜ[ℂ] bV i a.2) := by
    funext i
    simpa only [OrthonormalBasis.tensorProduct_apply'] using
      ((bU i).tensorProduct (bV i)).sum_repr (η i) |>.symm
  conv_lhs => rw [h, (slotVector R U V).map_sum]
  simp only [(slotVector R U V).map_smul_univ, slotBasis_apply]

/-- Coordinates of the actual fixed source vector are the product of its
individual source coordinates.
Source: polynomial-PEPS 04-compression.tex, lines 253–267 and 279–355. -/
theorem slotBasis_repr_slotVector (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (η : ∀ i, U i ⊗[ℂ] V i) (a : ∀ i, A i × B i) :
    (slotBasis R U V bU bV).repr (slotVector R U V η) a =
      ∏ i, ((bU i).tensorProduct (bV i)).repr (η i) (a i) := by
  classical
  rw [slotVector_eq_sum_slotBasis R U V bU bV η]
  simp [map_sum, OrthonormalBasis.repr_self, Pi.single_apply]

end TNLean.PEPS.PairEffect.SourceInventory
