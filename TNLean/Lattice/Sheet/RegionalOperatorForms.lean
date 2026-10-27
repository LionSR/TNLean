/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Splitting

/-!
# Operators supported in a single region

Let T and E be disjoint finite regions, and put U = (T ∪ E)ᶜ. In the
three-region coordinates, an operator supported in T has the form
(B ⊗ 1_E) ⊗ 1_U, and an operator supported in U has the form 1_{TE} ⊗ B.
Together with the middle-region form, these give the three local summands
of a nearest-neighbour operator away from the two crossing edges.
Empty regions and zero local dimension are included.

## References

ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821.
-/

open Matrix QuantumCircuit
open scoped Kronecker

noncomputable section

namespace TNLean.Lattice.Sheet

/-- An operator on a subset of T has a T-only factor in the three-region coordinates.
ALVV, arXiv:1602.08828v2, eq:H-mid-cut, lines 810–821. -/
theorem exists_threeSplit_eq_kronecker_one_kronecker_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {T E : Finset ι} (h : Disjoint T E) {D : Set ι} (hD : D ⊆ T)
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q D) :
    ∃ B : Matrix (T → Fin q) (T → Fin q) ℂ,
      A.submatrix (threeSplit q T E h).symm (threeSplit q T E h).symm =
        (B ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
          (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) := by
  refine exists_eq_of_mem_supportedOperators (threeSplit q T E h)
    (((kroneckerBilinear (R := ℂ)).flip
      (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)).comp
      ((kroneckerBilinear (R := ℂ)).flip
        (1 : Matrix (E → Fin q) (E → Fin q) ℂ)))
    (fun m hm => ?_) hA
  have hE : ∀ v : E, m v = 1 := fun v =>
    hm v fun hv => Finset.disjoint_left.mp h (hD hv) v.2
  have hU : ∀ v : ↥(T ∪ E)ᶜ, m v = 1 := fun v =>
    hm v fun hv => (Finset.mem_compl.mp v.2) (Finset.mem_union_left E (hD hv))
  refine ⟨rectKronecker (fun v : T => m v), ?_⟩
  rw [rectKronecker_submatrix_threeSplit h]
  simp only [hE, hU, rectKronecker_one]
  rfl

/-- An operator on a subset of U has a U-only factor in the three-region coordinates.
ALVV, arXiv:1602.08828v2, eq:H-mid-cut, lines 810–821. -/
theorem exists_threeSplit_eq_one_kronecker
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {T E : Finset ι} (h : Disjoint T E) {D : Set ι}
    (hD : D ⊆ ((T ∪ E)ᶜ : Finset ι))
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q D) :
    ∃ B : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ,
      A.submatrix (threeSplit q T E h).symm (threeSplit q T E h).symm =
        (1 : Matrix ((T → Fin q) × (E → Fin q))
          ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ B := by
  refine exists_eq_of_mem_supportedOperators (threeSplit q T E h)
    (kroneckerBilinear (R := ℂ)
      (1 : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ))
    (fun m hm => ?_) hA
  have hT : ∀ v : T, m v = 1 := fun v =>
    hm v fun hv => (Finset.mem_compl.mp (hD hv)) (Finset.mem_union_left E v.2)
  have hE : ∀ v : E, m v = 1 := fun v =>
    hm v fun hv => (Finset.mem_compl.mp (hD hv)) (Finset.mem_union_right T v.2)
  refine ⟨rectKronecker (fun v : ↥(T ∪ E)ᶜ => m v), ?_⟩
  rw [rectKronecker_submatrix_threeSplit h]
  change _ = (1 : Matrix ((T → Fin q) × (E → Fin q))
    ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ _
  simp only [hT, hE, rectKronecker_one, one_kronecker_one]

end TNLean.Lattice.Sheet
