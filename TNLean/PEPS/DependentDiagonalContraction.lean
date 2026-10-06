/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondCut

/-!
# Diagonal endpoint contractions

Identity matrices identify the two endpoint labels of every independent bond.
The resulting sum is exactly the ordinary single-label bond contraction, with
no dimension factor. This coordinate identity also allows a regional boundary
to close any extra cut incidences without changing the internal contraction.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.DependentBondNetwork

variable {Edge : Type*} (D : Edge → Type*)

/-- Independent endpoint labels, regrouped as a head assignment and a tail assignment. -/
def headTailConfigEquiv : EndpointConfig D ≃ ((e : Edge) → D e) × ((e : Edge) → D e) where
  toFun β := (fun e ↦ β (e, true), fun e ↦ β (e, false))
  invFun p e := if e.2 then p.1 e.1 else p.2 e.1
  left_inv β := by funext p; rcases p with ⟨e, b⟩; cases b <;> rfl
  right_inv _ := rfl

/-- The two endpoints carry the same bond label. -/
def diagonalEndpointConfig (η : (e : Edge) → D e) : EndpointConfig D := fun p ↦ η p.1

variable [Fintype Edge] [DecidableEq Edge]
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- Identity contractions eliminate one endpoint label per edge exactly. -/
theorem sum_identityWeight_mul (f : EndpointConfig D → ℂ) :
    (∑ β : EndpointConfig D,
      (∏ e, (1 : Matrix (D e) (D e) ℂ) (β (e, true)) (β (e, false))) * f β) =
      ∑ η : (e : Edge) → D e, f (diagonalEndpointConfig D η) := by
  classical
  rw [← (headTailConfigEquiv D).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro η _
  simp only [headTailConfigEquiv, Equiv.coe_fn_symm_mk, Bool.false_eq_true, ↓reduceIte,
    Matrix.one_apply, Fintype.prod_boole, ← funext_iff, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [ite_self]
  rfl

/-- Close the exposed endpoints of every selected edge by its identity matrix. -/
def cutIdentityWeight (C : Finset Edge) (θ : CutConfig C D) : ℂ :=
  ∏ e, if he : e ∈ C then
    (1 : Matrix (D e) (D e) ℂ) (θ (⟨e, he⟩, true)) (θ (⟨e, he⟩, false)) else 1

omit [∀ e, Fintype (D e)] in
/-- Closing the cut incidences supplies exactly the missing identity factors. -/
theorem cutIdentityWeight_mul_interior (C : Finset Edge) (β : EndpointConfig D) :
    cutIdentityWeight D C (cutRestriction D C β) * cutInteriorWeight D C β =
      ∏ e, (1 : Matrix (D e) (D e) ℂ) (β (e, true)) (β (e, false)) := by
  rw [cutIdentityWeight, cutInteriorWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : e ∈ C
  · simp only [he, ↓reduceDIte, ↓reduceIte, mul_one]
    rfl
  · simp only [he, ↓reduceDIte, ↓reduceIte, one_mul]

/-- A joint cut boundary can close every selected bond, retaining any
coefficient that depends on the remaining diagonal labels. -/
theorem sum_cutIdentityWeight_mul (C : Finset Edge)
    (f : CutConfig C D → ℂ) (g : EndpointConfig D → ℂ) :
    (∑ β : EndpointConfig D,
      (f (cutRestriction D C β) * cutIdentityWeight D C (cutRestriction D C β) *
        cutInteriorWeight D C β) * g β) =
      ∑ η : (e : Edge) → D e,
        f (cutRestriction D C (diagonalEndpointConfig D η)) *
          g (diagonalEndpointConfig D η) := by
  calc
    _ = ∑ β : EndpointConfig D,
        (∏ e, (1 : Matrix (D e) (D e) ℂ) (β (e, true)) (β (e, false))) *
          (f (cutRestriction D C β) * g β) := by
      apply Finset.sum_congr rfl
      intro β _
      rw [mul_assoc (f _), cutIdentityWeight_mul_interior]
      ring
    _ = _ := sum_identityWeight_mul D _

end TNLean.PEPS.DependentBondNetwork
