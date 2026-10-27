/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import TNLean.Algebra.TwoWindowFamily

/-!
# Three-region tensor forms after grouping two windows

The two-window family preserves the decomposition of every term other than
one selected term in each window into operators on three tensor factors.
The three regional arrays are grouped using exactly the same windows.
No finiteness or nonemptiness assumption on the tensor-factor index types
is required.

## Main results

- `Matrix.twoWindowFamily_eq_three_region_forms`: the grouped ordinary
  terms retain their three-region tensor forms.

## References

- ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821:
  the additive grouping used in the operator-Schmidt-rank argument.
-/

open scoped BigOperators Kronecker

/-- Grouping two windows preserves every ordinary three-region tensor form.
This is the additive assembly used with ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. The original ordinary identities are the
explicit hypotheses of this auxiliary; physical locality supplies them
at the application. -/
theorem Matrix.twoWindowFamily_eq_three_region_forms
    {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {N : ℕ}
    (H : Fin N → Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ)
    (HL : Fin N → Matrix X X ℂ) (HM : Fin N → Matrix Y Y ℂ)
    (HR : Fin N → Matrix Z Z ℂ)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N)
    (p s : Fin (2 * ℓ))
    (hord : ∀ r : Fin N, r.val ≠ a + p.val → r.val ≠ b + s.val →
      H r = (HL r ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ) +
        ((1 : Matrix X X ℂ) ⊗ₖ HM r) ⊗ₖ (1 : Matrix Z Z ℂ) +
        (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ HR r)
    (α : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)
    (hαL : α ≠ Sum.inl (Sum.inl p)) (hαR : α ≠ Sum.inl (Sum.inr s)) :
    Fin.twoWindowFamily H a b ℓ hab hbN α =
      (Fin.twoWindowFamily HL a b ℓ hab hbN α ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ
          (1 : Matrix Z Z ℂ) +
        ((1 : Matrix X X ℂ) ⊗ₖ Fin.twoWindowFamily HM a b ℓ hab hbN α) ⊗ₖ
          (1 : Matrix Z Z ℂ) +
        (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
          Fin.twoWindowFamily HR a b ℓ hab hbN α := by
  classical
  let k₁ : Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ →ₗ[ℂ]
      Matrix (X × Y) (X × Y) ℂ := Matrix.kroneckerBilinear
  let k₂ : Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix Z Z ℂ →ₗ[ℂ]
      Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ := Matrix.kroneckerBilinear
  let eL := (k₂.flip (1 : Matrix Z Z ℂ)).comp (k₁.flip (1 : Matrix Y Y ℂ))
  let eM := (k₂.flip (1 : Matrix Z Z ℂ)).comp (k₁ (1 : Matrix X X ℂ))
  let eR := k₂ (1 : Matrix (X × Y) (X × Y) ℂ)
  have hsum {k : ℕ} (idx : Fin k → Fin N)
      (hu : ∀ r, (idx r).val ≠ a + p.val)
      (hv : ∀ r, (idx r).val ≠ b + s.val) :
      (∑ r, H (idx r)) =
        ((∑ r, HL (idx r)) ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ) +
          ((1 : Matrix X X ℂ) ⊗ₖ (∑ r, HM (idx r))) ⊗ₖ (1 : Matrix Z Z ℂ) +
          (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ (∑ r, HR (idx r)) := by
    change (∑ r, H (idx r)) =
      eL (∑ r, HL (idx r)) + eM (∑ r, HM (idx r)) + eR (∑ r, HR (idx r))
    rw [map_sum, map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ ↦ hord (idx r) (hu r) (hv r)
  rcases α with (r | r) | t
  · have hrp : r ≠ p := fun h ↦ hαL (congrArg Sum.inl (congrArg Sum.inl h))
    exact hord ⟨a + r.val, by omega⟩
      (fun h ↦ hrp (Fin.ext (Nat.add_left_cancel h)))
      (show a + r.val ≠ b + s.val by omega)
  · exact hord ⟨b + r.val, by omega⟩
      (show b + r.val ≠ a + p.val by omega)
      (fun h ↦ hαR (congrArg Sum.inl (congrArg Sum.inr
        (Fin.ext (Nat.add_left_cancel h)))))
  · rcases t with ⟨t, ht⟩
    have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact hsum (fun r : Fin a ↦ ⟨r.val, by omega⟩)
        (fun r ↦ (show r.val ≠ a + p.val by omega))
        (fun r ↦ (show r.val ≠ b + s.val by omega))
    · exact hsum (fun r : Fin (b - (a + 2 * ℓ)) ↦
          ⟨a + 2 * ℓ + r.val, by omega⟩)
        (fun r ↦ (show a + 2 * ℓ + r.val ≠ a + p.val by omega))
        (fun r ↦ (show a + 2 * ℓ + r.val ≠ b + s.val by omega))
    · exact hsum (fun r : Fin (N - (b + 2 * ℓ)) ↦
          ⟨b + 2 * ℓ + r.val, by omega⟩)
        (fun r ↦ (show b + 2 * ℓ + r.val ≠ a + p.val by omega))
        (fun r ↦ (show b + 2 * ℓ + r.val ≠ b + s.val by omega))
