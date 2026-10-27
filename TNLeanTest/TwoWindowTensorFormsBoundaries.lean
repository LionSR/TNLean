/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoWindowTensorForms

/-!
# Applications of the grouped three-region tensor identities

The middle bulk contains three original terms. An empty left factor is
also permitted without a positivity assumption on its dimension.
-/

open scoped BigOperators Kronecker

-- Each constant regional operator is multiplied by the three-term middle-bulk length.
example (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    Fin.twoWindowFamily
      (fun _ : Fin 9 ↦ (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ C)
      1 6 1 (by decide) (by decide) (Sum.inr (1 : Fin 3)) =
      (((3 : ℕ) • A) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ((3 : ℕ) • B)) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ ((3 : ℕ) • C) := by
  simpa [Fin.twoWindowFamily] using
    (Matrix.twoWindowFamily_eq_three_region_forms
      (fun _ : Fin 9 ↦ (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ C)
      (fun _ ↦ A) (fun _ ↦ B) (fun _ ↦ C)
      1 6 1 (by decide) (by decide) (0 : Fin 2) 1 (fun _ _ _ ↦ rfl)
      (Sum.inr (1 : Fin 3)) (by decide) (by decide))

local notation "G₀" => ((Fin 0 × Fin 2) × Fin 2)

-- The theorem can be applied with an empty configuration factor.
example :
    Fin.twoWindowFamily (fun _ : Fin 9 ↦ (0 : Matrix G₀ G₀ ℂ))
      1 6 1 (by decide) (by decide) (Sum.inl (Sum.inl (1 : Fin 2))) =
      ((0 : Matrix (Fin 0) (Fin 0) ℂ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((1 : Matrix (Fin 0) (Fin 0) ℂ) ⊗ₖ (0 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (1 : Matrix (Fin 0 × Fin 2) (Fin 0 × Fin 2) ℂ) ⊗ₖ
          (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  exact Matrix.twoWindowFamily_eq_three_region_forms
    (fun _ : Fin 9 ↦ (0 : Matrix G₀ G₀ ℂ))
    (fun _ ↦ (0 : Matrix (Fin 0) (Fin 0) ℂ))
    (fun _ ↦ (0 : Matrix (Fin 2) (Fin 2) ℂ))
    (fun _ ↦ (0 : Matrix (Fin 2) (Fin 2) ℂ))
    1 6 1 (by decide) (by decide) (0 : Fin 2) 1
    (fun _ _ _ ↦ by simp)
    (Sum.inl (Sum.inl (1 : Fin 2))) (by decide) (by decide)
