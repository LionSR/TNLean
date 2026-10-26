import TNLean.Algebra.TwoWindowFamily

/-!
# Boundary cases for the grouped bond family

These examples retain empty complementary intervals and empty windows,
and check the original alphabet without identifying equal operator values.
-/

open scoped BigOperators

/-- Adjacent windows end at the final bond, leaving two empty bulks. -/
example :
    (∑ α, Fin.twoWindowFamily (fun r : Fin 5 ↦ (r.val : ℤ))
      1 3 1 (by decide) (by decide) α) = 10 := by
  exact (Fin.sum_twoWindowFamily (fun r : Fin 5 ↦ (r.val : ℤ))
    1 3 1 (by decide) (by decide)).trans (by decide)

/-- Zero-length windows retain all three complementary sums. -/
example :
    (∑ c : Fin 3, Fin.twoWindowFamily (fun r : Fin 4 ↦ (r.val : ℤ))
      1 3 0 (by decide) (by decide) (Sum.inr c)) = 6 := by
  simpa using (Fin.sum_twoWindowFamily (fun r : Fin 4 ↦ (r.val : ℤ))
    1 3 0 (by decide) (by decide)).trans (show (∑ t : Fin 4, (t.val : ℤ)) = 6 by decide)

/-- The full alphabet keeps all window and bulk labels. -/
example (ℓ : ℕ) :
    Fintype.card ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) = 4 * ℓ + 3 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- The selected window labels are distinct constructors. -/
example {ℓ : ℕ} (p q : Fin (2 * ℓ)) :
    (Sum.inl (Sum.inl p) : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) ≠
      Sum.inl (Sum.inr q) := by
  simp

/-- A nonzero projection that discards the second coordinate. -/
private def firstCoordinate : (ℤ × ℤ) →+ ℤ where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

example : ¬ Function.Injective firstCoordinate := by
  intro h
  exact (zero_ne_one : (0 : ℤ) ≠ 1)
    (congrArg Prod.snd (h (show firstCoordinate (0, 0) = firstCoordinate (0, 1) from rfl)))

/-- The same grouped array is preserved by a noninjective coordinate map. -/
example (α : (Fin 2 ⊕ Fin 2) ⊕ Fin 3) :
    Fin.twoWindowFamily (fun r : Fin 5 ↦ (r.val : ℤ))
      1 3 1 (by decide) (by decide) α =
        firstCoordinate (Fin.twoWindowFamily
          (fun r : Fin 5 ↦ ((r.val : ℤ), (r.val : ℤ) + 1))
          1 3 1 (by decide) (by decide) α) := by
  exact Fin.twoWindowFamily_map
    (fun r : Fin 5 ↦ ((r.val : ℤ), (r.val : ℤ) + 1)) firstCoordinate
    1 3 1 (by decide) (by decide) α
