import TNLean.MPS.AreaLaw.IntervalSymmDiff

/-!
# Boundary cases for moving the middle interval

Both middle-region conventions, a sharp endpoint example, clipping and an
empty chain are included.
-/

open scoped symmDiff

open TNLean.MPS.AreaLaw

-- The literal middle block of Proposition 5.7, at opposite window endpoints.
example : ((interval 8 2 5) ∆ (interval 8 1 6)).card ≤ 2 := by
  exact card_two_window_middle_symmDiff_le
    (L := 8) (a := 0) (b := 4) (ℓ := 1) (1 : Fin 2) 0 (0 : Fin 2)

-- Both changed sites actually occur in this case.
example : ((interval 8 2 5) ∆ (interval 8 1 6)).card = 2 := by decide

-- The middle block between the earlier pair of named cuts.
example : ((interval 8 1 5) ∆ (interval 8 2 6)).card ≤ 2 := by
  exact card_two_window_middle_symmDiff_le
    (L := 8) (a := 0) (b := 4) (ℓ := 1) (0 : Fin 2) 0 (1 : Fin 2)

-- Clipping both intervals at the right endpoint requires no admissibility hypothesis.
example : ((interval 3 4 7) ∆ (interval 3 2 9)).card ≤ 4 := by
  exact card_two_window_middle_symmDiff_le
    (L := 3) (a := 0) (b := 6) (ℓ := 2) (3 : Fin 4) 0 (0 : Fin 2)

-- There is no nonemptiness hypothesis on the chain.
example : ((interval 0 2 5) ∆ (interval 0 1 6)).card ≤ 2 := by
  exact card_two_window_middle_symmDiff_le
    (L := 0) (a := 0) (b := 4) (ℓ := 1) (1 : Fin 2) 0 (0 : Fin 2)
