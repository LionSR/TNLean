import TNLean.Algebra.TwoWindowSum

open scoped BigOperators

-- Adjacent windows exhaust the right endpoint, with an empty middle and tail.
example (f : Fin 5 → ℤ) :
    (∑ t, f t) =
      (∑ t : Fin 1, f ⟨t.val, by omega⟩) +
      (∑ r : Fin 2, f ⟨1 + r.val, by omega⟩) +
      (∑ r : Fin 0, f ⟨3 + r.val, by omega⟩) +
      (∑ r : Fin 2, f ⟨3 + r.val, by omega⟩) +
      (∑ r : Fin 0, f ⟨5 + r.val, by omega⟩) := by
  exact Fin.sum_univ_eq_five_parts_of_two_windows f 1 3 1 (by omega) (by omega)

-- Zero windows and empty end intervals are permitted.
example (f : Fin 3 → ℤ) :
    (∑ t, f t) =
      (∑ t : Fin 0, f ⟨t.val, by omega⟩) +
      (∑ r : Fin 0, f ⟨r.val, by omega⟩) +
      (∑ r : Fin 3, f ⟨r.val, by omega⟩) +
      (∑ r : Fin 0, f ⟨3 + r.val, by omega⟩) +
      (∑ r : Fin 0, f ⟨3 + r.val, by omega⟩) := by
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] using
    Fin.sum_univ_eq_five_parts_of_two_windows f 0 3 0 (by omega) (by omega)
