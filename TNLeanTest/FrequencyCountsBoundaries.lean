import TNLean.MPS.AreaLaw.FrequencyCounts

open scoped BigOperators

-- No residual degree and one ordinary coordinate.
example : Nat.card {α : Fin 3 → ℕ //
    (∑ a, α a) = 0 ∧ α 0 = 0 ∧ α 1 = 0} = 1 := by
  simpa using Nat.card_fun_sum_eq_and_two_eq_of_total (I := Fin 3) (s := 0)
    (by decide) (0 : Fin 3) 1 (by decide) 0 0 0

-- With one ordinary coordinate, every possible prescribed pair has one extension.
example : Nat.card {α : Fin 3 → ℕ //
    (∑ a, α a) = 7 ∧ α 0 = 2 ∧ α 1 = 3} = 1 := by
  simpa using Nat.card_fun_sum_eq_and_two_eq_of_total (I := Fin 3) (s := 0)
    (by decide) (0 : Fin 3) 1 (by decide) 7 2 3

-- Positive prescribed coordinates and zero residual degree.
example : Nat.card {α : Fin 4 → ℕ //
    (∑ a, α a) = 8 ∧ α 0 = 3 ∧ α 3 = 5} = 1 := by
  simpa using Nat.card_fun_sum_eq_and_two_eq_of_total (I := Fin 4) (s := 1)
    (by decide) (0 : Fin 4) 3 (by decide) 8 3 5

-- Positive residual degree and two ordinary coordinates.
example : Nat.card {α : Fin 4 → ℕ //
    (∑ a, α a) = 10 ∧ α 0 = 3 ∧ α 3 = 5} = 3 := by
  simpa using Nat.card_fun_sum_eq_and_two_eq_of_total (I := Fin 4) (s := 1)
    (by decide) (0 : Fin 4) 3 (by decide) 10 3 5

-- Impossible prescribed coordinates.
example : Nat.card {α : Fin 3 → ℕ //
    (∑ a, α a) = 1 ∧ α 0 = 1 ∧ α 1 = 1} = 0 := by
  simpa using Nat.card_fun_sum_eq_and_two_eq_of_total (I := Fin 3) (s := 0)
    (by decide) (0 : Fin 3) 1 (by decide) 1 1 1

-- The empty case needs neither a third label nor a cardinality hypothesis.
example : Nat.card {α : Fin 2 → ℕ //
    (∑ a, α a) = 2 ∧ α 0 = 2 ∧ α 1 = 1} = 0 := by
  exact Nat.card_fun_sum_eq_and_two_eq_of_lt (0 : Fin 2) 1 (by decide)
    2 2 1 (by decide)
