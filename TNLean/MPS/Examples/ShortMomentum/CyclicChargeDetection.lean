/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.SevenCyclicObstruction

/-!
# Detecting every noncentral charge at longer degrees

The explicit short words at degrees seven, eight and nine extend to
all larger degrees by appending one copy of each physical letter.
Their charge remains fixed and their two first-letter pairings remain
distinct. This supplies a uniform cyclic charge obstruction, without
asserting that seven-site constraints imply a global boundary space.

Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 850--880;
see `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

namespace MPSTensor.ShortMomentum

/-- Every charge outside the three omitted degree-six charges has an
explicit six-site physical word. -/
theorem exists_six_config_of_charge (u v : ZMod 5)
    (h04 : (u, v) ≠ (0, 4)) (h11 : (u, v) ≠ (1, 1)) (h40 : (u, v) ≠ (4, 0)) :
    ∃ σ : Cfg 3 6, wordCharge (List.ofFn σ) = (u, v) := by
  fin_cases u <;> fin_cases v
  · exact ⟨![0, 0, 1, 1, 2, 2], by decide⟩
  · exact ⟨![1, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨![0, 0, 0, 2, 2, 2], by decide⟩
  · exact ⟨![0, 1, 1, 1, 1, 2], by decide⟩
  · exact (h04 rfl).elim
  · exact ⟨![0, 2, 2, 2, 2, 2], by decide⟩
  · exact (h11 rfl).elim
  · exact ⟨![0, 0, 1, 1, 1, 2], by decide⟩
  · exact ⟨![1, 1, 2, 2, 2, 2], by decide⟩
  · exact ⟨![0, 0, 0, 1, 2, 2], by decide⟩
  · exact ⟨![1, 1, 1, 2, 2, 2], by decide⟩
  · exact ⟨![0, 0, 0, 1, 1, 2], by decide⟩
  · exact ⟨![0, 1, 2, 2, 2, 2], by decide⟩
  · exact ⟨![0, 0, 0, 0, 2, 2], by decide⟩
  · exact ⟨![0, 0, 1, 1, 1, 1], by decide⟩
  · exact ⟨![0, 0, 0, 0, 1, 2], by decide⟩
  · exact ⟨![0, 0, 2, 2, 2, 2], by decide⟩
  · exact ⟨![1, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨![0, 0, 0, 1, 1, 1], by decide⟩
  · exact ⟨![0, 1, 1, 2, 2, 2], by decide⟩
  · exact (h40 rfl).elim
  · exact ⟨![0, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨![0, 0, 0, 0, 1, 1], by decide⟩
  · exact ⟨![0, 0, 1, 2, 2, 2], by decide⟩
  · exact ⟨![2, 2, 2, 2, 2, 2], by decide⟩

/-- Explicit phase-detecting words at degree eight. -/
theorem exists_distinct_eight_cyclic_phases (u v : ZMod 5) (hne : (u, v) ≠ 0) :
    ∃ (i j : Fin 3) (σ τ : Cfg 3 7),
      wordCharge (i :: List.ofFn σ) = (u, v) ∧
      wordCharge (j :: List.ofFn τ) = (u, v) ∧
      letterPairing i (u, v) ≠ letterPairing j (u, v) := by
  fin_cases u <;> fin_cases v
  · exact (hne rfl).elim
  · exact ⟨0, 2, ![0, 0, 0, 2, 2, 2, 2], ![0, 0, 0, 0, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 1, 1, 1, 1, 2, 2], ![0, 0, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 1, 1, 1], ![1, 1, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 1, 2, 2, 2], ![0, 0, 0, 1, 2, 2, 2], by decide⟩
  · exact ⟨1, 2, ![1, 1, 1, 2, 2, 2, 2], ![1, 1, 1, 1, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 1, 1, 2, 2], ![0, 0, 0, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![1, 1, 2, 2, 2, 2, 2], ![0, 1, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 2, 2, 2], ![0, 0, 0, 0, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![0, 2, 2, 2, 2, 2, 2], ![0, 0, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 1, 2, 2], ![0, 0, 0, 0, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 1, 2, 2, 2, 2, 2], ![0, 0, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 2, 2, 2], ![1, 1, 1, 1, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![0, 0, 1, 1, 1, 1, 2], ![0, 0, 0, 1, 1, 1, 1], by decide⟩
  · exact ⟨0, 1, ![1, 1, 1, 2, 2, 2, 2], ![0, 1, 1, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 2, 2, 2, 2, 2], ![0, 0, 0, 1, 1, 1, 1], by decide⟩
  · exact ⟨0, 1, ![1, 1, 1, 1, 2, 2, 2], ![0, 1, 1, 1, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![0, 0, 0, 1, 1, 1, 2], ![0, 0, 0, 0, 1, 1, 1], by decide⟩
  · exact ⟨0, 1, ![0, 1, 1, 2, 2, 2, 2], ![0, 0, 1, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 1, 2, 2], ![2, 2, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 1, 1, 1, 2, 2, 2], ![0, 0, 1, 1, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![0, 0, 0, 0, 1, 1, 2], ![1, 1, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 2, 2, 2, 2], ![0, 0, 0, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![2, 2, 2, 2, 2, 2, 2], ![0, 1, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 1, 1], by decide⟩

/-- Explicit phase-detecting words at degree nine. -/
theorem exists_distinct_nine_cyclic_phases (u v : ZMod 5) (hne : (u, v) ≠ 0) :
    ∃ (i j : Fin 3) (σ τ : Cfg 3 8),
      wordCharge (i :: List.ofFn σ) = (u, v) ∧
      wordCharge (j :: List.ofFn τ) = (u, v) ∧
      letterPairing i (u, v) ≠ letterPairing j (u, v) := by
  fin_cases u <;> fin_cases v
  · exact (hne rfl).elim
  · exact ⟨0, 1, ![1, 1, 2, 2, 2, 2, 2, 2], ![0, 1, 2, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 2, 2, 2, 2], ![0, 0, 0, 0, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 2, 2, 2, 2, 2, 2, 2], ![0, 0, 1, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 1, 1, 1, 1], ![1, 1, 1, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 1, 2, 2, 2, 2, 2, 2], ![0, 0, 2, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 2, 2, 2, 2], ![1, 1, 1, 1, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 1, 1, 1, 2, 2], ![0, 0, 0, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![1, 1, 1, 2, 2, 2, 2, 2], ![0, 1, 1, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![0, 0, 0, 1, 1, 2, 2, 2], ![0, 0, 0, 0, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![1, 1, 1, 1, 2, 2, 2, 2], ![0, 1, 1, 1, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 1, 1, 2, 2], ![0, 0, 0, 0, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 1, 1, 2, 2, 2, 2, 2], ![0, 0, 1, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![0, 0, 0, 0, 1, 2, 2, 2], ![1, 2, 2, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 2, 2, 2, 2, 2, 2], ![0, 0, 0, 1, 1, 1, 1, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 1, 1, 2, 2], ![1, 2, 2, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 2, 2, 2, 2, 2], ![0, 0, 0, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![2, 2, 2, 2, 2, 2, 2, 2], ![0, 2, 2, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 1, 1, 1, 2], ![0, 0, 0, 0, 1, 1, 1, 2], by decide⟩
  · exact ⟨0, 1, ![0, 1, 1, 1, 2, 2, 2, 2], ![0, 0, 1, 1, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 2, 2, 2, 2, 2], ![0, 0, 0, 0, 1, 1, 1, 1], by decide⟩
  · exact ⟨0, 2, ![0, 1, 1, 1, 1, 2, 2, 2], ![0, 0, 1, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 1, 1, 1, 2], ![1, 1, 2, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 1, 2, 2, 2, 2], ![0, 0, 0, 1, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![1, 2, 2, 2, 2, 2, 2, 2], ![0, 2, 2, 2, 2, 2, 2, 2], by decide⟩

/-- Every noncentral charge is detected by two physical first
letters at every degree at least seven. -/
theorem exists_distinct_cyclic_phases (n : ℕ) (hn : 6 ≤ n)
    (u v : ZMod 5) (hne : (u, v) ≠ 0) :
    ∃ (i j : Fin 3) (σ τ : Cfg 3 n),
      wordCharge (i :: List.ofFn σ) = (u, v) ∧
      wordCharge (j :: List.ofFn τ) = (u, v) ∧
      letterPairing i (u, v) ≠ letterPairing j (u, v) := by
  suffices ∀ n : ℕ, 6 ≤ n →
      ∃ (i j : Fin 3) (σ τ : Cfg 3 n),
        wordCharge (i :: List.ofFn σ) = (u, v) ∧
        wordCharge (j :: List.ofFn τ) = (u, v) ∧
        letterPairing i (u, v) ≠ letterPairing j (u, v) from this n hn
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hn
      by_cases hlarge : 9 ≤ n
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
        obtain ⟨i, j, σ, τ, hi, hj, hij⟩ := ih k (by omega) (by omega)
        refine ⟨i, j, Fin.append σ ![0, 1, 2], Fin.append τ ![0, 1, 2], ?_, ?_, hij⟩
        · rw [List.ofFn_fin_append, ← List.cons_append, wordCharge_append]
          have hz : wordCharge (List.ofFn (![0, 1, 2] : Cfg 3 3)) = 0 := by decide
          rw [hz, add_zero, hi]
        · rw [List.ofFn_fin_append, ← List.cons_append, wordCharge_append]
          have hz : wordCharge (List.ofFn (![0, 1, 2] : Cfg 3 3)) = 0 := by decide
          rw [hz, add_zero, hj]
      · have hcases : n = 6 ∨ n = 7 ∨ n = 8 := by omega
        rcases hcases with rfl | rfl | rfl
        · exact exists_distinct_seven_cyclic_phases u v hne
        · exact exists_distinct_eight_cyclic_phases u v hne
        · exact exists_distinct_nine_cyclic_phases u v hne

end MPSTensor.ShortMomentum
