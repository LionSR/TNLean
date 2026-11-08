/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.List.Count
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Degree and charge for the three-letter fifth-root Weyl example

The three letters have charges (1,0), (0,1) and (-1,-1) modulo five.
At one fixed degree, the charge determines the residue of every letter
count. Every charge is reached at degree eight. At degree seven the
central charge is absent, whereas every degree at least eight admits
central counts. These are arithmetic and finite-word ingredients only;
no Hamiltonian kernel classification or counterexample is asserted here.

Source context: the finite-prefix obligation in SPWC10, arXiv:0909.5347,
Theorem 5, main.tex lines 850--880. The candidate construction is audited in
`docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

namespace MPSTensor.ShortMomentum

/-- The two virtual Weyl charges of the physical letter counts. -/
def countCharge (a b c : ℕ) : ZMod 5 × ZMod 5 :=
  ((a : ZMod 5) - c, (b : ZMod 5) - c)

/-- The charge of a three-letter physical word. -/
def wordCharge (w : List (Fin 3)) : ZMod 5 × ZMod 5 :=
  countCharge (w.count 0) (w.count 1) (w.count 2)

/-- The sorted physical word with the three prescribed letter counts. -/
def sortedWord (a b c : ℕ) : List (Fin 3) :=
  List.replicate a 0 ++ List.replicate b 1 ++ List.replicate c 2

/-- Concatenation adds the virtual charge. -/
theorem wordCharge_append (u v : List (Fin 3)) :
    wordCharge (u ++ v) = wordCharge u + wordCharge v := by
  apply Prod.ext <;> dsimp [wordCharge, countCharge] <;>
    simp only [List.count_append, Nat.cast_add] <;> ring

/-- The three letter counts sum to the word length. -/
theorem sum_letter_counts (w : List (Fin 3)) :
    w.count 0 + w.count 1 + w.count 2 = w.length := by
  induction w with
  | nil => simp
  | cons i w ih => fin_cases i <;> simp <;> omega

/-- The sorted word has precisely the prescribed total degree. -/
@[simp] theorem length_sortedWord (a b c : ℕ) : (sortedWord a b c).length = a + b + c := by
  simp [sortedWord, Nat.add_assoc]

/-- The sorted word has the charge of its prescribed letter counts. -/
@[simp] theorem wordCharge_sortedWord (a b c : ℕ) :
    wordCharge (sortedWord a b c) = countCharge a b c := by
  simp [sortedWord, wordCharge, countCharge, List.count_append, List.count_replicate]

/-- At fixed degree the charge determines all three count residues.
The inverse of three modulo five is two. -/
theorem residues_eq_of_degree_charge {a b c a' b' c' n : ℕ}
    (hdegree : a + b + c = n) (hdegree' : a' + b' + c' = n)
    (hcharge : countCharge a b c = countCharge a' b' c') :
    (a : ZMod 5) = a' ∧ (b : ZMod 5) = b' ∧ (c : ZMod 5) = c' := by
  have hs : (a : ZMod 5) + b + c = n := by
    simpa only [Nat.cast_add] using congrArg (fun k : ℕ ↦ (k : ZMod 5)) hdegree
  have hs' : (a' : ZMod 5) + b' + c' = n := by
    simpa only [Nat.cast_add] using congrArg (fun k : ℕ ↦ (k : ZMod 5)) hdegree'
  have hfirst : (a : ZMod 5) - c = (a' : ZMod 5) - c' := congrArg Prod.fst hcharge
  have hsecond : (b : ZMod 5) - c = (b' : ZMod 5) - c' := congrArg Prod.snd hcharge
  have hthree : (3 : ZMod 5) * ((c : ZMod 5) - c') = 0 := by
    linear_combination hs - hs' - hfirst - hsecond
  have hc : (c : ZMod 5) = c' := by
    have h := congrArg (fun z : ZMod 5 ↦ 2 * z) hthree
    rw [← mul_assoc, show (2 : ZMod 5) * 3 = 1 by decide, one_mul, mul_zero] at h
    exact sub_eq_zero.mp h
  refine ⟨?_, ?_, hc⟩
  · linear_combination hfirst + hc
  · linear_combination hsecond + hc

/-- Central counts cannot have degree seven. This is the missing
identity charge at that degree, not merely a chosen zero trace. -/
theorem not_central_counts_seven {a b c : ℕ} (hdegree : a + b + c = 7)
    (hab : (a : ZMod 5) = b) (hbc : (b : ZMod 5) = c) : False := by
  have h₁ := (ZMod.natCast_eq_natCast_iff' a b 5).mp hab
  have h₂ := (ZMod.natCast_eq_natCast_iff' b c 5).mp hbc
  omega

/-- Zero charge means that the three count residues coincide. -/
theorem countCharge_eq_zero_iff (a b c : ℕ) : countCharge a b c = 0 ↔
    (a : ZMod 5) = b ∧ (b : ZMod 5) = c := by
  constructor
  · intro h
    have ha : (a : ZMod 5) = c := sub_eq_zero.mp (congrArg Prod.fst h)
    have hb : (b : ZMod 5) = c := sub_eq_zero.mp (congrArg Prod.snd h)
    exact ⟨ha.trans hb.symm, hb⟩
  · rintro ⟨hab, hbc⟩
    apply Prod.ext <;> dsimp [countCharge] <;> simp [hab, hbc]

/-- No degree-seven physical word has central Weyl charge. -/
theorem wordCharge_ne_zero_of_length_seven {w : List (Fin 3)} (hw : w.length = 7) :
    wordCharge w ≠ 0 := by
  intro h
  obtain ⟨hab, hbc⟩ := (countCharge_eq_zero_iff (w.count 0) (w.count 1) (w.count 2)).mp h
  exact not_central_counts_seven ((sum_letter_counts w).trans hw) hab hbc

/-- Every noncentral charge is reached at degree seven. The only least
residue triple whose sum exceeds seven is the missing central triple. -/
theorem exists_counts_seven_of_charge (u v : ZMod 5) (hne : (u, v) ≠ 0) :
    ∃ a b c : ℕ, a + b + c = 7 ∧ countCharge a b c = (u, v) := by
  let c : ZMod 5 := 2 * ((7 : ZMod 5) - u - v)
  let a : ZMod 5 := u + c
  let b : ZMod 5 := v + c
  have hc : (3 : ZMod 5) * c = (7 : ZMod 5) - u - v := by
    dsimp [c]
    rw [← mul_assoc, show (3 : ZMod 5) * 2 = 1 by decide, one_mul]
  have hsum : a + b + c = (7 : ZMod 5) := by
    calc a + b + c = u + v + 3 * c := by dsimp [a, b]; ring
      _ = 7 := by rw [hc]; ring
  let S := a.val + b.val + c.val
  have hScast : (S : ZMod 5) = 7 := by
    simpa only [S, Nat.cast_add, ZMod.natCast_zmod_val] using hsum
  have hSmod : S % 5 = 2 := by
    have h := congrArg ZMod.val hScast
    norm_num only [ZMod.val_natCast] at h
    exact h
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hc' := ZMod.val_lt c
  have hSle : S ≤ 7 := by
    by_contra h
    have hmax : a.val = 4 ∧ b.val = 4 ∧ c.val = 4 := by dsimp [S] at *; omega
    have hac : a = c := ZMod.val_injective 5 (hmax.1.trans hmax.2.2.symm)
    have hbc : b = c := ZMod.val_injective 5 (hmax.2.1.trans hmax.2.2.symm)
    have hu : u = 0 := by
      simpa only [a, add_sub_cancel_right, sub_self] using congrArg (fun z ↦ z - c) hac
    have hv : v = 0 := by
      simpa only [b, add_sub_cancel_right, sub_self] using congrArg (fun z ↦ z - c) hbc
    exact hne (Prod.ext hu hv)
  have hpadding : ((7 - S : ℕ) : ZMod 5) = 0 := by
    rw [Nat.cast_sub hSle, hScast, Nat.cast_ofNat, sub_self]
  refine ⟨a.val + (7 - S), b.val, c.val, ?_, ?_⟩
  · dsimp [S] at hSle ⊢
    omega
  · simp only [countCharge, Nat.cast_add, ZMod.natCast_zmod_val, hpadding, add_zero]
    dsimp [a, b]
    apply Prod.ext <;> dsimp only <;> ring

/-- Every noncentral charge is reached by a word of length seven. -/
theorem exists_word_seven_of_charge (u v : ZMod 5) (hne : (u, v) ≠ 0) :
    ∃ w : List (Fin 3), w.length = 7 ∧ wordCharge w = (u, v) := by
  obtain ⟨a, b, c, hdegree, hcharge⟩ := exists_counts_seven_of_charge u v hne
  exact ⟨sortedWord a b c, by simpa using hdegree, by simpa using hcharge⟩

/-- Every virtual Weyl charge is reached by nonnegative letter counts
of total degree eight. The least residues have sum three or eight. -/
theorem exists_counts_eight_of_charge (u v : ZMod 5) :
    ∃ a b c : ℕ, a + b + c = 8 ∧ countCharge a b c = (u, v) := by
  let c : ZMod 5 := 2 * ((8 : ZMod 5) - u - v)
  let a : ZMod 5 := u + c
  let b : ZMod 5 := v + c
  have hc : (3 : ZMod 5) * c = (8 : ZMod 5) - u - v := by
    dsimp [c]
    rw [← mul_assoc, show (3 : ZMod 5) * 2 = 1 by decide, one_mul]
  have hsum : a + b + c = (8 : ZMod 5) := by
    calc a + b + c = u + v + 3 * c := by dsimp [a, b]; ring
      _ = 8 := by rw [hc]; ring
  let S := a.val + b.val + c.val
  have hScast : (S : ZMod 5) = 8 := by
    simpa only [S, Nat.cast_add, ZMod.natCast_zmod_val] using hsum
  have hSmod : S % 5 = 3 := by
    have h := congrArg ZMod.val hScast
    norm_num only [ZMod.val_natCast] at h
    exact h
  have hSbound : S ≤ 12 := by
    have ha := ZMod.val_lt a
    have hb := ZMod.val_lt b
    have hc' := ZMod.val_lt c
    dsimp [S]
    omega
  have hSle : S ≤ 8 := by omega
  have hpadding : ((8 - S : ℕ) : ZMod 5) = 0 := by
    rw [Nat.cast_sub hSle, hScast, Nat.cast_ofNat, sub_self]
  refine ⟨a.val + (8 - S), b.val, c.val, ?_, ?_⟩
  · dsimp [S] at hSle ⊢
    omega
  · simp only [countCharge, Nat.cast_add, ZMod.natCast_zmod_val, hpadding, add_zero]
    dsimp [a, b]
    apply Prod.ext <;> dsimp only <;> ring

/-- Every virtual charge is reached by a word of length eight. -/
theorem exists_word_eight_of_charge (u v : ZMod 5) :
    ∃ w : List (Fin 3), w.length = 8 ∧ wordCharge w = (u, v) := by
  obtain ⟨a, b, c, hdegree, hcharge⟩ := exists_counts_eight_of_charge u v
  exact ⟨sortedWord a b c, by simpa using hdegree, by simpa using hcharge⟩

/-- Every charge is reached at each degree at least eight, using an
degree-eight word followed by copies of the first physical letter. -/
theorem exists_word_of_eight_le_of_charge (n : ℕ) (hn : 8 ≤ n) (u v : ZMod 5) :
    ∃ w : List (Fin 3), w.length = n ∧ wordCharge w = (u, v) := by
  obtain ⟨w, hw, hc⟩ := exists_word_eight_of_charge (u - (n - 8 : ℕ)) v
  refine ⟨w ++ List.replicate (n - 8) 0, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, hw]
    omega
  · rw [wordCharge_append, hc]
    have hrep : wordCharge (List.replicate (n - 8) 0) =
        (((n - 8 : ℕ) : ZMod 5), 0) := by
      simp [wordCharge, countCharge, List.count_replicate]
    rw [hrep]
    apply Prod.ext <;> simp

/-- Every degree at least eight is a nonnegative combination of three
and five. This proves central reachability above the exceptional
short degree without extrapolating from a numerical sample. -/
theorem exists_three_five_decomposition (n : ℕ) (hn : 8 ≤ n) :
    ∃ a b : ℕ, n = 3 * a + 5 * b := by
  suffices ∀ n : ℕ, 8 ≤ n → ∃ a b : ℕ, n = 3 * a + 5 * b from this n hn
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hn
      by_cases hlarge : 11 ≤ n
      · obtain ⟨a, b, hab⟩ := ih (n - 3) (by omega) (by omega)
        exact ⟨a + 1, b, by omega⟩
      · have hcases : n = 8 ∨ n = 9 ∨ n = 10 := by omega
        rcases hcases with rfl | rfl | rfl
        · exact ⟨1, 1, rfl⟩
        · exact ⟨3, 0, rfl⟩
        · exact ⟨0, 2, rfl⟩

/-- Every degree at least eight has central counts, while degree
seven has none. -/
theorem exists_central_counts_of_eight_le (n : ℕ) (hn : 8 ≤ n) :
    ∃ a b c : ℕ, a + b + c = n ∧ (a : ZMod 5) = b ∧ (b : ZMod 5) = c := by
  obtain ⟨t, k, htk⟩ := exists_three_five_decomposition n hn
  refine ⟨t + 5 * k, t, t, by omega, ?_, rfl⟩
  have h5 : (5 : ZMod 5) = 0 := by decide
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h5, zero_mul, add_zero]

end MPSTensor.ShortMomentum
