/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoMarkerMiddleFactors
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Fin

/-!
# A two-binomial bound for decorated crossing words

A crossing word with fixed left and right frequencies is specified by the
positions of its left letters and by the two families of labels. Appending
the unused degree to its ordinary run lengths gives a weak composition.
These two counts yield a product of two binomial factors for
`TwoMarkerMiddleIndex`, with no positivity assumption on the degree,
frequencies or label cardinalities.

## References

Supporting finite count for ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333.
-/

open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- Pascal's identity increases both binomial arguments.
Supporting ALVV, Proposition 5.7, lines 1324–1333. -/
private theorem choose_le_diagonal_succ (n a : ℕ) :
    n.choose a ≤ (n + 1).choose (a + 1) := by
  rw [Nat.choose_succ_succ']
  exact Nat.le_add_right _ _

/-- Separating the two marker frequencies gives a product of two binomials.
Supporting ALVV, Proposition 5.7, lines 1324–1333. -/
private theorem choose_marker_run_le_separated (k i j : ℕ) (h : i + j ≤ k) :
    (k + 1).choose (i + j + 1) * (i + j).choose i ≤
      (k + 1).choose (i + 1) * (k + 1).choose (j + 1) := by
  have hs : k + 1 - (i + 1) = k - i := by omega
  have ht : i + j + 1 - (i + 1) = j := by omega
  calc
    _ ≤ (k + 1).choose (i + j + 1) * (i + j + 1).choose (i + 1) :=
      Nat.mul_le_mul_left _ (choose_le_diagonal_succ (i + j) i)
    _ = (k + 1).choose (i + 1) * (k - i).choose j := by
      simpa only [hs, ht] using
        (Nat.choose_mul (n := k + 1) (k := i + j + 1) (s := i + 1) (by omega))
    _ ≤ (k + 1).choose (i + 1) * (k + 1).choose (j + 1) := by
      apply Nat.mul_le_mul_left
      exact (choose_le_diagonal_succ (k - i) j).trans
        (Nat.choose_le_choose (j + 1) (by omega))

/-- Each separated binomial is bounded by its source composition factor.
Supporting ALVV, Proposition 5.7, lines 1324–1333. -/
private theorem choose_le_two_gap_factor (k i : ℕ) (hi : i ≤ k) :
    (k + 1).choose (i + 1) ≤ (k + i + 1).choose (2 * i + 1) := by
  calc
    _ = (k + 1).choose (k - i) :=
      Nat.choose_symm_of_eq_add (by omega)
    _ ≤ (k + i + 1).choose (k - i) :=
      Nat.choose_le_choose (k - i) (by omega)
    _ = (k + i + 1).choose (2 * i + 1) :=
      Nat.choose_symm_of_eq_add (by omega)

/-- The direct numerical inequality behind the two-binomial outer count.
No restriction on the two label cardinalities is needed.
Supporting ALVV, Proposition 5.7, lines 1324–1333. -/
private theorem marker_run_two_binomial_bound (k i j rU rV : ℕ) :
    (i + j).choose i * rU ^ i * rV ^ j * (k + 1).choose (i + j + 1) ≤
      rU ^ i * rV ^ j * (k + i + 1).choose (2 * i + 1) *
        (k + j + 1).choose (2 * j + 1) := by
  by_cases h : i + j ≤ k
  · have hsep := choose_marker_run_le_separated k i j h
    have hgap := Nat.mul_le_mul (choose_le_two_gap_factor k i (by omega))
      (choose_le_two_gap_factor k j (by omega))
    have hmul := Nat.mul_le_mul_left (rU ^ i * rV ^ j) (hsep.trans hgap)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  · have hz : (k + 1).choose (i + j + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp only [hz, Nat.mul_zero, Nat.zero_le]

/-- A marker word is determined by its left positions and its two label families.
Only an injection is needed, so no reconstruction predicate is imposed on the
right frequency. Supporting ALVV, Proposition 5.7, lines 1324–1333. -/
private theorem card_colored_marker_words_le (i j rU rV : ℕ) :
    Fintype.card {w : Fin (i + j) → Fin rU ⊕ Fin rV //
      (Finset.univ.filter (fun h ↦ (w h).isLeft)).card = i ∧
      (Finset.univ.filter (fun h ↦ (w h).isRight)).card = j} ≤
      (i + j).choose i * rU ^ i * rV ^ j := by
  classical
  let W := {w : Fin (i + j) → Fin rU ⊕ Fin rV //
    (Finset.univ.filter (fun h ↦ (w h).isLeft)).card = i ∧
    (Finset.univ.filter (fun h ↦ (w h).isRight)).card = j}
  let S := {s : Finset (Fin (i + j)) // s.card = i}
  let Y := Σ s : S, (↥s.1 → Fin rU) × (↥(s.1ᶜ) → Fin rV)
  let encode (w : W) : Y :=
    ⟨⟨Finset.univ.filter (fun h ↦ (w.1 h).isLeft), w.2.1⟩,
      (fun x ↦ (w.1 x.1).getLeft (Finset.mem_filter.mp x.2).2),
      fun x ↦ (w.1 x.1).getRight (Sum.not_isLeft.mp (by
        simpa only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
          using x.2))⟩
  let decode (y : Y) : Fin (i + j) → Fin rU ⊕ Fin rV := fun h ↦
    if hh : h ∈ y.1.1 then Sum.inl (y.2.1 ⟨h, hh⟩)
    else Sum.inr (y.2.2 ⟨h, by simpa only [Finset.mem_compl] using hh⟩)
  have hdecode (w : W) : decode (encode w) = w.1 := by
    funext h
    dsimp only [decode, encode]
    split_ifs <;> simp only [Sum.inl_getLeft, Sum.inr_getRight]
  have hinj : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    rw [← hdecode a, ← hdecode b, hab]
  have hcard (s : S) :
      Fintype.card ((↥s.1 → Fin rU) × (↥(s.1ᶜ) → Fin rV)) = rU ^ i * rV ^ j := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, Finset.card_compl, s.2, Nat.add_sub_cancel_left]
  calc
    Fintype.card W ≤ Fintype.card Y := Fintype.card_le_of_injective encode hinj
    _ = (i + j).choose i * rU ^ i * rV ^ j := by
      change Fintype.card (Σ s : S, (↥s.1 → Fin rU) × (↥(s.1ᶜ) → Fin rV)) = _
      simp only [Fintype.card_sigma, hcard]
      simp [S, Nat.mul_assoc]

/-- Appending the unused degree as one extra coordinate injects bounded run
lengths into a weak composition. Supporting ALVV, Proposition 5.7,
lines 1324–1333. -/
private theorem card_bounded_marker_runs_le (k m : ℕ) (hm : m ≤ k) :
    Fintype.card {a : Fin (m + 1) → Fin (k + 1) //
      (∑ h, (a h).val) + m ≤ k} ≤ (k + 1).choose (m + 1) := by
  classical
  let R := {a : Fin (m + 1) → Fin (k + 1) // (∑ h, (a h).val) + m ≤ k}
  let C := ↥(Finset.piAntidiag (Finset.univ : Finset (Fin (m + 2))) (k - m))
  have hsum (a : R) : (∑ h, (a.1 h).val) ≤ k - m := by
    have ha := a.2
    omega
  let encode (a : R) : C :=
    ⟨Fin.cons (k - m - ∑ h, (a.1 h).val) (fun h ↦ (a.1 h).val), by
      apply Finset.mem_piAntidiag.mpr
      constructor
      · simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
          (Nat.sub_add_cancel (hsum a))
      · intro h _
        exact Finset.mem_univ h⟩
  have hinj : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    funext h
    apply Fin.ext
    have hv := congrArg (fun c : C ↦ c.1 h.succ) hab
    simpa only [encode, Fin.cons_succ] using hv
  calc
    Fintype.card R ≤ Fintype.card C := Fintype.card_le_of_injective encode hinj
    _ = (k + 1).choose (m + 1) := by
      change Fintype.card
        ↥(Finset.piAntidiag (Finset.univ : Finset (Fin (m + 2))) (k - m)) = _
      rw [Fintype.card_coe, ← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ,
        Finset.card_univ, Sym.card_sym_eq_choose, Fintype.card_fin]
      have ht : m + 2 + (k - m) - 1 = k + 1 := by omega
      rw [ht]
      exact Nat.choose_symm_of_eq_add (by omega)

/-- The actual index separates into its marker word and its bounded run tuple.
Their independent counts give the usual marker-and-run upper bound.
Supporting ALVV, Proposition 5.7, lines 1324–1333. -/
private theorem card_twoMarkerMiddleIndex_marker_run_le (k i j rU rV : ℕ)
    (h : i + j ≤ k) :
    Fintype.card (TwoMarkerMiddleIndex k i j rU rV) ≤
      (i + j).choose i * rU ^ i * rV ^ j * (k + 1).choose (i + j + 1) := by
  classical
  let W := {w : Fin (i + j) → Fin rU ⊕ Fin rV //
    (Finset.univ.filter (fun h ↦ (w h).isLeft)).card = i ∧
    (Finset.univ.filter (fun h ↦ (w h).isRight)).card = j}
  let R := {a : Fin (i + j + 1) → Fin (k + 1) //
    (∑ h, (a h).val) + i + j ≤ k}
  let e : TwoMarkerMiddleIndex k i j rU rV ≃ W × R :=
    { toFun := fun p ↦ ⟨⟨p.1.1, p.2.1, p.2.2.1⟩, ⟨p.1.2, p.2.2.2⟩⟩
      invFun := fun p ↦ ⟨(p.1.1, p.2.1), p.1.2.1, p.1.2.2, p.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]
  apply Nat.mul_le_mul (card_colored_marker_words_le i j rU rV)
  simpa only [R, Nat.add_assoc] using card_bounded_marker_runs_le k (i + j) h

/-- Decorated crossing words with fixed left and right frequencies satisfy the
two-binomial count for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333.
The degree, frequencies and label cardinalities may vanish; frequencies whose
sum exceeds the degree give an empty set. -/
theorem card_twoMarkerMiddleIndex_two_binomial_le (k i j rU rV : ℕ) :
    Fintype.card (TwoMarkerMiddleIndex k i j rU rV) ≤
      rU ^ i * rV ^ j * (k + i + 1).choose (2 * i + 1) *
        (k + j + 1).choose (2 * j + 1) := by
  classical
  by_cases h : i + j ≤ k
  · exact (card_twoMarkerMiddleIndex_marker_run_le k i j rU rV h).trans
      (marker_run_two_binomial_bound k i j rU rV)
  · let : IsEmpty (TwoMarkerMiddleIndex k i j rU rV) := ⟨fun p ↦ by
      have hp := p.2.2.2
      omega⟩
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _

end TNLean.MPS.AreaLaw
