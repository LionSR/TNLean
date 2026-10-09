/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Labelled charge candidates and uniform padded slots

The candidates are labels, not vertices: distinct labels at one anchor remain distinct
sampling outcomes. Row cardinality and bounded anchor multiplicity give a uniform bound
on the number of candidates. Sorting those labels and appending empty slots gives exactly
one slot for each candidate. The uniform distribution on a side and a slot then has the
claimed atom weight, with an explicit positive constant after ceiling normalization.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, section file
  `08-scanner.tex`, lines 125–137 and 331–337, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {V I : Type*}

/-- Labels whose anchors lie in the closed oriented-depth interval
(`08-scanner.tex`, lines 127–129). -/
noncomputable def chargeCandidates [Fintype I] (depth : V → ℤ) (anchor : I → V)
    (lo hi : ℤ) : Finset I :=
  Finset.univ.filter fun i ↦ lo ≤ depth (anchor i) ∧ depth (anchor i) ≤ hi

@[simp]
theorem mem_chargeCandidates [Fintype I] (depth : V → ℤ) (anchor : I → V)
    (lo hi : ℤ) (i : I) :
    i ∈ chargeCandidates depth anchor lo hi ↔
      lo ≤ depth (anchor i) ∧ depth (anchor i) ≤ hi := by
  classical
  simp [chargeCandidates]

/-- An interval contains at most its number of rows times the row bound times the
label multiplicity. In particular repeated anchors are counted with their labels
(`08-scanner.tex`, lines 127–130). -/
theorem card_chargeCandidates_le [Fintype V] [Fintype I] [DecidableEq V]
    (depth : V → ℤ) (anchor : I → V) (lo hi : ℤ) (n μ : ℕ)
    (hrow : ∀ d ∈ Finset.Icc lo hi, (Finset.univ.filter fun v ↦ depth v = d).card ≤ n)
    (hmult : ∀ v, (Finset.univ.filter fun i ↦ anchor i = v).card ≤ μ) :
    (chargeCandidates depth anchor lo hi).card ≤ (hi - lo + 1).toNat * n * μ := by
  classical
  let vertices := Finset.univ.filter fun v ↦ lo ≤ depth v ∧ depth v ≤ hi
  have hv : vertices.card ≤ (hi - lo + 1).toNat * n := by
    have hm : (vertices : Set V).MapsTo depth (Finset.Icc lo hi) := by
      intro v hv
      simpa [vertices] using hv
    rw [Finset.card_eq_sum_card_fiberwise hm]
    calc
      ∑ d ∈ Finset.Icc lo hi, (vertices.filter fun v ↦ depth v = d).card
          ≤ ∑ d ∈ Finset.Icc lo hi, n := by
        apply Finset.sum_le_sum
        intro d hd
        exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans
          (hrow d hd)
      _ = (hi - lo + 1).toNat * n := by
        simp [Int.card_Icc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hm : ((chargeCandidates depth anchor lo hi : Finset I) : Set I).MapsTo anchor vertices := by
    intro i hlabel
    simpa [vertices] using (mem_chargeCandidates depth anchor lo hi i).mp hlabel
  rw [Finset.card_eq_sum_card_fiberwise hm]
  calc
    ∑ v ∈ vertices, ((chargeCandidates depth anchor lo hi).filter fun i ↦ anchor i = v).card
        ≤ ∑ v ∈ vertices, μ := by
      apply Finset.sum_le_sum
      intro v _
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans
        (hmult v)
    _ = vertices.card * μ := by simp
    _ ≤ (hi - lo + 1).toNat * n * μ := Nat.mul_le_mul_right μ hv

/-- The fixed number of padded slots at scale `n` and lookahead `D`
(`08-scanner.tex`, lines 129–130). -/
noncomputable def chargeSlotCount (C₁ : ℝ) (n D : ℕ) : ℕ := ⌈C₁ * n * D⌉₊

/-- The interval `[j-r₀,j+D]` fits into the prescribed ceiling when `r₀ ≤ D`,
`D ≥ 1`, and `C₁ ≥ 3μ` (`08-scanner.tex`, lines 127–130). -/
theorem card_chargeCandidates_le_chargeSlotCount [Fintype V] [Fintype I] [DecidableEq V]
    (depth : V → ℤ) (anchor : I → V)
    (j : ℤ) (r₀ n D μ : ℕ) (C₁ : ℝ) (hr : r₀ ≤ D) (hD : 1 ≤ D)
    (hC : 3 * (μ : ℝ) ≤ C₁)
    (hrow : ∀ d ∈ Finset.Icc (j - r₀) (j + D),
      (Finset.univ.filter fun v ↦ depth v = d).card ≤ n)
    (hmult : ∀ v, (Finset.univ.filter fun i ↦ anchor i = v).card ≤ μ) :
    (chargeCandidates depth anchor (j - r₀) (j + D)).card ≤ chargeSlotCount C₁ n D := by
  have hlen : (j + D - (j - r₀) + 1).toNat ≤ 3 * D := by omega
  have hc := card_chargeCandidates_le depth anchor (j - r₀) (j + D) n μ hrow hmult
  have hnat : (chargeCandidates depth anchor (j - r₀) (j + D)).card ≤ 3 * D * n * μ :=
    hc.trans (Nat.mul_le_mul_right μ (Nat.mul_le_mul_right n hlen))
  have hreal : ((chargeCandidates depth anchor (j - r₀) (j + D)).card : ℝ) ≤
      C₁ * n * D := by
    calc
      _ ≤ (3 : ℝ) * D * n * μ := by exact_mod_cast hnat
      _ = (3 * μ) * n * D := by ring
      _ ≤ C₁ * n * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg n))
          (Nat.cast_nonneg D)
  exact_mod_cast hreal.trans (Nat.le_ceil (C₁ * n * D))

/-- The ordered candidate list, with label multiplicity at an anchor preserved
(`08-scanner.tex`, lines 127–129). -/
noncomputable def orderedChargeCandidates [Fintype I] [LinearOrder I] (depth : V → ℤ)
    (anchor : I → V) (lo hi : ℤ) : List I :=
  (chargeCandidates depth anchor lo hi).sort

/-- Read an ordered list padded on the right by empty slots
(`08-scanner.tex`, lines 129–130). -/
def paddedChargeSlot (candidates : List I) (M : ℕ) (k : Fin M) : Option I :=
  candidates[k.val]?

/-- An occupied slot contains an entry of the original list. -/
theorem mem_of_paddedChargeSlot_eq_some {candidates : List I} {M : ℕ} {k : Fin M} {i : I}
    (h : paddedChargeSlot candidates M k = some i) : i ∈ candidates :=
  List.mem_iff_getElem?.mpr ⟨k.val, h⟩

/-- Exactly the slots beyond the candidate list are empty. -/
@[simp]
theorem paddedChargeSlot_eq_none_iff (candidates : List I) (M : ℕ) (k : Fin M) :
    paddedChargeSlot candidates M k = none ↔ candidates.length ≤ k.val := by
  simp [paddedChargeSlot]

/-- Every candidate label has exactly one slot; equal anchors do not identify labels
(`08-scanner.tex`, lines 127–130). -/
theorem existsUnique_paddedChargeSlot {candidates : List I} (hnodup : candidates.Nodup)
    {M : ℕ} (hM : candidates.length ≤ M) {i : I} (hi : i ∈ candidates) :
    ∃! k : Fin M, paddedChargeSlot candidates M k = some i := by
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hi
  refine ⟨⟨k, hk.trans_le hM⟩, ?_, ?_⟩
  · exact List.getElem?_eq_some_iff.mpr ⟨hk, hki⟩
  · intro l hl
    obtain ⟨hl', hli⟩ := List.getElem?_eq_some_iff.mp hl
    apply Fin.ext
    exact hnodup.getElem_inj_iff.mp (hli.trans hki.symm)

/-- Sorting the depth-selected labels and padding to any valid capacity assigns each
selected label a unique slot (`08-scanner.tex`, lines 127–130). -/
theorem existsUnique_orderedChargeSlot [Fintype I] [LinearOrder I]
    (depth : V → ℤ) (anchor : I → V) (lo hi : ℤ) {M : ℕ}
    (hM : (chargeCandidates depth anchor lo hi).card ≤ M)
    {i : I} (hlabel : lo ≤ depth (anchor i) ∧ depth (anchor i) ≤ hi) :
    ∃! k : Fin M, paddedChargeSlot (orderedChargeCandidates depth anchor lo hi) M k = some i := by
  apply existsUnique_paddedChargeSlot
  · exact Finset.sort_nodup _ _
  · simpa [orderedChargeCandidates] using hM
  · simpa [orderedChargeCandidates] using hlabel

/-- Positive scales and a positive uniform constant give a nonempty slot set
(`08-scanner.tex`, lines 129–130). -/
theorem chargeSlotCount_pos {C₁ : ℝ} (hC : 0 < C₁) {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D) :
    0 < chargeSlotCount C₁ n D := by
  apply Nat.one_le_ceil_iff.mpr
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD' : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  positivity

/-- The ceiling costs at most an additional unit in the uniform constant
(`08-scanner.tex`, lines 335–336). -/
theorem chargeSlotCount_le {C₁ : ℝ} (hC : 0 ≤ C₁) {n D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) :
    (chargeSlotCount C₁ n D : ℝ) ≤ (C₁ + 1) * n * D := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ C₁ * n * D by positivity)).le
  dsimp [chargeSlotCount]
  nlinarith

/-- An explicit positive sampling constant and the normalized lower bound for the actual
uniform side-and-slot law (`08-scanner.tex`, lines 335–336). -/
theorem chargeSlotWeight_lower_bound {C₁ : ℝ} (hC : 0 < C₁) {n D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) :
    0 < 1 / (2 * (C₁ + 1)) ∧
      (1 / (2 * (C₁ + 1))) / ((n : ℝ) * D) ≤
        1 / (2 * (chargeSlotCount C₁ n D : ℝ)) := by
  have hM : (0 : ℝ) < chargeSlotCount C₁ n D := by
    exact_mod_cast chargeSlotCount_pos hC hn hD
  have hbound := chargeSlotCount_le hC.le hn hD
  constructor
  · positivity
  · rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

end TNLean.PEPS.AreaLaw.Scan
