/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.PEPS.AreaLaw.InitialBuffer

/-!
# Intervals of a one-row domain and the interactions they split

On a one-row domain the dilations of a one-row rectangle are the interval regions, the
whole domain is a safe cut, and an interaction split by an interval has a site within
graph distance `R` of one of the two cut edges. Hence the number of split interactions is
bounded by a constant `N_R`, independent of the interval, and so is the logarithmic cut
budget of the marginal tail bound. These are the one-dimensional replacements for the
boundary-proportional budgets of the two-dimensional buffer lemma.

## Main results

* `rectRegion_rowRect_dilate`: dilated one-row rectangles cut out intervals.
* `isSafe_univ`: the whole domain is a safe cut for every rectangle.
* `card_crossingTerms_interval_le`: at most `N_R = 2 (R + 1) μ_R` supports are split by an
  interval.
* `cutLogBudget_interval_le`: the cut budget of an interval is at most `B_R`.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), Section 2, `eq:count` and `eq:BR`; the
  constant `N_R` here counts through the sites near the cut edges, as in the
  two-dimensional crossing count (`02-initial.tex`, lines 276–293), instead of through the
  subsets of a window.
-/

open TNLean.PEPS.AreaLaw

namespace TNLean.MPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ}

/-- The one-row rectangle `[l, r] × {0}`. -/
def rowRect (l r : ℤ) (h : l ≤ r) : IntRect := ⟨l, r, 0, 0, h, le_rfl⟩

/-- On a one-row domain, the dilation by `d` of the one-row rectangle `[l, r] × {0}` cuts
out the interval `[l - d, r + d]`. -/
theorem rectRegion_rowRect_dilate (hΛ : IsOneRow Λ) {l r : ℤ} (h : l ≤ r) (d : ℕ) :
    rectRegion (Finset.univ : Finset (Site Λ)) ((rowRect l r h).dilate d) =
      interval Λ (l - d) (r + d) := by
  ext v
  rw [mem_rectRegion, IntRect.mem_dilate, mem_interval]
  have := hΛ v.1 v.2
  simp only [rowRect, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, by omega, by omega⟩

/-- The whole domain has no boundary edge. -/
theorem edgeBoundary_univ : edgeBoundary Λ Finset.univ = ∅ := by
  ext e
  simp [edgeBoundary]

/-- The whole domain is a safe cut for every rectangle and every safety parameter. -/
theorem isSafe_univ (D₀ : ℕ) (Q : IntRect) : IsSafe Λ Finset.univ D₀ Q := by
  intro e he
  rw [edgeBoundary_univ] at he
  exact absurd he (Finset.notMem_empty e)

/-- A support of graph diameter at most `R` split by the interval `[a, b]` has a site
within distance `R` of one of the two ends: in `[a, a + R]` or in `[b - R, b]`. -/
theorem exists_mem_ends_of_splits_interval {a b : ℤ} {S : Finset (Site Λ)}
    (hS : IsAdmissibleSupport Λ R S)
    (hsplit : (∃ v ∈ S, v ∈ interval Λ a b) ∧ ∃ v ∈ S, v ∉ interval Λ a b) :
    ∃ v ∈ S, v ∈ interval Λ a (a + R) ∪ interval Λ (b - R) b := by
  obtain ⟨⟨v, hvS, hv⟩, ⟨w, hwS, hw⟩⟩ := hsplit
  obtain ⟨p, hp⟩ := hS.2 v hvS w hwS
  have hd := supDist_le_of_walk p hp
  simp only [supDist] at hd
  rw [mem_interval] at hv hw
  refine ⟨v, hvS, ?_⟩
  rw [Finset.mem_union, mem_interval, mem_interval]
  omega

/-- The number of admissible supports split by an interval: `N_R = 2 (R + 1) μ_R`, with
`μ_R = 2^{v_R - 1}` the number of admissible supports containing a given site. -/
def chainCrossConst (R : ℕ) : ℕ := 2 * (R + 1) * 2 ^ ((1 + 2 * R * (R + 1)) - 1)

/-- **Split supports of an interval.** On a one-row domain at most `N_R` admissible supports
of range `R` are split by any interval. -/
theorem card_crossingTerms_interval_le (hΛ : IsOneRow Λ) (a b : ℤ) :
    (Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) (interval Λ a b)).card ≤
      chainCrossConst R := by
  classical
  set ends : Finset (Site Λ) := interval Λ a (a + R) ∪ interval Λ (b - R) b
  have hcover : Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) (interval Λ a b) ⊆
      ends.biUnion fun v ↦ Finset.univ.filter fun X : AdmissibleSupport Λ R ↦ v ∈ X.1 := by
    intro X hX
    simp only [Entropy.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨v, hvS, hv⟩ := exists_mem_ends_of_splits_interval X.2 hX
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, hvS⟩
  have hends : ends.card ≤ 2 * (R + 1) := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := card_interval_le hΛ a (a + R)
    have h2 := card_interval_le hΛ (b - R) b
    have e1 : (a + R + 1 - a).toNat = R + 1 := by omega
    have e2 : (b + 1 - (b - R)).toNat = R + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    omega
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ ends.card * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
        Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦ card_admissibleSupport_containing_le v
    _ ≤ 2 * (R + 1) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) := Nat.mul_le_mul_right _ hends

/-- The logarithmic cut budget of an interval: `B_R = 1 + N_R log² (e q^{v_R})`. -/
noncomputable def chainBudgetConst (q R : ℕ) : ℝ :=
  1 + chainCrossConst R * Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2

/-- The cut budget constant is at least one. -/
theorem one_le_chainBudgetConst (q R : ℕ) : 1 ≤ chainBudgetConst q R := by
  unfold chainBudgetConst
  have := mul_nonneg (Nat.cast_nonneg (chainCrossConst R))
    (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1)))))
  linarith

/-- **The cut budget of an interval is bounded by a constant.** On a one-row domain the
parameter `ℬ` of the marginal tail bound at an interval cut is at most `B_R`. -/
theorem cutLogBudget_interval_le (hΛ : IsOneRow Λ) (hq : 1 ≤ q) (a b : ℤ) :
    cutLogBudget Λ q R (interval Λ a b) ≤ chainBudgetConst q R := by
  refine (cutLogBudget_le_card hq _).trans ?_
  unfold chainBudgetConst
  have hcard : ((Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1)
      (interval Λ a b)).card : ℝ) ≤ chainCrossConst R := by
    exact_mod_cast card_crossingTerms_interval_le hΛ a b
  have := mul_le_mul_of_nonneg_right hcard
    (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1)))))
  linarith

/-- The Hilbert-space dimension of an admissible support is at most `q^{v_R}`, as a real
number. -/
theorem supportDim_le_real (hq : 1 ≤ q) (X : AdmissibleSupport Λ R) :
    (Entropy.supportDim (fun _ : Site Λ ↦ q) X.1 : ℝ) ≤ (q : ℝ) ^ (1 + 2 * R * (R + 1)) := by
  exact_mod_cast supportDim_le hq X

end TNLean.MPS.AreaLaw
