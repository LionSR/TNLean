/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.GroupedWindowBounds

/-!
# Open-chain coercivity from grouped martingale differences

The filtration advances by \(p\) sites and the parent interaction has range
\(2p\). The local martingale window is therefore one parent interaction.
This gives constants one in conditions C1 and C2 and an overlap width of one
in the grouped index.

## References

* Nachtergaele, arXiv:cond-mat/9410110, conditions C1-prime and C3-prime,
  lines 1095--1120, and Theorem 2.1(ii), lines 1130--1139.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- The first grouped difference vanishes: neither the empty prefix nor the
length-\(p\) prefix contains a range-\(2p\) interaction. This discharges the
first index of the full-range martingale estimate. -/
theorem grouped_martingaleDifference_zero (A : MPSTensor d D)
    {p N : ℕ} (hp : 0 < p) :
    (groupedNestedGroundProjectionsES A p N).martingaleDifference 0 = 0 := by
  simp only [FrustrationFree.NestedGroundProjections.martingaleDifference,
    groupedNestedGroundProjectionsES, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  rw [openPrefixGroundProjectionES_eq_one_of_lt A (by omega),
    openPrefixGroundProjectionES_eq_one_of_lt A (by omega), sub_self]


/-- At the first complete grouped window, the local ground projection
annihilates the grouped martingale difference by idempotence. -/
theorem groupedIntervalGroundProjectionES_comp_martingaleDifference_one
    (A : MPSTensor d D) {p N : ℕ} (hp : 0 < p) (hPN : 2 * p ≤ N) :
    (groupedIntervalGroundProjectionES A p N 1).comp
      ((groupedNestedGroundProjectionsES A p N).martingaleDifference 1) = 0 := by
  have hQ : groupedIntervalGroundProjectionES A p N 1 =
      openPrefixGroundProjectionES A (2 * p) N (2 * p) := by
    simp only [groupedIntervalGroundProjectionES, openPrefixGroundProjectionES,
      show p * (1 + 1) = 2 * p by omega,
      openPrefixParentHamiltonianES_eq_openSuffixParentHamiltonianES_at_endpoint
        A (by omega : 0 < 2 * p) hPN]
  simp only [hQ, FrustrationFree.NestedGroundProjections.martingaleDifference,
    groupedNestedGroundProjectionsES,
    show p * (1 + 1) = 2 * p by omega,
    openPrefixGroundProjectionES_eq_one_of_lt A (by omega : p < 2 * p),
    ← Module.End.mul_eq_comp, mul_one]
  rw [mul_sub, mul_one]
  exact sub_eq_zero.mpr
    ((fixedAmbientNestedGroundProjectionsES A (2 * p) N).isSymmetricProjection
      (2 * p)).isIdempotentElem.eq.symm

/-- The grouped C3 bound needs verification only from the second grouped
index onwards. The omitted products vanish identically. -/
theorem grouped_martingaleDifference_norm_le_of_two_le
    (A : MPSTensor d D) {p N M : ℕ} (hp : 0 < p) (hPN : 2 * p ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hC3 : ∀ n, 2 ≤ n → n < M →
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p N n).comp
          ((groupedNestedGroundProjectionsES A p N).martingaleDifference n))‖ ≤ ε) :
    ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p N n).comp
          ((groupedNestedGroundProjectionsES A p N).martingaleDifference n))‖ ≤ ε := by
  intro n hn
  rcases n with _ | n
  · simpa only [grouped_martingaleDifference_zero A hp, LinearMap.comp_zero,
      map_zero, norm_zero] using hε
  · rcases n with _ | n
    · simpa only [Nat.zero_add,
        groupedIntervalGroundProjectionES_comp_martingaleDifference_one A hp hPN,
        map_zero, norm_zero] using hε
    · exact hC3 _ (by omega) (Finset.mem_range.mp hn)

/-- The grouped martingale estimate for the range-\(2p\) open parent
Hamiltonian. Conditions C1 and C2 have constants one; the active grouped
window has two indices, giving the coefficient \((1-\epsilon\sqrt2)^2\).
This is the chosen-range specialization of Nachtergaele's Theorem 2.1(ii),
arXiv:cond-mat/9410110, lines 1130--1139. -/
theorem openParentHamiltonianES_norm_gap_of_grouped_c3
    (A : MPSTensor d D) {p M : ℕ} (hp : 0 < p) (hM : 2 ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) (hεlt : ε < 1 / Real.sqrt 2)
    (hC3 : ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p (p * M) n).comp
          ((groupedNestedGroundProjectionsES A p (p * M)).martingaleDifference n))‖ ≤ ε) :
    ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A (2 * p) (p * M)))ᗮ,
      (1 - ε * Real.sqrt 2) ^ 2 * ‖v‖ ≤
        ‖openParentHamiltonianES A (2 * p) (p * M) v‖ := by
  have hgap :=
    FrustrationFree.NestedGroundProjections.norm_lower_bound_of_nachtergaele_c1_c3_full_range
      (groupedNestedGroundProjectionsES A p (p * M))
      (groupedIntervalGroundProjectionES A p (p * M))
      (fun n ↦ openSuffixParentHamiltonianES A (2 * p) (2 * p) (p * M) (p * (n + 1)))
      (openParentHamiltonianES A (2 * p) (p * M)) M 1
      (show openPrefixGroundProjectionES A (2 * p) (p * M) 0 = 1 from
        openPrefixGroundProjectionES_eq_one_of_lt A (by omega))
      (γ := (1 : ℝ)) (d := (1 : ℝ)) (ε := ε)
      (by norm_num) (by norm_num) hε (by simpa using hεlt)
      (fun _ _ ↦ Submodule.isSymmetricProjection_starProjection _)
      (fun _ _ _ hout ↦ grouped_martingaleDifference_commute A hp (by nlinarith) hout)
      (fun x ↦ by simpa only [one_mul] using grouped_openParentHamiltonianES_C1 A hp x)
      (fun n hn x ↦ by simpa only [one_mul] using
        grouped_openSuffixParentHamiltonianES_C2 A hp (Finset.mem_range.mp hn) x)
      hC3 (openParentHamiltonianES_isPositive A (2 * p) (p * M))
      (by simp only [groupedNestedGroundProjectionsES, openPrefixGroundProjectionES,
        Submodule.range_starProjection,
        openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES])
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, div_one, one_mul] using hgap

end MPSTensor
