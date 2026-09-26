/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbient

/-!
# Grouped open-chain ground projections

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

/-- Prefix ground projections sampled at lengths \(pn\), as in the grouped
martingale argument of Nachtergaele, Theorem 2.1(ii). -/
noncomputable def groupedNestedGroundProjectionsES (A : MPSTensor d D)
    (p N : ℕ) :
    FrustrationFree.NestedGroundProjections (E := EuclideanSpace ℂ (Cfg d N)) where
  projection n := openPrefixGroundProjectionES A (2 * p) N (p * n)
  isSymmetricProjection n := Submodule.isSymmetricProjection_starProjection _
  antitone_range := fun _ _ h ↦ by
    simpa only [openPrefixGroundProjectionES, Submodule.range_starProjection] using
      ker_openPrefixParentHamiltonianES_antitone A (2 * p) N (Nat.mul_le_mul_left p h)

/-- The ground projection of the length-\(2p\) interval ending at
\(p(n+1)\), as in Nachtergaele's condition C3-prime. -/
noncomputable def groupedIntervalGroundProjectionES (A : MPSTensor d D)
    (p N n : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  (LinearMap.ker
    (openSuffixParentHamiltonianES A (2 * p) (2 * p) N (p * (n + 1)))).starProjection.toLinearMap

/-- Outside the two active grouped indices, the grouped martingale difference
commutes with the local ground projection. This is the locality step in
Nachtergaele's proof of Theorem 2.1(ii). -/
theorem grouped_martingaleDifference_commute (A : MPSTensor d D)
    {p N m n : ℕ} (hp : 0 < p) (hPN : 2 * p ≤ N)
    (hout : m < n - 1 ∨ n < m) :
    ((groupedNestedGroundProjectionsES A p N).martingaleDifference m).comp
        (groupedIntervalGroundProjectionES A p N n) =
      (groupedIntervalGroundProjectionES A p N n).comp
        ((groupedNestedGroundProjectionsES A p N).martingaleDifference m) := by
  have hQ : groupedIntervalGroundProjectionES A p N n =
      openIntervalGroundProjectionES A (2 * p) (2 * p - 1) N (p * (n + 1) - 1) := by
    simp only [groupedIntervalGroundProjectionES, openIntervalGroundProjectionES,
      Nat.sub_add_cancel (by omega : 1 ≤ 2 * p),
      Nat.sub_add_cancel (by nlinarith : 1 ≤ p * (n + 1))]
  simp only [hQ, FrustrationFree.NestedGroundProjections.martingaleDifference,
    groupedNestedGroundProjectionsES, LinearMap.sub_comp, LinearMap.comp_sub]
  rcases hout with hleft | hright
  · have hsep := Nat.mul_le_mul_left p (show m + 2 ≤ n by omega)
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at hsep ⊢
    rw [openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_le
        A hPN (by omega),
      openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_le
        A hPN (by omega)]
  · have hsep := Nat.mul_le_mul_left p (show n + 1 ≤ m by omega)
    simp only [Nat.mul_add, Nat.mul_one] at hsep ⊢
    rw [openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_lt
        A (by omega),
      openPrefixGroundProjectionES_commute_openIntervalGroundProjectionES_of_lt
        A (by omega)]

end MPSTensor
