/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftWordNodeEnergy

/-!
# A middle soft center from actual child energy estimates

The attained parent and middle minima are retained from the regional soft
construction. Actual collar minima are chosen before the child estimates.
The two child errors of width 49/16 yield a parent-sum error of width 57/8;
subtracting the collar minima and two gives a middle estimate of width ten.
This construction is independent of the family, target and terminal image.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631,
and the energy-estimation argument at line 1807.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw.ALVV

/-- The same attained parent and middle minima admit actual collar minima
whose child-dependent middle center is one-sided and has error at most ten.
The exact parent-sum width is 57/8. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631 and line 1807. -/
theorem exists_regional_middle_center_of_child_estimates {L q l u v r : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (eP eM : ℝ) (xP xM : (Fin L → Fin q) → ℂ)
    (hxP : star xP ⬝ᵥ xP = 1)
    (hPxP : aklvRegionalHamiltonians l r h 1 *ᵥ xP = (eP : ℂ) • xP)
    (hPmin : (aklvRegionalHamiltonians l r h 1 - (eP : ℂ) • 1).PosSemidef)
    (hxM : star xM ⬝ᵥ xM = 1)
    (hMxM : aklvRegionalHamiltonians u v h 1 *ᵥ xM = (eM : ℂ) • xM)
    (hMmin : (aklvRegionalHamiltonians u v h 1 - (eM : ℂ) • 1).PosSemidef) :
    ∃ (eLeft eRight : ℝ) (xLeft xRight : (Fin L → Fin q) → ℂ),
      star xLeft ⬝ᵥ xLeft = 1 ∧
      aklvRegionalHamiltonians l u h 1 *ᵥ xLeft = (eLeft : ℂ) • xLeft ∧
      (aklvRegionalHamiltonians l u h 1 - (eLeft : ℂ) • 1).PosSemidef ∧
      star xRight ⬝ᵥ xRight = 1 ∧
      aklvRegionalHamiltonians v r h 1 *ᵥ xRight = (eRight : ℂ) • xRight ∧
      (aklvRegionalHamiltonians v r h 1 - (eRight : ℂ) • 1).PosSemidef ∧
      ∀ (k : ℕ), l ≤ k → k ≤ r → ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate h l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate h k r (49 / 16) p2 →
        let center := p1 + p2 - eLeft - eRight - 2
        eM - 10 ≤ center ∧ center ≤ eM ∧
          IsRegionalLowerEnergyEstimate h u v 10 center ∧
          IsRegionalLowerEnergyEstimate h l r (57 / 8) (p1 + p2) := by
  classical
  obtain ⟨eLeft, eMiddle, eRight, eParent, xLeft, xMiddle, xRight, xParent,
    hxLeft, hLeft, hLeftMin, hxMiddle, hMiddle, hMiddleMin,
    hxRight, hRight, hRightMin, hxParent, hParent, hParentMin,
    _hThreeLower, _hThreeUpper, hcenter⟩ :=
    exists_regional_central_energy_estimate hq hlu huv hvr hrL h hs h0 h1
  have heP : eP = eParent := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians l r h 1) eP eParent xP xParent
    hPxP hxP hParent hxParent hPmin hParentMin
  have heM : eM = eMiddle := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians u v h 1) eM eMiddle xM xMiddle
    hMxM hxM hMiddle hxMiddle hMmin hMiddleMin
  refine ⟨eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
    hxRight, hRight, hRightMin, ?_⟩
  intro k hlk hkr p1 p2 hp1 hp2 center
  obtain ⟨eA, eB, eMerge, x, z, hx, hAx, hBx, hAmin, hBmin,
    hz, hMerge, hMergeMin, hMergeLower, hMergeUpper, _⟩ :=
    exists_adjacent_interval_energy_merge hq hlk hkr hrL h hs h0 h1
  have heMerge : eMerge = eParent := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians l r h 1) eMerge eParent z xParent
    hMerge hz hParent hxParent hMergeMin hParentMin
  obtain ⟨e1, y1, hy1, hAy1, hA1min, hp1l, hp1u⟩ := hp1
  obtain ⟨e2, y2, hy2, hBy2, hB2min, hp2l, hp2u⟩ := hp2
  have he1 : e1 = eA := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians l k h 1) e1 eA y1 x hAy1 hy1 hAx hx hA1min hAmin
  have he2 : e2 = eB := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians k r h 1) e2 eB y2 x hBy2 hy2 hBx hx hB2min hBmin
  have hsumLower : eParent - 57 / 8 ≤ p1 + p2 := by
    linarith only [hMergeUpper, heMerge, he1, he2, hp1l, hp2l]
  have hsumUpper : p1 + p2 ≤ eParent := by
    linarith only [hMergeLower, heMerge, he1, he2, hp1u, hp2u]
  obtain ⟨hcenterLower, hcenterUpper⟩ := hcenter (p1 + p2)
    (by linarith only [hsumLower]) hsumUpper
  rw [← heM] at hcenterLower hcenterUpper
  refine ⟨hcenterLower, hcenterUpper,
    ⟨eM, xM, hxM, hMxM, hMmin, hcenterLower, hcenterUpper⟩,
    eP, xP, hxP, hPxP, hPmin, ?_, ?_⟩
  · linarith only [hsumLower, heP]
  · linarith only [hsumUpper, heP]

end TNLean.MPS.AreaLaw.ALVV
