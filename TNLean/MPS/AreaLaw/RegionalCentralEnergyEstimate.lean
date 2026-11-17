/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalEnergyMergePhysical

/-!
# A one-sided center for the middle of a parent interval

The actual minima on the left collar, middle and right collar sum to within
at most two of the parent minimum. A one-sided parent estimate of width eight
therefore supplies a one-sided middle estimate of width ten after subtracting
the two collar minima and two. All minima and normalized attaining vectors
are constructed from the original nearest-neighbour interactions.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2,
`def:soft-trunc`, lines 1178–1185, and `eq:defjgapped`, lines 1380–1384.
**Local fix (one-sided middle center):** The source efficient-generation
input allows absolute parent error ten, whereas soft truncation requires a
one-sided estimate for the smaller middle. This theorem instead derives the
middle center from a one-sided parent estimate of width eight. See
https://sirui-lu.com/TNLean/paper-gaps/alvv16_soft_regional_energy_centering.pdf.
No efficient computation of the collar minima or generation algorithm is claimed.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Original supported positive-contraction interactions determine attained
minima on three consecutive subintervals and their parent. Their sum is at
most two below the parent minimum. Subtracting the two collar minima and two
from every lower parent estimate of error at most eight yields an actual
lower middle estimate of error at most ten. Empty intervals and endpoints
are included. Auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc`,
lines 1178–1185, and `eq:defjgapped`, lines 1380–1384. -/
theorem exists_regional_central_energy_estimate {L q l u v r : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let A := aklvRegionalHamiltonians l u h 1
    let M := aklvRegionalHamiltonians u v h 1
    let B := aklvRegionalHamiltonians v r h 1
    let P := aklvRegionalHamiltonians l r h 1
    ∃ (eA eM eB eP : ℝ) (xA xM xB xP : (Fin L → Fin q) → ℂ),
      star xA ⬝ᵥ xA = 1 ∧ A *ᵥ xA = (eA : ℂ) • xA ∧
      (A - (eA : ℂ) • 1).PosSemidef ∧
      star xM ⬝ᵥ xM = 1 ∧ M *ᵥ xM = (eM : ℂ) • xM ∧
      (M - (eM : ℂ) • 1).PosSemidef ∧
      star xB ⬝ᵥ xB = 1 ∧ B *ᵥ xB = (eB : ℂ) • xB ∧
      (B - (eB : ℂ) • 1).PosSemidef ∧
      star xP ⬝ᵥ xP = 1 ∧ P *ᵥ xP = (eP : ℂ) • xP ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
      eA + eM + eB ≤ eP ∧ eP ≤ eA + eM + eB + 2 ∧
      ∀ pP : ℝ, eP - 8 ≤ pP → pP ≤ eP →
        let pM := pP - eA - eB - 2
        eM - 10 ≤ pM ∧ pM ≤ eM := by
  intro A M B P
  obtain ⟨eA, eRest, eP, x, z, hx, hAx, hRestx, hA, hRest,
    hz, hPz, hP, hlower, hupper, _⟩ :=
    exists_adjacent_interval_energy_merge hq hlu (huv.trans hvr) hrL h hs h0 h1
  obtain ⟨eM, eB, eRest', y, w, hy, hMy, hBy, hM, hB,
    hw, hRestw, hRest', hlower', hupper', _⟩ :=
    exists_adjacent_interval_energy_merge hq huv hvr hrL h hs h0 h1
  have heRest : eRest' = eRest := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians u r h 1) eRest' eRest w x
    hRestw hw hRestx hx hRest' hRest
  refine ⟨eA, eM, eB, eP, x, y, y, z, hx, hAx, hA, hy, hMy, hM,
    hy, hBy, hB, hz, hPz, hP, ?_, ?_, ?_⟩
  · linarith only [hlower, hlower', heRest]
  · linarith only [hupper, hupper', heRest]
  · intro pP hpLower hpUpper pM
    constructor <;> dsimp only [pM] <;>
      linarith only [hlower, hlower', hupper, hupper', heRest, hpLower, hpUpper]

end TNLean.MPS.AreaLaw
