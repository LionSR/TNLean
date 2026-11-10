/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftTerminalEnergyCalibration
import TNLean.MPS.AreaLaw.ALVV.RegionalChildEnergyCenter

/-!
# A terminal soft-energy update from actual child estimates

The original parent, middle and collar minima precede all child estimates.
The child-dependent middle center is derived from these actual minima. The
update is the last eigenvalue of the same untrimmed terminal image's native
soft compression, minus three; it again has one-sided width 49/16.

**Scope restriction (same target and untrimmed image certificates):** The
target comparison and exact terminal image viability remain legitimate inputs
for the later physical-family and actual Raw-history event application.
Final retained-space viability alone is not substituted for that history.
There is no energy statement on the final trimmed space and no runtime claim.
See `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631,
and the energy-estimation argument at line 1807.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- Actual one-sided child estimates determine an admissible middle center
and a terminal compressed-energy update of width 49/16. All attained minima
are chosen first; no center, trial vector or successful compressed energy
is supplied. Auxiliary to ALVV, arXiv:1602.08828v2, line 1631 and line 1807. -/
theorem exists_calibrated_soft_terminal_node_energy_update
    {L q l u v r ell : ℕ} {ι : Type*} [Fintype ι]
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (g : ℝ) (hg : 0 < g) (t Tcut : ℝ) (m D : ℕ)
    (hm : 2 ≤ m) (hD : 2 ≤ D)
    (ht : 156 + 2 * g ≤ t) (hTcut : 156 + 2 * g ≤ Tcut)
    (Delta : ℝ) (hDelta0 : 0 ≤ Delta) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let J := interval L l r
    let beta := fun _ : Fin L ↦ Fin q
    let split := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split
    let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
      (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
    let coords := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
      (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
    let P := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r), h i
    let M := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ u ≤ i.val ∧ i.val + 1 < v), h i
    let sigma0 : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
    let y0 := ((Entropy.cutEquiv (fun _ : Fin L ↦ q) J) sigma0).2
    let native := fun x : J → Fin q ↦
      (Entropy.cutEquiv (fun _ : Fin L ↦ q) J).symm (x, y0)
    let budget := t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 14
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let tau := 1 / ((D : ℝ) ^ 24 * Msoft ^ 10)
    let rho := 32 * Real.exp (-(Tcut - 48) / 8) + (t / (m : ℝ)) * (Tcut / t) ^ m
    let loss := Delta / (91 / 100 : ℝ) ^ 2
    Delta ≤ 1 / ((D : ℝ) ^ 12 * Msoft ^ 10) →
    3 * (32 * Real.exp (-(Tcut - 156 - 2 * g) / 8) +
      (t / (m : ℝ)) * (Tcut / t) ^ m) ≤ tau * g / 1000000 →
    ∃ (eP eM : ℝ) (xP xM : (Fin L → Fin q) → ℂ),
      star xP ⬝ᵥ xP = 1 ∧ P *ᵥ xP = (eP : ℂ) • xP ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
      star xM ⬝ᵥ xM = 1 ∧ M *ᵥ xM = (eM : ℂ) • xM ∧
      (M - (eM : ℂ) • 1).PosSemidef ∧
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
          IsRegionalLowerEnergyEstimate h u v 10 center ∧
          eM - 10 ≤ center ∧ center ≤ eM ∧
          let R := P - M + (center : ℂ) • 1 +
            cfc (Real.softTruncation t m) (M - (center : ℂ) • 1)
          let Rnat := R.submatrix native native
          Rnat.IsHermitian ∧ ∃ (eSoft : ℝ) (w : (Fin L → Fin q) → ℂ),
            R = Entropy.localLift (n := fun _ : Fin L ↦ q) J Rnat ∧
            star w ⬝ᵥ w = 1 ∧ R *ᵥ w = (eSoft : ℂ) • w ∧
            (Rnat - (eSoft : ℂ) • 1).PosSemidef ∧
            ‖R - (eSoft : ℂ) • 1‖ ≤ budget ∧
            eSoft ≤ eP ∧ eP - eSoft ≤ rho ∧
            ∀ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))),
              Module.finrank ℂ T = Module.finrank ℂ G → Submodule.IsCloseTo (3 * tau / 200) G T →
              ∀ {d : ℕ} (e : Fin d ≃ (J → Fin q))
                (A : ι → EuclideanSpace ℂ (J → Fin q) →L[ℂ]
                  EuclideanSpace ℂ (J → Fin q))
                (Q : Matrix (Fin d) (Fin d) ℂ),
                let Y := (toEuclideanLin (Matrix.familySupportProj
                  (fun i ↦ Entropy.nativeFamilyMatrix e A i * Q))).range
                Submodule.IsViable loss Y (T.map coords.toLinearEquiv.toLinearMap) →
                ∃ (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ Y)
                  (energy : Fin (n + 1) → ℝ),
                  Module.finrank ℂ Y = n + 1 ∧
                  (∀ j, Y.orthogonalCompression
                    (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Rnat).toLinearMap
                      (b j) = (energy j : ℂ) • b j) ∧
                  Antitone energy ∧ eSoft ≤ energy (Fin.last n) ∧
                  energy (Fin.last n) ≤ eSoft + 3 ∧
                  eP - 3 - rho ≤ energy (Fin.last n) - 3 ∧
                  eP - 49 / 16 ≤ energy (Fin.last n) - 3 ∧
                  energy (Fin.last n) - 3 ≤ eP := by
  classical
  intro config H hH G J beta split U Phi coords P M sigma0 y0 native
    budget Msoft tau rho loss hDelta htail
  obtain ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, hterminal⟩ :=
    exists_calibrated_native_soft_terminal_compressed_energy_estimate (ι := ι)
      hq hlu huv hvr hrL hleft hright h hs h0 h1 g hg t Tcut m D hm hD ht hTcut
      Delta hDelta0 hDelta htail
  obtain ⟨eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
    hxRight, hRight, hRightMin, hcenter⟩ :=
    exists_regional_middle_center_of_child_estimates hq hlu huv hvr hrL h hs h0 h1
      eP eM xP xM hxP hPxP hPmin hxM hMxM hMmin
  refine ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin,
    eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
    hxRight, hRight, hRightMin, ?_⟩
  intro k hlk hkr p1 p2 hp1 hp2 center
  obtain ⟨hcenterLower, hcenterUpper, hMiddle, _hParentSum⟩ :=
    hcenter k hlk hkr p1 p2 hp1 hp2
  exact ⟨hMiddle, hcenterLower, hcenterUpper, hterminal center hcenterLower hcenterUpper⟩

end TNLean.MPS.AreaLaw.ALVV
