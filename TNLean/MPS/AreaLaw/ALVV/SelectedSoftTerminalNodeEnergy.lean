/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftTerminalNodeEnergy
import QICLean.Analysis.GroundSpectrumMinimum
import QICLean.Entropy.RegionalViability

/-!
# Energy estimation on a selected interval family

The family is fixed before the child estimates and the terminal matrix.
Its selected middle minimum is identified with the middle minimum used in
the regional soft-energy construction. The actual terminal image is kept
unchanged. Its compression is taken with the soft regional Hamiltonian,
not the original regional Hamiltonian or the global approximating operator.

**Scope restriction (selected target and terminal image certificates):**
The selected target's dimension and directed comparison with the original
ground space, together with the literal terminal image's viability, are
inputs to this auxiliary. They are supplied by the selected physical family
and its original-target history. No trial vector or successful compressed
energy is assumed. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631,
and the energy-estimation argument at line 1807.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- A fixed family and an attained middle minimum admit the actual child
energy update on the same terminal image. The spectral lower value is
identified with the original least energy, and the regional tensor
coordinates are the canonical interval coordinates. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631 and line 1807. -/
theorem exists_selected_soft_terminal_node_energy_update
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
    (Delta : ℝ) (hDelta0 : 0 ≤ Delta) (mu eSelected : ℝ)
    (xSelected : (Fin L → Fin q) → ℂ)
    (A : ι → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q)) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let J := interval L l r
    let coords := Entropy.regionTensorCoordinates q J
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
    mu ∈ spectrum ℝ H →
    (∀ z ∈ spectrum ℝ H, mu ≤ z) →
    star xSelected ⬝ᵥ xSelected = 1 →
    M *ᵥ xSelected = (eSelected : ℂ) • xSelected →
    (M - (eSelected : ℂ) • 1).PosSemidef →
    Delta ≤ 1 / ((D : ℝ) ^ 12 * Msoft ^ 10) →
    3 * (32 * Real.exp (-(Tcut - 156 - 2 * g) / 8) +
      (t / (m : ℝ)) * (Tcut / t) ^ m) ≤ tau * g / 1000000 →
    ∃ (eP : ℝ) (xP : (Fin L → Fin q) → ℂ),
      star xP ⬝ᵥ xP = 1 ∧ P *ᵥ xP = (eP : ℂ) • xP ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
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
          eSelected - 10 ≤ center ∧ center ≤ eSelected ∧
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
  intro config H hH G J coords P M sigma0 y0 native budget Msoft tau rho loss
    hmu hlow hxSelected hMSelected hSelectedMin hDelta htail
  have hmin := hH.minEigenvalue_eq_of_mem_spectrum_of_le mu hmu hlow
  obtain ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin,
    eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
    hxRight, hRight, hRightMin, hchildren⟩ :=
    exists_calibrated_soft_terminal_node_energy_update (ι := ι)
      hq hlu huv hvr hrL hleft hright h hs h0 h1 g hg t Tcut m D hm hD ht hTcut
      Delta hDelta0 hDelta htail
  have heM : eM = eSelected := groundEnergy_eq_of_normalized_eigenvectors M
    eM eSelected xM xSelected hMxM hxM hMSelected hxSelected hMmin hSelectedMin
  refine ⟨eP, xP, hxP, hPxP, hPmin,
    eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
    hxRight, hRight, hRightMin, ?_⟩
  intro k hlk hkr p1 p2 hp1 hp2 center
  obtain ⟨hMiddle, hcenterLower, hcenterUpper, hRnat, eSoft, w, hLift,
    hw, hRw, hRmin, hRnorm, heSoft, hResidual, hterminal⟩ :=
    hchildren k hlk hkr p1 p2 hp1 hp2
  refine ⟨hMiddle, heM ▸ hcenterLower, heM ▸ hcenterUpper,
    hRnat, eSoft, w, hLift, hw, hRw, hRmin, hRnorm, heSoft, hResidual, ?_⟩
  intro T hdim hclose d e Q Y hY
  have hdimMin : Module.finrank ℂ T = Module.finrank ℂ
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)) := by
    rw [hmin]
    exact hdim
  have hcloseMin : Submodule.IsCloseTo (3 * tau / 200)
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)) T := by
    rw [hmin]
    exact hclose
  apply hterminal T hdimMin hcloseMin e A Q
  simpa only [coords, Entropy.regionTensorCoordinates_eq_exteriorFirst,
    Submodule.euclideanTensorEquiv, J, loss, Y] using hY

end TNLean.MPS.AreaLaw.ALVV
