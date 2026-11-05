/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftTerminalEnergyEstimate
import QICLean.Analysis.SoftTerminalEnergyParameters

/-!
# Calibrated energy of the same terminal untrimmed image

The calibrated comparison and filter losses discharge all norm-dependent
energy budgets on the actual regional soft operator. Its true minimum and
native compression remain those of the explicit-budget construction.

**Scope restriction (given target and terminal certificates):** The
comparison and exact image viability must come from the same physical
family and successful complete parent. This theorem does not select a
second family or assert energy of the final trimmed space. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
Supporting ALVV, arXiv:1602.08828v2, the energy estimate at line 1807.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- The same calibrated scales and exact terminal loss give a compressed
minimum within three of the actual soft minimum and a one-sided original
parent estimate of width 49/16. The norm-dependent energy budgets are derived,
not supplied. Auxiliary to ALVV, arXiv:1602.08828v2, line 1807. -/
theorem exists_calibrated_native_soft_terminal_compressed_energy_estimate
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
      ∀ p : ℝ, eM - 10 ≤ p → p ≤ eM →
        let R := P - M + (p : ℂ) • 1 +
          cfc (Real.softTruncation t m) (M - (p : ℂ) • 1)
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
  have ht0 : 0 ≤ t := by linarith only [ht, hg]
  obtain ⟨hA0, hAM, h3t, hM⟩ := Real.soft_terminal_regional_norm_bounds
    (ell := (ell : ℝ)) ht0 (Nat.cast_nonneg ell) (by omega : 1 ≤ m)
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  obtain ⟨htauM, htauSmall, hlossSmall⟩ := Real.soft_terminal_energy_precision_bounds
    hDreal hM hA0 hAM hDelta0 hDelta
  have htau0 : 0 ≤ tau := by dsimp only [tau]; positivity
  have hgM : g ≤ Msoft := by linarith only [h3t, ht, hg]
  have hrho := Real.soft_terminal_regional_residual_le hg.le hgM htau0
    (htauM.trans (by norm_num)) htail
  obtain ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, hterminal⟩ :=
    exists_native_soft_terminal_compressed_energy_estimate (ι := ι)
      hq hlu huv hvr hrL hleft hright h hs h0 h1
  refine ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, ?_⟩
  intro p hpl hpu
  exact hterminal p t Tcut (3 * tau / 200) Delta m hpl hpu
    (by linarith only [ht, hg]) hm (by linarith only [hTcut, hg])
    (by positivity) hDelta0 hrho htauSmall hlossSmall

end TNLean.MPS.AreaLaw.ALVV
