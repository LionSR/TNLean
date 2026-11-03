/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftParentEnergy
import QICLean.Analysis.CanonicalHalfSamplingParent
import QICLean.Analysis.RegionalEnergyCalibration
import QICLean.Analysis.ViableProjectionNonzero
import QICLean.Analysis.CompressionEnergyInterval
import QICLean.Analysis.QuadraticScalarShift
import QICLean.Entropy.RegionalOperatorCoordinates

/-!
# Soft energy of the actual terminal untrimmed image

The native matrix compressed here is the uncentered regional soft replacement.
The norm and original-ground energy estimates concern its positive shift by its
actual minimum. The candidate is the full family image of the actual terminal
matrix; no projection assumption on that matrix is needed.

**Scope restriction (explicit numerical energy budgets):** This auxiliary
retains the target comparison and the exact terminal loss as hypotheses.
The physical improving-family calibration and the complete parent's successful
event must supply these certificates. It neither estimates energy on the final
trimmed space nor replaces the centered soft operator by the original regional
Hamiltonian. See `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631,
and the energy-estimation argument at lines 1793–1807.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- Original interactions construct the actual soft minimum and native matrix
before every terminal candidate. The least eigenvalue of the compression to
the same untrimmed family image lies within three of this soft minimum.
The residual then gives a one-sided original-parent estimate. No trial vector,
regional energy estimate or successful compressed energy is assumed.
Auxiliary to ALVV, arXiv:1602.08828v2, line 1631 and lines 1793–1807. -/
theorem exists_native_soft_terminal_compressed_energy_estimate
    {L q l u v r ell : ℕ} {ι : Type*} [Fintype ι]
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
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
    ∃ (eP eM : ℝ) (xP xM : (Fin L → Fin q) → ℂ),
      star xP ⬝ᵥ xP = 1 ∧ P *ᵥ xP = (eP : ℂ) • xP ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
      star xM ⬝ᵥ xM = 1 ∧ M *ᵥ xM = (eM : ℂ) • xM ∧
      (M - (eM : ℂ) • 1).PosSemidef ∧
      ∀ (p t Tcut tau Delta : ℝ) (m : ℕ), eM - 10 ≤ p → p ≤ eM →
        48 ≤ t → 2 ≤ m → 48 ≤ Tcut →
        let budget := t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 14
        let rho := 32 * Real.exp (-(Tcut - 48) / 8) + (t / (m : ℝ)) * (Tcut / t) ^ m
        let loss := Delta / (91 / 100 : ℝ) ^ 2
        0 ≤ tau → 0 ≤ Delta → rho ≤ 1 / 16 →
        tau ≤ 1 / (1024 * (budget + 1)) → loss ≤ 1 / (100 * (budget + 1)) →
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
            Module.finrank ℂ T = Module.finrank ℂ G → Submodule.IsCloseTo tau G T →
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
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, hsoft⟩ :=
    exists_native_soft_parent_energy_bound hq hlu huv hvr hrL hleft hright h hs h0 h1
  refine ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, ?_⟩
  intro p t Tcut tau Delta m hpl hpu ht hm hTcut budget rho loss
    htau0 hDelta hrho htau hloss R Rnat
  have hPpos : P.PosSemidef := (Finset.sum_nonneg fun i _ ↦ h0 i).posSemidef
  have hMpos : M.PosSemidef := (Finset.sum_nonneg fun i _ ↦ h0 i).posSemidef
  have hscalar : IsSelfAdjoint ((p : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) :=
    IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (by simp [IsSelfAdjoint])
  have hRself : IsSelfAdjoint R :=
    (((hPpos.isHermitian.isSelfAdjoint.sub hMpos.isHermitian.isSelfAdjoint).add hscalar).add
      IsSelfAdjoint.cfc)
  have hRnat : Rnat.IsHermitian := hRself.isHermitian.submatrix native
  obtain ⟨eSoft, K, w, hK, _hKnorm, hR, hw, hRw, hC, hCnorm, hresidual⟩ :=
    hsoft p t m hpl hpu (by linarith only [ht]) hm
  obtain ⟨hSoftLE, hShift, hGenergy⟩ := hresidual Tcut ht hTcut
  have hCeq : R - (eSoft : ℂ) • 1 =
      Entropy.localLift (n := fun _ : Fin L ↦ q) J K := sub_eq_iff_eq_add.mpr hR
  have hGenergyC : ∀ g ∈ G,
      RCLike.re (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (R - (eSoft : ℂ) • 1) g) g) ≤ (2 + rho) * ‖g‖ ^ 2 := by
    intro g hg
    rw [hCeq]
    exact hGenergy g hg
  have hRnative : R = Entropy.localLift (n := fun _ : Fin L ↦ q) J
      (K + (eSoft : ℂ) • 1) := by
    rw [Entropy.localLift_add, Entropy.localLift_smul, Entropy.localLift_one]
    exact hR
  have hNative : Rnat = K + (eSoft : ℂ) • 1 := by
    ext x y
    change Entropy.cutOperator J R (x, y0) (y, y0) = _
    rw [hRnative, Entropy.cutOperator_localLift]
    simp
  have hRawLift : R = Entropy.localLift (n := fun _ : Fin L ↦ q) J Rnat := by
    rw [hNative]
    exact hRnative
  have hRawLower : (Rnat - (eSoft : ℂ) • 1).PosSemidef := by
    rw [hNative, add_sub_cancel_right]
    exact hK
  refine ⟨hRnat, eSoft, w, hRawLift, hw, hRw, hRawLower, hCnorm, hSoftLE, hShift, ?_⟩
  intro T hdimT hGT d e A Q Y hY
  have htpos : 0 < t := by linarith only [ht]
  have hTpos : 0 < Tcut := by linarith only [hTcut]
  have hrho0 : 0 ≤ rho := by dsimp only [rho]; positivity
  have hloss0 : 0 ≤ loss := div_nonneg hDelta (sq_nonneg _)
  let U := (Y.tensorProd
    (⊤ : Submodule ℂ (EuclideanSpace ℂ (↥(Jᶜ) → Fin q)))).comap
      coords.toLinearEquiv.toLinearMap
  have hmapU : U.map coords.toLinearEquiv.toLinearMap = Y.tensorProd
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (↥(Jᶜ) → Fin q))) :=
    Submodule.map_comap_eq_of_surjective coords.surjective _
  have hUT : Submodule.IsCloseTo loss U T := by
    apply (Submodule.isCloseTo_map_iff coords).mp
    rw [hmapU]
    exact hY
  have hproject := hGT.map_starProjection_energy_le_three_of_close_target hUT
    (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (R - (eSoft : ℂ) • 1))
    hC.isPositive_toEuclideanCLM hGenergyC hCnorm hrho0 hrho
    htau0 htau hloss0 hloss
  have hGne : G ≠ ⊥ := by
    obtain ⟨j, hj⟩ := minEigenvalue_achieved hH
    apply hH.spectralSpanLE_ne_bot_of_mem_spectrum _ le_rfl
    rw [← hj]
    exact hH.eigenvalues_mem_spectrum_real j
  have hTne : T ≠ ⊥ := by
    apply Submodule.one_le_finrank_iff.mp
    rw [hdimT]
    exact Submodule.one_le_finrank_iff.mpr hGne
  obtain ⟨t, htT, htne⟩ := T.ne_bot_iff.mp hTne
  have hloss1 : loss < 1 :=
    (Real.projected_nine_quarters_energy_le_three
      ((norm_nonneg _).trans hCnorm) hloss0 hloss).1
  let z := U.starProjection t
  have hzne : z ≠ 0 := hUT.starProjection_ne_zero hloss1 htT htne
  have hzU : z ∈ U := U.starProjection_apply_mem t
  have hzenergy := hproject z (Submodule.mem_map_of_mem htT)
  have hRawEnergy : (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) R z) z).re ≤
      (eSoft + 3) * ‖z‖ ^ 2 := by
    change (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (R - (eSoft : ℂ) • 1) z) z).re ≤ 3 * ‖z‖ ^ 2 at hzenergy
    rw [Matrix.re_inner_toEuclideanCLM_sub_ofReal_smul_one R eSoft z] at hzenergy
    nlinarith only [hzenergy]
  have hConj : coords.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) R ∘L
        coords.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Rnat)
        (1 : EuclideanSpace ℂ (↥(Jᶜ) → Fin q) →L[ℂ]
          EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) := by
    rw [hRawLift]
    exact Entropy.localLift_middleFirst_conjugation J Rnat
  have hTA : coords (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) R z) =
      TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Rnat)
        (1 : EuclideanSpace ℂ (↥(Jᶜ) → Fin q) →L[ℂ]
          EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) (coords z) := by
    have hh := congrArg (fun f ↦ f (coords z)) hConj
    change coords (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      R (coords.symm (coords z))) = _ at hh
    rw [coords.symm_apply_apply] at hh
    exact hh
  have hTensorEnergy : (inner ℂ
      (TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Rnat)
        (1 : EuclideanSpace ℂ (↥(Jᶜ) → Fin q) →L[ℂ]
          EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) (coords z)) (coords z)).re ≤
      (eSoft + 3) * ‖coords z‖ ^ 2 := by
    rw [← hTA, coords.inner_map_map, coords.norm_map]
    exact hRawEnergy
  have hTensorNe : coords z ≠ 0 := by
    intro hz
    exact hzne (coords.injective (hz.trans coords.map_zero.symm))
  obtain ⟨n, hn, hlower, hupper⟩ := hRnat.exists_compression_min_between_of_tensor_energy
    Y eSoft (eSoft + 3) hRawLower hzU hTensorNe hTensorEnergy
  let hSym := Y.orthogonalCompression_isSymmetric
    (isSymmetric_toEuclideanLin_iff.mpr hRnat)
  change hSym.eigenvalues hn (Fin.last n) ≤ eSoft + 3 at hupper
  change eSoft ≤ hSym.eigenvalues hn (Fin.last n) at hlower
  refine ⟨n, hSym.eigenvectorBasis hn, hSym.eigenvalues hn, hn,
    hSym.apply_eigenvectorBasis hn, hSym.eigenvalues_antitone hn,
    hlower, hupper, ?_, ?_, ?_⟩
  · linarith only [hlower, hShift]
  · linarith only [hlower, hShift, hrho]
  · linarith only [hupper, hSoftLE]

end TNLean.MPS.AreaLaw.ALVV
