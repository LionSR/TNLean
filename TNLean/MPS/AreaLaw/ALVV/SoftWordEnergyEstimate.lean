/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftParentEnergy
import TNLean.MPS.AreaLaw.AdjacentIntervalMerge
import QICLean.Analysis.SoftRegionalEnergyParameters
import QICLean.Analysis.RegionalEnergyCalibration
import QICLean.Analysis.ViableProjectionNonzero
import QICLean.Analysis.ViableSubspaceOrder
import QICLean.Analysis.CompressionEnergyInterval
import QICLean.Analysis.QuadraticScalarShift
import QICLean.Entropy.RegionalOperatorCoordinates

/-!
# Raw regional energy on the same untrimmed word candidate

A specified target and its own certified word family determine the energy
candidate. The raw native matrix is a fixed-complement principal slice of
the literal soft replacement, before its true minimum is chosen. Its actual
compressed minimum gives a one-sided original-parent estimate. No target-energy
bound, projected vector or compressed eigenvalue is supplied.

This is a corrected conditional auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and its energy proof at line 1807. The
certificate comes from the calibrated hard-clipped construction; that family
is not identified with literal soft Generate.

**Scope restriction (given family certificate):** The target, its own word
family and the calibrated count conditions are inputs supplied by the proved
physical factory. No regional energy or spectral minimum is assumed. The
substitution into the actual tree and its recursive energy assignment remain
separate. See `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- The actual raw compressed minimum on the specified family's one-word
child image yields a one-sided parent estimate. The soft operator and its
minimum are constructed from the original bonds. The target/family certificate,
count bounds and one-sided estimated middle center are explicit inputs. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631, and line 1807. -/
theorem exists_native_soft_word_compressed_energy_estimate
    {L q l u v r ell D s N : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (hell : 21 ≤ ell) (hD : 2 ≤ D) (hcount : 50 * ell ^ 2 ≤ D) (hsample : 1 ≤ s)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q)) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let J := interval L l r
    let coords := Entropy.regionTensorCoordinates q J
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let Delta := 1 / (200000 * (D : ℝ) ^ 12)
    let loss := Delta / (1 - (1 / 4 : ℝ)) ^ 2
    let rho := 32 * Real.exp (-(((384 : ℝ) - 48) / 8)) +
      (768 / (12 : ℝ)) * (384 / (768 : ℝ)) ^ 12
    Module.finrank ℂ T = Module.finrank ℂ G → Submodule.IsCloseTo tau G T →
    (∀ S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)),
      Submodule.IsViable (1 / 4 : ℝ) S (T.map coords.toLinearEquiv.toLinearMap) →
      let grow : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) := ⨆ w : Fin 1 → Fin N,
        S.map ((List.ofFn (fun j ↦ F (w j))).prod : _ →ₗ[ℂ] _)
      Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
        Submodule.IsViable loss grow (T.map coords.toLinearEquiv.toLinearMap)) →
    let P := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r), h i
    let M := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ u ≤ i.val ∧ i.val + 1 < v), h i
    let sigma0 : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
    let y0 := ((Entropy.cutEquiv (fun _ : Fin L ↦ q) J) sigma0).2
    let native := fun x : J → Fin q ↦
      (Entropy.cutEquiv (fun _ : Fin L ↦ q) J).symm (x, y0)
    0 ≤ rho ∧ rho < 1 / 16 ∧
    ∃ (eP eM : ℝ) (xP xM : (Fin L → Fin q) → ℂ),
      star xP ⬝ᵥ xP = 1 ∧ P *ᵥ xP = (eP : ℂ) • xP ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
      star xM ⬝ᵥ xM = 1 ∧ M *ᵥ xM = (eM : ℂ) • xM ∧
      (M - (eM : ℂ) • 1).PosSemidef ∧
      ∀ p : ℝ, eM - 10 ≤ p → p ≤ eM →
        let R := P - M + (p : ℂ) • 1 +
          cfc (Real.softTruncation 768 12) (M - (p : ℂ) • 1)
        let Kraw := R.submatrix native native
        Kraw.IsHermitian ∧ ∃ (eSoft : ℝ) (w : (Fin L → Fin q) → ℂ),
          R = Entropy.localLift (n := fun _ : Fin L ↦ q) J Kraw ∧
          star w ⬝ᵥ w = 1 ∧ R *ᵥ w = (eSoft : ℂ) • w ∧
          (Kraw - (eSoft : ℂ) • 1).PosSemidef ∧
          eSoft ≤ eP ∧ eP - eSoft ≤ rho ∧
          ∀ (k : ℕ) (hlk : l ≤ k) (hkr : k ≤ r)
            (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
            (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))),
            Submodule.IsViable (3 / 200 : ℝ) S1
              (G.map (Entropy.regionTensorCoordinates q
                (interval L l k)).toLinearEquiv.toLinearMap) →
            Submodule.IsViable (3 / 200 : ℝ) S2
              (G.map (Entropy.regionTensorCoordinates q
                (interval L k r)).toLinearEquiv.toLinearMap) →
            let W : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) :=
              adjacentIntervalMerge L q l k r hlk hkr S1 S2
            let V : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) := ⨆ word : Fin 1 → Fin N,
              W.map ((List.ofFn (fun j ↦ F (word j))).prod : _ →ₗ[ℂ] _)
            Module.finrank ℂ V ≤ D ^ 2 * Module.finrank ℂ W ∧
              ∃ (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ V)
                (energy : Fin (n + 1) → ℝ),
                Module.finrank ℂ V = n + 1 ∧
                (∀ j, V.orthogonalCompression
                  (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Kraw).toLinearMap
                    (b j) = (energy j : ℂ) • b j) ∧
                Antitone energy ∧ eSoft ≤ energy (Fin.last n) ∧
                energy (Fin.last n) ≤ eSoft + 3 ∧
                eP - 3 - rho ≤ energy (Fin.last n) - 3 ∧
                energy (Fin.last n) - 3 ≤ eP := by
  classical
  intro config H hH G J coords a tau Delta loss rho hdimT hGT hword
    P M sigma0 y0 native
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨htau0, htau, hloss0, hloss⟩ :=
    Real.soft_regional_filter_precision_bounds D s hD hsample
  have hnorm := Real.soft_regional_fixed_norm_bound ell D hell hcount
  obtain ⟨hrho0, hrho⟩ := Real.soft_regional_fixed_residual_lt
  have htauSmall : tau ≤ 1 / 100 := by
    apply htau.trans
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100)
    have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith only [hDR]
  obtain ⟨eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, hsoft⟩ :=
    exists_native_soft_parent_energy_bound hq hlu huv hvr hrL hleft hright h hs h0 h1
  refine ⟨hrho0, hrho, eP, eM, xP, xM, hxP, hPxP, hPmin, hxM, hMxM, hMmin, ?_⟩
  intro p hpl hpu R Kraw
  have hPpos : P.PosSemidef := (Finset.sum_nonneg fun i _ ↦ h0 i).posSemidef
  have hMpos : M.PosSemidef := (Finset.sum_nonneg fun i _ ↦ h0 i).posSemidef
  have hscalar : IsSelfAdjoint ((p : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) :=
    IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (by simp [IsSelfAdjoint])
  have hRself : IsSelfAdjoint R :=
    (((hPpos.isHermitian.isSelfAdjoint.sub hMpos.isHermitian.isSelfAdjoint).add hscalar).add
      IsSelfAdjoint.cfc)
  have hKraw : Kraw.IsHermitian := hRself.isHermitian.submatrix native
  obtain ⟨eSoft, K, w, hK, _hKnorm, hR, hw, hRw, hC, hCnorm, hresidual⟩ :=
    hsoft p 768 12 hpl hpu (by norm_num) (by norm_num)
  obtain ⟨hSoftLE, hShift, hGenergy⟩ := hresidual 384 (by norm_num) (by norm_num)
  norm_num only at hShift hGenergy hCnorm
  have hrhoEq : 32 * Real.exp (-42) + (1 : ℝ) / 64 = rho := by norm_num [rho]
  rw [hrhoEq] at hShift hGenergy
  have hNormD : ‖R - (eSoft : ℂ) • 1‖ ≤ (D : ℝ) := by
    have hbudget : 768 * (1 + Real.log (12 : ℝ)) + 4 * (ell : ℝ) + 14 ≤ D := by
      linarith only [hnorm.2]
    exact hCnorm.trans hbudget
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
  have hNative : Kraw = K + (eSoft : ℂ) • 1 := by
    ext x y
    change Entropy.cutOperator J R (x, y0) (y, y0) = _
    rw [hRnative, Entropy.cutOperator_localLift]
    simp
  have hRawLift : R = Entropy.localLift (n := fun _ : Fin L ↦ q) J Kraw := by
    rw [hNative]
    exact hRnative
  have hRawLower : (Kraw - (eSoft : ℂ) • 1).PosSemidef := by
    rw [hNative, add_sub_cancel_right]
    exact hK
  refine ⟨hKraw, eSoft, w, hRawLift, hw, hRw, hRawLower, hSoftLE, hShift, ?_⟩
  intro k hlk hkr S1 S2 hS1 hS2 W V
  have hmerged := isViable_adjacentIntervalMerge hlk hkr G S1 S2 hS1 hS2
  have hGTmap : Submodule.IsCloseTo tau
      (G.map coords.toLinearEquiv.toLinearMap) (T.map coords.toLinearEquiv.toLinearMap) :=
    (Submodule.isCloseTo_map_iff coords).mpr hGT
  have hWT : Submodule.IsViable (1 / 4 : ℝ) W (T.map coords.toLinearEquiv.toLinearMap) := by
    apply Submodule.IsCloseTo.of_le (Submodule.IsCloseTo.trans hmerged hGTmap (by norm_num))
    linarith only [htauSmall]
  obtain ⟨hdimV, hV⟩ := hword W hWT
  refine ⟨hdimV, ?_⟩
  let U := (V.tensorProd
    (⊤ : Submodule ℂ (EuclideanSpace ℂ (↥(Jᶜ) → Fin q)))).comap
      coords.toLinearEquiv.toLinearMap
  have hmapU : U.map coords.toLinearEquiv.toLinearMap = V.tensorProd
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (↥(Jᶜ) → Fin q))) :=
    Submodule.map_comap_eq_of_surjective coords.surjective _
  have hUT : Submodule.IsCloseTo loss U T := by
    apply (Submodule.isCloseTo_map_iff coords).mp
    rw [hmapU]
    exact hV
  have hproject := hGT.map_starProjection_energy_le_three_of_close_target hUT
    (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (R - (eSoft : ℂ) • 1))
    hC.isPositive_toEuclideanCLM hGenergyC hNormD hrho0 hrho.le
    htau0.le htau hloss0.le hloss
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
      (by positivity : (0 : ℝ) ≤ D) hloss0.le hloss).1
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
  have hConj := Entropy.regionTensorCoordinates_conjugation_localLift q J Kraw
  have hTA : coords (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) R z) =
      TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Kraw)
        (1 : EuclideanSpace ℂ (↥(Jᶜ) → Fin q) →L[ℂ]
          EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) (coords z) := by
    have hh := congrArg (fun f ↦ f (coords z)) hConj
    change coords (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (Entropy.localLift (n := fun _ : Fin L ↦ q) J Kraw) (coords.symm (coords z))) = _ at hh
    rw [coords.symm_apply_apply, ← hRawLift] at hh
    exact hh
  have hTensorEnergy : (inner ℂ
      (TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Kraw)
        (1 : EuclideanSpace ℂ (↥(Jᶜ) → Fin q) →L[ℂ]
          EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) (coords z)) (coords z)).re ≤
      (eSoft + 3) * ‖coords z‖ ^ 2 := by
    rw [← hTA, coords.inner_map_map, coords.norm_map]
    exact hRawEnergy
  have hTensorNe : coords z ≠ 0 := by
    intro hz
    exact hzne (coords.injective (hz.trans coords.map_zero.symm))
  obtain ⟨n, hn, hlower, hupper⟩ := hKraw.exists_compression_min_between_of_tensor_energy
    V eSoft (eSoft + 3) hRawLower hzU hTensorNe hTensorEnergy
  let hSym := V.orthogonalCompression_isSymmetric
    (isSymmetric_toEuclideanLin_iff.mpr hKraw)
  change hSym.eigenvalues hn (Fin.last n) ≤ eSoft + 3 at hupper
  change eSoft ≤ hSym.eigenvalues hn (Fin.last n) at hlower
  refine ⟨n, hSym.eigenvectorBasis hn, hSym.eigenvalues hn, hn,
    hSym.apply_eigenvectorBasis hn, hSym.eigenvalues_antitone hn,
    hlower, hupper, ?_, ?_⟩
  · linarith only [hlower, hShift]
  · linarith only [hupper, hSoftLE]

end TNLean.MPS.AreaLaw.ALVV
