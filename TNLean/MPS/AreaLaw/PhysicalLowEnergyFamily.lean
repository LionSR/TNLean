/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ChebyshevViability
import QICLean.Analysis.EuclideanEigenvectorBasis
import TNLean.MPS.AreaLaw.ActualClippedPolynomialFamily
import TNLean.MPS.AreaLaw.PhysicalLowEnergyCloseness

import TNLean.MPS.AreaLaw.IndependentFiveRegionResidual

/-!
# Improving families between buffered physical low-energy spaces

One actual three-bulk truncation supplies low-energy targets at distinct cutoffs.
Its common polynomial family contains the constructed Chebyshev filter,
which improves viability from the upper target to the lower one. The same
truncated Hamiltonian is used in the physical spectral comparisons and in
its tensor decomposition. This supports ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041.

The spectral buffers and five-region geometry are explicit. No low-density
bootstrap, efficient central tensor representation or merge-tree conclusion
is asserted. The false soft-cluster estimate is not used.

**Scope restriction (buffers and geometry):** The physical existence result
uses `3*w < eta` and the stated interior five-region geometry. The source
hypothesis at line 1027 gives `eta₁ ≥ 6*w` after the substitution
`w = mu/(3*log n)` for integers `n ≥ 2`. The substitution, finite short
chains and boundary regions are treated in `LowEnergyIntervalFamily`;
see `docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

**Local fix (closed cutoffs and filter sign):** The spectral estimates use
closed cutoffs; positivity of the unsquared Chebyshev filter is not claimed.
See the companion notes
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.
-/

open Matrix

open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator
  ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- A common polynomial family gives one actual Chebyshev filter and its
finite tensor decomposition before any viable subspace is chosen. It
improves viability from the upper closed spectral span to the lower one,
without assuming a gap between them. The polynomial family is an explicit
input to this auxiliary; the physical theorem constructs it separately.
ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1037–1041. -/
theorem exists_chebyshev_nested_viability_of_polynomial_family
    {σ ι m e : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype ι]
    [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e]
    {N degree : ℕ}
    (B : Matrix σ σ ℂ) (hB : B.IsHermitian)
    (v : OrthonormalBasis ι ℂ (EuclideanSpace ℂ σ)) (lam : ι → ℝ)
    (hv : ∀ i, B.toEuclideanLin (v i) = (lam i : ℂ) • v i)
    (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval B Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)))
    (eta0 eta1 upper : ℝ) (hsep : eta0 < eta1) (hend : eta1 ≤ upper)
    (hnorm : ‖B‖ ≤ upper) :
    let A : Fin N → EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m := fun r ↦
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r)
    let lower := (Submodule.spectralSpanLE v lam eta0).map Tm.toLinearEquiv.toLinearMap
    let higher := (Submodule.spectralSpanLE v lam eta1).map Tm.toLinearEquiv.toLinearMap
    let Delta := (2 * Real.exp
      (-2 * (degree : ℝ) * Real.sqrt ((eta1 - eta0) / (upper - eta0)))) ^ 2
    ∃ p : Polynomial ℝ, p.natDegree = degree ∧ p.eval eta0 = 1 ∧
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)
              (Polynomial.aeval B (p.map (algebraMap ℝ ℂ))) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL (A r)
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)) ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ m)) (delta : ℝ),
          Submodule.IsViable (F := EuclideanSpace ℂ e) delta S higher → delta < 1 →
          let grow := ⨆ r : Fin N, S.map (A r).toLinearMap
          Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
            Submodule.IsViable (F := EuclideanSpace ℂ e)
              (Delta / (1 - delta) ^ 2) grow lower := by
  intro A lower higher Delta
  -- Coincident endpoints obtain only the canonical coordinates, without a gap.
  obtain ⟨hK, _htrivial, hupper, hmap⟩ :=
    Matrix.exists_canonical_isometric_spectral_data B hB v lam hv eta0 eta0 upper rfl hnorm Tm
  let Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B ∘L
      Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hHm : (Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →ₗ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e)).IsSymmetric := hK
  have hhigher : higher = Submodule.span ℂ
      (hHm.eigenvectorBasis rfl '' {j | hHm.eigenvalues rfl j ≤ eta1}) := hmap eta1
  have hlower : lower = Submodule.span ℂ
      (hHm.eigenvectorBasis rfl '' {j | hHm.eigenvalues rfl j ≤ eta0}) := hmap eta0
  obtain ⟨p, hdegree, hp0, hp⟩ :=
    Submodule.exists_isSpectralProjector_chebyshev Hm hHm rfl degree hsep hend hupper
  obtain ⟨M, hM⟩ := hdecomp (p.map (algebraMap ℝ ℂ))
    (Polynomial.natDegree_map_le.trans hdegree.le)
  have hfilter (Q : Polynomial ℂ) : Polynomial.aeval Hm Q =
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval B Q)) :=
    (Polynomial.aeval_algHom_apply
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B) Q).trans
      (congrArg Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
        (Polynomial.aeval_algHom_apply
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)).toAlgEquiv.toAlgHom B Q))
  refine ⟨p, hdegree, hp0, M, hM, fun S delta hS hdelta ↦ ?_⟩
  rw [hhigher] at hS
  simpa only [hlower, Fintype.card_fin] using
    (Submodule.IsViable.spectralProjector_between_cutoffs
      (𝕜 := ℂ) (M := EuclideanSpace ℂ m) (R := EuclideanSpace ℂ e) hp hsep.le A
      (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r))
      ((hfilter _).trans hM) hS hdelta (sq_nonneg _))

/-- One threshold controls every cutoff below the prescribed bandwidth.
ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968, and
Theorem `t:aisgapless`, lines 1027–1041. -/
private theorem exists_common_low_energy_residual_threshold
    (eta w delta : ℝ) (heta : 0 ≤ eta) (hw : 0 < w) (hdelta : 0 < delta) :
    ∃ t : ℝ, t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (delta * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      let xi := (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8)
      xi ≤ 1 ∧ 2 * (6 + eta) * xi ≤ delta * w ^ 2 := by
  let C := 288 * Real.exp (11 / 8)
  let z := min 1 (delta * w ^ 2 / (2 * (6 + eta)))
  have hden : 0 < 2 * (6 + eta) := by linarith only [heta]
  have hz : 0 < z := lt_min (by norm_num) (div_pos (by positivity) hden)
  have hz1 : z ≤ 1 := min_le_left _ _
  have hC1 : 1 ≤ C := by
    have he : 1 ≤ Real.exp (11 / 8) := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp only [C]
    linarith only [he]
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hquot : 1 ≤ C / z := (one_le_div hz).mpr (hz1.trans hC1)
  have hlog : 0 ≤ Real.log (C / z) := Real.log_nonneg hquot
  let t := 21 + eta + 8 * Real.log (C / z)
  have harg : -(t - eta) / 8 = -21 / 8 - Real.log (C / z) := by
    dsimp only [t]
    ring
  have htail : C * Real.exp (-(t - eta) / 8) ≤ z := by
    rw [harg, Real.exp_sub, Real.exp_log (div_pos hC hz)]
    have he : Real.exp (-21 / 8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have heq : C * (Real.exp (-21 / 8) / (C / z)) = Real.exp (-21 / 8) * z := by
      field_simp
    rw [heq]
    exact (mul_le_mul_of_nonneg_right he hz.le).trans_eq (one_mul z)
  refine ⟨t, rfl, by dsimp only [t]; linarith only [heta, hlog],
    by dsimp only [t]; linarith only [hlog], htail.trans hz1, ?_⟩
  have hsmall := (le_div_iff₀ hden).mp (min_le_right 1 (delta * w ^ 2 / (2 * (6 + eta))))
  exact (mul_le_mul_of_nonneg_left htail hden.le).trans (by nlinarith only [hsmall])

/-- A single physical clipping threshold supplies both buffered spectral
comparisons. ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041. The bandwidths remain strictly positive. -/
private theorem exists_five_region_physical_buffered_targets
    (L q a b ell : ℕ) (eta w epsilon : ℝ)
    (hbuffer : 3 * w < eta) (hw : 0 < w) (hepsilon : 0 < epsilon)
    (hq : 2 ≤ q) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b) (hbL : b + 2 * ell ≤ L - 1)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, h i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B : ℝ → (Fin 5 → ℝ) → Finset (Fin 5) →
        Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun t e T ↦
      (∑ j, ((if j ∈ T then
        cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
          (e j : ℂ) • 1)) + Y
    ∃ (t : ℝ) (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
      (hO : (B t e ∅).IsHermitian) (hC : (B t e K).IsHermitian),
      t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (epsilon * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      lower ≤ higher ∧
      Submodule.IsCloseTo epsilon
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo epsilon lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) := by
  classical
  intro k A Cross Y K B
  obtain ⟨t, htformula, ht, hcut, hxi1, hsmall⟩ :=
    exists_common_low_energy_residual_threshold eta w epsilon
      (by linarith only [hw, hbuffer]) hw hepsilon
  obtain ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, hres⟩ :=
    exists_five_region_independent_truncation_residual L q a b ell t
      (by omega) hell (by linarith only [ht]) (hab.trans (Nat.le_succ b))
      (hbL.trans (Nat.sub_le L 1)) h hs h0 h1
  have hpos (T : Finset (Fin 5)) : (B t e T).PosSemidef :=
    (Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t T
      (fun j ↦ (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian)
      (fun j ↦ Matrix.le_iff.mpr (hlo j)) x hx (by linarith only [ht])).1.add
      (show Y.PosSemidef from Matrix.nonneg_iff_posSemidef.mp
        (Finset.sum_nonneg fun i _ ↦ h0 i))
  refine ⟨t, e, E0, x, z, (hpos ∅).isHermitian, (hpos K).isHermitian,
    htformula, ht, hcut, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, ?_⟩
  intro lower higher
  have heigen (T : Finset (Fin 5)) (j : Fin L → Fin q) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e T)
          ((hpos T).isHermitian.eigenvectorBasis j) =
        ((hpos T).isHermitian.eigenvalues j : ℂ) •
          (hpos T).isHermitian.eigenvectorBasis j :=
    (hpos T).isHermitian.toEuclideanCLM_eigenvectorBasis j
  have hresBound (T : Finset (Fin 5)) (c : ℝ) (hc : 0 < c) (hce : c ≤ eta) :
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (B t e ∅ - B t e K)).domRestrict
        (Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
          (hpos T).isHermitian.eigenvalues (E0 + c))‖ ≤
        (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8) :=
    (hres T c hc.le (by linarith only [hcut, hce])
      (hpos T).isHermitian.eigenvectorBasis (hpos T).isHermitian.eigenvalues (heigen T)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hce]))
        (by positivity))
  have hpert (T : Finset (Fin 5)) (c : ℝ) (hc : 0 < c) (hce : c ≤ eta)
      (v : EuclideanSpace ℂ (Fin L → Fin q))
      (hv : v ∈ Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
        (hpos T).isHermitian.eigenvalues (E0 + c)) :
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e ∅) v -
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e K) v‖ ≤
        ((288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8)) * ‖v‖ := by
    simpa only [map_sub, ContinuousLinearMap.coe_domRestrict, Set.domRestrict_apply,
      _root_.sub_apply, ← Submodule.norm_coe] using
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (B t e ∅ - B t e K)).domRestrict
          (Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
            (hpos T).isHermitian.eigenvalues (E0 + c))).le_of_opNorm_le
              (hresBound T c hc hce) ⟨v, hv⟩
  have hclose (c : ℝ) (hc : 0 < c) (hce : c ≤ eta) :
      Submodule.IsCloseTo epsilon
          (Submodule.spectralSpanLE (hpos K).isHermitian.eigenvectorBasis
            (hpos K).isHermitian.eigenvalues (E0 + c + w))
          (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
            (hpos ∅).isHermitian.eigenvalues (E0 + c)) ∧
        Submodule.IsCloseTo epsilon
          (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
            (hpos ∅).isHermitian.eigenvalues (E0 + c + w))
          (Submodule.spectralSpanLE (hpos K).isHermitian.eigenvectorBasis
            (hpos K).isHermitian.eigenvalues (E0 + c)) := by
    let xi := (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8)
    have hxi : 0 < xi := by positivity
    have hsmallc : 2 * (6 + c) * xi ≤ epsilon * w ^ 2 :=
      (mul_le_mul_of_nonneg_right (by linarith only [hce]) hxi.le).trans hsmall
    have hbudget := Real.spectral_window_budget_bound E0 c xi w epsilon hE0 hE04
      hc.le hxi hxi1 hw.le hepsilon.le hsmallc
    refine ⟨Submodule.isCloseTo_spectralSpanLE_of_perturbation
      (hpos ∅).isHermitian.eigenvectorBasis (hpos K).isHermitian.eigenvectorBasis
      (hpos ∅).isHermitian.eigenvalues (hpos K).isHermitian.eigenvalues
      (heigen ∅) (heigen K) (hpert ∅ c hc hce) hxi
      (fun j _ ↦ (hpos ∅).eigenvalues_nonneg j) (by linarith only [hE0, hc])
      (by linarith only [hw])
      (by simpa only [sub_zero, add_sub_cancel_left] using hbudget), ?_⟩
    exact Submodule.isCloseTo_spectralSpanLE_of_perturbation
      (hpos K).isHermitian.eigenvectorBasis (hpos ∅).isHermitian.eigenvectorBasis
      (hpos K).isHermitian.eigenvalues (hpos ∅).isHermitian.eigenvalues
      (heigen K) (heigen ∅)
      (fun v hv ↦ (norm_sub_rev _ _).trans_le (hpert K c hc hce v hv)) hxi
      (fun j _ ↦ (hpos K).eigenvalues_nonneg j) (by linarith only [hE0, hc])
      (by linarith only [hw])
      (by simpa only [sub_zero, add_sub_cancel_left] using hbudget)
  have hupperClose : Submodule.IsCloseTo epsilon
      (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
        (hpos ∅).isHermitian.eigenvalues (E0 + eta)) higher := by
    simpa only [higher,
      show E0 + (eta - w) = E0 + eta - w by ring,
      show E0 + eta - w + w = E0 + eta by ring] using
      (hclose (eta - w) (by linarith only [hbuffer, hw]) (by linarith only [hw])).2
  have hlowerClose : Submodule.IsCloseTo epsilon lower
      (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
        (hpos ∅).isHermitian.eigenvalues (E0 + eta - 3 * w)) := by
    simpa only [lower,
      show E0 + (eta - 3 * w) = E0 + eta - 3 * w by ring,
      show E0 + eta - 3 * w + w = E0 + eta - 2 * w by ring] using
      (hclose (eta - 3 * w) (sub_pos.mpr hbuffer) (by linarith only [hw])).1
  have hnest : lower ≤ higher := Submodule.span_mono
    (Set.image_mono (fun j hj ↦ hj.trans
      (show E0 + eta - 2 * w ≤ E0 + eta - w by linarith only [hw])))
  exact ⟨hnest, hupperClose, hlowerClose⟩

/-- One physically constructed three-bulk truncation has buffered nested
low-energy targets and one common operator family containing the actual
Chebyshev filter. Regional minima, ground data, spectral bases, polynomial,
tensor factors and both one-sided spectral comparisons are derived from
the original supported positive contractions. They precede every viable
subspace. ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.
This five-region statement retains its buffers and explicit filter error;
it is not the low-density bootstrap or the unrestricted source theorem. -/
theorem exists_five_region_physical_low_energy_filter_family
    (L q a b ell : ℕ) (eta w epsilon : ℝ)
    (hbuffer : 3 * w < eta) (hw : 0 < w) (hepsilon : 0 < epsilon)
    (hq : 2 ≤ q) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b) (hbL : b + 2 * ell ≤ L - 1)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, h i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B : ℝ → (Fin 5 → ℝ) → Finset (Fin 5) →
        Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun t e T ↦
      (∑ j, ((if j ∈ T then
        cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
          (e j : ℂ) • 1)) + Y
    ∃ (t : ℝ) (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
      (hO : (B t e ∅).IsHermitian) (hC : (B t e K).IsHermitian),
      t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (epsilon * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      let J := interval L (a + ell) (b + ell + 1)
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let D := (q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))
      let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
        Real.sqrt (w / (3 * t + 4 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
      lower ≤ higher ∧
      Submodule.IsCloseTo epsilon
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo epsilon lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) ∧
      ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
        ∃ p : Polynomial ℝ, p.natDegree = ell ^ 2 ∧ p.eval (E0 + eta - 2 * w) = 1 ∧
          ∃ M : Fin N → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
            Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (B t e K) (p.map (algebraMap ℝ ℂ))) ∘L
                Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
              ∑ j, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j))
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥(Jᶜ) → Fin q) (M j)) ∧
            ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
              Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
                (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
              let grow := ⨆ j : Fin N, S.map
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
              Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
                Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                  (Delta / (1 - delta) ^ 2) grow (lower.map Tm.toLinearEquiv.toLinearMap) := by
  classical
  intro k A Cross Y K B
  obtain ⟨t, e, E0, x, z, hO, hC, htformula, ht, hcut, hxunit, hx, hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, htargets⟩ :=
    exists_five_region_physical_buffered_targets L q a b ell eta w epsilon
      hbuffer hw hepsilon hq hell hab hbL h hs h0 h1
  change (B t e ∅).IsHermitian at hO
  change (B t e K).IsHermitian at hC
  change ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) at hnorm
  refine ⟨t, e, E0, x, z, hO, hC, htformula, ht, hcut, hxunit, hx, hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, ?_⟩
  intro lower higher J beta tau U Phi Tm D Delta
  obtain ⟨hnest, hupperClose, hlowerClose⟩ := htargets
  have heigen (j : Fin L → Fin q) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (B t e K) (hC.eigenvectorBasis j) =
        (hC.eigenvalues j : ℂ) • hC.eigenvectorBasis j :=
    hC.toEuclideanCLM_eigenvectorBasis j
  refine ⟨hnest, hupperClose, hlowerClose, ?_⟩
  have hdegree : 1 ≤ ell ^ 2 := by
    rw [pow_two]
    simpa only [Nat.one_mul] using Nat.mul_le_mul hell hell
  obtain ⟨N, W, hNraw, hdecomp⟩ :=
    exists_actual_regional_clipped_polynomial_family_fin
      L q a b ell (ell ^ 2) hell hq hdegree hab hbL h hs e t J
  have hN : N ≤ D ^ 2 := by
    simpa only [J, D, Finset.sdiff_self, Finset.card_empty, Nat.mul_zero, Nat.zero_add,
      pow_zero, mul_one] using hNraw
  obtain ⟨p, hpdegree, hp0, M, hM, himprove⟩ :=
    exists_chebyshev_nested_viability_of_polynomial_family
      (B t e K) hC hC.eigenvectorBasis hC.eigenvalues heigen W Tm
      (fun Q hQ ↦ (hdecomp Q hQ).imp fun M hM ↦ hM.2)
      (E0 + eta - 2 * w) (E0 + eta - w) (3 * t + 4 * (ell : ℝ))
      (by linarith only [hw])
      (by linarith only [hE04, hcut, ht, (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell), hw, hbuffer]) hnorm
  refine ⟨N, W, hN, p, hpdegree, hp0, M, hM, ?_⟩
  simpa only [Delta,
    show (E0 + eta - w) - (E0 + eta - 2 * w) = w by ring] using himprove

end TNLean.MPS.AreaLaw
