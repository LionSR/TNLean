/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowDensityAccurateViability
import TNLean.MPS.AreaLaw.LowDensityLogDimension
import TNLean.MPS.AreaLaw.DGEntropyParameters
import QICLean.Analysis.ViableSubspaceEntropy
import QICLean.Analysis.ViableSubspaceMinimum

/-!
# Entropy in an original low-energy band

One fixed regional viable space for an outer original spectral band is
refined by the actual accurate interval families. Their image spaces control
tails of one fixed physical reduced state, with no spectral gap or invariance
assumption on the original band. Summing these actual tails gives coefficient
exactly one on the logarithm of the full-band dimension.

The constants are chosen before the physical data at each fixed positive
bandwidth. This is the entropy argument supporting ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105, and Proposition `prop:albootstrap-ld`,
lines 1107–1128. The sharper accuracy-dependent MPS rate is separate.

**Scope restriction (physical intervals and fixed bandwidth):** The statements
retain `q ≥ 2` and one coefficient for each fixed bandwidth. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

open Matrix

-- The original physical marginal is retained in its actual interval coordinates.
/-- Entropy of every unit vector in an original low-energy band, with explicit
capped-width costs and coefficient one on the full-band logarithmic dimension.
The constant-viable initial space is fixed before the accuracy choices. ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_interval_low_energy_entropy_bound_capped
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ Kb Cf : ℝ, 0 < Kb ∧ 100 ≤ Cf ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 2 ≤ q), p ≤ r → r ≤ L → 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let b := min v (etaLD / 2)
      let g := min (b / 6) 1
      let m := q * ⌈Real.exp 100⌉₊
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
        Entropy.regionEntropy J ψ ≤ Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
          Kb / (b / 2) * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3 +
          14872 * (Cf + 1) * (6 + 2 * Real.log (Cf + 1)) / g * u ^ 3 +
          54 * Real.log 2 := by
  classical
  obtain ⟨Kb, hKb, hinitial⟩ :=
    exists_fixed_bandwidth_interval_low_energy_viable_subspace_log_bound etaLD hLD
  obtain ⟨Cf, hCf, _hCfeta, hrefine⟩ :=
    exists_fixed_bandwidth_interval_low_energy_dyadic_refinement etaLD hLD
  refine ⟨Kb, Cf, hKb, hCf, ?_⟩
  intro L q p r v hq hpr hrL hv h hs h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  intro J G b g m u ψ hψG hψ
  let beta := fun _ : Fin L ↦ Fin q
  let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
  let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
    (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
  let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
    (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
    (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
  let EM := EuclideanSpace ℂ (J → Fin q)
  let EE := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)
  have hb : 0 < b := lt_min hv (by positivity)
  have hbv : b ≤ v := min_le_left _ _
  have hbcap : b ≤ etaLD / 2 := min_le_right _ _
  have hw : 0 < b / 6 := by positivity
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hG {a c : ℝ} (hac : a ≤ c) : G a ≤ G c :=
    Submodule.spectralSpanLE_mono_cutoff hRaw.eigenvectorBasis hRaw.eigenvalues
      (by linarith only [hac])
  obtain ⟨W0, hWdim, hW0⟩ :=
    hinitial L q p r (b / 2) hq hpr hrL (by positivity) h hs h0 h1
  have hψupper : ψ ∈ G (etaLD - b / 2) :=
    hG (by linarith only [hbv, hb]) hψG
  have hupperne : (G (etaLD - b / 2)).map Tm.toLinearEquiv.toLinearMap ≠ ⊥ := by
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨Tm ψ, ⟨ψ, hψupper, rfl⟩, ?_⟩
    intro hz
    have hn : ‖Tm ψ‖ = 1 := by simpa only [LinearIsometryEquiv.norm_map] using hψ
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hWne : W0 ≠ ⊥ :=
    Submodule.isViable_ne_bot_of_target_ne_bot hW0 (by norm_num) hupperne
  have hr0 : 1 ≤ Module.finrank ℂ W0 := Submodule.one_le_finrank_iff.mpr hWne
  have hGne : G etaLD ≠ ⊥ := by
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨ψ, hG (by linarith only [hv]) hψG, ?_⟩
    intro hz
    rw [hz, norm_zero] at hψ
    norm_num at hψ
  have hrank : 1 ≤ Module.finrank ℂ (G etaLD) := Submodule.one_le_finrank_iff.mpr hGne
  have hr0R : (0 : ℝ) < Module.finrank ℂ W0 := by
    exact_mod_cast (by omega : 0 < Module.finrank ℂ W0)
  have hrR : (0 : ℝ) < Module.finrank ℂ (G etaLD) := by
    exact_mod_cast (by omega : 0 < Module.finrank ℂ (G etaLD))
  have hlogInitial : Real.log (Module.finrank ℂ W0 : ℝ) ≤
      Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
        Kb / (b / 2) * (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3 := by
    have h := Real.log_le_log hr0R hWdim
    rwa [Real.log_mul hrR.ne' (Real.exp_ne_zero _), Real.log_exp] at h
  obtain ⟨hqm, hm, _hlogm, _hlogmup⟩ := Real.regularized_filter_count_base_bounds q hq
  let D : ℕ → ℕ := fun i ↦
    let mi := m * 2 ^ i
    let ui := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
    let ell : ℕ := ⌈Cf * ui ^ 2 / g⌉₊
    (mi * ell ^ 2) ^ (22 * ell)
  let Kf := 22 * (Cf + 1) * (6 + 2 * Real.log (Cf + 1)) / g
  have hCf1 : 1 ≤ Cf := (by norm_num : (1 : ℝ) ≤ 100).trans hCf
  have hKf : 0 ≤ Kf := by
    have hlog := Real.log_nonneg (by linarith only [hCf] : 1 ≤ Cf + 1)
    dsimp only [Kf]
    positivity
  have hmi (i : ℕ) : 2 ≤ m * 2 ^ i :=
    hm.trans (Nat.le_mul_of_pos_right m (pow_pos (by decide) i))
  have hD (i : ℕ) : 1 ≤ D i := by
    obtain ⟨_, _, _, hDpos, _, _⟩ :=
      Real.polynomial_filter_count_bounds Cf (m * 2 ^ i) g hCf1 (hmi i) hg hg1
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hDpos.ne')
  have hlogD (i : ℕ) : Real.log (D i : ℝ) ≤
      Kf * (1 + Real.log ((m * 2 ^ i : ℕ) : ℝ) + Real.log (1 / g)) ^ 3 :=
    (Real.polynomial_filter_count_bounds Cf (m * 2 ^ i) g hCf1 (hmi i) hg hg1).2.2.2.2.2
  obtain ⟨hp, hsum, hentropy, htailOfViable⟩ :=
    Submodule.unit_cut_spectral_probability Tm (G (etaLD - v)) ψ hψG hψ
  let coord := (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm (Tm ψ)
  let Cψ := Matrix.schmidtCoeffMatrix (WithLp.ofLp coord)
  let hρ := Matrix.posSemidef_self_mul_conjTranspose Cψ
  let probability := hρ.isHermitian.eigenvalues₀
  have htail (i : ℕ) (_hi : i < Fintype.card (J → Fin q)) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin (Fintype.card (J → Fin q)) ↦
        Module.finrank ℂ W0 * D 0 ^ 24 * D i ^ 2 ≤ a.val), probability a) ≤
          1 / (2 : ℝ) ^ (i + 1) := by
    obtain ⟨_hell, _hlog, A, hA⟩ :=
      hrefine L q m p r i (b / 6) hq hqm hpr hrL hw h hs h0 h1
    have hbuffer : 6 * (b / 6) ≤ etaLD - b / 2 := by linarith only [hbcap, hb]
    obtain ⟨hdim, hV⟩ := hA (etaLD - b / 2) hbuffer (by linarith only [hb]) W0 hW0
    have hVraw : Submodule.IsViable (F := EE) (1 / (2 : ℝ) ^ (i + 1))
        (⨆ j : Fin (D i ^ 2), W0.map (A j).toLinearMap)
        ((G (etaLD - b)).map Tm.toLinearEquiv.toLinearMap) := by
      simpa only [show etaLD - b / 2 - 3 * (b / 6) = etaLD - b by ring] using hV
    have hVinner := hVraw.of_target_le
      (Submodule.map_mono (hG (a := etaLD - v) (c := etaLD - b)
        (by linarith only [hbv])))
    have hdim' : Module.finrank ℂ ↥(⨆ j : Fin (D i ^ 2), W0.map (A j).toLinearMap) ≤
        Module.finrank ℂ W0 * D 0 ^ 24 * D i ^ 2 := by
      calc
        _ ≤ D i ^ 2 * Module.finrank ℂ W0 := hdim
        _ = Module.finrank ℂ W0 * D i ^ 2 := Nat.mul_comm _ _
        _ ≤ _ := by
          have hp : 1 ≤ D 0 ^ 24 :=
            Nat.one_le_pow 24 (D 0) (lt_of_lt_of_le Nat.zero_lt_one (hD 0))
          have hmul := Nat.mul_le_mul_left (Module.finrank ℂ W0) hp
          simpa only [mul_one] using Nat.mul_le_mul_right (D i ^ 2) hmul
    have hdelta : (1 : ℝ) / 2 ^ (i + 1) < 1 := by
      apply (div_lt_one (by positivity)).mpr
      have hp : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      nlinarith only [hp]
    exact htailOfViable _ _ _ hdelta hdim' hVinner
  have hraw := Entropy.probabilityEntropy_le_of_logarithmic_rank_tail_bounds
    m (Module.finrank ℂ W0) g Kf D hm hr0 hg hg1 hKf hD hlogD probability hp hsum htail
  have hactual := (Submodule.actualRegionSplit_marginal_and_entropy
    (n := fun _ : Fin L ↦ q) J ψ).2
  have hEntropy : Entropy.regionEntropy J ψ ≤
      Real.log (Module.finrank ℂ W0 : ℝ) + 676 * Kf * u ^ 3 + 54 * Real.log 2 := by
    rw [← hactual, hentropy]
    exact hraw
  have hcoef : 676 * Kf * u ^ 3 =
      14872 * (Cf + 1) * (6 + 2 * Real.log (Cf + 1)) / g * u ^ 3 := by
    dsimp only [Kf]
    ring
  rw [hcoef] at hEntropy
  linarith only [hEntropy, hlogInitial]

end TNLean.MPS.AreaLaw
