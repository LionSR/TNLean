/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGSharpApproximation
import TNLean.MPS.AreaLaw.MPSApproximation
import QICLean.Analysis.ViableSubspaceEntropy
import QICLean.Channel.MaximalOverlap

/-!
# One physical matrix product approximant at all cuts

Fixed-cut normalized approximants control the discarded spectral mass of the
original marginals. The output vector is the single sequential truncation
onto their leading eigenspaces, followed by normalization. This supports the
global matrix product state conclusion of ALVV, arXiv:1602.08828v2,
Theorem 4.9, source lines 1080–1086.

**Local fix (parameter choice):** The independent scales are documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Scope restriction (gap dependence):** The bound uses `min gamma 1`.
Comparison with the printed quantitative dependence is for `0 < gamma ≤ 1`;
the larger-gap comparison remains as recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

The distinct spectral values express Assumption (DG) of the source,
lines 275–279, which requires a second smallest eigenvalue.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- The actual normalized regional rank approximant controls the original
marginal's missing leading mass. The coordinate map is constructed internally.
This is the Ky Fan step in ALVV, arXiv:1602.08828v2, proof of Theorem 4.9,
source lines 1080–1086. -/
private theorem one_sub_regional_kyFanNorm_le_twice_error
    {L q : ℕ} (J : Finset (Fin L))
    (ψ φ : EuclideanSpace ℂ (Fin L → Fin q)) (hφ : ‖φ‖ = 1)
    (delta : ℝ) (hdelta1 : delta ≤ 1) (D : ℕ) :
    let beta := fun _ : Fin L ↦ Fin q
    let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
      (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
      (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
    let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm
    Matrix.schmidtRank (WithLp.ofLp (e φ)) ≤ D →
    1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ →
    1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) J ψ).kyFanNorm D ≤
      2 * delta := by
  intro beta tau U Phi Tm e hrank hoverlap
  have hφe : ‖e φ‖ = 1 := by simpa only [LinearIsometryEquiv.norm_map] using hφ
  have hinner : ‖⟪e ψ, e φ⟫_ℂ‖ = ‖⟪φ, ψ⟫_ℂ‖ := by
    rw [e.inner_map_map, norm_inner_symm]
  have hmass := Matrix.normSq_inner_le_kyFanNorm (e ψ) (e φ) hφe D hrank
  rw [hinner] at hmass
  have hactual : Matrix.schmidtCoeffMatrix (WithLp.ofLp (e ψ)) *
      (Matrix.schmidtCoeffMatrix (WithLp.ofLp (e ψ)))ᴴ = Entropy.regionState J ψ :=
    (Submodule.actualRegionSplit_marginal_and_entropy (n := fun _ : Fin L ↦ q) J ψ).1
  have hmass' : ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ≤
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) J ψ).kyFanNorm D := by
    simpa only [hactual] using hmass
  have hsquare := pow_le_pow_left₀ (by linarith only [hdelta1] : 0 ≤ 1 - delta) hoverlap 2
  nlinarith only [hsquare, hmass', sq_nonneg delta]

/-- An integer rank below a logarithmic budget is bounded by the ground-space
factor times a single rounded exponential. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem 4.9, global approximation at source line 1086. -/
private theorem rank_le_mul_ceil_exp {s r : ℕ} (hr : 1 ≤ r) (E : ℝ)
    (hlog : Real.log (s : ℝ) ≤ Real.log (r : ℝ) + E) :
    s ≤ r * ⌈Real.exp E⌉₊ := by
  by_cases hs : s = 0
  · simp only [hs, Nat.zero_le]
  · have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hspos, Real.exp_add, Real.exp_log hrpos] at hexp
    have hbound : (s : ℝ) ≤ ((r * ⌈Real.exp E⌉₊ : ℕ) : ℝ) := by
      calc
        (s : ℝ) ≤ (r : ℝ) * Real.exp E := hexp
        _ ≤ (r : ℝ) * (⌈Real.exp E⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.le_ceil _) hrpos.le
        _ = _ := by rw [Nat.cast_mul]
    exact_mod_cast hbound

/-- Uniform missing marginal mass gives one normalized sequential matrix
product state, rather than a collection of cut-dependent vectors. Auxiliary
to ALVV, arXiv:1602.08828v2, Theorem 4.9, source line 1086; the product estimate
is Verstraete--Cirac Proposition 7.1 in the one-dimensional note. -/
private theorem exists_unit_mps_of_uniform_prefix_mass
    {L q : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
    (D : ℕ) (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htail : ∀ k ∈ Finset.Ico 1 L,
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm D ≤ delta / (8 * ((L : ℝ) + 1))) :
    ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
      IsOpenMPS L q D (fun x ↦ Φ x) ∧ 1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ ∧
      ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  have hLpos : 0 < (L : ℝ) + 1 := by positivity
  have hcard : ((Finset.Ico 1 L).card : ℝ) ≤ (L : ℝ) + 1 := by
    exact_mod_cast (show (Finset.Ico 1 L).card ≤ L + 1 by rw [Nat.card_Ico]; omega)
  have hsum : (∑ k ∈ Finset.Ico 1 L,
      (1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm D)) ≤ delta / 8 := by
    calc
      _ ≤ (Finset.Ico 1 L).card • (delta / (8 * ((L : ℝ) + 1))) :=
        Finset.sum_le_card_nsmul _ _ _ htail
      _ = ((Finset.Ico 1 L).card : ℝ) * (delta / (8 * ((L : ℝ) + 1))) := by
        rw [nsmul_eq_mul]
      _ ≤ ((L : ℝ) + 1) * (delta / (8 * ((L : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = delta / 8 := by field_simp
  let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
    (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
      (leftBlock L k) ψ).leadingEigenprojection D
  let Φ0 := sequentialTruncation P (L - 1) ψ
  have hmps0 : IsOpenMPS L q D (fun x ↦ Φ0 x) :=
    (isOpenMPS_sequentialTruncation_leadingEigenprojection ψ hψ D).1
  have herr : ‖Φ0 - ψ‖ ^ 2 ≤ delta / 8 :=
    (norm_sequentialTruncation_leadingEigenprojection_sub_sq_le ψ hψ D).trans hsum
  have hdistlt : ‖Φ0 - ψ‖ < 1 := by nlinarith only [herr, hdelta1, norm_nonneg (Φ0 - ψ)]
  have hpos : 0 < ‖Φ0‖ := by
    have hn := norm_sub_norm_le ψ Φ0
    rw [hψ, norm_sub_rev] at hn
    linarith only [hn, hdistlt]
  let Φ : EuclideanSpace ℂ (Fin L → Fin q) := (‖Φ0‖ : ℂ)⁻¹ • Φ0
  have hΦ : ‖Φ‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) (norm_pos_iff.mp hpos)
  have hdist : ‖Φ - ψ‖ ≤ 2 * ‖Φ0 - ψ‖ :=
    norm_inv_norm_smul_sub_le_two_mul hψ (norm_pos_iff.mp hpos)
  have hsq : ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    nlinarith only [hs, herr]
  have hoverlap : 1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ := by
    have heq := norm_sub_sq (𝕜 := ℂ) Φ ψ
    simp only [hΦ, hψ, one_pow, RCLike.re_to_complex] at heq
    have hre := Complex.re_le_norm (⟪Φ, ψ⟫_ℂ)
    nlinarith only [heq, hre, hsq, hdelta]
  exact ⟨Φ, hΦ, hmps0.smul (‖Φ0‖ : ℂ)⁻¹, hoverlap, hsq⟩

/-- Rounding a nonnegative exponential costs at most one in its logarithm.
Auxiliary to the integer bond bound in ALVV, arXiv:1602.08828v2,
Theorem 4.9, source line 1086. -/
private theorem log_ceil_exp_le_add_one (E : ℝ) (hE : 0 ≤ E) :
    1 ≤ ⌈Real.exp E⌉₊ ∧ Real.log (⌈Real.exp E⌉₊ : ℝ) ≤ E + 1 := by
  have hexp : 1 ≤ Real.exp E := Real.one_le_exp hE
  have hB : 1 ≤ ⌈Real.exp E⌉₊ := by exact_mod_cast hexp.trans (Nat.le_ceil _)
  have hBpos : (0 : ℝ) < (⌈Real.exp E⌉₊ : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hB)
  have hupper : (⌈Real.exp E⌉₊ : ℝ) ≤ 2 * Real.exp E := by
    have hceil := (Nat.ceil_lt_add_one (Real.exp_nonneg E)).le
    linarith only [hceil, hexp]
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  refine ⟨hB, ?_⟩
  calc
    Real.log (⌈Real.exp E⌉₊ : ℝ) ≤ Real.log (2 * Real.exp E) :=
      Real.log_le_log hBpos hupper
    _ = Real.log 2 + E := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero E), Real.log_exp]
    _ ≤ E + 1 := by linarith only [hlog2]

/-- Every original ground vector has one normalized open-boundary matrix
product approximant with simultaneous bond control at all cuts. The factor
beyond the ground-space dimension is chosen before the vector. The proof
constructs one sequential projection product and then normalizes it.
Supporting ALVV, arXiv:1602.08828v2, Theorem 4.9, global conclusion,
source lines 1080–1086. -/
theorem exists_physical_dg_normalized_isOpenMPS_approximation :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ),
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let b := 16 + Real.log (1 / g) + Real.log (16 * ((L : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ G * B) (fun x ↦ Φ x) ∧
        1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  obtain ⟨K, hK, hfixed⟩ := exists_physical_dg_interval_normalized_approximation
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  intro L q h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G g u
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  intro delta hdelta hdelta1 b
  let deltaCut := delta / (16 * ((L : ℝ) + 1))
  have hden : 0 < 16 * ((L : ℝ) + 1) := by positivity
  have hcut : 0 < deltaCut := div_pos hdelta hden
  have hcut1 : deltaCut ≤ 1 := by
    apply (div_le_iff₀ hden).2
    have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith only [hdelta1, hL]
  have hrecip : 1 / deltaCut = 16 * ((L : ℝ) + 1) / delta := by
    dsimp only [deltaCut]
    field_simp
  have hb : 16 ≤ b := by
    have hlogcut := Real.log_nonneg ((one_le_div hcut).2 hcut1)
    rw [hrecip] at hlogcut
    dsimp only [b]
    linarith only [hlogg, hlogcut]
  let F := u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u
  have hbase : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
    linarith only [hu3, hg1])
  have hroot : 0 ≤ (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by positivity
  have hsum : 1 ≤ u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by
    linarith only [hbase, hroot]
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by linarith only [hb])
  have hF : 1 ≤ F := hsum
  have hPone : 1 ≤ 1 + Real.log b := by linarith only [hlogb]
  have hFP : 1 ≤ F * (1 + Real.log b) := by
    simpa only [one_mul] using
      (mul_le_mul hF hPone (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hF))
  let E := K * F * (1 + Real.log b)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg hK.le (zero_le_one.trans hF))
    (zero_le_one.trans hPone)
  let B : ℕ := ⌈Real.exp E⌉₊
  obtain ⟨hB, hlogB⟩ := log_ceil_exp_le_add_one E hE
  refine ⟨B, hB, ?_, ?_⟩
  · change Real.log (B : ℝ) ≤ (K + 1) * F * (1 + Real.log b)
    change Real.log (B : ℝ) ≤ E + 1 at hlogB
    dsimp only [E] at hlogB
    nlinarith only [hlogB, hFP]
  · intro ψ hψG hψ
    have htail : ∀ k ∈ Finset.Ico 1 L,
        1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
          (leftBlock L k) ψ).kyFanNorm (Module.finrank ℂ G * B) ≤
            delta / (8 * ((L : ℝ) + 1)) := by
      intro k hk
      have hkL : k ≤ L := (Finset.mem_Ico.mp hk).2.le
      obtain ⟨φ, hφ, hoverlap, hlogrank⟩ :=
        hfixed L q 0 k (Nat.zero_le k) hkL h hs h0 h1 mu nu gamma hgamma
          hmu hnu hmunu hgap deltaCut hcut hcut1 ψ hψG hψ
      rw [hrecip] at hlogrank
      have hregional := one_sub_regional_kyFanNorm_le_twice_error
        (interval L 0 k) ψ φ hφ deltaCut hcut1 (Module.finrank ℂ G * B)
        (rank_le_mul_ceil_exp hrG E hlogrank) hoverlap
      rw [leftBlock_eq_interval]
      convert hregional using 1
      dsimp only [deltaCut]
      field_simp; ring
    exact exists_unit_mps_of_uniform_prefix_mass ψ hψ (Module.finrank ℂ G * B)
      delta hdelta hdelta1 htail

end TNLean.MPS.AreaLaw
