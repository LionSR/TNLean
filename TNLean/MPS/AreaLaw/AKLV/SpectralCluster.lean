/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.EuclideanEigenvectorBasis
import TNLean.MPS.AreaLaw.AKLV.Normalization
import QICLean.Analysis.GaussianFilter.SpectralGap
import QICLean.Analysis.LowEnergyCluster

/-!
# The actual low spectral cluster of the two exterior truncations

The original unit ground vector and global gap identify a one-dimensional low
cluster of the actual two-exterior truncation. Its full cutoff band is empty,
and its spectral subspace approaches the original ground line at the prescribed
accuracy. A canonical eigenvector is the unique unit ground vector up to phase,
with gap at least `9*g/10` and squared phase error at most `tau/100`.
The restricted residuals are constructed from the original bonds.

Source: AKLV, arXiv:1301.1162v1, Section 6.3, proof of Theorem 6.1.
This is a quantitative low-cluster comparison, above an explicit threshold derived
from the physical exponential tail. It does not assume a perturbation estimate.

**Local fixes (energy shift and spectral windows):** The actual aggregate middle
normalization uses the corrected count from
`docs/paper-gaps/aklv13_two_block_robustness.tex`. The finite-window comparison
uses the corrected count documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.
Only the original nearest-neighbour geometry is considered; the source's arbitrary
exterior-operator formulation and comparison with its printed threshold are separate.
-/

open Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- An explicit threshold for the actual two-block spectral comparison.
It absorbs the derived original-bond exponential residual at squared projection
accuracy `tau/200`. Auxiliary to AKLV, arXiv:1301.1162v1, Theorem 6.1;
no identification with the source's printed threshold is asserted. -/
noncomputable def aklvTwoBlockThreshold (g tau : ℝ) : ℝ :=
  max (g + 11)
    (g + 8 * Real.log ((1000000 * (64 * Real.exp (3 / 4))) / (tau * g)))

private theorem aklv_two_block_threshold_bounds {g tau t : ℝ}
    (hg : 0 < g) (htau : 0 < tau) (ht : aklvTwoBlockThreshold g tau ≤ t) :
    g + 11 ≤ t ∧ (64 * Real.exp (3 / 4)) * Real.exp (-(t - g) / 8) ≤
      tau * g / 1000000 := by
  let C : ℝ := 64 * Real.exp (3 / 4)
  let D : ℝ := (1000000 * C) / (tau * g)
  have hC : 0 < C := by positivity
  have hD : 0 < D := by positivity
  have ht0 : g + 11 ≤ t := (le_max_left _ _).trans ht
  have htlog : g + 8 * Real.log D ≤ t := (le_max_right _ _).trans ht
  have hexp : Real.exp (-(t - g) / 8) ≤ D⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log D) := Real.exp_le_exp.mpr (by linarith)
      _ = D⁻¹ := by rw [Real.exp_neg, Real.exp_log hD]
  have hcancel : C * D⁻¹ = tau * g / 1000000 := by
    dsimp only [D]
    field_simp
  exact ⟨ht0, (mul_le_mul_of_nonneg_left hexp hC.le).trans hcancel.le⟩

open Classical in
/-- The two exterior truncations have one low spectral line, separated by a
uniform interval, and approximating the original ground line. The actual
canonical ground eigenvector has gap at least `9*g/10` and squared phase error
at most `tau/100`. All physical operators and both restricted residuals are
constructed internally. Auxiliary
to AKLV, arXiv:1301.1162v1, Theorem 6.1 and its proof in Section 6.3. -/
theorem exists_aklv_two_block_scaled_low_cluster {L q a s : ℕ} (hq : 0 < q)
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) :
    ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ tau t : ℝ, 0 < tau → tau ≤ 1 → aklvTwoBlockThreshold g tau ≤ t →
        let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t
        ∃ hB : ∀ T, (B T).IsHermitian,
          let v := (hB Finset.univ).eigenvectorBasis
          let lam := (hB Finset.univ).eigenvalues
          let U := Submodule.spectralSpanLE v lam (E0 + g / 20)
          U = Submodule.spectralSpanLE v lam (E0 + 19 * g / 20) ∧
            Module.finrank ℂ U = 1 ∧
            Submodule.IsCloseTo (tau / 200) U (Submodule.span ℂ {Ω}) ∧
            Submodule.IsCloseTo (tau / 200) (Submodule.span ℂ {Ω}) U ∧
            (∀ w : ℝ, E0 + g / 20 ≤ w → w ≤ E0 + 19 * g / 20 →
              Submodule.spectralSpanLE v lam w = U) ∧
            (∀ j, lam j ≤ E0 + g / 10 ∨ E0 + 9 * g / 10 ≤ lam j) ∧
            ∃ j0, lam j0 ≤ E0 + g / 20 ∧
              (∀ j, j ≠ j0 → lam j0 + 9 * g / 10 ≤ lam j) ∧
              ∃ θ : ℝ, ‖v j0 - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ tau / 100 := by
  obtain ⟨e, x, z, E0, hx, hxe, he, _he0, hz, hzE, hE, hE0, hE6, hres⟩ :=
    exists_aklv_normalized_two_block_residual hq hs ha h hsupp h0 h1
  let S : ℝ := ∑ j, e j
  let H := (∑ i, h i) - (S : ℂ) • 1
  have hΩunit : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hΩ]
    norm_num
  have hQ := Matrix.one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one
    (WithLp.ofLp Ω) (by simpa only [← EuclideanSpace.norm_sq_eq, hΩ, one_pow]
      using (le_refl (1 : ℝ)))
  have hrawlow : ((∑ i, h i) - (mu : ℂ) • 1).PosSemidef := by
    simpa only [sub_add_cancel] using hgap.add (hQ.smul (Complex.zero_le_real.mpr hg.le))
  have hshift : H - ((mu - S : ℝ) : ℂ) • 1 = (∑ i, h i) - (mu : ℂ) • 1 := by
    dsimp only [H]
    rw [Complex.ofReal_sub, sub_smul]
    abel
  have hNΩ : H *ᵥ WithLp.ofLp Ω = ((mu - S : ℝ) : ℂ) • WithLp.ofLp Ω := by
    dsimp only [H]
    rw [sub_mulVec, smul_mulVec, one_mulVec, hground, Complex.ofReal_sub, sub_smul]
  have hEeq : E0 = mu - S := Matrix.groundEnergy_eq_of_normalized_eigenvectors
    H E0 (mu - S) z (WithLp.ofLp Ω) hzE hz hNΩ hΩunit hE (by rw [hshift]; exact hrawlow)
  have hNΩ' : H *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω := by
    rw [hEeq]
    exact hNΩ
  have hNgap : (H - (E0 : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    rw [hEeq, hshift]
    exact hgap
  refine ⟨e, E0, ⟨x, hx, hxe, he⟩,
    by change E0 + S = mu; linarith, hE0, hE6, ?_⟩
  intro tau t htau htau1 ht B
  obtain ⟨ht11, htail⟩ := aklv_two_block_threshold_bounds hg htau ht
  obtain ⟨hB, hcenter, hresFull⟩ := hres g t hg.le ht11
  change B ∅ = H at hcenter
  let b0 := (hB ∅).eigenvectorBasis
  let a0 := (hB ∅).eigenvalues
  let v := (hB Finset.univ).eigenvectorBasis
  let lam := (hB Finset.univ).eigenvalues
  let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
  let ξ := (64 * Real.exp (3 / 4)) * Real.exp (-(t - g) / 8)
  have hξ : 0 ≤ ξ := by positivity
  have hEigen (T : Finset (Fin 2)) (j : Fin L → Fin q) :
      ι (B T) ((hB T).eigenvectorBasis j) =
        ((hB T).eigenvalues j : ℂ) • (hB T).eigenvectorBasis j := by
    exact (hB T).toEuclideanCLM_eigenvectorBasis j
  have hBΩ : B ∅ *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω := by
    rw [hcenter]
    exact hNΩ'
  have hBgap : (B ∅ - (E0 : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    rw [hcenter]
    exact hNgap
  have hdich (j : Fin L → Fin q) :
      (a0 j = E0 ∧ b0 j = ⟪Ω, b0 j⟫_ℂ • Ω) ∨
        (g ≤ a0 j - E0 ∧ ⟪b0 j, Ω⟫_ℂ = 0) :=
    GaussianFilter.eigenvector_ground_or_gap (hB ∅) hΩ hBΩ hBgap hg j
  have hspec (j : Fin L → Fin q) : a0 j = E0 ∨ E0 + g ≤ a0 j := by
    rcases hdich j with h | h
    · exact Or.inl h.1
    · exact Or.inr (by linarith [h.1])
  have hsmall (T : Finset (Fin 2)) (η : ℝ) (hη : η ≤ g) :
      ‖(ι (B ∅) - ι (B Finset.univ)).domRestrict
        (Submodule.spectralSpanLE (hB T).eigenvectorBasis (hB T).eigenvalues (E0 + η))‖ ≤ ξ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hξ
    intro w
    have hmem : (w : EuclideanSpace ℂ (Fin L → Fin q)) ∈
        Submodule.spectralSpanLE (hB T).eigenvectorBasis (hB T).eigenvalues (E0 + g) :=
      (Submodule.mem_spectralSpanLE_iff _ _ _ _).mpr (by
        intro j hj
        exact (Submodule.mem_spectralSpanLE_iff _ _ _ _).mp
          w.property j (by linarith))
    have hbound := ((ι (H - B Finset.univ)).domRestrict
      (Submodule.spectralSpanLE
        (hB T).eigenvectorBasis (hB T).eigenvalues (E0 + g))).le_of_opNorm_le
        (hresFull T) ⟨w, hmem⟩
    change ‖(ι (H - B Finset.univ)) (w : EuclideanSpace ℂ (Fin L → Fin q))‖ ≤
      ξ * ‖(w : EuclideanSpace ℂ (Fin L → Fin q))‖ at hbound
    change ‖(ι (B ∅) - ι (B Finset.univ))
      (w : EuclideanSpace ℂ (Fin L → Fin q))‖ ≤
        ξ * ‖(w : EuclideanSpace ℂ (Fin L → Fin q))‖
    simpa only [map_sub, ← hcenter] using hbound
  obtain ⟨hUV, hdim, hUG, hGU, hwindow, hnewspec⟩ :=
    Submodule.low_spectral_cluster_of_scaled_restricted_residuals
      (ι (B ∅)) (ι (B Finset.univ)) b0 v a0 lam (hEigen ∅) (hEigen Finset.univ)
      E0 g ξ tau hg htau htau1 hξ htail hspec
      (hsmall ∅ (g / 40) (by linarith))
      (hsmall Finset.univ (19 * g / 20) (by linarith))
  have hG : Submodule.spectralSpanLE b0 a0 E0 = Submodule.span ℂ {Ω} := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      change a0 j ≤ E0 at hj
      rcases hdich j with h | h
      · rw [h.2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton Ω))
      · exfalso
        linarith [h.1]
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      rw [Submodule.mem_spectralSpanLE_iff]
      intro j hj
      rcases hdich j with h | h
      · exfalso
        linarith [h.1]
      · rw [OrthonormalBasis.repr_apply_apply, h.2]
  have hdimG : Module.finrank ℂ (Submodule.span ℂ {Ω}) = 1 :=
    finrank_span_singleton (by intro hzero; simp [hzero] at hΩ : Ω ≠ 0)
  let U := Submodule.spectralSpanLE v lam (E0 + g / 20)
  have hdimU : Module.finrank ℂ U = 1 := hdim.trans ((congrArg
    (fun W : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) ↦ Module.finrank ℂ W)
    hG).trans hdimG)
  have hsome : ∃ j0, lam j0 ≤ E0 + g / 20 := by
    by_contra! hn
    have hset : {j | lam j ≤ E0 + g / 20} = (∅ : Set (Fin L → Fin q)) := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (hn j)
    have hUzero : U = ⊥ := by simp [U, Submodule.spectralSpanLE, hset]
    have hdimZero : Module.finrank ℂ U = 0 :=
      (congrArg
        (fun W : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) ↦ Module.finrank ℂ W)
        hUzero).trans (finrank_bot ℂ _)
    omega
  obtain ⟨j0, hj0⟩ := hsome
  have hj0mem : v j0 ∈ U := Submodule.subset_span ⟨j0, hj0, rfl⟩
  have hUSpan : U = Submodule.span ℂ {v j0} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdimU hj0mem (v.toBasis.ne_zero j0)
  have hlowunique (j : Fin L → Fin q) (hj : lam j ≤ E0 + 19 * g / 20) : j = j0 := by
    have hjmem : v j ∈ U := by
      rw [show U = Submodule.spectralSpanLE v lam (E0 + 19 * g / 20) from hUV]
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    rw [hUSpan] at hjmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hjmem
    by_contra hjne
    have hc0 : c = 0 := by
      have hh := congrArg (fun w ↦ v.repr w j0) hc
      simpa [hjne] using hh
    rw [hc0, zero_smul] at hc
    exact v.toBasis.ne_zero j hc.symm
  have hGU' : Submodule.IsCloseTo (tau / 200) (Submodule.span ℂ {Ω}) U := by
    simpa only [hG] using hGU
  have hmass := Submodule.isCloseTo_iff.mp hGU' (v j0) hj0mem
  rw [v.norm_eq_one, one_pow, Submodule.starProjection_unit_singleton ℂ hΩ,
    norm_smul, hΩ, mul_one] at hmass
  obtain ⟨θ, _hmin, hphase⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap
    (Δ := 1) (ε := tau / 200) (by norm_num) (v.norm_eq_one j0) hΩ
    (by linarith : (1 : ℝ) * (1 - ‖⟪Ω, v j0⟫_ℂ‖ ^ 2) ≤ tau / 200)
  refine ⟨hB, hUV, hdimU, ?_, ?_, fun w hw0 hw1 ↦ (hwindow w hw0 hw1).1,
    hnewspec, j0, hj0, ?_, θ, ?_⟩
  · simpa only [hG] using hUG
  · simpa only [hG] using hGU
  · intro j hj
    have hhigh : E0 + 19 * g / 20 < lam j := by
      by_contra! hnot
      exact hj (hlowunique j hnot)
    linarith
  · linarith

end TNLean.MPS.AreaLaw
