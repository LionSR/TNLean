/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.FavorableFilter
import QICLean.Analysis.NormSquaredTriangle
import QICLean.Channel.FilterNormalization
import QICLean.Entropy.FilterPrefix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Physical product-overlap initialization for AKLV

The product vector is chosen for the actual clipped ground vector, rather
than for the original ground vector. Applying the constructed favorable
filter first, and choosing the phase of its normalized output, gives a unit
vector of controlled cut rank close to both targets.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, the initial step in Lemma `l:5`,
lines 1016--1024, using Lemma 2.2 for the clipped target.

**Scope restriction (available window):** The uniformly selected window must
fit in the chain. Its width is at least twenty-one and uses the normalization
and support conventions of `docs/paper-gaps/aklv13_two_block_robustness.tex`.
The later changing-target sequence and finite boundary cases remain separate.

**Local fix (initial product overlap):** Source line 1023 prints the overlap
inequality in the opposite direction and names the original target. Here
Lemma 2.2 is applied to the clipped target fixed by the constructed filter;
see `docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem exists_cut_product_filtered_output {L q k D : ℕ}
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (φ : EuclideanSpace ℂ (Fin L → Fin q)) (hφ : ‖φ‖ = 1)
    (hfix : toEuclideanLin K φ = φ) {delta : ℝ} (hdelta : 0 ≤ delta) (hD : 0 < D)
    (hperp : ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
      ⟪φ, toEuclideanLin K ψ⟫_ℂ = 0 ∧ ‖toEuclideanLin K ψ‖ ^ 2 ≤ delta)
    (hrank : operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) K) ≤ D) (htrade : (D : ℝ) * delta ≤ 1 / 2) :
    ∃ (χ : EuclideanSpace ℂ (Fin L → Fin q))
      (u : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) → ℂ)
      (v : ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q) → ℂ) (c : ℂ),
      ‖χ‖ = 1 ∧ Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) χ =
        WithLp.toLp 2 (fun z ↦ u z.1 * v z.2) ∧
      1 / Real.sqrt (2 * (D : ℝ)) ≤ ‖⟪φ, χ⟫_ℂ‖ ∧
      toEuclideanLin K χ ≠ 0 ∧ ‖c‖ = 1 ∧
      let ψ := c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ
      ‖ψ‖ = 1 ∧
      schmidtRank (WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ)) ≤ D ∧ ‖ψ - φ‖ ^ 2 ≤ 4 * (D : ℝ) * delta := by
  classical
  let cut := leftBlock L k
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Entropy.cutEquiv (fun _ : Fin L ↦ q) cut)
  let Kcut := Entropy.cutOperator (n := fun _ : Fin L ↦ q) cut K
  have hU (x : EuclideanSpace ℂ (Fin L → Fin q)) : U x = Entropy.cutVector cut x := by
    ext z
    rfl
  have hintertwine (x : EuclideanSpace ℂ (Fin L → Fin q)) :
      toEuclideanLin Kcut (U x) = U (toEuclideanLin K x) := by
    simpa only [hU] using (Entropy.cutVector_toEuclideanLin cut K x).symm
  have hφcut : ‖U φ‖ = 1 := (U.norm_map φ).trans hφ
  have hfixcut : toEuclideanLin Kcut (U φ) = U φ :=
    (hintertwine φ).trans (congrArg U hfix)
  have hperpcut : ∀ x, ‖x‖ = 1 → ⟪U φ, x⟫_ℂ = 0 →
      ⟪U φ, toEuclideanLin Kcut x⟫_ℂ = 0 ∧ ‖toEuclideanLin Kcut x‖ ^ 2 ≤ delta := by
    intro x hx horth
    obtain ⟨horthK, hnormK⟩ := hperp (U.symm x) ((U.symm.norm_map x).trans hx)
      ((U.inner_map_eq_flip φ x).symm.trans horth)
    have hKx : toEuclideanLin Kcut x = U (toEuclideanLin K (U.symm x)) := by
      simpa only [U.apply_symm_apply] using hintertwine (U.symm x)
    constructor
    · simpa only [hKx, U.inner_map_map] using horthK
    · simpa only [hKx, U.norm_map] using hnormK
  obtain ⟨u, v, hx, hoverlap⟩ := exists_unit_product_overlap_ge_of_operatorSchmidtRank
    Kcut (U φ) hφcut hfixcut hperpcut hrank htrade
  let x := WithLp.toLp 2 (fun z : _ × _ ↦ u z.1 * v z.2)
  change ‖x‖ = 1 at hx
  change 1 / Real.sqrt (2 * (D : ℝ)) ≤ ‖⟪U φ, x⟫_ℂ‖ at hoverlap
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have haSq : 1 / (2 * (D : ℝ)) ≤ ‖⟪U φ, x⟫_ℂ‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / Real.sqrt (2 * (D : ℝ))) hoverlap 2
    simpa only [div_pow, one_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (D : ℝ))] using hh
  have ha0 : ⟪U φ, x⟫_ℂ ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at haSq
    exact (not_le_of_gt (by positivity : (0 : ℝ) < 1 / (2 * (D : ℝ)))) haSq
  have hres : ‖x - ⟪U φ, x⟫_ℂ • U φ‖ ^ 2 ≤ 1 := by
    have hp := (Submodule.span ℂ {U φ})ᗮ.norm_starProjection_apply_le x
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℂ hφcut] at hp
    simpa only [hx, one_pow] using pow_le_pow_left₀ (norm_nonneg _) hp 2
  obtain ⟨hKx0, c, hc, hψunit, hψrank, hψerror⟩ :=
    exists_phase_normalized_filter_output_of_operatorSchmidtRank Kcut (U φ) x
      hφcut hfixcut delta hperpcut ha0
  let y := c • (‖toEuclideanLin Kcut x‖⁻¹ : ℂ) • toEuclideanLin Kcut x
  change ‖y‖ = 1 at hψunit
  change schmidtRank (WithLp.ofLp y) ≤ operatorSchmidtRank Kcut * schmidtRank (WithLp.ofLp x)
    at hψrank
  change ‖y - U φ‖ ^ 2 ≤
    2 * delta * ‖x - ⟪U φ, x⟫_ℂ • U φ‖ ^ 2 / ‖⟪U φ, x⟫_ℂ‖ ^ 2 at hψerror
  have hxrank : schmidtRank (WithLp.ofLp x) ≤ 1 :=
    schmidtRank_product_le_one u v
  have hyrank : schmidtRank (WithLp.ofLp y) ≤ D :=
    hψrank.trans (by simpa only [mul_one] using Nat.mul_le_mul hrank hxrank)
  have hyerror : ‖y - U φ‖ ^ 2 ≤ 4 * (D : ℝ) * delta := by
    calc
      _ ≤ 2 * delta * ‖x - ⟪U φ, x⟫_ℂ • U φ‖ ^ 2 / ‖⟪U φ, x⟫_ℂ‖ ^ 2 := hψerror
      _ ≤ 2 * delta / ‖⟪U φ, x⟫_ℂ‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hres (by positivity : 0 ≤ 2 * delta)
      _ ≤ 2 * delta / (1 / (2 * (D : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) haSq
      _ = _ := by field_simp; ring
  let χ := U.symm x
  let ψ := U.symm y
  have hχ : U χ = x := U.apply_symm_apply x
  have hψ : U ψ = y := U.apply_symm_apply y
  have haction : toEuclideanLin Kcut x = U (toEuclideanLin K χ) := by
    simpa only [hχ] using hintertwine χ
  have hKχ : toEuclideanLin K χ ≠ 0 := by
    intro hz
    exact hKx0 (by simpa only [hz, map_zero] using haction)
  have hψformula : ψ = c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ := by
    simp only [ψ, y, map_smul, haction, U.symm_apply_apply, U.norm_map]
  refine ⟨χ, u, v, c, (U.symm.norm_map x).trans hx, ?_, ?_, hKχ, hc, ?_, ?_, ?_⟩
  · rw [← hU χ, hχ]
  · simpa only [← U.inner_map_map φ χ, hχ] using hoverlap
  · rw [← hψformula]
    exact (U.symm.norm_map y).trans hψunit
  · rw [← hψformula, ← hU ψ, hψ]
    exact hyrank
  · rw [← hψformula, ← U.norm_map (ψ - φ), map_sub, hψ]
    exact hyerror

/-- A product vector for the actual clipped ground state, followed by its
constructed favorable filter, gives a phase-aligned low-rank unit vector close
to both the clipped and original ground states. AKLV, arXiv:1301.1162v1,
Section 6.1, lines 1016--1024. The product overlap is with the clipped target. -/
theorem exists_aklv_physical_product_initialization :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q a : ℕ)
        (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      (∀ i, 0 ≤ h i) → (∀ i, h i ≤ 1) → ‖Ω‖ = 1 →
      (∑ i, h i) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      ((∑ i, h i) - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ (∑ i, h i) →
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let s : ℕ := ⌈A * u ^ 2 / g⌉₊
      let t0 : ℝ := 1024 + 16 * Real.log (1 / g)
      let D : ℕ := (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
      a + s + 1 ≤ L →
      2 ≤ q ∧ g ≤ 1 ∧ 21 ≤ s ∧
      Real.log (D : ℝ) ≤ 198 * (A + 1) * (6 + 2 * Real.log (A + 1)) / g * u ^ 3 ∧
      ∃ (e : Fin 3 → ℝ) (E0 E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q))
        (p : Polynomial ℝ),
        (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
          (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ x = (e j : ℂ) • x) ∧
          ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef) ∧
        E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
        let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t0 Finset.univ
        B.PosSemidef ∧ ‖B‖ ≤ 2 * t0 + (s : ℝ) ∧ 0 ≤ E ∧ ‖φ‖ = 1 ∧
        toEuclideanLin B φ = (E : ℂ) • φ ∧
        (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
          (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
        ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t0 / 16) / 100 ∧
        p.natDegree = s ^ 2 ∧ p.eval E = 1 ∧
        let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
        toEuclideanLin K φ = φ ∧
        operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
          (leftBlock L (a + s / 2)) K) ≤ D ∧
        ∃ (χ : EuclideanSpace ℂ (Fin L → Fin q))
          (vL : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L (a + s / 2)) → ℂ)
          (vR : ((i : {i : Fin L // i ∉ leftBlock L (a + s / 2)}) → Fin q) → ℂ) (c : ℂ),
          ‖χ‖ = 1 ∧
          Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L (a + s / 2)) χ =
            WithLp.toLp 2 (fun z ↦ vL z.1 * vR z.2) ∧
          1 / Real.sqrt (2 * (D : ℝ)) ≤ ‖⟪φ, χ⟫_ℂ‖ ∧
          toEuclideanLin K χ ≠ 0 ∧ ‖c‖ = 1 ∧
          let ψ := c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ
          ‖ψ‖ = 1 ∧
          schmidtRank (WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q)
            (leftBlock L (a + s / 2)) ψ)) ≤ D ∧
          ‖ψ - φ‖ ^ 2 ≤ 1 / 64 ∧ ‖ψ - Ω‖ ^ 2 ≤ 1 / 16 := by
  obtain ⟨A, hA, hA21, hphysical⟩ := exists_aklv_physical_favorable_filter
  refine ⟨A, hA, hA21, ?_⟩
  intro L q a h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited u s t0 D ha
  obtain ⟨hq, hg1, hs, hdelta, htrade, hlogD, e, E0, E, φ, p,
      hregional, hEeq, hE0, hE6, hBpos, hBnorm, hE, hφ, heigen, hprojector,
      hclose, hdegree, hpE, hfix, hrank, _herr, hperp⟩ :=
    hphysical L q a h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited ha
  let delta : ℝ := 4 * Real.exp (-(4 * (s ^ 2 : ℕ) *
    Real.sqrt ((9 * g / 10) / (2 * t0 + (s : ℝ)))))
  change 0 < delta at hdelta
  change (D : ℝ) * delta ≤ 1 / 100000 at htrade
  have hD : 0 < D := by
    dsimp only [D]
    exact Nat.pow_pos (Nat.mul_pos (by omega) (by omega))
  obtain ⟨χ, vL, vR, c, hχ, hproduct, hoverlap, hKχ, hc, hψ, hψrank, hψclose⟩ :=
    exists_cut_product_filtered_output _ φ hφ hfix hdelta.le hD hperp hrank
      (by linarith)
  let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    Polynomial.aeval (aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t0 Finset.univ) p
  let ψ := c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ
  have hψφ : ‖ψ - φ‖ ^ 2 ≤ 1 / 64 := by
    calc
      _ ≤ 4 * (D : ℝ) * delta := hψclose
      _ ≤ 1 / 64 := by linarith
  have ht0 : 0 ≤ t0 := by
    have hlog : 0 ≤ Real.log (1 / g) :=
      Real.log_nonneg ((le_div_iff₀ hg).mpr (by simpa using hg1))
    dsimp only [t0]
    positivity
  have hφΩ : ‖φ - Ω‖ ^ 2 ≤ 1 / 100 := by
    exact hclose.trans (div_le_div_of_nonneg_right
      (Real.exp_le_one_iff.mpr (by linarith)) (by norm_num))
  have hψΩ : ‖ψ - Ω‖ ^ 2 ≤ 1 / 16 := by
    have hsquare := norm_sub_sq_le_two_mul_add ψ φ Ω
    nlinarith
  exact ⟨hq, hg1, hs, hlogD, e, E0, E, φ, p, hregional, hEeq, hE0, hE6,
    hBpos, hBnorm, hE, hφ, heigen, hprojector, hclose, hdegree, hpE, hfix, hrank,
    χ, vL, vR, c, hχ, hproduct, hoverlap, hKχ, hc, hψ, hψrank, hψφ, hψΩ⟩

end TNLean.MPS.AreaLaw
