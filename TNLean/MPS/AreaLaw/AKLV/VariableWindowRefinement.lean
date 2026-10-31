/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.Initialization

/-!
# Refinement by an actual clipped filter with a variable window

A unit input close to the original ground vector has uniformly nonzero overlap
with the actual clipped ground vector. For every fitting window, threshold and
polynomial degree, the physical clipped Chebyshev construction therefore gives
an actual normalized filtered image. Its error contracts relative to that
clipped target, and its rank retains the sharp window-dependent exponent.

Source: AKLV, arXiv:1301.1162v1, Lemma `l:5`, lines 1025--1052, and the separate
accuracy-dependent window choice in lines 1503--1517.

**Scope restriction (available window):** The window has at least six
interactions and fits in the chain. The actual first excited energy is part of
the original physical data. See `docs/paper-gaps/aklv13_two_block_robustness.tex`.
No approximation sequence, scalar degree optimization or final MPS estimate is
asserted here.
-/

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem normalized_cut_schmidtRank_le {L q k : ℕ}
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) (c : ℂ) (hc : c ≠ 0)
    (hKx : toEuclideanLin K x ≠ 0) :
    let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
    schmidtRank (WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q)
      (leftBlock L k) ψ)) ≤
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
        (leftBlock L k) K) *
      schmidtRank (WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q)
        (leftBlock L k) x)) := by
  change schmidtRank (c • (‖toEuclideanLin K x‖⁻¹ : ℂ) •
    WithLp.ofLp (Entropy.cutVector (leftBlock L k) (toEuclideanLin K x))) ≤ _
  rw [schmidtRank_smul_eq_of_ne_zero c hc,
    schmidtRank_smul_eq_of_ne_zero _ (by
      exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hKx)),
    Entropy.cutVector_toEuclideanLin]
  exact schmidtRank_mulVec_le _ _


/-- The physical clipped filter refines any unit input close to the original
unit ground vector, for every available window and degree. The sharp rank
exponent retains its dependence on the chosen window. AKLV,
arXiv:1301.1162v1, Lemma `l:5`, lines 1025--1052, and lines 1503--1517. -/
theorem exists_aklv_variable_window_filtered_output {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ (∑ i, h i))
    (x : EuclideanSpace ℂ (Fin L → Fin q)) (hx : ‖x‖ = 1)
    (hxΩ : ‖x - Ω‖ ^ 2 ≤ 1 / 16) :
    2 ≤ q ∧ g ≤ 1 ∧ ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ z = (e j : ℂ) • z) ∧
        ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, aklvLogarithmicThreshold g ≤ t →
        let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ
        B.PosSemidef ∧ ‖B‖ ≤ 2 * t + s ∧
        ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
          0 ≤ E ∧ ‖φ‖ = 1 ∧ toEuclideanLin B φ = (E : ℂ) • φ ∧
          (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
            (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
          ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 ∧
          ‖x - φ‖ ^ 2 ≤ 1 / 4 ∧ 1 / 2 ≤ ‖⟪φ, x⟫_ℂ‖ ∧
          ∀ ell : ℕ, ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval E = 1 ∧
            let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
            let D : ℕ := (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))
            let delta : ℝ := (2 * Real.exp (-2 * (ell : ℝ) *
              Real.sqrt ((9 * g / 10) / (2 * t + s)))) ^ 2
            toEuclideanLin K φ = φ ∧
            operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
              (leftBlock L (a + s / 2)) K) ≤ D ∧ toEuclideanLin K x ≠ 0 ∧
            ∃ c : ℂ, ‖c‖ = 1 ∧
              let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
              ‖ψ‖ = 1 ∧
              schmidtRank (WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q)
                (leftBlock L (a + s / 2)) ψ)) ≤
                  D * schmidtRank (WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q)
                    (leftBlock L (a + s / 2)) x)) ∧
              ‖ψ - φ‖ ^ 2 ≤ 8 * delta * ‖x - φ‖ ^ 2 ∧
              ‖ψ - Ω‖ ^ 2 ≤ 16 * delta + Real.exp (-t / 16) / 50 := by
  classical
  obtain ⟨hq, hg1, e, E0, hregional, hEeq, hE0, hE6, hfilter⟩ :=
    exists_aklv_logarithmic_clipped_chebyshev_filter hs ha h hsupp h0 h1
      mu g Ω hΩ hground hgap hg hexcited
  refine ⟨hq, hg1, e, E0, hregional, hEeq, hE0, hE6, ?_⟩
  intro t ht B
  obtain ⟨hBpos, hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose, hpoly⟩ := hfilter t ht
  have ht0 : 0 ≤ t := by
    have hlog : 0 ≤ Real.log (1 / g) :=
      Real.log_nonneg ((le_div_iff₀ hg).mpr (by simpa only [one_mul] using hg1))
    dsimp only [aklvLogarithmicThreshold] at ht
    linarith
  have hφΩ : ‖φ - Ω‖ ^ 2 ≤ 1 / 100 :=
    hclose.trans (div_le_div_of_nonneg_right
      (Real.exp_le_one_iff.mpr (by linarith)) (by norm_num))
  have hxφ : ‖x - φ‖ ^ 2 ≤ 1 / 4 := by
    have hsq := norm_sub_sq_le_two_mul_add x Ω φ
    rw [norm_sub_rev Ω φ] at hsq
    nlinarith
  have hoverlap : 1 / 2 ≤ ‖⟪φ, x⟫_ℂ‖ := by
    have hid := norm_sub_sq (𝕜 := ℂ) φ x
    rw [hφ, hx, norm_sub_rev φ x] at hid
    change ‖x - φ‖ ^ 2 = 1 ^ 2 - 2 * (⟪φ, x⟫_ℂ).re + 1 ^ 2 at hid
    have hre := Complex.re_le_norm ⟪φ, x⟫_ℂ
    nlinarith
  have hoverlap0 : ⟪φ, x⟫_ℂ ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at hoverlap
    linarith
  have hresNorm : ‖x - ⟪φ, x⟫_ℂ • φ‖ ≤ ‖x - φ‖ := by
    have hp := (Submodule.span ℂ {φ})ᗮ.norm_starProjection_apply_le (x - φ)
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℂ hφ] at hp
    have hφφ : ⟪φ, φ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hφ]
    simp only [inner_sub_right, hφφ, sub_smul, one_smul] at hp
    convert hp using 1
    congr 1
    module
  have hres : ‖x - ⟪φ, x⟫_ℂ • φ‖ ^ 2 ≤ ‖x - φ‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hresNorm 2
  have hinner : (1 : ℝ) / 4 ≤ ‖⟪φ, x⟫_ℂ‖ ^ 2 := by nlinarith
  refine ⟨hBpos, hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose, hxφ, hoverlap, ?_⟩
  intro ell
  obtain ⟨p, hdegree, hpE, hfix, _herr, hrank, hperp⟩ := hpoly ell
  let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
  let D : ℕ := (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))
  let delta : ℝ := (2 * Real.exp (-2 * (ell : ℝ) *
    Real.sqrt ((9 * g / 10) / (2 * t + s)))) ^ 2
  obtain ⟨hKx, c, hc, hψunit, hψerror⟩ :=
    exists_phase_normalized_filter_output K φ x hφ hfix delta hperp hoverlap0
  let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
  have hdelta : 0 ≤ delta := sq_nonneg _
  have hcontract : ‖ψ - φ‖ ^ 2 ≤ 8 * delta * ‖x - φ‖ ^ 2 := by
    calc
      _ ≤ 2 * delta * ‖x - ⟪φ, x⟫_ℂ • φ‖ ^ 2 / ‖⟪φ, x⟫_ℂ‖ ^ 2 := hψerror
      _ ≤ 2 * delta * ‖x - φ‖ ^ 2 / ‖⟪φ, x⟫_ℂ‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hres (by positivity)
      _ ≤ 2 * delta * ‖x - φ‖ ^ 2 / (1 / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hinner
      _ = _ := by ring
  have hψΩ : ‖ψ - Ω‖ ^ 2 ≤ 16 * delta + Real.exp (-t / 16) / 50 := by
    have hψφ : ‖ψ - φ‖ ^ 2 ≤ 8 * delta :=
      hcontract.trans (by nlinarith)
    have hsq := norm_sub_sq_le_two_mul_add ψ φ Ω
    nlinarith
  refine ⟨p, hdegree, hpE, hfix, hrank, hKx, c, hc, hψunit, ?_, hcontract, hψΩ⟩
  exact (normalized_cut_schmidtRank_le K x c
    (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hc) hKx).trans
      (Nat.mul_le_mul_right _ hrank)

end TNLean.MPS.AreaLaw
