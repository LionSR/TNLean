/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.ClippedFilter
import TNLean.MPS.AreaLaw.AKLV.FavorableParameters

/-!
# A favorable filter for the actual clipped AKLV Hamiltonian

One universal scalar choice determines the window and square polynomial degree.
When that window fits in the original positive nearest-neighbour chain, the
actual two-exterior truncation supplies a unit clipped ground vector and a
Chebyshev filter with the favorable rank and shrinking tradeoff. The ground
vector is chosen before the polynomial, and the regional minima are constructed
from the original interactions.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, the construction following
Theorem `thm:Ht` and the initial step in Lemma `l:5`, lines 1016--1024.

**Scope restriction (available window):** The scalar window must fit in the
chain. The construction has width at least twenty-one, hence respects the
six-interaction restriction and conventions in
`docs/paper-gaps/aklv13_two_block_robustness.tex`. Small boundary regions and
the subsequent varying-target sequence remain separate.
-/

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The original physical chain determines a favorable square-degree filter for
its actual clipped ground vector. No filter, rank bound, spectral ceiling or
clipped target is supplied. The scalar constant is uniform before all physical
data. AKLV, arXiv:1301.1162v1, Section 6.1, lines 1016--1024. -/
theorem exists_aklv_physical_favorable_filter :
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
      let ell : ℕ := s ^ 2
      let t0 : ℝ := 1024 + 16 * Real.log (1 / g)
      let R : ℝ := 2 * t0 + (s : ℝ)
      let D : ℕ := (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
      let delta : ℝ := 4 * Real.exp (-(4 * (ell : ℝ) * Real.sqrt ((9 * g / 10) / R)))
      a + s + 1 ≤ L →
      2 ≤ q ∧ g ≤ 1 ∧ 21 ≤ s ∧ 0 < delta ∧ (D : ℝ) * delta ≤ 1 / 100000 ∧
      Real.log (D : ℝ) ≤ 198 * (A + 1) * (6 + 2 * Real.log (A + 1)) / g * u ^ 3 ∧
      ∃ (e : Fin 3 → ℝ) (E0 E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q))
        (p : Polynomial ℝ),
        (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
          (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ x = (e j : ℂ) • x) ∧
          ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef) ∧
        E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
        let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t0 Finset.univ
        B.PosSemidef ∧ ‖B‖ ≤ R ∧ 0 ≤ E ∧ ‖φ‖ = 1 ∧
        toEuclideanLin B φ = (E : ℂ) • φ ∧
        (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
          (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
        ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t0 / 16) / 100 ∧
        p.natDegree = ell ∧ p.eval E = 1 ∧
        let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
        toEuclideanLin K φ = φ ∧
        operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
          (leftBlock L (a + s / 2)) K) ≤ D ∧
        ‖K - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))‖ ≤
          2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((9 * g / 10) / R)) ∧
        ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
          ⟪φ, toEuclideanLin K ψ⟫_ℂ = 0 ∧ ‖toEuclideanLin K ψ‖ ^ 2 ≤ delta := by
  obtain ⟨A, hA, hA21, hscalar⟩ := Real.exists_aklv_favorable_scalar_parameters
  refine ⟨A, hA, hA21, ?_⟩
  intro L q a h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited u s ell t0 R D delta ha
  have hH : (∑ i, h i).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have hmu := Matrix.mem_spectrum_real_of_mulVec_eq_smul
    (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hΩ) hground
  have hq2 : 2 ≤ q := hH.two_le_local_dimension_of_two_spectral_values
    hmu hexcited (by linarith)
  have hgs : Matrix.IsGappedGroundState (∑ i, h i) mu Ω g :=
    Matrix.isGappedGroundState_iff.mpr ⟨hΩ, hground, hgap⟩
  have hg1 := gap_le_one_of_positive_nearest_neighbor_terms (by omega : 0 < L)
    hq2 h hsupp h0 h1 hgs
  obtain ⟨_hsLower, _hsUpper, hs21, _hsb, hdiv, hsqrt, _hR, _hRup, _hDaux,
      hdelta, htrade, _htradeSmall, hlogD⟩ := hscalar q g hq2 hg hg1
  change 21 ≤ s at hs21
  change ell / s = s at hdiv
  change Nat.sqrt ell = s at hsqrt
  obtain ⟨_hq, _hg, e, E0, hregional, hEeq, hE0, hE6, hfilter⟩ :=
    exists_aklv_logarithmic_clipped_chebyshev_filter (by omega) ha h hsupp h0 h1
      mu g Ω hΩ hground hgap hg hexcited
  obtain ⟨hBpos, hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose, hpoly⟩ :=
    hfilter t0 le_rfl
  obtain ⟨p, hdegree, hpE, hfix, herr, hrank, hperp⟩ := hpoly ell
  have hrankD : operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L (a + s / 2))
      (Polynomial.aeval
        (aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t0 Finset.univ) p)) ≤ D := by
    change _ ≤ (q * (ell + 1)) ^ (32 * (2 * s + 1))
    simpa only [hdiv, hsqrt, two_mul] using hrank
  have hDeltaEq :
      (2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((9 * g / 10) / R))) ^ 2 = delta := by
    dsimp only [delta]
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
    congr 1
    congr 1
    ring
  refine ⟨hq2, hg1, hs21, hdelta, htrade, hlogD, e, E0, E, φ, p,
    hregional, hEeq, hE0, hE6, hBpos, hBnorm, hE, hφ, heigen, hprojector,
    hclose, hdegree, hpE, hfix, hrankD, herr, ?_⟩
  intro ψ hψ horth
  obtain ⟨horthK, hnormK⟩ := hperp ψ hψ horth
  exact ⟨horthK, hnormK.trans_eq hDeltaEq⟩

end TNLean.MPS.AreaLaw
