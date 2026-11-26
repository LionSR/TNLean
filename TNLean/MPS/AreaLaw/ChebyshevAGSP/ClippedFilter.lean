/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChebyshevAGSP.ClippedHamiltonian
import TNLean.MPS.AreaLaw.ChebyshevAGSP.PhysicalRobustness
import TNLean.MPS.AreaLaw.ChebyshevAGSP.SchmidtRank.PolynomialRank
import QICLean.Spectral.Eigenvalue.EuclideanEigenvectorBasis
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.Analysis.TraceNorm.OptimizedPureStateTraceError
import TNLean.MPS.AreaLaw.ChebyshevAGSP.FavorableParameters
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Analysis.Norm.SquaredTriangle
import QICLean.Channel.Schmidt.ProductOverlapBootstrap
import QICLean.ManyBody.Entropy.Filter.Prefix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The actual clipped AKLV Chebyshev filter

The original positive nearest-neighbour interactions determine the regional
energy shifts, the two exterior truncations, their ground vector and their
spectral ceiling. The resulting Chebyshev polynomial has the sharp spatial
rank bound at the original central cut.

Source: AKLV, arXiv:1301.1162v1, Lemmas 4.1 and 4.2 and Section 6.1,
Theorem `thm:Ht` and the choice of the truncated filter after that theorem.

**Scope restriction (window width):** Windows contain at least six
interactions. The support and aggregate energy-shift conventions are those in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.

**Local fix (count):** The polynomial rank estimate uses the corrected word
count recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
The robustness comparison uses the corrected spectral-window estimate at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.

## A favorable filter for the actual clipped AKLV Hamiltonian

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_cut_product_filtered_output`,
  `TNLean.MPS.AreaLaw.exists_aklv_physical_product_initialization`: physical product-overlap
  initialization for AKLV.
-/

section ClippedFilter

section

open ManyBody (interval)

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem canonical_rankOne_gap {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℂ} (hB : B.IsHermitian) (j0 : n) (g : ℝ)
    (hgap : ∀ j, j ≠ j0 → hB.eigenvalues j0 + g ≤ hB.eigenvalues j) :
    (B - (hB.eigenvalues j0 : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp (hB.eigenvectorBasis j0))
        (star (WithLp.ofLp (hB.eigenvectorBasis j0))))).PosSemidef := by
  let b := hB.eigenvectorBasis
  let D := B - (hB.eigenvalues j0 : ℂ) • 1 - (g : ℂ) •
    (1 - vecMulVec (WithLp.ofLp (b j0)) (star (WithLp.ofLp (b j0))))
  let d := fun j ↦ if j = j0 then 0 else hB.eigenvalues j - hB.eigenvalues j0 - g
  have hd (j : n) : 0 ≤ d j := by
    dsimp only [d]
    split_ifs with hj
    · exact le_rfl
    · linarith [hgap j hj]
  have hdiag (j : n) : toEuclideanLin D (b j) = (d j : ℂ) • b j := by
    have heigen : toEuclideanLin B (b j) = (hB.eigenvalues j : ℂ) • b j :=
      hB.toEuclideanCLM_eigenvectorBasis j
    simp only [D, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, toLpLin_one,
      LinearMap.id_apply, toEuclideanLin_vecMulVec_star_self_apply, heigen]
    by_cases hj : j = j0
    · subst j
      rw [b.inner_eq_one]
      simp only [one_smul, sub_self, smul_zero, d, ite_true, Complex.ofReal_zero, zero_smul]
    · rw [b.inner_eq_zero (Ne.symm hj)]
      simp only [zero_smul, sub_zero, d, ite_eq_right hj]
      push_cast
      module
  change D.PosSemidef
  rw [← isPositive_toEuclideanLin_iff]
  refine ⟨isSymmetric_toEuclideanLin_iff.mpr (hB.gap _ _ _), fun x ↦ ?_⟩
  rw [inner_re_symm, RCLike.re_to_complex,
    b.re_inner_apply_eq_sum_of_eigen d (toEuclideanLin D) hdiag x]
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hd j) (sq_nonneg _)

private theorem rankOne_gap_of_canonical_gap {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℂ} (hB : B.IsHermitian) (j0 : n) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ j, j ≠ j0 → hB.eigenvalues j0 + g ≤ hB.eigenvalues j)
    (φ : EuclideanSpace ℂ n) (hφ : ‖φ‖ = 1)
    (heigen : B *ᵥ WithLp.ofLp φ = (hB.eigenvalues j0 : ℂ) • WithLp.ofLp φ) :
    (B - (hB.eigenvalues j0 : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef := by
  have hcan := canonical_rankOne_gap hB j0 g hgap
  have hφeq := hcan.eq_inner_smul_of_gap hg
    (hB.eigenvectorBasis.norm_eq_one j0) heigen
  have hcoeff : ‖inner ℂ (hB.eigenvectorBasis j0) φ‖ = 1 := by
    have hn := (congrArg norm hφeq.symm).trans hφ
    simpa only [norm_smul, hB.eigenvectorBasis.norm_eq_one, mul_one] using hn
  have hproj : vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)) =
      vecMulVec (WithLp.ofLp (hB.eigenvectorBasis j0))
        (star (WithLp.ofLp (hB.eigenvectorBasis j0))) := by
    conv_lhs => rw [hφeq]
    rw [vecMulVec_ofLp_smul_self, hcoeff, one_pow, one_smul]
  rw [hproj]
  exact hcan

private theorem shorter_window_div_le {s ell : ℕ} (hs : 6 ≤ s) :
    ell / (s - 2) ≤ 2 * (ell / s) + 1 := by
  have hrem : ell < (ell / s + 1) * s :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < s)).mp (Nat.lt_succ_self (ell / s))
  have hs' : s ≤ 2 * (s - 2) := by omega
  have hmul : (ell / s + 1) * s ≤ (2 * (ell / s) + 2) * (s - 2) := by
    nlinarith [Nat.mul_le_mul_left (ell / s + 1) hs']
  have hdiv : ell / (s - 2) < 2 * (ell / s) + 2 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < s - 2)).mpr (hrem.trans_le hmul)
  omega

open Classical in
/-- The actual clipped AKLV filter is available above the logarithmic
threshold `1024 + 16*log(1/g)`, with its spectral ceiling, projector gap and
sharp same-cut operator Schmidt rank derived from the original physical
interactions. The actual gap bounds `2 ≤ q` and `g ≤ 1` are also derived.
AKLV, arXiv:1301.1162v1, Lemmas 4.1--4.2 and Section 6.1 after Theorem `thm:Ht`.
The regional minima are chosen before the threshold and the clipped ground
vector before the polynomial degree. -/
theorem exists_aklv_logarithmic_clipped_chebyshev_filter {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian) :
    2 ≤ q ∧ g ≤ 1 ∧ ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, aklvLogarithmicThreshold g ≤ t →
        let B := ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
          (a + 2) (a + s - 1) Φ e t Finset.univ
        B.PosSemidef ∧ ‖B‖ ≤ 2 * t + s ∧
        ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
          0 ≤ E ∧ ‖φ‖ = 1 ∧ toEuclideanLin B φ = (E : ℂ) • φ ∧
          (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
            (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
          ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 ∧
          ∀ ell : ℕ, ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval E = 1 ∧
            let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
            toEuclideanLin K φ = φ ∧
            ‖K - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))‖ ≤
              2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((9 * g / 10) / (2 * t + s))) ∧
            operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
              (interval L 0 (a + s / 2)) K) ≤
                (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1)) ∧
            ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
              ⟪φ, toEuclideanLin K ψ⟫_ℂ = 0 ∧
              ‖toEuclideanLin K ψ‖ ^ 2 ≤
                (2 * Real.exp (-2 * (ell : ℝ) *
                  Real.sqrt ((9 * g / 10) / (2 * t + s)))) ^ 2 := by
  obtain ⟨hq2, hg1, e, E0, hregional, hEeq, hE0, hE6, hrobust⟩ :=
    exists_aklv_logarithmic_robustness (by omega) ha Φ h0 h1 mu g Ω hΩ hground hgap hg
      hexcited
  let : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  let : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.mpr hq2
  obtain ⟨x, hxunit, hxeigen, he⟩ := hregional
  have he1 : 0 ≤ e 1 := by
    have hA : (aklvNormalizationHamiltonians a s Φ 1).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)
    exact hA.nonneg_of_normalized_eigenvector (e 1) x (hxeigen 1) hxunit
  refine ⟨hq2, hg1, e, E0, ⟨x, hxunit, hxeigen, he⟩, hEeq, hE0, hE6, ?_⟩
  intro t ht B
  have ht0 : 0 ≤ t := by
    have hlog : 0 ≤ Real.log (1 / g) :=
      Real.log_nonneg ((le_div_iff₀ hg).mpr (by simpa only [one_mul] using hg1))
    dsimp only [aklvLogarithmicThreshold] at ht
    linarith
  obtain ⟨hBpos, hBnorm⟩ :=
    aklv_clipped_hamiltonian_posSemidef_norm_le (by omega) ha Φ h0 h1 e he he1 ht0
  obtain ⟨hB, j0, φ, hφ, heigen, hnewgap, hclose⟩ := hrobust t ht
  have heigenRaw : B *ᵥ WithLp.ofLp φ =
      (hB.eigenvalues j0 : ℂ) • WithLp.ofLp φ := by
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using
      congrArg WithLp.ofLp heigen
  have hprojector := rankOne_gap_of_canonical_gap hB j0 (by positivity : 0 < 9 * g / 10)
    hnewgap φ hφ heigenRaw
  have hE : 0 ≤ hB.eigenvalues j0 := hBpos.eigenvalues_nonneg j0
  have hupper (r : ℝ) (hr : r ∈ spectrum ℝ B) : r ≤ 2 * t + s :=
    (le_abs_self r).trans ((by simpa only [Real.norm_eq_abs] using
      spectrum.norm_le_norm_of_mem hr : |r| ≤ ‖B‖).trans hBnorm)
  obtain ⟨j1, hj1⟩ := exists_ne j0
  have hgu : hB.eigenvalues j0 + 9 * g / 10 ≤ 2 * t + s :=
    (hnewgap j1 hj1).trans (hupper _ (hB.eigenvalues_mem_spectrum_real j1))
  refine ⟨hBpos, hBnorm, hB.eigenvalues j0, φ, hE, hφ, heigen, hprojector, hclose, ?_⟩
  intro ell
  let H := fun j : Fin (s - 2) ↦ Φ.term ⟨a + 1 + j.val, by omega⟩
  obtain ⟨HL, HR, hL, hR, hmiddle, hdecomp, hcenter⟩ :=
    aklv_clipped_hamiltonian_decomposition (by omega) ha Φ e t
  have hR' : ManyBody.IsSupportedOn HR (interval L (a + 1 + (s - 2)) L) := by
    convert hR using 1
    congr 1
    omega
  obtain ⟨p, hdegree, hp0, hfix, herr, hrank, horth⟩ :=
    exists_aklv_chebyshev_filter (by omega : 1 ≤ q) (by omega : 0 < s - 2)
      (by omega : a + 1 + (s - 2) + 1 ≤ L) H hmiddle HL HR
      (by simpa only [Nat.add_assoc] using hL) hR'
      (by rwa [← hdecomp]) hφ (by rwa [← hdecomp]) (by rwa [← hdecomp])
      (by positivity : 0 < 9 * g / 10) hgu (by rwa [← hdecomp]) ell
  rw [← hdecomp] at hfix herr hrank horth
  rw [hcenter] at hrank
  have hden : 0 < 2 * t + s - hB.eigenvalues j0 := by linarith
  have hratio : (9 * g / 10) / (2 * t + s) ≤
      (9 * g / 10) / (2 * t + s - hB.eigenvalues j0) :=
    div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  have hamp : 2 * Real.exp (-2 * (ell : ℝ) *
      Real.sqrt ((9 * g / 10) / (2 * t + s - hB.eigenvalues j0))) ≤
        2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((9 * g / 10) / (2 * t + s))) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt hratio) (by nlinarith : -2 * (ell : ℝ) ≤ 0)
  have hexponent : 16 * (ell / (s - 2) + Nat.sqrt ell + 1) ≤
      32 * (ell / s + Nat.sqrt ell + 1) := by
    have hh := shorter_window_div_le (ell := ell) hs
    omega
  have hbase : 1 ≤ q * (ell + 1) := by nlinarith
  refine ⟨p, hdegree, hp0, hfix, herr.trans hamp,
    hrank.trans (Nat.pow_le_pow_right hbase hexponent), ?_⟩
  intro ψ hψ hperp
  obtain ⟨hortho, hshrink⟩ := horth ψ hψ hperp
  exact ⟨hortho, hshrink.trans (pow_le_pow_left₀ (by positivity) hamp 2)⟩

open Classical in
/-- The actual two-exterior truncation admits a Chebyshev filter whose norm
error and operator Schmidt rank are both derived from the original physical
chain. The retained window has width `s-2` and the original central cut.
AKLV, arXiv:1301.1162v1, Lemmas 4.1--4.2 and Section 6.1 after Theorem `thm:Ht`.
The ground vector and energy shifts are chosen before the polynomial degree. -/
theorem exists_aklv_clipped_chebyshev_filter {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian) :
    ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, (1024 / g) * (E0 / g + 1) ≤ t →
        let B := ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
          (a + 2) (a + s - 1) Φ e t Finset.univ
        B.PosSemidef ∧ ‖B‖ ≤ 2 * t + s ∧
        ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
          0 ≤ E ∧ ‖φ‖ = 1 ∧ toEuclideanLin B φ = (E : ℂ) • φ ∧
          (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
            (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
          ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 ∧
          ∀ ell : ℕ, ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval E = 1 ∧
            let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
            toEuclideanLin K φ = φ ∧
            ‖K - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))‖ ≤
              2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((9 * g / 10) / (2 * t + s))) ∧
            operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
              (interval L 0 (a + s / 2)) K) ≤
                (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1)) ∧
            ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
              ⟪φ, toEuclideanLin K ψ⟫_ℂ = 0 ∧
              ‖toEuclideanLin K ψ‖ ^ 2 ≤
                (2 * Real.exp (-2 * (ell : ℝ) *
                  Real.sqrt ((9 * g / 10) / (2 * t + s)))) ^ 2 := by
  obtain ⟨_hq2, hg1, e, E0, hregional, hEeq, hE0, hE6, hsharp⟩ :=
    exists_aklv_logarithmic_clipped_chebyshev_filter hs ha Φ h0 h1
      mu g Ω hΩ hground hgap hg hexcited
  refine ⟨e, E0, hregional, hEeq, hE0, hE6, ?_⟩
  intro t ht
  exact hsharp t (aklvLogarithmicThreshold_le_of_polynomial hg hg1 hE0 ht)

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-- The original physical chain determines a favorable square-degree filter for
its actual clipped ground vector. No filter, rank bound, spectral ceiling or
clipped target is supplied. The scalar constant is uniform before all physical
data. AKLV, arXiv:1301.1162v1, Section 6.1, lines 1016--1024. -/
theorem exists_aklv_physical_favorable_filter :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q a : ℕ)
        (Φ : ManyBody.BondInteraction L q)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ i, 0 ≤ Φ.term i) → (∀ i, Φ.term i ≤ 1) → ‖Ω‖ = 1 →
      Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ Φ.hamiltonian →
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
          (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
          ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
        E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
        let B := ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
          (a + 2) (a + s - 1) Φ e t0 Finset.univ
        B.PosSemidef ∧ ‖B‖ ≤ R ∧ 0 ≤ E ∧ ‖φ‖ = 1 ∧
        toEuclideanLin B φ = (E : ℂ) • φ ∧
        (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
          (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
        ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t0 / 16) / 100 ∧
        p.natDegree = ell ∧ p.eval E = 1 ∧
        let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
        toEuclideanLin K φ = φ ∧
        operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
          (interval L 0 (a + s / 2)) K) ≤ D ∧
        ‖K - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))‖ ≤
          2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((9 * g / 10) / R)) ∧
        ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
          ⟪φ, toEuclideanLin K ψ⟫_ℂ = 0 ∧ ‖toEuclideanLin K ψ‖ ^ 2 ≤ delta := by
  obtain ⟨A, hA, hA21, hscalar⟩ := Real.exists_aklv_favorable_scalar_parameters
  refine ⟨A, hA, hA21, ?_⟩
  intro L q a Φ mu g Ω h0 h1 hΩ hground hgap hg hexcited u s ell t0 R D delta ha
  have hH : Φ.hamiltonian.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have hmu := Matrix.mem_spectrum_real_of_mulVec_eq_smul
    (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hΩ) hground
  have hq2 : 2 ≤ q := hH.two_le_local_dimension_of_two_spectral_values
    hmu hexcited (by linarith)
  obtain ⟨-, -, hgapI, hspan⟩ := (ManyBody.isGapped_and_groundSpace_eq_span_iff hg Ω).mp
    ⟨hΩ, by rw [← (WithLp.ofLp_injective 2).eq_iff, Matrix.ofLp_toEuclideanCLM,
      WithLp.ofLp_smul]; exact hground, hgap⟩
  have hg1 := ManyBody.BondInteraction.gap_le_one_of_nonneg_of_le_one (by omega : 0 < L)
    hq2 Φ h0 h1 hΩ hgapI hspan
  obtain ⟨_hsLower, _hsUpper, hs21, _hsb, hdiv, hsqrt, _hR, _hRup, _hDaux,
      hdelta, htrade, _htradeSmall, hlogD⟩ := hscalar q g hq2 hg hg1
  change 21 ≤ s at hs21
  change ell / s = s at hdiv
  change Nat.sqrt ell = s at hsqrt
  obtain ⟨_hq, _hg, e, E0, hregional, hEeq, hE0, hE6, hfilter⟩ :=
    exists_aklv_logarithmic_clipped_chebyshev_filter (by omega) ha Φ h0 h1
      mu g Ω hΩ hground hgap hg hexcited
  obtain ⟨hBpos, hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose, hpoly⟩ :=
    hfilter t0 le_rfl
  obtain ⟨p, hdegree, hpE, hfix, herr, hrank, hperp⟩ := hpoly ell
  have hrankD : operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
      (interval L 0 (a + s / 2))
      (Polynomial.aeval
        (ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
          (a + 2) (a + s - 1) Φ e t0 Finset.univ) p)) ≤ D := by
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

end

end ClippedFilter

section Initialization

/-!
## Physical product-overlap initialization for AKLV

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

open ManyBody (interval)

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A fixed unit vector `φ` of an operator `K` that preserves its orthogonal complement,
contracts squared norms there by `δ`, and has operator Schmidt rank at most `D` at the cut
`k`, with `Dδ ≤ 1/2`, is approximated by a phase-aligned normalized image `Kχ/‖Kχ‖` of a
product vector `χ`: this image has Schmidt rank at most `D` at the cut and squared distance
at most `4Dδ` from `φ`. AKLV, arXiv:1301.1162v1, Lemma 2.2 (`lem:mu1`), lines 332–337,
and the state of constant overlap in Section 5, lines 862–863. -/
theorem exists_cut_product_filtered_output {L q k D : ℕ}
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (φ : EuclideanSpace ℂ (Fin L → Fin q)) (hφ : ‖φ‖ = 1)
    (hfix : toEuclideanLin K φ = φ) {delta : ℝ} (hdelta : 0 ≤ delta) (hD : 0 < D)
    (hperp : ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
      ⟪φ, toEuclideanLin K ψ⟫_ℂ = 0 ∧ ‖toEuclideanLin K ψ‖ ^ 2 ≤ delta)
    (hrank : operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
      (interval L 0 k) K) ≤ D) (htrade : (D : ℝ) * delta ≤ 1 / 2) :
    ∃ (χ : EuclideanSpace ℂ (Fin L → Fin q))
      (u : (ManyBody.RegionConfig (fun _ ↦ Fin q) (interval L 0 k)) → ℂ)
      (v : ((i : {i : Fin L // i ∉ interval L 0 k}) → Fin q) → ℂ) (c : ℂ),
      ‖χ‖ = 1 ∧ ManyBody.cutVector (X := fun _ ↦ Fin q) (interval L 0 k) χ =
        WithLp.toLp 2 (fun z ↦ u z.1 * v z.2) ∧
      1 / Real.sqrt (2 * (D : ℝ)) ≤ ‖⟪φ, χ⟫_ℂ‖ ∧
      toEuclideanLin K χ ≠ 0 ∧ ‖c‖ = 1 ∧
      let ψ := c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ
      ‖ψ‖ = 1 ∧
      schmidtRank (WithLp.ofLp (ManyBody.cutVector (X := fun _ ↦ Fin q)
        (interval L 0 k) ψ)) ≤ D ∧ ‖ψ - φ‖ ^ 2 ≤ 4 * (D : ℝ) * delta := by
  classical
  let cut := interval L 0 k
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv (fun _ ↦ Fin q) cut)
  let Kcut := ManyBody.cutOperator (X := fun _ ↦ Fin q) cut K
  have hU (x : EuclideanSpace ℂ (Fin L → Fin q)) : U x = ManyBody.cutVector cut x := by
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
        (Φ : ManyBody.BondInteraction L q)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ i, 0 ≤ Φ.term i) → (∀ i, Φ.term i ≤ 1) → ‖Ω‖ = 1 →
      Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ Φ.hamiltonian →
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
          (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
          ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
        E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
        let B := ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
          (a + 2) (a + s - 1) Φ e t0 Finset.univ
        B.PosSemidef ∧ ‖B‖ ≤ 2 * t0 + (s : ℝ) ∧ 0 ≤ E ∧ ‖φ‖ = 1 ∧
        toEuclideanLin B φ = (E : ℂ) • φ ∧
        (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
          (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
        ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t0 / 16) / 100 ∧
        p.natDegree = s ^ 2 ∧ p.eval E = 1 ∧
        let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
        toEuclideanLin K φ = φ ∧
        operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
          (interval L 0 (a + s / 2)) K) ≤ D ∧
        ∃ (χ : EuclideanSpace ℂ (Fin L → Fin q))
          (vL : (ManyBody.RegionConfig (fun _ ↦ Fin q) (interval L 0 (a + s / 2))) → ℂ)
          (vR : ((i : {i : Fin L // i ∉ interval L 0 (a + s / 2)}) → Fin q) → ℂ) (c : ℂ),
          ‖χ‖ = 1 ∧
          ManyBody.cutVector (X := fun _ ↦ Fin q) (interval L 0 (a + s / 2)) χ =
            WithLp.toLp 2 (fun z ↦ vL z.1 * vR z.2) ∧
          1 / Real.sqrt (2 * (D : ℝ)) ≤ ‖⟪φ, χ⟫_ℂ‖ ∧
          toEuclideanLin K χ ≠ 0 ∧ ‖c‖ = 1 ∧
          let ψ := c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ
          ‖ψ‖ = 1 ∧
          schmidtRank (WithLp.ofLp (ManyBody.cutVector (X := fun _ ↦ Fin q)
            (interval L 0 (a + s / 2)) ψ)) ≤ D ∧
          ‖ψ - φ‖ ^ 2 ≤ 1 / 64 ∧ ‖ψ - Ω‖ ^ 2 ≤ 1 / 16 := by
  obtain ⟨A, hA, hA21, hphysical⟩ := exists_aklv_physical_favorable_filter
  refine ⟨A, hA, hA21, ?_⟩
  intro L q a Φ mu g Ω h0 h1 hΩ hground hgap hg hexcited u s t0 D ha
  obtain ⟨hq, hg1, hs, hdelta, htrade, hlogD, e, E0, E, φ, p,
      hregional, hEeq, hE0, hE6, hBpos, hBnorm, hE, hφ, heigen, hprojector,
      hclose, hdegree, hpE, hfix, hrank, _herr, hperp⟩ :=
    hphysical L q a Φ mu g Ω h0 h1 hΩ hground hgap hg hexcited ha
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
    Polynomial.aeval (ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
      (a + 2) (a + s - 1) Φ e t0 Finset.univ) p
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

end Initialization
