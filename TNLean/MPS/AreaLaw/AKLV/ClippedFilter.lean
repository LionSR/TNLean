/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.ClippedHamiltonian
import TNLean.MPS.AreaLaw.AKLV.PhysicalRobustness
import TNLean.MPS.AreaLaw.AKLV.ChebyshevFilter
import QICLean.Analysis.EuclideanEigenvectorBasis
import QICLean.Analysis.LowEnergyPerturbation
import QICLean.Analysis.OptimizedPureStateTraceError

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
-/

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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ (∑ i, h i)) :
    2 ≤ q ∧ g ≤ 1 ∧ ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ x = (e j : ℂ) • x) ∧
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
          ∀ ell : ℕ, ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval E = 1 ∧
            let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
            toEuclideanLin K φ = φ ∧
            ‖K - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))‖ ≤
              2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((9 * g / 10) / (2 * t + s))) ∧
            operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
              (leftBlock L (a + s / 2)) K) ≤
                (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1)) ∧
            ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
              ⟪φ, toEuclideanLin K ψ⟫_ℂ = 0 ∧
              ‖toEuclideanLin K ψ‖ ^ 2 ≤
                (2 * Real.exp (-2 * (ell : ℝ) *
                  Real.sqrt ((9 * g / 10) / (2 * t + s)))) ^ 2 := by
  obtain ⟨hq2, hg1, e, E0, hregional, hEeq, hE0, hE6, hrobust⟩ :=
    exists_aklv_logarithmic_robustness hs ha h hsupp h0 h1 mu g Ω hΩ hground hgap hg hexcited
  let : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  let : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.mpr hq2
  obtain ⟨x, hxunit, hxeigen, he⟩ := hregional
  have he1 : 0 ≤ e 1 := by
    have hA : (aklvNormalizationHamiltonians a s h 1).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)
    exact hA.nonneg_of_normalized_eigenvector (e 1) x (hxeigen 1) hxunit
  refine ⟨hq2, hg1, e, E0, ⟨x, hxunit, hxeigen, he⟩, hEeq, hE0, hE6, ?_⟩
  intro t ht B
  have ht0 : 0 ≤ t := by
    have hlog : 0 ≤ Real.log (1 / g) :=
      Real.log_nonneg ((le_div_iff₀ hg).mpr (by simpa only [one_mul] using hg1))
    dsimp only [aklvLogarithmicThreshold] at ht
    linarith
  obtain ⟨hBpos, hBnorm⟩ := aklv_clipped_hamiltonian_posSemidef_norm_le hs ha h h0 h1 e he he1 ht0
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
  let H := fun j : Fin (s - 2) ↦ h ⟨a + 1 + j.val, by omega⟩
  obtain ⟨HL, HR, hL, hR, hmiddle, hdecomp, hcenter⟩ :=
    aklv_clipped_hamiltonian_decomposition hs ha h hsupp e t
  have hR' : Entropy.IsSupportedOn HR (interval L (a + 1 + (s - 2)) L) := by
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ (∑ i, h i)) :
    ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, (1024 / g) * (E0 / g + 1) ≤ t →
        let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ
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
            operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
              (leftBlock L (a + s / 2)) K) ≤
                (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1)) ∧
            ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
              ⟪φ, toEuclideanLin K ψ⟫_ℂ = 0 ∧
              ‖toEuclideanLin K ψ‖ ^ 2 ≤
                (2 * Real.exp (-2 * (ell : ℝ) *
                  Real.sqrt ((9 * g / 10) / (2 * t + s)))) ^ 2 := by
  obtain ⟨_hq2, hg1, e, E0, hregional, hEeq, hE0, hE6, hsharp⟩ :=
    exists_aklv_logarithmic_clipped_chebyshev_filter hs ha h hsupp h0 h1
      mu g Ω hΩ hground hgap hg hexcited
  refine ⟨e, E0, hregional, hEeq, hE0, hE6, ?_⟩
  intro t ht
  apply hsharp t
  apply (aklvLogarithmicThreshold_le_div hg hg1).trans
  have hnorm : 0 ≤ E0 / g := div_nonneg hE0 hg.le
  have hcoef : 0 < 1024 / g := div_pos (by norm_num) hg
  nlinarith

end TNLean.MPS.AreaLaw
