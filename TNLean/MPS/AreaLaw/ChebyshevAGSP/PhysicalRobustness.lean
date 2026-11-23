/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Eigenvalue.EuclideanEigenvectorBasis
import TNLean.MPS.AreaLaw.ChebyshevAGSP.SpectralCluster
import QICLean.ManyBody.Hamiltonian.Chain.GapUpperBound
import QICLean.Spectral.LowEnergy.Coordinates
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# The AKLV physical robustness bound at logarithmic and polynomial thresholds

The original bounded-term nearest-neighbour setting of AKLV Section 6.1 is
retained. The actual first excited energy determines the gap, and the endpoint
trial-vector argument derives its upper bound one. The three original regional
minima are chosen before the truncation threshold. The actual two exterior
truncations preserve a constant fraction of the gap and have a phase-aligned
unit ground vector with exponentially small squared error.

Source: AKLV, arXiv:1301.1162v1, `1dfrustrated34.tex`, lines 879--963,
Theorem `thm:Ht`.

**Local fix (window width):** The enlarged arrangement, whose clipped exteriors
contain one further window bond each, needs at least three interactions so that
its two exterior sums have disjoint supports. For windows of one or two
interactions the reference arrangement is used instead: it clips the two
reference sums themselves at the cuts `a+1` and `a+s`, whose supports are disjoint
for every window of at least one interaction, and gives the same conclusions.
See `docs/paper-gaps/aklv13_two_block_robustness.tex`.

**Local fixes (support and energy shift):** The left support follows the actual
bounded-term sum in source line 907, including its boundary site, rather than
the shorter support printed in line 897. The middle energy is subtracted once
from its actual aggregate sum. Both corrections are recorded in the same note.
The spectral comparison also uses the corrected window count documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.
-/

open ManyBody (interval)

open Matrix

open ManyBody (IsGapped groundSpace)
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A logarithmic truncation threshold for the actual AKLV exterior sums.
This sufficient threshold follows from the exponential residual comparison
underlying AKLV, arXiv:1301.1162v1, Section 6.1, Theorem `thm:Ht`. -/
noncomputable def aklvLogarithmicThreshold (g : ℝ) : ℝ :=
  1024 + 16 * Real.log (1 / g)

/-- The logarithmic threshold is bounded by the coarser inverse-gap threshold
when the physical gap is at most one. This compares the strengthened robustness
bound with AKLV, arXiv:1301.1162v1, Theorem `thm:Ht`, line 955. -/
theorem aklvLogarithmicThreshold_le_div {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) :
    aklvLogarithmicThreshold g ≤ 1024 / g := by
  have hinv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa only [one_mul] using hg1)
  have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr hg)
  dsimp only [aklvLogarithmicThreshold]
  simp only [div_eq_mul_inv, one_mul] at *
  linarith

/-- The polynomial threshold `(1024/g)*(E0/g+1)` of AKLV, arXiv:1301.1162v1,
Theorem `thm:Ht`, line 955, lies above the logarithmic threshold when `0 < g ≤ 1`
and `0 ≤ E0`. -/
theorem aklvLogarithmicThreshold_le_of_polynomial {g E0 t : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hE0 : 0 ≤ E0) (ht : (1024 / g) * (E0 / g + 1) ≤ t) :
    aklvLogarithmicThreshold g ≤ t := by
  apply (aklvLogarithmicThreshold_le_div hg hg1).trans
  have hnorm : 0 ≤ E0 / g := div_nonneg hE0 hg.le
  have hcoef : 0 < 1024 / g := div_pos (by norm_num) hg
  nlinarith

private theorem logarithmic_robustness_scalar_threshold {g t : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (ht : aklvLogarithmicThreshold g ≤ t) :
    0 < Real.exp (-t / 16) ∧ Real.exp (-t / 16) ≤ 1 ∧
      aklvTwoBlockThreshold g (Real.exp (-t / 16)) ≤ t := by
  have hlogInv : 0 ≤ Real.log (1 / g) :=
    Real.log_nonneg ((le_div_iff₀ hg).mpr (by simpa only [one_mul] using hg1))
  have ht0 : 0 ≤ t := by dsimp only [aklvLogarithmicThreshold] at ht; linarith
  have hlog10 : Real.log (10 : ℝ) ≤ 9 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogMillion : Real.log (1000000 : ℝ) = 6 * Real.log 10 := by
    rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlogC : Real.log ((1000000 : ℝ) * (64 * Real.exp (3 / 4))) ≤ 61 := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp,
      hlogMillion, hlog64]
    linarith
  have hlogInvEq : Real.log (1 / g) = -Real.log g := by
    rw [Real.log_div one_ne_zero (ne_of_gt hg), Real.log_one, zero_sub]
  dsimp only [aklvLogarithmicThreshold] at ht
  rw [hlogInvEq] at ht
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), ?_⟩
  apply max_le
  · linarith
  · rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hg), Real.log_exp]
    linarith

open Classical in
/-- The actual AKLV exterior truncations at two cuts whose regional sums dominate
the genuine reference minima have gap at least `9*g/10` and a
phase-aligned unit ground vector with squared error at most `exp(-t/16)/100`
for `t ≥ 1024 + 16*log(1/g)`. The actual first excited energy and endpoint
trial-vector argument also derive local dimension at least two and `g ≤ 1`.
The regional minima are chosen before `t`. This strengthens the sufficient
threshold in AKLV, arXiv:1301.1162v1, Theorem `thm:Ht`, lines 879--963,
using the exponential residual of its original nearest-neighbour construction. -/
private theorem exists_aklv_cut_logarithmic_robustness {L q a s l r : ℕ}
    (hs : 1 ≤ s) (ha : a + s + 1 ≤ L) (hlr : l ≤ r) (hrL : r ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian)
    (hcut : ∀ e : Fin 3 → ℝ, (∀ j, (aklvNormalizationHamiltonians a s Φ j -
      (e j : ℂ) • 1).PosSemidef) → ∀ j, (e j : ℂ) • 1 ≤ aklvRegionalHamiltonians l r Φ j) :
    2 ≤ q ∧ g ≤ 1 ∧ ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, aklvLogarithmicThreshold g ≤ t →
        let B := aklvTwoBlockHamiltonian l r Φ e t Finset.univ
        ∃ hB : B.IsHermitian,
          let lam := hB.eigenvalues
          ∃ (j0 : Fin L → Fin q) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
            ‖φ‖ = 1 ∧ Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B φ =
              (lam j0 : ℂ) • φ ∧
            (∀ j, j ≠ j0 → lam j0 + 9 * g / 10 ≤ lam j) ∧
            ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 := by
  have hH : Φ.hamiltonian.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  obtain ⟨-, -, hgapI, hspan⟩ := (ManyBody.isGapped_and_groundSpace_eq_span_iff hg Ω).mp
    ⟨hΩ, by rw [← (WithLp.ofLp_injective 2).eq_iff, Matrix.ofLp_toEuclideanCLM,
      WithLp.ofLp_smul]; exact hground, hgap⟩
  have hmu := Matrix.mem_spectrum_real_of_mulVec_eq_smul
    (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hΩ) hground
  have hq2 : 2 ≤ q := hH.two_le_local_dimension_of_two_spectral_values
    hmu hexcited (by linarith)
  have hg1 := ManyBody.BondInteraction.gap_le_one_of_nonneg_of_le_one
    (by omega : 0 < L) hq2 Φ h0 h1 hΩ hgapI hspan
  obtain ⟨e, E0, hregional, hEeq, hE0, hE6, hcluster⟩ :=
    exists_aklv_cut_scaled_low_cluster (by omega) hs ha hlr hrL Φ h0 h1
      mu g Ω hΩ hground hgap hg hcut
  refine ⟨hq2, hg1, e, E0, hregional, hEeq, hE0, hE6, ?_⟩
  intro t ht B
  obtain ⟨htau, htau1, hthreshold⟩ := logarithmic_robustness_scalar_threshold hg hg1 ht
  obtain ⟨hBall, _hUV, _hdim, _hUG, _hGU, _hwindow, _hspec, j0, _hj0,
      hnewgap, θ, hphase⟩ := hcluster (Real.exp (-t / 16)) t htau htau1 hthreshold
  let ζ : ℂ := Complex.exp ((-θ : ℝ) * Complex.I)
  let φ := ζ • (hBall Finset.univ).eigenvectorBasis j0
  have hζ : ‖ζ‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hcancel : ζ * Complex.exp (θ * Complex.I) = 1 := by
    dsimp only [ζ]
    rw [← Complex.exp_add]
    have heq : ((-θ : ℝ) : ℂ) * Complex.I + (θ : ℂ) * Complex.I = 0 := by
      push_cast
      ring
    rw [heq, Complex.exp_zero]
  refine ⟨hBall Finset.univ, j0, φ, ?_, ?_, hnewgap, ?_⟩
  · dsimp only [φ]
    rw [norm_smul, hζ, (hBall Finset.univ).eigenvectorBasis.norm_eq_one, mul_one]
  · have heigen : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B
        ((hBall Finset.univ).eigenvectorBasis j0) =
          ((hBall Finset.univ).eigenvalues j0 : ℂ) •
            (hBall Finset.univ).eigenvectorBasis j0 := by
      exact (hBall Finset.univ).toEuclideanCLM_eigenvectorBasis j0
    dsimp only [φ]
    rw [map_smul, heigen, smul_smul, smul_smul, mul_comm]
  · have hdiff : φ - Ω = ζ • ((hBall Finset.univ).eigenvectorBasis j0 -
        Complex.exp (θ * Complex.I) • Ω) := by
      rw [smul_sub, smul_smul, hcancel, one_smul]
    rw [hdiff, norm_smul, hζ, one_mul]
    exact hphase

open Classical in
/-- The actual AKLV exterior truncations have gap at least `9*g/10` and a
phase-aligned unit ground vector with squared error at most `exp(-t/16)/100`
for `t ≥ 1024 + 16*log(1/g)`. The actual first excited energy and endpoint
trial-vector argument also derive local dimension at least two and `g ≤ 1`.
The regional minima are chosen before `t`. This strengthens the sufficient
threshold in AKLV, arXiv:1301.1162v1, Theorem `thm:Ht`, lines 879--963,
using the exponential residual of its original nearest-neighbour construction. -/
theorem exists_aklv_logarithmic_robustness {L q a s : ℕ}
    (hs : 3 ≤ s) (ha : a + s + 1 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian) :
    2 ≤ q ∧ g ≤ 1 ∧ ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, aklvLogarithmicThreshold g ≤ t →
        let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) Φ e t Finset.univ
        ∃ hB : B.IsHermitian,
          let lam := hB.eigenvalues
          ∃ (j0 : Fin L → Fin q) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
            ‖φ‖ = 1 ∧ Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B φ =
              (lam j0 : ℂ) • φ ∧
            (∀ j, j ≠ j0 → lam j0 + 9 * g / 10 ≤ lam j) ∧
            ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 :=
  exists_aklv_cut_logarithmic_robustness (by omega) ha (by omega) (by omega) Φ h0 h1
    mu g Ω hΩ hground hgap hg hexcited
    (fun e he ↦ aklv_normalization_le_two_block_regions hs Φ h0 e he)

open Classical in
/-- The reference arrangement of the AKLV exterior truncations, which clips the two
reference sums themselves at the cuts `a+1` and `a+s` and retains all `s` window
interactions, has gap at least `9*g/10` and a
phase-aligned unit ground vector with squared error at most `exp(-t/16)/100`
for `t ≥ 1024 + 16*log(1/g)`. The actual first excited energy and endpoint
trial-vector argument also derive local dimension at least two and `g ≤ 1`.
The regional minima are chosen before `t`. This strengthens the sufficient
threshold in AKLV, arXiv:1301.1162v1, Theorem `thm:Ht`, lines 879--963,
using the exponential residual of its original nearest-neighbour construction.
Every window of at least one interaction is admitted; for one or two interactions
the enlarged exterior sums overlap, while the reference sums are disjoint. -/
theorem exists_aklv_reference_logarithmic_robustness {L q a s : ℕ}
    (hs : 1 ≤ s) (ha : a + s + 1 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian) :
    2 ≤ q ∧ g ≤ 1 ∧ ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, aklvLogarithmicThreshold g ≤ t →
        let B := aklvTwoBlockHamiltonian (a + 1) (a + s) Φ e t Finset.univ
        ∃ hB : B.IsHermitian,
          let lam := hB.eigenvalues
          ∃ (j0 : Fin L → Fin q) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
            ‖φ‖ = 1 ∧ Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B φ =
              (lam j0 : ℂ) • φ ∧
            (∀ j, j ≠ j0 → lam j0 + 9 * g / 10 ≤ lam j) ∧
            ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 :=
  exists_aklv_cut_logarithmic_robustness hs ha (by omega) (by omega) Φ h0 h1 mu g Ω hΩ hground
    hgap hg hexcited (fun e he ↦ aklv_normalization_le_reference_regions Φ h0 e he)

open Classical in
/-- The actual two exterior truncations of the original positive-contraction
nearest-neighbour chain have gap at least `9*g/10` and a phase-aligned unit
ground vector with squared error at most `exp(-t/16)/100` once
`t ≥ (1024/g)*(E0/g+1)`. Here `E0` is the constructed normalized original
ground energy in `[0,6]`. The gap is the actual first excited energy difference.
AKLV, arXiv:1301.1162v1, Theorem `thm:Ht`, lines 879--963. -/
theorem exists_aklv_physical_robustness {L q a s : ℕ}
    (hs : 3 ≤ s) (ha : a + s + 1 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian) :
    ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, (1024 / g) * (E0 / g + 1) ≤ t →
        let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) Φ e t Finset.univ
        ∃ hB : B.IsHermitian,
          let lam := hB.eigenvalues
          ∃ (j0 : Fin L → Fin q) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
            ‖φ‖ = 1 ∧ Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B φ =
              (lam j0 : ℂ) • φ ∧
            (∀ j, j ≠ j0 → lam j0 + 9 * g / 10 ≤ lam j) ∧
            ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 := by
  obtain ⟨_hq2, hg1, e, E0, hregional, hEeq, hE0, hE6, hsharp⟩ :=
    exists_aklv_logarithmic_robustness hs ha Φ h0 h1 mu g Ω hΩ hground hgap hg hexcited
  refine ⟨e, E0, hregional, hEeq, hE0, hE6, ?_⟩
  intro t ht
  exact hsharp t (aklvLogarithmicThreshold_le_of_polynomial hg hg1 hE0 ht)

open Classical in
/-- The reference arrangement, clipping the two reference sums at the cuts `a+1` and
`a+s`, of the original positive-contraction
nearest-neighbour chain have gap at least `9*g/10` and a phase-aligned unit
ground vector with squared error at most `exp(-t/16)/100` once
`t ≥ (1024/g)*(E0/g+1)`. Here `E0` is the constructed normalized original
ground energy in `[0,6]`. The gap is the actual first excited energy difference.
Every window of at least one interaction is admitted, including windows of one or
two interactions. AKLV, arXiv:1301.1162v1, Theorem `thm:Ht`, lines 879--963. -/
theorem exists_aklv_reference_physical_robustness {L q a s : ℕ}
    (hs : 1 ≤ s) (ha : a + s + 1 ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1)
    (hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ Φ.hamiltonian) :
    ∃ (e : Fin 3 → ℝ) (E0 : ℝ),
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
      ∀ t : ℝ, (1024 / g) * (E0 / g + 1) ≤ t →
        let B := aklvTwoBlockHamiltonian (a + 1) (a + s) Φ e t Finset.univ
        ∃ hB : B.IsHermitian,
          let lam := hB.eigenvalues
          ∃ (j0 : Fin L → Fin q) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
            ‖φ‖ = 1 ∧ Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B φ =
              (lam j0 : ℂ) • φ ∧
            (∀ j, j ≠ j0 → lam j0 + 9 * g / 10 ≤ lam j) ∧
            ‖φ - Ω‖ ^ 2 ≤ Real.exp (-t / 16) / 100 := by
  obtain ⟨_hq2, hg1, e, E0, hregional, hEeq, hE0, hE6, hsharp⟩ :=
    exists_aklv_reference_logarithmic_robustness hs ha Φ h0 h1 mu g Ω hΩ hground hgap hg
      hexcited
  refine ⟨e, E0, hregional, hEeq, hE0, hE6, ?_⟩
  intro t ht
  exact hsharp t (aklvLogarithmicThreshold_le_of_polynomial hg hg1 hE0 ht)

end TNLean.MPS.AreaLaw
