/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.ChangingTargets
import TNLean.MPS.AreaLaw.AKLV.SharpPerCutApproximation
import TNLean.MPS.AreaLaw.AKLV.SequenceEntropy
import TNLean.MPS.AreaLaw.AKLV.CutApproximationTail

/-!
# Physical AKLV entropy from the actual changing-target sequence

The actual coherent normalized filter sequence gives dyadic marginal tails.
Finite entropy summation then gives a uniform bound at every cut. If the
initial window does not fit, the exact smaller-side dimension bound suffices.
No independent area-law theorem is used.

Source: AKLV, arXiv:1301.1162v1, lines 1003--1075.

**Scope restriction (actual first excited energy):** The positive projector
lower bound is also required to be an actual first excitation. The explicit
bound retains logarithms of the inverse gap. The physical support and
normalization conventions are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

open Matrix Real
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

theorem aklv_regionEntropy_le_short_side {L q k : ℕ}
    (hk : k ≤ L) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω ≤
      ((min k (L - k) : ℕ) : ℝ) * log (q : ℝ) := by
  classical
  let ρ := Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω
  have hρ := Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω
  have htrace : ρ.trace = 1 := Entropy.trace_regionState_eq_one hΩ
  have hrank : ρ.rank ≤ q ^ min k (L - k) := by
    rw [show ρ = cutMatrix Ω k * (cutMatrix Ω k)ᴴ from regionState_leftBlock_eq Ω k]
    exact (rank_mul_le_left _ _).trans (aklv_rank_cutMatrix_le_pow_min hk Ω)
  have hpos : 0 < (ρ.rank : ℝ) := by exact_mod_cast hρ.rank_pos_of_trace_one htrace
  change vonNeumannEntropy ρ _ ≤ _
  calc
    _ ≤ log (ρ.rank : ℝ) := vonNeumannEntropy_le_log_rank hρ htrace
    _ ≤ log ((q ^ min k (L - k) : ℕ) : ℝ) :=
      log_le_log hpos (by exact_mod_cast hrank)
    _ = _ := by rw [Nat.cast_pow, log_pow]

/-- The actual coherent changing-target filters imply a uniform entropy
bound at every physical cut. Exact finite-dimensional boundary estimates
cover endpoints and chains shorter than the initial window. -/
theorem exists_aklv_physical_entropy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L q : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h j) (interval L j.val (j.val + 2))) →
      (∀ j, 0 ≤ h j) → (∀ j, h j ≤ 1) → ‖Ω‖ = 1 →
      (∑ j, h j) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      ((∑ j, h j) - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ (∑ j, h j) →
      ∀ k : ℕ, k ≤ L →
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω ≤
        C / g * (1 + log (q : ℝ) + log (1 / g)) ^ 3 := by
  classical
  obtain ⟨A, hA, _hA21, hsequence⟩ := exists_aklv_physical_changing_target_sequence
  let C := 300000 * aklvInitialRankLogCoefficient A + (A + 1)
  have hC0 : 0 < aklvInitialRankLogCoefficient A := by
    have hlog : 0 ≤ log (A + 1) := log_nonneg (by linarith)
    unfold aklvInitialRankLogCoefficient
    positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro L q h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited k hk
  obtain ⟨_hL, hq, hg1⟩ :=
    aklv_chain_dimension_and_gap_bounds h hsupp h0 h1 mu g Ω hΩ hground hgap hg hexcited
  let u := 1 + log (q : ℝ) + log (1 / g)
  let s : ℕ := ⌈A * u ^ 2 / g⌉₊
  obtain ⟨hu, hs, hgapS, _hloggap, hT, hupper, hlogD⟩ :=
    aklv_initial_width_bounds hA hg hg1 q (by omega)
  change 1 ≤ u at hu
  change 1 ≤ s at hs
  change 1 / g ≤ (s : ℝ) at hgapS
  change aklvLogarithmicThreshold g ≤ 1040 * (s : ℝ) at hT
  change (s : ℝ) ≤ (A + 1) * u ^ 2 / g at hupper
  change log (((q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) : ℕ) : ℝ) ≤
    aklvInitialRankLogCoefficient A / g * u ^ 3 at hlogD
  by_cases hfit : ∃ a : ℕ, a + s / 2 = k ∧ a + s + 1 ≤ L
  · obtain ⟨a, hcenter, hfit⟩ := hfit
    obtain ⟨_hq, _hg1, _hs, _hlog, e, E0, ψ,
        _hregional, _henergy, _hE0, _hE6, hstates, _hinit, _hsteps⟩ :=
      hsequence L q a h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited hfit
    let ρ := Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω
    let H := Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω
    have hρ := Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω
    have htrace : ρ.trace = 1 := Entropy.trace_regionState_eq_one hΩ
    have htail (i : ℕ) : 1 - H.kyFanNorm (aklvSequenceRankBound q g s i) ≤
        aklvSequenceWeight i / 16 := by
      obtain ⟨hunit, herror, hrank⟩ := hstates i
      change (cutMatrix (ψ i) (a + s / 2)).rank ≤ aklvSequenceRankBound q g s i at hrank
      rw [hcenter] at hrank
      exact one_sub_kyFanNorm_le_of_unit_cut_rank_approximation Ω (ψ i)
        hΩ hunit herror hrank
    have hp (b : Fin (Fintype.card (Entropy.RegionConfig
        (fun _ : Fin L ↦ q) (leftBlock L k)))) : 0 ≤ H.eigenvalues₀ b := by
      simpa only [Matrix.IsHermitian.descEigenvalue, dite_eq_left b.isLt] using
        hρ.descEigenvalue_nonneg b.val
    have hsum : ∑ b, H.eigenvalues₀ b = 1 := by
      have h := H.sum_eigenvalues₀_filter_le 0
      rw [Entropy.trace_regionState_eq_one hΩ, Complex.one_re] at h
      simpa only [Nat.zero_le, Finset.filter_true, Matrix.IsHermitian.kyFanNorm_zero,
        sub_zero] using h
    have hent := probabilityEntropy_le_aklvSequenceRankBound hq hg hg1 hs hgapS hT
      (fun b ↦ H.eigenvalues₀ b) hp hsum (fun i _ ↦ by
        rw [H.sum_eigenvalues₀_filter_le, Entropy.trace_regionState_eq_one hΩ, Complex.one_re]
        exact htail i)
    have hbound : Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω ≤
        300000 * log (aklvSequenceRankBound q g s 0 : ℝ) := by
      rw [Entropy.regionEntropy, vonNeumannEntropy_eq_probabilityEntropy_eigenvalues₀]
      exact hent
    rw [(aklvSequenceRankBound_zero_succ q g s 0).1] at hbound
    calc
      _ ≤ 300000 * log (((q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) : ℕ) : ℝ) := hbound
      _ ≤ 300000 * (aklvInitialRankLogCoefficient A / g * u ^ 3) :=
        mul_le_mul_of_nonneg_left hlogD (by norm_num)
      _ = (300000 * aklvInitialRankLogCoefficient A) / g * u ^ 3 := by ring
      _ ≤ C / g * u ^ 3 := by gcongr; dsimp only [C]; linarith
  · have hshort := aklv_short_side_of_no_centered_window hk hfit
    have hsmall : min k (L - k) ≤ s := hshort.trans (Nat.sub_le _ _)
    have hlogq : log (q : ℝ) ≤ u := by
      have hgaplog : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
      dsimp only [u]
      linarith
    calc
      _ ≤ ((min k (L - k) : ℕ) : ℝ) * log (q : ℝ) :=
        aklv_regionEntropy_le_short_side hk Ω hΩ
      _ ≤ (s : ℝ) * u := mul_le_mul (by exact_mod_cast hsmall) hlogq
        (log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))) (Nat.cast_nonneg s)
      _ ≤ ((A + 1) * u ^ 2 / g) * u := mul_le_mul_of_nonneg_right hupper (by linarith)
      _ = (A + 1) / g * u ^ 3 := by ring
      _ ≤ C / g * u ^ 3 := by gcongr; dsimp only [C]; linarith

end TNLean.MPS.AreaLaw
