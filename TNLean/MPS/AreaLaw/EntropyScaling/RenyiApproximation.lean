/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.EfficientApproximation
import TNLean.MPS.AreaLaw.MPSApproximation
import TNLean.Algebra.FlatDensityRenyiEntropy
import QICLean.Entropy.RenyiTail
import QICLean.Analysis.SubnormalizedPureStateError

/-!
# Matrix product state approximation from Rényi entropy bounds

Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, `paper_v2.tex`,
lines 198–210 and 271–276; Verstraete–Cirac, arXiv:cond-mat/0505140v6, Lemmas 1 and 2.
The approximants are normalized, and the error is the full trace norm of the
pure-density difference. The accuracy is fixed before choosing the polynomial
bond bound, which is uniform over the family. Order zero is treated by rank.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace TNLean.MPS.AreaLaw

/-- Verstraete–Cirac Lemma 2 in terms of the existing Rényi entropy and Ky Fan tail. -/
theorem one_sub_kyFanNorm_le_of_renyiEntropy_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {a T : ℝ} {D : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) (hT : 0 < T)
    (hS : renyiEntropy ρ hρ.isHermitian a ≤
      Real.log ((D : ℝ) / (1 - a)) + a / (1 - a) * Real.log T) :
    1 - hρ.isHermitian.kyFanNorm D ≤ T := by
  have heq : (∑ i ∈ Finset.univ.filter
      (fun i : Fin (Fintype.card ι) ↦ D ≤ i.val), hρ.isHermitian.eigenvalues₀ i) =
      1 - hρ.isHermitian.kyFanNorm D := by
    simpa [htr] using hρ.isHermitian.sum_eigenvalues₀_filter_le D
  rw [← heq]
  by_cases ht : 0 < ∑ i ∈ Finset.univ.filter
      (fun i : Fin (Fintype.card ι) ↦ D ≤ i.val), hρ.isHermitian.eigenvalues₀ i
  · apply (Real.log_le_log_iff ht hT).mp
    have hb : 0 < 1 - a := sub_pos.mpr ha1
    have hbound := hρ.log_eigenvalue_tail_le hD ha ha1 ht
    simp only [renyiEntropy, ha.ne', ha1.ne, ↓reduceIte, inv_mul_eq_div] at hS
    calc
      _ ≤ (1 - a) / a * (a / (1 - a) * Real.log T) := hbound.trans
        (mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hb.le ha.le))
      _ = _ := by field_simp
  · exact (le_of_not_gt ht).trans hT.le

private theorem exists_normalized_isOpenMPS_of_sq_error {L q D : ℕ}
    {ψ Φ : EuclideanSpace ℂ (Fin L → Fin q)} (hψ : ‖ψ‖ = 1)
    (hΦ : IsOpenMPS L q D (fun x ↦ Φ x)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (herr : ‖Φ - ψ‖ ^ 2 ≤ (δ / 4) ^ 2) :
    ∃ χ : EuclideanSpace ℂ (Fin L → Fin q), ‖χ‖ = 1 ∧
      IsOpenMPS L q D (fun x ↦ χ x) ∧
      rectangularTraceNorm (euclideanOuterProduct ψ ψ - euclideanOuterProduct χ χ) ≤ δ := by
  have he : ‖Φ - ψ‖ ≤ δ / 4 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp herr
  have hpos : 0 < ‖Φ‖ := by
    have hn := norm_sub_norm_le ψ Φ
    rw [hψ, norm_sub_rev] at hn
    linarith
  let c : ℂ := (‖Φ‖ : ℂ)⁻¹
  let χ : EuclideanSpace ℂ (Fin L → Fin q) := c • Φ
  have hχ : ‖χ‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) (norm_pos_iff.mp hpos)
  have hdiff : ‖χ - Φ‖ = |1 - ‖Φ‖| := by
    have hs : χ - Φ = ((‖Φ‖⁻¹ - 1 : ℝ) : ℂ) • Φ := by
      simp [χ, c, sub_smul]
    rw [hs, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      ← abs_of_nonneg (norm_nonneg Φ), ← abs_mul]
    congr 1
    rw [abs_of_nonneg (norm_nonneg Φ)]
    field_simp
  have hdiff_le : ‖χ - Φ‖ ≤ ‖Φ - ψ‖ := by
    simpa [hdiff, hψ, norm_sub_rev] using abs_norm_sub_norm_le ψ Φ
  have hdist : ‖χ - ψ‖ ≤ δ / 2 := (norm_sub_le_norm_sub_add_norm_sub χ Φ ψ).trans (by linarith)
  refine ⟨χ, hχ, hΦ.smul c,
    (rectangularTraceNorm_pure_density_sub_le_two ψ χ hψ.le hχ.le).trans ?_⟩
  nlinarith [norm_sub_rev ψ χ]

/-- Finite-chain consequence of Verstraete–Cirac Lemmas 1 and 2, with normalized
approximants and full trace norm. The denominator `L + 1` also covers empty chains. -/
theorem exists_normalized_isOpenMPS_of_renyiEntropy_le {L q D : ℕ}
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
    {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hS : ∀ k ∈ Finset.Ico 1 L,
      renyiEntropy (Entropy.regionState (leftBlock L k) ψ)
        (Entropy.regionState_isHermitian (leftBlock L k) ψ) a ≤
      Real.log ((D : ℝ) / (1 - a)) + a / (1 - a) *
        Real.log (δ ^ 2 / (16 * ((L : ℝ) + 1)))) :
    ∃ χ : EuclideanSpace ℂ (Fin L → Fin q), ‖χ‖ = 1 ∧
      IsOpenMPS L q D (fun x ↦ χ x) ∧
      rectangularTraceNorm (euclideanOuterProduct ψ ψ - euclideanOuterProduct χ χ) ≤ δ := by
  have hmps := (isOpenMPS_sequentialTruncation_leadingEigenprojection ψ hψ D).1
  apply exists_normalized_isOpenMPS_of_sq_error hψ hmps hδ hδ1
  refine (norm_sequentialTruncation_leadingEigenprojection_sub_sq_le ψ hψ D).trans ?_
  have htail (k : ℕ) (hk : k ∈ Finset.Ico 1 L) :
      1 - (Entropy.regionState_isHermitian (leftBlock L k) ψ).kyFanNorm D ≤
        δ ^ 2 / (16 * ((L : ℝ) + 1)) :=
    one_sub_kyFanNorm_le_of_renyiEntropy_le
      (Entropy.regionState_posSemidef (leftBlock L k) ψ)
      (Entropy.trace_regionState_eq_one hψ) ha ha1 hD (by positivity) (hS k hk)
  refine (Finset.sum_le_sum htail).trans ?_
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 1 := by
    exact_mod_cast (by omega : L - 1 ≤ L + 1)
  refine (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq ?_
  field_simp
  ring

/-- The order-zero case of Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2,
lines 271–276: a bound on every internal marginal rank gives an exact MPS. -/
theorem isOpenMPS_of_regionState_rank_le {L q D : ℕ}
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
    (hr : ∀ k ∈ Finset.Ico 1 L, (Entropy.regionState (leftBlock L k) ψ).rank ≤ D) :
    IsOpenMPS L q D (fun x ↦ ψ x) := by
  have ht (k : ℕ) (hk : k ∈ Finset.Ico 1 L) :
      1 - (Entropy.regionState_isHermitian (leftBlock L k) ψ).kyFanNorm D = 0 := by
    have he := (Entropy.regionState_isHermitian (leftBlock L k) ψ).sum_eigenvalues₀_filter_le D
    have hz := Matrix.PosSemidef.eigenvalue_tail_eq_zero_of_rank_le
      (Entropy.regionState_posSemidef (leftBlock L k) ψ) (hr k hk)
    simpa [Entropy.trace_regionState_eq_one hψ] using he.symm.trans hz
  have he := norm_sequentialTruncation_leadingEigenprojection_sub_sq_le ψ hψ D
  simp only [Finset.sum_eq_zero ht] at he
  have heq := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm he (sq_nonneg _))))
  simpa only [heq] using (isOpenMPS_sequentialTruncation_leadingEigenprojection ψ hψ D).1

private theorem exists_polynomial_renyi_cutoff {a c c' δ : ℝ}
    (ha1 : a < 1) (hδ : 0 < δ) :
    ∃ K m : ℕ, 0 < K ∧ ∀ N : ℕ,
      c * Real.log ((N : ℝ) + 1) + c' ≤
        Real.log (((K * (N + 1) ^ m : ℕ) : ℝ) / (1 - a)) +
          a / (1 - a) * Real.log (δ ^ 2 / (16 * ((N : ℝ) + 1))) := by
  let t := a / (1 - a)
  let b := c' + t * Real.log (16 / δ ^ 2) + Real.log (1 - a)
  let K := ⌈Real.exp b⌉₊ + 1
  let m := ⌈c + t⌉₊
  refine ⟨K, m, by dsimp [K]; omega, ?_⟩
  intro N
  have hK : Real.exp b ≤ (K : ℝ) := (Nat.le_ceil _).trans (by simp [K])
  have hbK : b ≤ Real.log K := by simpa using Real.log_le_log (Real.exp_pos b) hK
  have hm : (c + t) * Real.log ((N : ℝ) + 1) ≤ (m : ℝ) * Real.log ((N : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil _)
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith))
  have hp : 0 < (K : ℝ) ∧ 0 < 1 - a ∧ 0 < (N : ℝ) + 1 :=
    ⟨(Real.exp_pos b).trans_le hK, sub_pos.mpr ha1, by positivity⟩
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Real.log_div (mul_pos hp.1 (pow_pos hp.2.2 m)).ne' hp.2.1.ne',
    Real.log_mul hp.1.ne' (pow_pos hp.2.2 m).ne', Real.log_pow]
  rw [Real.log_div (pow_pos hδ 2).ne' (mul_pos (by norm_num : (0 : ℝ) < 16) hp.2.2).ne',
    Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hp.2.2.ne']
  simp only [b, Real.log_div (by norm_num : (16 : ℝ) ≠ 0) (pow_pos hδ 2).ne'] at hbK
  dsimp [t] at hbK hm
  nlinarith only [hbK, hm]

/-- Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, lines 271–276:
a uniform logarithmic bound on Rényi entropy at an order below one implies
efficient MPS approximation. It suffices to bound the internal prefix marginals.
The constants and the Rényi order are independent of the chain length and the
accuracy. Order zero is proved separately by exact rank bounds. -/
theorem isEfficientlyApproximableByMPS_of_renyiEntropy_le
    {q : ℕ} {lengths : Set ℕ}
    (ψ : ∀ N : lengths, EuclideanSpace ℂ (Fin N.val → Fin q))
    (hψ : ∀ N, ‖ψ N‖ = 1) {a c c' : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hc : 0 ≤ c)
    (hS : ∀ (N : lengths) (k : ℕ), k ∈ Finset.Ico 1 N.val →
      renyiEntropy (Entropy.regionState (leftBlock N.val k) (ψ N))
        (Entropy.regionState_isHermitian (leftBlock N.val k) (ψ N)) a ≤
        c * Real.log (N.val : ℝ) + c') :
    IsEfficientlyApproximableByMPS ψ := by
  intro δ hδ
  let ε := min δ 1
  have hε : 0 < ε := lt_min hδ zero_lt_one
  obtain ⟨K, m, hK, hbound⟩ := exists_polynomial_renyi_cutoff (c := c) (c' := c') ha1 hε
  refine ⟨K, by exact_mod_cast hK, m, ?_⟩
  intro N
  have hcut (k : ℕ) (hk : k ∈ Finset.Ico 1 N.val) :
      renyiEntropy (Entropy.regionState (leftBlock N.val k) (ψ N))
        (Entropy.regionState_isHermitian (leftBlock N.val k) (ψ N)) a ≤
      Real.log (((K * (N.val + 1) ^ m : ℕ) : ℝ) / (1 - a)) +
        a / (1 - a) * Real.log (ε ^ 2 / (16 * ((N.val : ℝ) + 1))) := by
    refine (hS N k hk).trans (le_trans ?_ (hbound N.val))
    gcongr
    · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
        ((Finset.mem_Ico.mp hk).1.trans (Finset.mem_Ico.mp hk).2.le))
    · linarith
  have hD : 0 < K * (N.val + 1) ^ m := Nat.mul_pos hK (pow_pos (Nat.succ_pos _) _)
  by_cases ha0 : a = 0
  · refine ⟨K * (N.val + 1) ^ m, ψ N, by simp, hψ N, ?_, by simpa using hδ.le⟩
    apply isOpenMPS_of_regionState_rank_le (ψ N) (hψ N)
    intro k hk
    have hl : Real.log ((Entropy.regionState (leftBlock N.val k) (ψ N)).rank : ℝ) ≤
        Real.log ((K * (N.val + 1) ^ m : ℕ) : ℝ) := by
      simpa [ha0, renyiEntropy] using hcut k hk
    rcases Nat.eq_zero_or_pos (Entropy.regionState (leftBlock N.val k) (ψ N)).rank with hr | hr
    · simp [hr]
    · exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hr) (by exact_mod_cast hD)).mp hl
  · obtain ⟨φ, hφ, hmps, herr⟩ := exists_normalized_isOpenMPS_of_renyiEntropy_le
      (ψ N) (hψ N) (lt_of_le_of_ne ha (Ne.symm ha0)) ha1 hD hε (min_le_right _ _) hcut
    exact ⟨_, φ, by simp, hφ, hmps, herr.trans (min_le_left _ _)⟩

end TNLean.MPS.AreaLaw
