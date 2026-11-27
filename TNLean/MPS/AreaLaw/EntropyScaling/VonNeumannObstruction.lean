/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.EfficientApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TNLean.MPS.Tensor.OpenMPS.CutReducedState
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.ManyBody.Entropy.Cut.RegionTraceNorm
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Linear von Neumann entropy obstructs efficient MPS approximation

Efficient approximation bounds block entropy by an arbitrarily small multiple
of chain length plus a logarithmic remainder, uniformly in the chain length.
Consequently, positive linear entropy growth on macroscopic contiguous blocks
precludes efficient approximation. No consistency across lengths is assumed.
Source: SWVC08, arXiv:0705.0292v2, lines 278–305.

**Local fix (finite-chain range and boundary count):** the proof chooses accuracy
strictly below one and uses the two-boundary rank bound, as documented in
`docs/paper-gaps/swvc08_von_neumann_error_range.tex` and
`docs/paper-gaps/swvc08_interior_block_bond_rank.tex`. The qualitative obstruction
is unaffected by these corrections.

It also contains the following results.

* `TNLean.MPS.AreaLaw.IsOpenMPS.regionEntropy_interval_le_log_add_half_error`,
  `TNLean.MPS.AreaLaw.IsOpenMPS.regionEntropy_sdiff_interval_le_two_log_add_half_error`: von
  Neumann entropy bounds from MPS approximation.
-/

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

section VonNeumannApproximationLowerBound

/-!
## Von Neumann entropy bounds from MPS approximation

A unit chain vector approximated by an open-boundary MPS in full pure-density
trace norm with error `δ < 1` has regional entropy bounded by the logarithm of
the approximant's regional rank, plus `δ / 2` times the logarithm of the regional
dimension, plus `log 2`. The approximating vector need not be normalized.
A prefix uses one bond; a general contiguous block uses two.

**Local fix (error range and interior rank):** these theorems establish the
small-error range `δ < 1`, repairing the unrestricted printed range discussed
in `docs/paper-gaps/swvc08_von_neumann_error_range.tex`. The interior-block bound
has `2 * log D`, as documented in
`docs/paper-gaps/swvc08_interior_block_bond_rank.tex`. They do not formalize the
unrestricted printed entropy statement. Source: SWVC08, arXiv:0705.0292v2,
`paper_v2.tex`, lines 269–305.
-/

/-- The logarithm of an integer rank budget is unchanged by replacing zero by one,
with the convention `Real.log 0 = 0`. -/
private theorem log_max_one_nat (D : ℕ) : Real.log (max 1 D : ℕ) = Real.log D := by
  rw [Nat.cast_max, Nat.cast_one, ← Real.posLog_eq_log_max_one (Nat.cast_nonneg D)]
  exact max_eq_right (Real.log_natCast_nonneg D)

/-- The small-error von Neumann bound at a single chain boundary. This is the
corrected small-error form of SWVC08, arXiv:0705.0292v2, lines 278–305.
Empty and full prefixes and chains of length zero or one are included. -/
theorem IsOpenMPS.regionEntropy_interval_le_log_add_half_error {L q D : ℕ}
    {ψ φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) (hψ : ‖ψ‖ = 1) (k : ℕ)
    {δ : ℝ} (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin q) ψ (interval L 0 k) ≤
      Real.log D + δ / 2 * ((interval L 0 k).card : ℝ) * Real.log q + Real.log 2 := by
  have ht := Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error
    ψ φ hψ (interval L 0 k) (hφ.rank_regionState_interval_le_max k) hδ herror
  have hb := ManyBody.regionEntropy_le_log_rank_add_spectral_tail ψ hψ (interval L 0 k) ht
  simpa only [log_max_one_nat] using hb

/-- The small-error von Neumann bound for a contiguous block. Two boundaries give
`2 * log D`. This is the corrected form of SWVC08, arXiv:0705.0292v2,
lines 269–305, including empty blocks, endpoints, and short chains. -/
theorem IsOpenMPS.regionEntropy_sdiff_interval_le_two_log_add_half_error {L q D : ℕ}
    {ψ φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) (hψ : ‖ψ‖ = 1)
    {a b : ℕ} (hab : a ≤ b) {δ : ℝ} (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin q)
      ψ (interval L 0 b \ interval L 0 a) ≤
      2 * Real.log D + δ / 2 * ((interval L 0 b \ interval L 0 a).card : ℝ) *
        Real.log q + Real.log 2 := by
  have ht := Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error
    ψ φ hψ (interval L 0 b \ interval L 0 a)
    (hφ.rank_regionState_sdiff_interval_le_max_sq hab) hδ herror
  have hb := ManyBody.regionEntropy_le_log_rank_add_spectral_tail ψ hψ
    (interval L 0 b \ interval L 0 a) ht
  simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, log_max_one_nat] using hb

end VonNeumannApproximationLowerBound

section VonNeumannObstruction

/-- Efficient approximation forces arbitrarily small linear entropy bounds up to
a logarithmic remainder. This follows from the corrected small-error estimate
in SWVC08, arXiv:0705.0292v2, lines 278–305. -/
theorem IsEfficientlyApproximableByMPS.exists_vonNeumann_bound
    {q : ℕ} {lengths : Set ℕ}
    {ψ : ∀ N : lengths, EuclideanSpace ℂ (Fin N.val → Fin q)}
    (happrox : IsEfficientlyApproximableByMPS ψ) (hψ : ∀ N, ‖ψ N‖ = 1)
    (a b : lengths → ℕ) (hab : ∀ N, a N ≤ b N) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∃ m : ℕ, ∀ N : lengths,
      ManyBody.regionEntropy (X := fun _ ↦ Fin q)
        (ψ N) (interval N.val 0 (b N) \ interval N.val 0 (a N)) ≤
        K + (m : ℝ) * Real.log ((N.val : ℝ) + 1) + ε * N.val := by
  let δ := min (1 / 2 : ℝ) (ε / (Real.log q + 1))
  have hlq := Real.log_natCast_nonneg q
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hcoef : δ / 2 * Real.log q ≤ ε := by
    have h := (le_div_iff₀ (show 0 < Real.log q + 1 by linarith)).mp
      (min_le_right (1 / 2 : ℝ) (ε / (Real.log q + 1)))
    change δ * (Real.log q + 1) ≤ ε at h
    nlinarith
  obtain ⟨C, hC, m, happrox⟩ := happrox δ hδpos
  refine ⟨2 * |Real.log C| + Real.log 2, 2 * m, fun N ↦ ?_⟩
  obtain ⟨D, φ, hD, hφ, herror⟩ := happrox N
  have hbound := hφ.regionEntropy_sdiff_interval_le_two_log_add_half_error
    (hψ N) (hab N) hδ herror
  have hx : 0 < (N.val : ℝ) + 1 := by positivity
  have hlogD : Real.log D ≤ |Real.log C| + (m : ℝ) * Real.log ((N.val : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos D with rfl | hDpos
    · simp only [Nat.cast_zero, Real.log_zero]
      exact add_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by linarith [(show (0 : ℝ) ≤ N.val from Nat.cast_nonneg _)])))
    · have hlog := Real.log_le_log (Nat.cast_pos.mpr hDpos) hD
      rw [Real.log_mul hC.ne' (pow_pos hx m).ne', Real.log_pow] at hlog
      exact hlog.trans (add_le_add (le_abs_self _) le_rfl)
  have hcard : ((interval N.val 0 (b N) \ interval N.val 0 (a N)).card : ℝ) ≤ N.val := by
    have h := Finset.card_le_univ (interval N.val 0 (b N) \ interval N.val 0 (a N))
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  have hmass := mul_le_mul_of_nonneg_right hcoef
    (Nat.cast_nonneg (interval N.val 0 (b N) \ interval N.val 0 (a N)).card)
  have hmass' := mul_le_mul_of_nonneg_left hcard hε.le
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

open Filter Asymptotics in
/-- A logarithmic function with an additive constant is eventually smaller than any
positive linear function. -/
private theorem eventually_logarithmic_lt_linear (K m : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, K + m * Real.log x < c * x := by
  have hconst : (fun _ : ℝ ↦ K) =o[atTop] (fun x : ℝ ↦ x) :=
    isLittleO_const_left.mpr (Or.inr tendsto_abs_atTop_atTop)
  have hf := hconst.add (Real.isLittleO_log_id_atTop.const_mul_left m)
  filter_upwards [hf.bound (show 0 < c / 2 by positivity), eventually_gt_atTop (0 : ℝ)]
    with x hb hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx] at hb
  nlinarith [le_abs_self (K + m * Real.log x)]

/-- Positive linear von Neumann entropy growth on macroscopic contiguous blocks
precludes efficient MPS approximation. This is the qualitative obstruction of
SWVC08, arXiv:0705.0292v2, lines 278–305, proved using the corrected finite-chain
estimate. Arbitrary infinite sets of lengths and finite exceptional lengths
are allowed. -/
theorem not_isEfficientlyApproximableByMPS_of_linear_vonNeumann_growth
    {q : ℕ} {lengths : Set ℕ}
    {ψ : ∀ N : lengths, EuclideanSpace ℂ (Fin N.val → Fin q)}
    (hlengths : lengths.Infinite) (hψ : ∀ N, ‖ψ N‖ = 1)
    (a b : lengths → ℕ) (hab : ∀ N, a N ≤ b N)
    {c η : ℝ} (hc : 0 < c) (hη : 0 < η) (N₀ : ℕ)
    (hlinear : ∀ N : lengths, N₀ ≤ N.val →
      η * (N.val : ℝ) ≤ ((interval N.val 0 (b N) \ interval N.val 0 (a N)).card : ℝ))
    (hentropy : ∀ N : lengths, N₀ ≤ N.val →
      c * ((interval N.val 0 (b N) \ interval N.val 0 (a N)).card : ℝ) ≤
        ManyBody.regionEntropy (X := fun _ ↦ Fin q)
          (ψ N) (interval N.val 0 (b N) \ interval N.val 0 (a N))) :
    ¬ IsEfficientlyApproximableByMPS ψ := by
  intro happrox
  have hcη : 0 < c * η := mul_pos hc hη
  obtain ⟨K, m, hbound⟩ := happrox.exists_vonNeumann_bound hψ a b hab (half_pos hcη)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    (eventually_logarithmic_lt_linear K (m : ℝ) (show 0 < c * η / 4 by positivity))
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max x₀ 1)
  obtain ⟨n, hn, hnlarge⟩ := hlengths.exists_gt (max N₀ n₀)
  let N : lengths := ⟨n, hn⟩
  have hN₀ : N₀ ≤ N.val := by dsimp only [N]; omega
  have hnn₀ : (n₀ : ℝ) < (N.val : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (le_max_right N₀ n₀) hnlarge)
  have hN₁ : (1 : ℝ) ≤ N.val := by linarith [le_max_right x₀ 1]
  have hxN : x₀ ≤ (N.val : ℝ) + 1 := by linarith [le_max_left x₀ 1]
  have hlog := hx₀ _ hxN
  have hscale : c * η / 4 * ((N.val : ℝ) + 1) ≤ c * η / 2 * N.val := by
    nlinarith [mul_nonneg hcη.le (sub_nonneg.mpr hN₁)]
  have hlower := (mul_le_mul_of_nonneg_left (hlinear N hN₀) hc.le).trans (hentropy N hN₀)
  have hupper := hbound N
  nlinarith [hlog.trans_le hscale]

end VonNeumannObstruction

end TNLean.MPS.AreaLaw
