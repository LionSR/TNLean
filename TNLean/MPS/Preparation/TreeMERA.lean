/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.BinaryMERA

/-!
# The tree-RG circuit as a finite-range MERA

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, paragraph "Connection to MERA") observe that
the tree-RG circuit of eq. (16) is a finite-range MERA with `O(log log N)` layers: the
isometries `V⁽ʲ⁾` of eq. (16) are the isometries of the MERA, and all disentanglers are the
identity except those of the first layer, which prepare the fixed-point state. Hence, within
the approximation error, normal translation-invariant MPS are finite-range MERA with
`O(log log N)` layers.

This file gives a minimal definition of a binary finite-range MERA on a ring and proves the
statement for block length `q = 2^{k+1}`.

## The MERA

A `MPSPreparation.BinaryMERA n D k` consists of

* one layer of disentanglers: a unitary `u` on `ℂ^D ⊗ ℂ^D`, applied to `|0⟩|0⟩` on every
  pair `R_i L_{i+1}` of neighbouring bond legs of the ring of top sites `ℂ^{D²} = L_i ⊗ R_i`;
* `k + 1` layers of isometries: `k` coarse isometries `ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` and a finest
  isometry `ℂ^{D²} → ℂⁿ ⊗ ℂⁿ`, each copied on every site of its layer.

Every isometry maps one site to two neighbouring sites and every disentangler acts on two
neighbouring legs, so the network has range two and bond dimension `D²` in every layer. The
disentanglers of the lower layers are the identity, as in the source's identification; the
class is therefore a subclass of the finite-range MERA with `k + 2` layers.

## Main declarations

* `MPSTensor.binaryTreeMatrix` — the product `W^{⊗2^k} (V₀)^{⊗2^{k-1}} ⋯ V_{k-1}` of a
  binary tree of layers, regrouped along neighbouring pairs.
* `MPSPreparation.BinaryMERA` and `MPSPreparation.BinaryMERA.state` — the MERA and its state on
  `M 2^{k+1}` sites; `MPSPreparation.BinaryMERA.norm_state` — the state is a unit vector.
* `MPSPreparation.treeMERA` — the MERA whose isometries are the layers `V⁽ʲ⁾` of eq. (16) and
  whose disentanglers prepare the pairs `|ω⟩` of the fixed-point state.
* `MPSPreparation.approximatingMPVState_eq_state_treeMERA` — the approximating state
  `|φ'_N⟩ = V^{⊗M} |Ω⟩` of eq. (10) for `q = 2^{k+1}` is the state of `treeMERA` (exact).
* `MPSPreparation.exists_state_treeMERA_approximationError_le` — with the approximation-error
  bound `exists_approximationError_le_mul` at `γ = 1/2` (the rate `e^{-2γq/ξ}` of that theorem,
  which strengthens Lemma 1'(i) of the source, stated there for `0 < γ < 1/2` with rate
  `e^{-γq/ξ}`), the error of the MERA state against `|φ_N⟩` is at most `ε` once
  `2^{k+1} ≥ ξ log(C N/ε)`;
  `MPSPreparation.exists_state_treeMERA_approximationError_le_and_le_logb` shows that for every
  `M` such a `k` exists with `k ≤ log₂(max 1 (ξ log(C N/ε)))`, so
  `k + 1 = O(log log(N/ε))` layers suffice.
* `MPSPreparation.mul_mul_exp_neg_div_le_of_mul_log_le` and
  `MPSPreparation.exists_mul_log_le_mul_two_pow_and_le_logb` — the two real inequalities behind
  these bounds, also used with registers of `s` sites in
  `TNLean.MPS.Preparation.TreeMERARegisters`.

**Scope restriction (chain length):** the theorems
`approximatingMPVState_eq_state_treeMERA`, `exists_state_treeMERA_approximationError_le` and
`exists_state_treeMERA_approximationError_le_and_le_logb` (and the definition `treeMERA`) assume
that the two-site blocked tensor is injective, so that every layer `V⁽ʲ⁾` is an isometry, as in
the source, whose eq. (16) starts from a blocked tensor and calls the layers isometries.
`TNLean.MPS.Preparation.TreeMERARegisters` applies `treeMERA` to the tensor blocked over `s`
sites, with registers of `s` sites, and covers every normal tensor. The chain length is
`N = M 2^{k+1}`: the layer count holds for the chain lengths `M 2^{k+1}` with `k` given by the
threshold, not for every fixed `N` and `ε` (for `N = 2p` with `p` odd only `k = 0` is available).
The sibling construction in `TNLean.MPS.Preparation.UnequalTreeMERA` covers every positive
length with nonzero periodic state, using uniformly bounded physical leaves chosen before
`N` and `ε`. The resolved scope is documented in `docs/paper-gaps/mswc24_tree_mera_scope.tex`.

## References

* arXiv:2307.01696, paragraphs "The tree-RG circuit" (eq. (16)) and "Connection to MERA".
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSPreparation

variable {d n D k : ℕ}

/-- **The approximating state is a MERA state** (arXiv:2307.01696, paragraph "Connection to
MERA", with eqs. (10) and (16)). Let the two-site blocked tensor of `A` be injective, let
`σ ≥ 0` with `Tr σ = 1`, and let `u` be a unitary with `u |0⟩|0⟩ = |ω⟩`. For block length
`q = 2^{k+1}` and `M ≥ 1` blocks, the approximating state `|φ'_N⟩ = V^{⊗M} |Ω⟩` of eq. (10) is
exactly the state of the tree-RG MERA with `k + 1` isometry layers. -/
theorem approximatingMPVState_eq_state_treeMERA [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsInjective (blockTensor A 2)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (k M : ℕ) [NeZero M]
    (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ) (hu0 : ∀ p, u p (0, 0) = fixedPointPair σ p) :
    approximatingMPVState A σ (2 ^ (k + 1)) M = (treeMERA A hA k u hu).state M := by
  have hq : Kraus.IsInjective (blockTensor A (2 ^ (k + 1))) := by
    have := blockTensor_isInjective_mul_of_blockTensor_isInjective A
      (pow_pos two_pos k) hA
    rwa [← pow_succ] at this
  rw [(inner_approximatingMPVState_mpvState A hq hσ htr M).1]
  have htop : (treeMERA A hA k u hu).topPair = fixedPointPair σ := funext hu0
  have htree : (treeMERA A hA k u hu).treeMatrix = polarIsoMatrix (blockTensor A (2 ^ (k + 1))) :=
    (binaryTreeMatrix_treeLayers k A).trans (polarIsoMatrix_blockTensor_eq_treeIsoMatrix k A).symm
  ext s
  rw [approximatingMPVStateRaw_apply, BinaryMERA.state_apply, BinaryMERA.amplitude, htop, htree,
    mpv_approximatingTensor]

/-! ### The threshold of the number of layers -/

/-- **From the threshold of the MERA to the error.** For `K, ξ, ε > 0` and `M, q ≥ 1`, if
`ξ log(K M q/ε) ≤ q` then `K (M e^{-q/ξ}) ≤ ε`. -/
theorem mul_mul_exp_neg_div_le_of_mul_log_le {K M q ξ ε : ℝ} (hK : 0 < K) (hM : 1 ≤ M)
    (hq : 1 ≤ q) (hξ : 0 < ξ) (hε : 0 < ε) (h : ξ * Real.log (K * (M * q) / ε) ≤ q) :
    K * (M * Real.exp (-(q / ξ))) ≤ ε := by
  have hM0 : 0 < M := by linarith
  refine mul_mul_exp_neg_le_of_log_le hK hM0 hε ?_
  rw [← Real.log_mul hK.ne' hM0.ne', ← Real.log_div (by positivity) hε.ne', le_div_iff₀ hξ]
  refine le_trans ?_ ((mul_comm _ _).trans_le h)
  refine mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) ?_) hξ.le
  gcongr
  exact le_mul_of_one_le_right hM0.le hq

/-- **The least number of layers with the threshold.** For `ξ, C, M, ε > 0` and `s ≥ 1` there is
`k` with `x ≤ s 2^{k+1}` and `k ≤ log₂(max 1 x)`, where `x = ξ log(C M s 2^{k+1}/ε)`. The left
side of the threshold grows linearly in `k` and the right side exponentially; for the least such
`k`, if `k ≥ 1` the threshold fails at `k - 1`, so `2^k ≤ s 2^k < x`. -/
theorem exists_mul_log_le_mul_two_pow_and_le_logb {ξ C M ε s : ℝ} (hξ : 0 < ξ) (hC : 0 < C)
    (hM : 0 < M) (hε : 0 < ε) (hs : 1 ≤ s) : ∃ k : ℕ,
      ξ * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε) ≤ s * 2 ^ (k + 1) ∧
      (k : ℝ) ≤ Real.logb 2 (max 1 (ξ * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε))) := by
  classical
  set x : ℕ → ℝ := fun k => ξ * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε) with hx
  have hxk : ∀ k : ℕ,
      x k = ξ * Real.log (C * M * s / ε) + ξ * Real.log 2 * ((k + 1 : ℕ) : ℝ) := by
    intro k
    simp only [hx]
    rw [show C * (M * (s * 2 ^ (k + 1))) / ε = C * M * s / ε * 2 ^ (k + 1) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hex : ∃ k, x k ≤ s * 2 ^ (k + 1) := by
    have hlim : Filter.Tendsto (fun m : ℕ => ξ * Real.log (C * M * s / ε) * ((m : ℝ) ^ 0 / 2 ^ m) +
        ξ * Real.log 2 * ((m : ℝ) ^ 1 / 2 ^ m)) Filter.atTop (nhds 0) := by
      simpa using ((tendsto_pow_const_div_const_pow_of_one_lt 0 one_lt_two).const_mul
        (ξ * Real.log (C * M * s / ε))).add
          ((tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_two).const_mul (ξ * Real.log 2))
    obtain ⟨m, hm1, hm⟩ := ((Filter.eventually_ge_atTop 1).and
      (hlim.eventually (gt_mem_nhds one_pos))).exists
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine ⟨k, ?_⟩
    rw [hxk]
    have h2m : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    simp only [pow_zero, pow_one] at hm
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_lt_one h2m, mul_one] at hm
    calc _ ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hm.le
      _ ≤ s * 2 ^ (k + 1) := le_mul_of_one_le_left h2m.le hs
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  obtain h0 | ⟨j, hj⟩ : Nat.find hex = 0 ∨ ∃ j, Nat.find hex = j + 1 :=
    (Nat.eq_zero_or_pos _).imp id fun hpos => ⟨Nat.find hex - 1, by omega⟩
  · rw [h0, Nat.cast_zero]
    exact Real.logb_nonneg one_lt_two (le_max_left _ _)
  · rw [hj]
    have hfail : ¬ x j ≤ s * 2 ^ (j + 1) := Nat.find_min hex (by omega)
    have hmono : x j ≤ x (j + 1) := by
      rw [hxk, hxk]
      have : 0 ≤ ξ * Real.log 2 := mul_nonneg hξ.le (Real.log_nonneg one_le_two)
      gcongr
      omega
    have hlt : (2 : ℝ) ^ (j + 1) < x (j + 1) :=
      (le_mul_of_one_le_left (by positivity) hs).trans_lt ((not_le.1 hfail).trans_le hmono)
    have hx1 : 1 < x (j + 1) := (one_le_pow₀ one_le_two).trans_lt hlt
    rw [max_eq_right hx1.le]
    refine (Real.lt_logb_iff_rpow_lt one_lt_two (zero_lt_one.trans hx1)).2 ?_ |>.le
    rwa [Real.rpow_natCast]

/-- **Normal MPS are finite-range MERA with `O(log log(N/ε))` layers, within `ε`**
(arXiv:2307.01696, paragraph "Connection to MERA"). Let `A` be normal, in the
gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` of eq. (5), let `0 < t < 1` bound the
moduli of the eigenvalues of `E_A` other than `1`, with `ξ = -1/log t`, and let the two-site
blocked tensor of `A` be injective. Then there is `C > 0` such that for every unitary `u` with
`u |0⟩|0⟩ = |ω⟩`, every `ε > 0`, and every `k` and `M ≥ 1` with
`ξ log(C N/ε) ≤ 2^{k+1}`, `N = M 2^{k+1}`, the state of the tree-RG MERA with `k + 1` isometry
layers has error `1 - |⟨ψ|φ_N⟩| ≤ ε` against the normalized state `|φ_N⟩` of `A`.

The error bound is `exists_approximationError_le_mul` at `γ = 1/2`, with rate `e^{-q/ξ}`; that
theorem strengthens Lemma 1'(i) of the source, which is stated for `0 < γ < 1/2` with rate
`e^{-γq/ξ}` and would give the threshold `(ξ/γ) log(C N/ε)` instead. The MERA state is the
approximating state (`approximatingMPVState_eq_state_treeMERA`). -/
theorem exists_state_treeMERA_approximationError_le [NeZero D] (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) (h2 : Kraus.IsInjective (blockTensor A 2))
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ), (∀ p, u p (0, 0) = fixedPointPair σ p) →
      ∀ ε : ℝ, 0 < ε → ∀ (k M : ℕ) [NeZero M],
        correlationLength (t : ℂ) * Real.log (C * (M * 2 ^ (k + 1)) / ε) ≤ 2 ^ (k + 1) →
          1 - ‖⟪(treeMERA A h2 k u hu).state M, normalizedMPVState A (M * 2 ^ (k + 1))⟫_ℂ‖ ≤
            ε := by
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hξ : 0 < correlationLength (t : ℂ) :=
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])
  obtain ⟨K, hK, herr⟩ := exists_approximationError_le_mul A hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm.symm)
    (γ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨K, hK, fun u hu hu0 ε hε k M _ hk => ?_⟩
  rw [← approximatingMPVState_eq_state_treeMERA A h2 hσ.posSemidef htr k M u hu hu0]
  refine (herr _ M).trans ?_
  set ξ := correlationLength (t : ℂ)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hq1 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ one_le_two
  have hexp : Real.exp (-(2 * (1 / 2 : ℝ)) * ((2 ^ (k + 1) : ℕ) : ℝ) / ξ) =
      Real.exp (-((2 : ℝ) ^ (k + 1) / ξ)) := by
    push_cast
    ring_nf
  rw [hexp]
  exact mul_mul_exp_neg_div_le_of_mul_log_le hK hM1 hq1 hξ hε hk

/-- **The number of layers is `O(log log(N/ε))`** (arXiv:2307.01696, paragraph "Connection to
MERA": "a finite-range MERA with $O(\log \log N)$ layers"). In the setting of
`exists_state_treeMERA_approximationError_le`, for every unitary `u` with `u |0⟩|0⟩ = |ω⟩`, every
`ε > 0` and every `M ≥ 1` there is `k` such that, with `N = M 2^{k+1}` and
`x = ξ log(C N/ε)`, the threshold `x ≤ 2^{k+1}` holds, the tree-RG MERA with `k + 1` isometry
layers has error at most `ε`, and `k ≤ log₂(max 1 x)`. The exponent `k` is the least one with the
threshold: the left side of the threshold grows linearly in `k` and the right side exponentially,
and if `k ≥ 1` the threshold fails at `k - 1`, so `2^k < x`. -/
theorem exists_state_treeMERA_approximationError_le_and_le_logb [NeZero D] (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) (h2 : Kraus.IsInjective (blockTensor A 2))
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ), (∀ p, u p (0, 0) = fixedPointPair σ p) →
      ∀ ε : ℝ, 0 < ε → ∀ (M : ℕ) [NeZero M], ∃ k : ℕ,
        correlationLength (t : ℂ) * Real.log (C * (M * 2 ^ (k + 1)) / ε) ≤ 2 ^ (k + 1) ∧
        1 - ‖⟪(treeMERA A h2 k u hu).state M, normalizedMPVState A (M * 2 ^ (k + 1))⟫_ℂ‖ ≤ ε ∧
        (k : ℝ) ≤ Real.logb 2 (max 1
          (correlationLength (t : ℂ) * Real.log (C * (M * 2 ^ (k + 1)) / ε))) := by
  obtain ⟨C, hC, h⟩ := exists_state_treeMERA_approximationError_le A hN hA h2 hσ htr hfix ht0 ht1
    hlam
  refine ⟨C, hC, fun u hu hu0 ε hε M _ => ?_⟩
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨k, hk, hlog⟩ := exists_mul_log_le_mul_two_pow_and_le_logb
    (correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])) hC
    (M := (M : ℝ)) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)) hε (s := 1) le_rfl
  simp only [one_mul] at hk hlog
  exact ⟨k, hk, h u hu hu0 ε hε k M hk, hlog⟩

end MPSPreparation
