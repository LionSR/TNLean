/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthLogBound
import TNLean.MPS.Preparation.RegisterTreeState

/-!
# Preparation with measurements in depth `O(log log(N/ε))`

The paragraph "Tree-RG circuit with measurements" of arXiv:2307.01696 teleports the registers of
the tree-RG circuit of eq. (16) next to each other, so that "every isometry in eq. (16) takes
constant time using measurement", and concludes that "this gives a preparation algorithm for
short-range correlated MPS with depth `O(log log(N/ε))`". This file proves it for normal
tensors.

## The protocol

Let `A` be a tensor whose blocked tensor over `s` sites is injective, so that `D² ≤ d^s` and a
register of `s` sites carries `ℂ^{D²}`. Cut the ring of `N = M q` sites, `q = s 2^{k+1}`, into
`M` blocks of `q` sites. The protocol

1. applies a local circuit preparing the pairs `|ω⟩_{R_b L_{b+1}}` of the fixed-point state on
   the last `s` sites of every block and the first `s` sites of the next, as in eq. (12), in one
   round without measurements;
2. applies to every block the tree of unitaries `MPSPreparation.regTreeGate` of the `k + 1`
   layers of eq. (16), on registers of `s` sites, with the measurement rounds of
   `MPSPreparation.exists_rounds_blockLayerOp_regTreeOp`, of depth `4s + K + 2` per layer.

After every sequence of outcomes the output is a scalar multiple of the approximating state
`|φ'_N⟩ = V^{⊗M} |Ω⟩` of eq. (10) with blocks of `q` sites
(`MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_approximatingMPVState`): the
tree of every block implements the isometry `V` of the polar decomposition of the blocked
tensor (`MPSPreparation.regTreeOp_apply_blockInputCfg`). The total depth is at most `C (k + 1)`,
with `C` depending only on `d` and `s`.

## The depth

For a normal tensor, the gauge of eq. (5) gives a length `s` from which on the blocked tensors
are injective. With the error bound of Lemma 1'(i) at a slope `a > ξ/2`
(`MPSPreparation.exists_approximationError_le_of_slope`), the error is at most `ε` once
`s 2^{k+1} ≥ a log(N/ε) + b`; if moreover `s 2^{k+1} ≤ 2 (a log(N/ε) + b)`, then
`k ≤ log₂(a log(N/ε) + b)` and the depth `C (k + 1)` is `O(log log(N/ε))`
(`MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_le_logb_log`).

The blocks here all have length `q = s 2^{k+1}`, which divides `N`, and every tree is complete:
the theorems of this file hold for the chain lengths `N` divisible by `s 2^{k+1}` for some `k` in
the window `a log(N/ε) + b ≤ s 2^{k+1} ≤ 2 (a log(N/ε) + b)`. Every chain length `N ≥ 2` with
`|φ_N(A)⟩ ≠ 0`, with blocks of unequal lengths as in the Supplemental Material, proof of
Theorem 1, and trees on leaves of unequal widths, is treated by
`MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpvState_ne_zero`,
and every chain length `N ≥ N₀` by
`MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_le_log_log`.

## Main results

* `MPSPreparation.isZeroOn_regCentralSites_pairLayerOp_mulVec` — the pairs leave `|0⟩` at the
  sites of every block other than its first and its last `s` sites.
* `MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_approximatingMPVState`.
* `MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_approximationError_le`.
* `MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_le_logb_log`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eqs. (5), (10)–(12) and (16), Lemma 1'(i),
  paragraph "Tree-RG circuit with measurements", and Supplemental Material, proof of Theorem 1.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace
open QuantumCircuit

namespace MPSPreparation

open TeleportHop

/-! ### The pairs -/

section Pairs

variable {d s M N : ℕ} [NeZero d] [NeZero N] {k : ℕ}

omit [NeZero N] in
/-- The layer of pairs applied to the all-`|0⟩` state leaves `|0⟩` at every site of every block
other than its first and its last `s` sites. -/
theorem isZeroOn_regCentralSites_pairLayerOp_mulVec (hN : ∑ _ : Fin M, s * 2 ^ (k + 1) = N)
    (hr : ∀ _ : Fin M, s + s ≤ s * 2 ^ (k + 1))
    (W : Fin M → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) :
    IsZeroOn (regCentralSites (k := k) (s := s) hN)
      (pairLayerOp hN hr W *ᵥ productVector fun _ => Pi.single ⟨0, NeZero.pos d⟩ 1) :=
  isZeroOn_pairLayerOp_mulVec_productVector hN hr W

end Pairs

/-! ### The approximating state with measurements -/

/-- Injectivity of the blocked tensor over `s` sites passes to blocks of `s 2^{k+1}` sites. -/
private theorem isInjective_blockTensor_mul_two_pow {d D s : ℕ} {A : MPSTensor d D}
    (hA : Kraus.IsInjective (blockTensor A s)) (k : ℕ) :
    Kraus.IsInjective (blockTensor A (s * 2 ^ (k + 1))) := by
  have := blockTensor_isInjective_mul_of_blockTensor_isInjective A
    (m := 2 ^ (k + 1)) (pow_pos two_pos _) hA
  rwa [mul_comm] at this

/-- **The approximating state is prepared with measurements in depth `O(k)`** (arXiv:2307.01696,
paragraph "Tree-RG circuit with measurements", with eqs. (10)–(12) and (16)). For every `d ≥ 1`
and `s ≥ 1` there is `C`, depending only on `d` and `s`, with the following property. Let `A`
be a tensor whose blocked tensor over `s` sites is injective, and let `σ ≥ 0` with `Tr σ = 1`.
For every `k` and every number of blocks `M ≥ 1`, the approximating state `|φ'_N⟩` of eq. (10)
with blocks of `q = s 2^{k+1}` sites, on `N = M q` sites, is prepared with measurement rounds in
depth at most `C (k + 1)`: the pairs of the fixed point are prepared by a local circuit, and the
tree-RG circuit of every block, on registers of `s` sites, is applied with measurements one
layer at a time. No outcome is post-selected. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_approximatingMPVState (d s : ℕ)
    [NeZero d] [NeZero s] :
    ∃ C : ℕ, ∀ {D : ℕ} (A : MPSTensor d D), Kraus.IsInjective (blockTensor A s) →
      ∀ (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosSemidef → σ.trace = 1 →
        ∀ (k M : ℕ) [NeZero M],
          IsPreparedWithMeasurementRoundsInDepth (C * (k + 1))
            fun x => approximatingMPVState A σ (s * 2 ^ (k + 1)) M x := by
  classical
  have hd : 0 < d := NeZero.pos d
  have hs : 0 < s := NeZero.pos s
  obtain ⟨K, hK⟩ := exists_isPairProduct (n := s + s) hd (by omega)
  refine ⟨2 * K + 4 * s + 4, fun {D} A hA σ hσ htr k M _ => ?_⟩
  set q := s * 2 ^ (k + 1) with hq
  have : NeZero (M * q) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) (Nat.mul_ne_zero hs.ne' (by positivity))⟩
  have hN : ∑ _ : Fin M, q = M * q := by simp
  have hr : ∀ _ : Fin M, s + s ≤ q := fun _ => by
    have : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right two_pos (by omega)
    rw [hq]; nlinarith
  -- Registers of `s` sites carry the bond legs and `ℂ^{D²}`.
  have hDD : D * D ≤ d ^ s := mul_self_le_pow_of_isInjective_blockTensor hA
  obtain ⟨enc⟩ : Nonempty (Fin (D * D) ↪ Cfg d s) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hDD)
  obtain ⟨dig⟩ : Nonempty (Fin D ↪ Cfg d s) :=
    Function.Embedding.nonempty_of_card_le (by simpa using (Nat.le_mul_self D).trans hDD)
  have h2 : Kraus.IsInjective (blockTensor (blockTensor A s) 2) := isInjective_blockTensor_two hA
  have hBq : Kraus.IsInjective (blockTensor A q) := isInjective_blockTensor_mul_two_pow hA k
  -- The pairs of the fixed point.
  obtain ⟨W, hWu, hW⟩ := exists_pairUnitary hd dig.injective (fixedPointPair σ)
    (by rw [fixedPointPair_norm_sq hσ, htr])
  obtain ⟨Ls, hLs, -, hLsW⟩ := isCircuitOn_pairLayerOp hN hr fun _ => hK W hWu
  -- The trees of the blocks.
  set T := regTreeGate dig enc (blockTensor A s) k with hT
  obtain ⟨Rs, hRs, hRsE⟩ := exists_rounds_blockLayerOp_regTreeOp (X := T) (hN := hN)
    (K := K) fun j p => hK _ (regTreeGate_mem_unitary dig enc (blockTensor A s) k j p)
  set v₀ : Fin (M * q) → Fin d → ℂ := fun _ => Pi.single ⟨0, hd⟩ 1
  have hv₀ : productVector v₀ ≠ 0 := fun h => by
    have := congrFun h fun _ => ⟨0, hd⟩
    rw [productVector_single_zero_apply hd] at this
    simp at this
  have h₀ : MeasurementRound.IsRoundsImplementationOn [round Ls [] valid_nil] {productVector v₀}
      (pairLayerOp hN hr fun _ => W) := by
    have := (isImplementationOn_round (d := d) Ls (valid_nil (N := M * q))).isRoundsImplementationOn
    rw [chainPerm_nil, Matrix.one_mul, ← hLsW] at this
    exact this.mono fun v _ => fun _ _ _ h => h.elim
  have hall := h₀.append hRsE fun v hv => by
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact isZeroOn_regCentralSites_pairLayerOp_mulVec hN hr _
  have hprep := hall.isPreparedWithMeasurementRoundsInDepth hv₀ rfl
  have hdepth : (([round Ls [] valid_nil] ++ Rs).map MeasurementRound.depth).sum ≤
      (2 * K + 4 * s + 4) * (k + 1) := by
    rw [List.map_append, List.sum_append, hRs]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, depth_round, hLs]
    nlinarith
  have hψ : (fun x => approximatingMPVState A σ q M x) =
      ((blockLayerOp hN fun _ => regTreeOp T k (k + 1)) * pairLayerOp hN hr fun _ => W) *ᵥ
        productVector v₀ := by
    funext x
    rw [approximatingMPVState_eq_blockIsometryState A hBq hσ htr M hN]
    exact blockIsometryState_eq_mulVec hd hN hr dig.injective A (fixedPointPair σ)
      (fun _ l r τ => regTreeOp_apply_blockInputCfg A h2 dig.injective enc.injective l r τ) hW x
  rw [hψ]
  exact hprep.mono hdepth

/-! ### Error `ε` in depth `O(log log(N/ε))` -/

/-- **Error `ε` with measurements in depth `C (k + 1)` for `s 2^{k+1} ≥ a log(N/ε) + b`.**
For every normal tensor `A` there are a register length `s ≥ 1`, a constant `C`, and `a > 0`,
`b ≥ 1`, all depending only on `A`, with the following property. For `ε > 0` and every `k`
such that `s 2^{k+1}` divides `N ≥ 1` and `s 2^{k+1} ≥ a log(N/ε) + b`, some unit vector
`|ψ⟩` on `N` sites with `ε(ψ, φ_N) = 1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared with measurement rounds in
depth at most `C (k + 1)`.

arXiv:2307.01696, paragraph "Tree-RG circuit with measurements", with Lemma 1'(i): the vector
`|ψ⟩` is the approximating state of eq. (10) with blocks of `q = s 2^{k+1}` sites for the tensor
in the gauge of eq. (5) (`MPSPreparation.exists_normalGaugeData`), with `s` a length at which its
blocked tensor is injective, and the slope is `a = ξ`
(`MPSPreparation.exists_approximationError_le_of_slope`). -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_approximationError_le {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    ∃ (s C : ℕ) (a b : ℝ), 1 ≤ s ∧ 0 < a ∧ 1 ≤ b ∧ ∀ ε : ℝ, 0 < ε →
      ∀ (N k : ℕ) [NeZero N], s * 2 ^ (k + 1) ∣ N →
        a * Real.log (N / ε) + b ≤ (s * 2 ^ (k + 1) : ℕ) →
          ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧
            IsPreparedWithMeasurementRoundsInDepth (C * (k + 1)) (fun x => ψ x) ∧
            1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  obtain ⟨B, ζ, σ, t, L, hζ, hmpv, hNB, hLC, hσ, htr, hfix, ht0, ht1, hlam, hnorm, hinj⟩ :=
    exists_normalGaugeData hA
  have hξ : 0 < correlationLength (t : ℂ) :=
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])
  obtain ⟨b₀, hb₀, herr⟩ := exists_approximationError_le_of_slope hζ hmpv hNB hLC hσ htr hfix
    ht0 ht1 (fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm) (half_lt_self hξ)
  have hBs : Kraus.IsInjective (blockTensor B (L + 1)) := hinj (L + 1) (by omega)
  have : NeZero d := ⟨fun hd => by
    have h := mul_self_le_pow_of_isInjective_blockTensor hBs
    rw [hd, zero_pow (by omega)] at h
    exact absurd h (Nat.not_le.2 (Nat.mul_pos (NeZero.pos D) (NeZero.pos D)))⟩
  obtain ⟨C, hC⟩ := exists_isPreparedWithMeasurementRoundsInDepth_approximatingMPVState d (L + 1)
  refine ⟨L + 1, C, _, b₀ + 1, by omega, hξ, by linarith, fun ε hε N k _ hdvd hq => ?_⟩
  obtain ⟨M, hM⟩ := hdvd
  rw [mul_comm] at hM
  subst hM
  have : NeZero M := ⟨fun h => NeZero.ne (M * ((L + 1) * 2 ^ (k + 1))) (by rw [h, zero_mul])⟩
  have hBq : Kraus.IsInjective (blockTensor B ((L + 1) * 2 ^ (k + 1))) :=
    isInjective_blockTensor_mul_two_pow hBs k
  refine ⟨approximatingMPVState B σ _ M, norm_approximatingMPVState B hBq hσ.posSemidef htr M,
    hC B hBs σ hσ.posSemidef htr k M, herr ε hε _ M (Nat.one_le_iff_ne_zero.2 (by positivity)) ?_⟩
  push_cast at hq ⊢
  linarith

/-- **Preparation with measurements in depth `O(log log(N/ε))`** (arXiv:2307.01696, paragraph
"Tree-RG circuit with measurements": "this gives a preparation algorithm for short-range
correlated MPS with depth `O(log log(N/ε))`"). In the setting of
`exists_isPreparedWithMeasurementRoundsInDepth_approximationError_le`, if moreover
`s 2^{k+1} ≤ 2 (a log(N/ε) + b)`, then `k ≤ log₂(a log(N/ε) + b)`: the unit vector `|ψ⟩` with
error at most `ε` against `|φ_N⟩` is prepared with measurement rounds in depth at most
`C (k + 1) ≤ C (log₂(a log(N/ε) + b) + 1)`. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_le_logb_log {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    ∃ (s C : ℕ) (a b : ℝ), 1 ≤ s ∧ 0 < a ∧ 1 ≤ b ∧ ∀ ε : ℝ, 0 < ε →
      ∀ (N k : ℕ) [NeZero N], s * 2 ^ (k + 1) ∣ N →
        a * Real.log (N / ε) + b ≤ (s * 2 ^ (k + 1) : ℕ) →
        ((s * 2 ^ (k + 1) : ℕ) : ℝ) ≤ 2 * (a * Real.log (N / ε) + b) →
          (k : ℝ) ≤ Real.logb 2 (a * Real.log (N / ε) + b) ∧
          ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧
            IsPreparedWithMeasurementRoundsInDepth (C * (k + 1)) (fun x => ψ x) ∧
            1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  obtain ⟨s, C, a, b, hs, ha, hb, h⟩ :=
    exists_isPreparedWithMeasurementRoundsInDepth_approximationError_le A hA
  refine ⟨s, C, a, b, hs, ha, hb, fun ε hε N k _ hdvd hq hq2 => ⟨?_, h ε hε N k hdvd hq⟩⟩
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h2k : (2 : ℝ) ^ k ≤ a * Real.log (N / ε) + b := by
    push_cast at hq2
    have : (2 : ℝ) ^ (k + 1) ≤ s * 2 ^ (k + 1) :=
      le_mul_of_one_le_left (by positivity) hs1
    rw [pow_succ] at this hq2
    linarith
  rw [Real.le_logb_iff_rpow_le one_lt_two ((pow_pos two_pos k).trans_le h2k), Real.rpow_natCast]
  exact h2k

end MPSPreparation
