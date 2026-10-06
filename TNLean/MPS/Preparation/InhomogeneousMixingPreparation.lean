/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrderedMixingPairRate
import TNLean.MPS.Preparation.InhomogeneousUniformRate

/-!
# Physical logarithmic-depth preparation from ordered mixing

Uniform exponential mixing of the actual ordered transfer products towards one faithful
trace-one state implies a uniform normalized pair-approximation rate, and hence physical
preparation in depth `O(log(N/ε))`. The constants are independent of the ring and partition.
The assumption concerns nonwrapping contiguous intervals in the chosen linear ordering,
not separate eigenvalue bounds on sites.

The all-positive-length theorem requires nonzero targets because the source compares
normalized quantum states. This retains finite short rings for which decay alone may not
exclude a zero periodic vector. The eventual theorem instead derives nonvanishing beyond
a uniform cutoff, without changing the family. Existing exact short-ring preparation
handles scales longer than the ring.

This is a quantitative sufficient condition for arXiv:2307.01696, paragraph "Inhomogeneous
short-range correlated MPS". The paper's qualitative finite-correlation definition alone
does not supply the ordered mixing hypothesis.

**Scope restriction (ordered mixing):** the quantitative ordered-product bounds and common
faithful reference state are additional hypotheses, not consequences of the source's
qualitative finite-correlation definition. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS" and the logarithmic
  blocking choice following Lemma 1 in the translation-invariant case.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSPreparation

private theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing_from
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r) (N₀ : ℕ)
    (hne : ∀ (N : ℕ) [NeZero N], N₀ ≤ N → chainState (A N) ≠ 0)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
          K * Real.exp (-(r * ℓ j))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hp⟩ := exists_isPairApproximable_of_ordered_mixing hσ htr
  let B (N : ℕ) := ofChain (A N)
  have hstate (N : ℕ) [NeZero N] : state (B N) = chainState (A N) := by
    rw [state_eq_chainState, zeroPad_ofChain]
  have hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N → N₀ ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsPairApproximable (B N) hN (Cp * K * ((N : ℝ) ^ 1 * Real.exp (-(r * q)))) := by
    intro N _ q hq hqN hN₀
    exact hp d N (A N) K r hK hr (hne N hN₀) (hmix N) q hq hqN
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate_from
    d D hd B (Cp * K) r 1 (mul_pos hCp hK) hr N₀ hrate
  refine ⟨C, fun ε hε hε1 N _ hN₀ => ?_⟩
  simpa only [hstate] using hC ε hε hε1 N hN₀

/-- Actual ordered transfer mixing gives normalized physical preparation in logarithmic
accuracy-dependent depth. Fix `K,r > 0` and one faithful normalized reference state before
the ring length is chosen. Every positive nonwrapping contiguous block has transfer-matrix error at
most `K exp(-r ℓ)`, in the `L²` operator norm. Then the normalized nonzero chain states can
be approximated to error `ε` in depth `C log(N/ε)`.

The finite-dimensional norm conversions and overlap estimates have constants depending only
on the fixed bond dimension and reference state. The pair-approximation rate is proved from
the tensors, rather than supplied as a hypothesis. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hne : ∀ (N : ℕ) [NeZero N], chainState (A N) ≠ 0)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
          K * Real.exp (-(r * ℓ j))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N],
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing_from
    d D hd A hσ htr K r hK hr 0 (fun N _ _ => hne N) hmix
  exact ⟨C, fun ε hε hε1 N _ => hC ε hε hε1 N (Nat.zero_le N)⟩

/-- Uniform ordered mixing alone gives physical logarithmic-depth preparation of the
original family at every sufficiently large ring length. The cutoff is chosen before
`N` and `ε`: the whole-ring norm estimate makes the squared norm at least `1/2` beyond
that cutoff. No nonzero condition is imposed on finitely many short rings, and no tensor
in the physical family is replaced.

This quantitative sufficient condition includes normal families with vanishing short
periodic vectors; it does not derive ordered mixing from qualitative finite correlation.
See `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_ordered_mixing
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
          K * Real.exp (-(r * ℓ j))) :
    ∃ N₀ : ℕ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_chainState_sq_sub_one_le hσ.posSemidef htr
  let L := Kn * K + 1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((Real.log L - Real.log (1 / 2 : ℝ)) / r)
  have hne (N : ℕ) [NeZero N] (hcut : N₀ ≤ N) : chainState (A N) ≠ 0 := by
    have hsmall : L * Real.exp (-(r * N)) ≤ 1 / 2 :=
      mul_exp_neg_mul_le_of_div_log_le hL hr (by norm_num)
        (hN₀.trans (Nat.cast_le.mpr hcut))
    have hsingle : ∑ _ : Fin 1, N = N := by simp
    have hi := blockSite_singleton hsingle
    have ht := hmix N (fun _ : Fin 1 => N) hsingle 0
      (Nat.pos_of_ne_zero (NeZero.ne N))
    simp only [hi] at ht
    rw [← MPSChainTensor.transferMap_blockTensor] at ht
    have hb : |‖chainState (A N)‖ ^ 2 - 1| ≤ 1 / 2 := by
      calc |‖chainState (A N)‖ ^ 2 - 1|
          ≤ Kn * ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (A N))) -
            transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ := hnorm _
        _ ≤ Kn * (K * Real.exp (-(r * N))) := mul_le_mul_of_nonneg_left ht hKn
        _ ≤ L * Real.exp (-(r * N)) := by
            dsimp only [L]
            nlinarith [Real.exp_pos (-(r * N))]
        _ ≤ 1 / 2 := hsmall
    intro hz
    norm_num [hz] at hb
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing_from
    d D hd A hσ htr K r hK hr N₀ hne hmix
  exact ⟨N₀, C, hC⟩

end MPSPreparation
