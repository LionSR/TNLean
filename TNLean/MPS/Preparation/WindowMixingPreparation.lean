/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.WindowMixing
import QICLean.Analysis.GeometricDecay
import TNLean.MPS.Preparation.VaryingReferencePreparation

/-!
# Physical preparation from a local window criterion

Trace-preserving actual site tensors and a uniform Choi minorization on every fixed-width
nonwrapping window imply eventual physical logarithmic-depth preparation. The reference
densities and global mixing rate are derived rather than supplied. The window minorizers
may vary with the ring and position and may be singular.

**Scope restriction (local minorization):** this is an explicit local quantitative sufficient
condition for arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS". It does
not derive a rate from that paragraph's qualitative convergence definition. Bond spaces
remain square with a fixed dimension; see `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
* Wolf, *Quantum Channels & Operations*, Theorem 8.17 and Eq. (8.86) (the local Choi criterion).
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace MPSPreparation

/-- A fixed-width local Choi minorization criterion gives eventual physical logarithmic-depth
preparation of the original tensor family. Actual sites preserve trace, and every actual
nonwrapping window of `s ≥ 1` sites has normalized Choi matrix at least `(η/D) (τ ⊗ I)` for
some density matrix `τ`. The density may depend on the ring and window and may be singular.
For `η > 0`, the actual window at length `s` forces `η ≤ 1`; compatible references and
uniform ordered mixing are derived internally.

The cutoff is at least `s`. No cyclic-wrap window, supplied global rate, common stationary
state, faithful reference, or short-ring nonzero premise is required. The endpoint `η = 1`
is handled by weakening to `η/2` before taking a logarithm. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_window_domination
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    (s : ℕ) (hs : 0 < s) {η : ℝ} (hη : 0 < η)
    (htp : ∀ (N : ℕ) (i : Fin N), IsTracePreservingMap (Kraus.transferMap (A N i)))
    (hwindow : ∀ (N a : ℕ) (ha : a + s ≤ N), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.blockTensor ((A N).interval a s ha))) ≥
          ((η : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) :
    ∃ N₀ : ℕ, s ≤ N₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun x => ψ x) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨τ₀, hτ₀, hτ₀tr, _⟩ := hwindow s 0 (by omega)
  have := Matrix.neZero_of_trace_eq_one hτ₀tr
  have hη1 : η ≤ 1 := by
    have hg := norm_gram_blockTensor_sub_transport_le_of_window_domination
      (A s) s hs η (htp s) (hwindow s) τ₀ hτ₀ hτ₀tr
    have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
    have hp : 0 ≤ 2 * D * (1 - η) :=
      (norm_nonneg _).trans (by simpa only [Nat.div_self hs, pow_one] using hg)
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (mul_pos two_pos hD)).mp hp)
  have hρhalf : 1 / 2 ≤ 1 - η / 2 := by linarith
  have hρ0 : 0 < 1 - η / 2 := by linarith
  have hρ1 : 1 - η / 2 < 1 := by linarith
  let r := -Real.log (1 - η / 2) / s
  have hr : 0 < r := div_pos (neg_pos.mpr (Real.log_neg hρ0 hρ1)) (Nat.cast_pos.mpr hs)
  have hweak : ∀ (N a : ℕ) (ha : a + s ≤ N), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.blockTensor ((A N).interval a s ha))) ≥
          (((η / 2 : ℝ) : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    intro N a ha
    obtain ⟨τ, hτ, htr, hc⟩ := hwindow N a ha
    refine ⟨τ, hτ, htr, le_trans ?_ hc⟩
    apply Matrix.le_iff.mpr
    rw [← sub_smul]
    apply (hτ.kronecker Matrix.PosSemidef.one).smul
    have heq : (η : ℂ) / D - ((η / 2 : ℝ) : ℂ) / D = ((η / (2 * D) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq]
    exact Complex.zero_le_real.mpr (by positivity)
  obtain ⟨K, hK, hmix⟩ := exists_norm_transferMatrix_interval_sub_le_of_window_domination D
  choose σ hσ hcyc hm using fun N => hmix (A N) s hs (η / 2) (htp N) (hweak N)
  have happrox := exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_varying_reference
    d D hd A (fun N j => σ N j.val) (fun N _ j => (hσ N j.val).1)
    (fun N _ j => (hσ N j.val).2) (2 * K) r (by positivity) hr
  have hm' : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M) (hj : 0 < ℓ j),
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor
          (σ N (blockSite hN j ⟨0, hj⟩).val)))‖ ≤
        (2 * K) * Real.exp (-(r * ℓ j)) := by
    intro N _ M ℓ hN j hj
    have hbound : blockOffset ℓ j.val + ℓ j ≤ N := by
      have hb := blockOffset_mono ℓ j.isLt
      rw [blockOffset_of_le ℓ le_rfl, hN, blockOffset_succ ℓ j] at hb
      exact hb
    have h := hm N (blockOffset ℓ j.val) (ℓ j) hbound
    have hg := Real.pow_nat_div_le_two_mul_exp s (ℓ j) hs (1 - η / 2) hρhalf hρ1
    have hfinal := h.trans (mul_le_mul_of_nonneg_left hg hK.le)
    simpa only [MPSChainTensor.transferMap_blockTensor, MPSChainTensor.interval,
      blockSite, Nat.add_zero, mul_assoc, mul_left_comm K 2] using hfinal
  obtain ⟨N₀, C, hC⟩ := happrox hm'
  refine ⟨max s N₀, le_max_left _ _, C, fun ε hε hε1 N _ hN => ?_⟩
  exact hC ε hε hε1 N ((le_max_right s N₀).trans hN)

end MPSPreparation
