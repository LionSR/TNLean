/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PureStateTraceNorm
import TNLean.Circuit.Measurement.Protocol

/-!
# Asymptotic preparation of sequences of states with measurements

Piroli, Styliaris and Cirac (arXiv:2103.13367, paragraph "Phases of matter") compare sequences
of states `Ψ = {|ψ_M⟩}` and `Φ = {|φ_M⟩}` on chains of increasing size: `Ψ ↦ Φ` when, for some
`k`, compositions of `k` channels of `QCcc` of depth `f(M)` map `|ψ_M⟩` to states `σ_M` with
`‖σ_M - |φ_M⟩⟨φ_M|‖₁ → 0`, where `f` is polylogarithmic in `M`. This file records the case in
which `Ψ` is the trivial sequence of product states and every `σ_M` is pure and prepared
deterministically: a sequence `φ` is *asymptotically prepared with measurements in depth `f`*
when, for all large `N`, a unit vector `ψ_N` is prepared with measurements and a circuit in
depth at most `f N`, and `‖|ψ_N⟩⟨ψ_N| - |φ_N⟩⟨φ_N|‖₁ → 0`.

A preparation with measurements followed by a circuit
(`QuantumCircuit.IsPreparedWithMeasurementsAndCircuitInDepth`) is the composition of two
channels of `QCcc`, the second without measurements, each of depth at most the total depth, so
this is the relation `Ψ ↦ Φ` of arXiv:2103.13367 with `k = 2` and `Ψ` the product states.

## Main definitions

* `QuantumCircuit.IsAsymptoticallyPreparedWithMeasurementsInDepth` — the sequence `φ` is
  prepared up to a trace-norm error tending to zero, in depth at most `f N`.

## Main results

* `QuantumCircuit.isAsymptoticallyPreparedWithMeasurementsInDepth_of_one_sub_norm_inner_le` —
  preparations whose overlap error `1 - |⟨ψ_N|φ_N⟩|` tends to zero give an asymptotic
  preparation.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), paragraph "Phases of matter".
-/

open Filter Topology Matrix
open scoped InnerProductSpace

namespace QuantumCircuit

variable {d : ℕ}

/-- **Asymptotic preparation with measurements.** The sequence of vectors `φ N` on the rings of
`N` sites is prepared with measurements in depth `f` when there are unit vectors `ψ N`, each
prepared for all large `N` with measurements and a circuit in depth at most `f N`, with
`‖|ψ_N⟩⟨ψ_N| - |φ_N⟩⟨φ_N|‖₁ → 0`.

Source: arXiv:2103.13367, paragraph "Phases of matter": `Ψ ↦ Φ` "if `∃ k ∈ ℕ` and a sequence of
(mixed) states `{σ_M}`, s.t. `|ψ_M⟩ → σ_M` under `QCcc^{(k)}_{f(M)}` and
`‖σ_M - |φ_M⟩⟨φ_M|‖₁ → 0`", here with `|ψ_M⟩` the product state, `k = 2` (a preparation with
measurements, then a circuit), and `σ_M = |ψ_M⟩⟨ψ_M|` pure. -/
def IsAsymptoticallyPreparedWithMeasurementsInDepth (f : ℕ → ℝ)
    (φ : (N : ℕ) → EuclideanSpace ℂ (Fin N → Fin d)) : Prop :=
  ∃ ψ : (N : ℕ) → EuclideanSpace ℂ (Fin N → Fin d),
    (∀ᶠ N in atTop, ∀ [NeZero N], ‖ψ N‖ = 1 ∧
      ∃ T : ℕ, (T : ℝ) ≤ f N ∧ IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ N s)) ∧
    Tendsto (fun N => traceNormPureSub (ψ N) (φ N)) atTop (𝓝 0)

/-- **Overlap errors tending to zero give an asymptotic preparation.** If the target vectors are
eventually unit vectors, and for all large `N` some unit vector `ψ` with
`1 - |⟨ψ|φ_N⟩| ≤ ε N` is prepared with measurements and a circuit in depth at most `f N`, where
`ε N → 0`, then `φ` is asymptotically prepared with measurements in depth `f`: by
`Matrix.traceNormPureSub_le`, `‖|ψ⟩⟨ψ| - |φ_N⟩⟨φ_N|‖₁ ≤ 2 √(2 ε N)`.

Source: arXiv:2103.13367, paragraph "Phases of matter" (the trace-norm convergence). -/
theorem isAsymptoticallyPreparedWithMeasurementsInDepth_of_one_sub_norm_inner_le {f : ℕ → ℝ}
    {φ : (N : ℕ) → EuclideanSpace ℂ (Fin N → Fin d)} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hφ : ∀ᶠ N in atTop, ‖φ N‖ = 1)
    (h : ∀ᶠ N in atTop, ∀ [NeZero N], ∃ ψ : EuclideanSpace ℂ (Fin N → Fin d), ‖ψ‖ = 1 ∧
      (∃ T : ℕ, (T : ℝ) ≤ f N ∧ IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ s)) ∧
      1 - ‖⟪ψ, φ N⟫_ℂ‖ ≤ ε N) :
    IsAsymptoticallyPreparedWithMeasurementsInDepth f φ := by
  classical
  -- The property asked of `ψ N`, at a positive length.
  let P : (N : ℕ) → [NeZero N] → EuclideanSpace ℂ (Fin N → Fin d) → Prop := fun N _ ψ =>
    ‖ψ‖ = 1 ∧ (∃ T : ℕ, (T : ℝ) ≤ f N ∧
      IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ s)) ∧ 1 - ‖⟪ψ, φ N⟫_ℂ‖ ≤ ε N
  have key : ∀ N, ∃ ψ : EuclideanSpace ℂ (Fin N → Fin d),
      ∀ [NeZero N], (∃ ψ', P N ψ') → P N ψ := by
    intro N
    by_cases hN : N = 0
    · exact ⟨0, fun _ => absurd hN (NeZero.ne N)⟩
    · have : NeZero N := ⟨hN⟩
      by_cases hex : ∃ ψ', P N ψ'
      · obtain ⟨ψ', hψ'⟩ := hex
        exact ⟨ψ', fun _ => hψ'⟩
      · exact ⟨0, fun h' => absurd h' hex⟩
  choose ψ hψ using key
  have hev : ∀ᶠ N in atTop, ∀ [NeZero N], P N (ψ N) :=
    h.mono fun N hN _ => hψ N (hN)
  refine ⟨ψ, hev.mono fun N hN _ => ⟨hN.1, hN.2.1⟩, ?_⟩
  -- The trace-norm bound `2 √(2 ε N)`.
  have hlim : Tendsto (fun N => 2 * Real.sqrt (2 * ε N)) atTop (𝓝 0) := by
    simpa using ((hε.const_mul 2).sqrt).const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun N => traceNormPureSub_nonneg _ _) ?_ hlim
  filter_upwards [hev, hφ, eventually_ge_atTop 1] with N hN hφN hN1
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hψ1, -, herr⟩ := hN
  calc traceNormPureSub (ψ N) (φ N) ≤ 2 * Real.sqrt (2 * (1 - ‖⟪ψ N, φ N⟫_ℂ‖)) :=
        traceNormPureSub_le hψ1 hφN
    _ ≤ 2 * Real.sqrt (2 * ε N) := by gcongr

end QuantumCircuit
