/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Measurement.Asymptotic
import TNLean.MPS.Preparation.OverlappingMeasurementPreparation

/-!
# Translation-invariant MPS are reached from product states by `QCcc`

Piroli, Styliaris and Cirac (arXiv:2103.13367, Theorem `MPS_classification`) state: "In 1D, all
translational invariant MPS with fixed bond dimension are in the same phase as the trivial
state", for the equivalence of sequences of states defined in the paragraph "Phases of matter":
`Ψ` and `Φ` are equivalent when `Ψ ↦ Φ` and `Φ ↦ Ψ`, where `Ψ ↦ Φ` asks for compositions of
channels of `QCcc` of polylogarithmic depth mapping `|ψ_M⟩` to states `σ_M` with
`‖σ_M - |φ_M⟩⟨φ_M|‖₁ → 0`. The proof in the Supplemental Material approximates the blocked MPS
by a renormalization fixed point, with error `O(N e^{-βq})`, and prepares the fixed point with
measurements in depth polynomial in the block length `q`.

This file proves the direction `trivial ↦ MPS`: the normalized periodic states of a
translation-invariant MPS are asymptotically prepared with measurements in depth `C log N`, with
trace-norm error tending to zero
(`MPSPreparation.isAsymptoticallyPreparedWithMeasurementsInDepth_normalizedMPVState`). It
follows from the preparation of a state of error `ε` in depth `c log(N/ε)`
(`MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero`)
at `ε = 1/N`.

**Scope restriction (one direction, canonical form):** only the direction `trivial ↦ MPS` of the
equivalence is proved; the converse direction `MPS ↦ trivial` needs channels of `QCcc` acting on
arbitrary input states, which the preparation model of `TNLean.Circuit.Measurement.Protocol`
does not include. The tensor is taken in the canonical form `⊕ⱼ diag(μ_{j,k}) ⊗ A_j` with
normal blocks in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j > 0`, and with the mixed
transfer maps of distinct blocks of spectral radius below one, and the periodic states are
assumed nonzero for all large `N`, as a sequence of states presupposes. Documented in
`docs/paper-gaps/psc21_mps_classification_scope.tex`.

## Main results

* `MPSPreparation.isAsymptoticallyPreparedWithMeasurementsInDepth_normalizedMPVState` — the
  direction `trivial ↦ MPS` of arXiv:2103.13367, Theorem `MPS_classification`.

## References

* [PSC21] L. Piroli, G. Styliaris, J. I. Cirac,
  *Quantum circuits assisted by local operations and classical communication:
  transformations and phases of matter*, arXiv:2103.13367, paragraph "Phases of matter",
  Theorem `MPS_classification`, and Supplemental Material, "Proof of Theorem
  MPS_classification".
* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*, arXiv:2307.01696,
  paragraph "Long-range MPS using measurements".
-/

open Filter Topology MPSTensor QuantumCircuit
open scoped InnerProductSpace ComplexOrder

namespace MPSPreparation

variable {d : ℕ}

/-- **Translation-invariant MPS are reached from product states with measurements in
logarithmic depth** (arXiv:2103.13367, Theorem `MPS_classification`, the direction
`trivial ↦ MPS`). Let `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` with every block `A_j` normal
in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`, and with the
mixed transfer maps of distinct blocks of spectral radius below one. If the periodic states
`|φ_N(A)⟩` are nonzero for all large `N`, there is `C` such that the normalized periodic states
are asymptotically prepared with measurements in depth `C log N`: unit vectors `|ψ_N⟩`, prepared
with measurements and a circuit in depth at most `C log N`, satisfy
`‖|ψ_N⟩⟨ψ_N| - |φ_N⟩⟨φ_N|‖₁ → 0`.

The depth `C log N` is polylogarithmic in `N`, as the paragraph "Phases of matter" of
arXiv:2103.13367 requires of `f(M)`. The proof takes the error `ε = 1/N` in
`exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero`, whose depth
is then `c log(N²) = 2c log N`. The hypotheses beyond the source are those of the module's
scope restriction. -/
theorem isAsymptoticallyPreparedWithMeasurementsInDepth_normalizedMPVState
    {D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ < 1)
    (h0 : ∀ᶠ N in atTop, mpvState (repeatedBlockSum Aj ι μ) N ≠ 0) :
    ∃ C : ℝ, IsAsymptoticallyPreparedWithMeasurementsInDepth (fun N => C * Real.log N)
      (fun N => normalizedMPVState (repeatedBlockSum Aj ι μ) N) := by
  obtain ⟨c, hc⟩ := exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero
    hι hdisj μ hN hA hσ htr hfix hmix
  refine ⟨2 * c, isAsymptoticallyPreparedWithMeasurementsInDepth_of_one_sub_norm_inner_le
    (ε := fun N => 1 / (N : ℝ)) tendsto_one_div_atTop_nhds_zero_nat
    (h0.mono fun N hN => norm_normalizedMPVState hN) ?_⟩
  filter_upwards [h0, eventually_ge_atTop 2] with N hN0 hN2
  intro _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hε1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨ψ, T, hψ1, hT, hprep, herr⟩ := hc (1 / (N : ℝ)) (by positivity) hε1 N hN2 hN0
  refine ⟨ψ, hψ1, ⟨T, ?_, hprep⟩, herr⟩
  have hlog : Real.log (N / (1 / (N : ℝ))) = 2 * Real.log N := by
    have hsq : (N : ℝ) / (1 / (N : ℝ)) = (N : ℝ) ^ 2 := by field_simp
    rw [hsq, Real.log_pow]
    norm_num
  rw [hlog] at hT
  linarith

end MPSPreparation
