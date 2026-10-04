/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceNormContractivity
import QICLean.Analysis.TraceNormVariational
import TNLean.Circuit.Channel.Conversion

/-!
# Approximate local channel conversions

A conversion of depth at most `T` and error at most `ε` maps `ρ` to a matrix within trace
norm `ε` of `σ`. For Hermitian inputs, composing two conversions adds their depths and
errors: the second channel contracts the first error, and the triangle inequality adds
the second error. In particular this applies to density matrices.

**Scope restriction (no classical feedforward):** the protocols are the local channels of
`QuantumCircuit.IsLocalChannelProtocol`. They do not include the measurements and classical
communication in the `QCcc` equivalence of arXiv:2103.13367, paragraph "Phases of matter".
The trace-norm approximation is that of the source, restricted to this class of channels.
Documented in `docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

## Main definitions

* `QuantumCircuit.chainTraceNorm` — trace norm of a matrix indexed by chain configurations.
* `QuantumCircuit.IsApproxLocalChannelConversion` — a depth-and-error bounded conversion.

## Main results

* `QuantumCircuit.IsApproxLocalChannelConversion.mono` — increasing either bound preserves
  approximate conversion.
* `QuantumCircuit.IsApproxLocalChannelConversion.trans` — composition with additive depth
  and error for Hermitian inputs.
* `QuantumCircuit.isApproxLocalChannelConversion_zero_iff` — zero-error conversion is exact.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, paragraph "Phases of matter".
* Wolf, *Quantum Channels & Operations*, Theorem 8.16 (trace-norm contractivity).
-/

open Matrix

noncomputable section

namespace QuantumCircuit

variable {d e f N : ℕ}

/-- Trace norm of a matrix on an `N`-site chain, after enumerating its configurations.
The trace norm is the sum of the singular values, not the ambient matrix norm. -/
def chainTraceNorm (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : ℝ :=
  traceNorm (equivReindexMap (Fintype.equivFin (Fin N → Fin d)) A)

theorem chainTraceNorm_nonneg (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    0 ≤ chainTraceNorm A := traceNorm_nonneg _

@[simp] theorem chainTraceNorm_zero :
    chainTraceNorm (0 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) = 0 := by
  simp [chainTraceNorm, traceNorm_zero]

@[simp] theorem chainTraceNorm_eq_zero_iff
    (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : chainTraceNorm A = 0 ↔ A = 0 := by
  rw [chainTraceNorm, traceNorm_eq_zero_iff]
  exact (Matrix.reindexLinearEquiv ℂ ℂ
    (Fintype.equivFin (Fin N → Fin d)) (Fintype.equivFin (Fin N → Fin d))).map_eq_zero_iff

/-- Triangle inequality for the trace norm of chain operators. -/
theorem chainTraceNorm_add_le (A B : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    chainTraceNorm (A + B) ≤ chainTraceNorm A + chainTraceNorm B := by
  simpa only [chainTraceNorm, map_add] using
    traceNorm_add_le (equivReindexMap (Fintype.equivFin _) A)
      (equivReindexMap (Fintype.equivFin _) B)

variable [NeZero N]

/-- A local channel protocol contracts the trace norm of a Hermitian chain operator.
This is Wolf's Theorem 8.16 applied after enumerating the input and output configurations. -/
theorem IsLocalChannelProtocol.chainTraceNorm_map_le {T : ℕ}
    {Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (hΨ : IsLocalChannelProtocol T Ψ)
    {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ} (hA : A.IsHermitian) :
    chainTraceNorm (Ψ A) ≤ chainTraceNorm A := by
  let ed := Fintype.equivFin (Fin N → Fin d)
  let ee := Fintype.equivFin (Fin N → Fin e)
  let Ψ' := equivReindexMap ee ∘ₗ Ψ ∘ₗ equivReindexMap ed.symm
  have hΨ' : IsKrausCPTP Ψ' :=
    isKrausCPTP_comp (isKrausCPTP_comp
      (equivReindexMap_isKrausCPTP ed.symm) hΨ.isKrausCPTP)
      (equivReindexMap_isKrausCPTP ee)
  have h := traceNorm_map_le_of_positive_of_tracePreserving
    (fun _ hX ↦ hΨ'.map_posSemidef hX) hΨ'.trace_map (hA.reindex ed)
  simpa [Ψ', chainTraceNorm, equivReindexMap, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, ed, ee] using h

/-- A matrix `ρ` is approximately converted into `σ` in depth at most `T` with trace-norm
error at most `ε` if a local channel protocol `Ψ` of depth at most `T` satisfies
`‖Ψ(ρ) - σ‖₁ ≤ ε`.

Source: arXiv:2103.13367, paragraph "Phases of matter", restricted to local channels
without classical feedforward. -/
def IsApproxLocalChannelConversion (T : ℕ) (ε : ℝ)
    (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) : Prop :=
  ∃ S ≤ T, ∃ Ψ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ,
    IsLocalChannelProtocol S Ψ ∧ chainTraceNorm (Ψ ρ - σ) ≤ ε

/-- An exact local channel conversion has zero trace-norm error. -/
theorem IsLocalChannelConversion.approx {T : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsLocalChannelConversion T ρ σ) : IsApproxLocalChannelConversion T 0 ρ σ := by
  obtain ⟨S, hS, Ψ, hΨ, rfl⟩ := h
  exact ⟨S, hS, Ψ, hΨ, by simp⟩

namespace IsApproxLocalChannelConversion

/-- Every matrix is converted into itself with depth and error zero. -/
theorem refl (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    IsApproxLocalChannelConversion 0 0 ρ ρ := (IsLocalChannelConversion.refl ρ).approx

/-- Increasing either the depth bound or the error bound preserves conversion. -/
theorem mono {T T' : ℕ} {ε ε' : ℝ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsApproxLocalChannelConversion T ε ρ σ) (hT : T ≤ T') (hε : ε ≤ ε') :
    IsApproxLocalChannelConversion T' ε' ρ σ := by
  obtain ⟨S, hS, Ψ, hΨ, herr⟩ := h
  exact ⟨S, hS.trans hT, Ψ, hΨ, herr.trans hε⟩

/-- Composition adds depth and error. The Hermiticity hypotheses hold for density matrices;
contractivity controls the first error and the triangle inequality adds the second.

Source: arXiv:2103.13367, paragraph "Phases of matter", the transitivity argument,
restricted to local channels without classical feedforward. -/
theorem trans {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsApproxLocalChannelConversion T₁ ε₁ ρ σ)
    (h₂ : IsApproxLocalChannelConversion T₂ ε₂ σ τ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    IsApproxLocalChannelConversion (T₁ + T₂) (ε₁ + ε₂) ρ τ := by
  obtain ⟨S₁, hS₁, Ψ₁, hΨ₁, herr₁⟩ := h₁
  obtain ⟨S₂, hS₂, Ψ₂, hΨ₂, herr₂⟩ := h₂
  refine ⟨S₁ + S₂, add_le_add hS₁ hS₂, Ψ₂ ∘ₗ Ψ₁, hΨ₁.comp hΨ₂, ?_⟩
  have hA : (Ψ₁ ρ - σ).IsHermitian :=
    (hΨ₁.isKrausCPTP.isKrausCP.isPositiveMap.map_isHermitian hρ).sub hσ
  have herr : chainTraceNorm (Ψ₂ (Ψ₁ ρ - σ) + (Ψ₂ σ - τ)) ≤ ε₁ + ε₂ :=
    (chainTraceNorm_add_le _ _).trans
      (add_le_add ((hΨ₂.chainTraceNorm_map_le hA).trans herr₁) herr₂)
  simpa only [LinearMap.comp_apply, map_sub, sub_add_sub_cancel] using herr

end IsApproxLocalChannelConversion

/-- Zero-error approximate conversion is exactly local channel conversion. -/
theorem isApproxLocalChannelConversion_zero_iff {T : ℕ}
    {ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ} :
    IsApproxLocalChannelConversion T 0 ρ σ ↔ IsLocalChannelConversion T ρ σ := by
  refine ⟨?_, IsLocalChannelConversion.approx⟩
  rintro ⟨S, hS, Ψ, hΨ, herr⟩
  exact ⟨S, hS, Ψ, hΨ, sub_eq_zero.mp
    ((chainTraceNorm_eq_zero_iff _).mp (le_antisymm herr (chainTraceNorm_nonneg _)))⟩

end QuantumCircuit
