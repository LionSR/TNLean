/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TNLean.Circuit.Channel.ApproximateConversion

/-!
# Asymptotic local channel conversions

Families of chain operators are asymptotically locally convertible if their trace-norm
conversion errors tend to zero and their circuit depths are eventually bounded by
`C (1 + log (N + 1))^k`, for constants `C ≥ 0` and `k : ℕ`. The shift in the logarithm only
fixes the values at small sizes; this is a polylogarithmic bound. Mutual convertibility is
an equivalence relation on Hermitian families, and hence on density-matrix families.

**Scope restriction (enlarged sites, no classical feedforward):** these are the protocols of
`QuantumCircuit.IsLocalChannelProtocol`, with unit-cost two-site layers even after onsite
channels enlarge the local dimension. Intermediate dimensions have no uniform bound across
system sizes. The source's intersite gates act on fixed-dimensional physical qudits, and
its `QCcc` protocols also allow classical feedforward. This is a local-channel model variant
inspired by the source's asymptotic criterion; no uniform depth simulation or inclusion in
the source relation is established. Finite compositions in this model have additive depth.
Documented in `docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

## Main definitions

* `QuantumCircuit.IsAsymptoticLocalChannelConversion` — polylogarithmic-depth conversion
  with vanishing trace-norm error.
* `QuantumCircuit.IsLocalChannelPhaseEquivalent` — conversion in both directions.

## Main results

* `QuantumCircuit.IsAsymptoticLocalChannelConversion.trans` — asymptotic conversions compose.
* `QuantumCircuit.IsLocalChannelPhaseEquivalent.equivalence` — an equivalence relation on
  families that are eventually Hermitian.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, paragraph "Phases of matter".
-/

open Matrix Filter Topology

namespace QuantumCircuit

variable {d e f : ℕ}

/-- Asymptotic local conversion with polylogarithmic depth and trace-norm error tending to
zero. Only the tail of the families matters.

Motivated by arXiv:2103.13367, paragraph "Phases of matter", in the enlarged-site
local-channel model; see `docs/paper-gaps/psc21_local_channel_phase_scope.tex`. -/
def IsAsymptoticLocalChannelConversion
    (ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) : Prop :=
  ∃ (k : ℕ) (C : ℝ) (ε : ℕ → ℝ), 0 ≤ C ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ (N : ℕ) in atTop, ∀ [NeZero N], ∃ T : ℕ,
      (T : ℝ) ≤ C * (1 + Real.log ((N : ℝ) + 1)) ^ k ∧
      IsApproxLocalChannelConversion T (ε N) (ρ N) (σ N)

namespace IsAsymptoticLocalChannelConversion

/-- The identity channels give an asymptotic conversion with zero depth and error. -/
theorem refl (ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    IsAsymptoticLocalChannelConversion ρ ρ := by
  refine ⟨0, 0, fun _ ↦ 0, le_rfl, tendsto_const_nhds, Eventually.of_forall ?_⟩
  intro N _
  exact ⟨0, by simp, IsApproxLocalChannelConversion.refl (ρ N)⟩

/-- Asymptotic conversions compose for eventually Hermitian families, in particular for
families of density matrices. The new error is `ε₁ + ε₂`; the sum of two polylogarithmic
depth bounds is again polylogarithmic.

The transitivity argument is that of arXiv:2103.13367, paragraph "Phases of matter",
for the enlarged-site local-channel model of
`docs/paper-gaps/psc21_local_channel_phase_scope.tex`. -/
theorem trans
    {ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : (N : ℕ) → Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsAsymptoticLocalChannelConversion ρ σ)
    (h₂ : IsAsymptoticLocalChannelConversion σ τ)
    (hρ : ∀ᶠ N in atTop, (ρ N).IsHermitian)
    (hσ : ∀ᶠ N in atTop, (σ N).IsHermitian) :
    IsAsymptoticLocalChannelConversion ρ τ := by
  obtain ⟨k₁, C₁, ε₁, hC₁, hε₁, h₁⟩ := h₁
  obtain ⟨k₂, C₂, ε₂, hC₂, hε₂, h₂⟩ := h₂
  refine ⟨max k₁ k₂, C₁ + C₂, fun N ↦ ε₁ N + ε₂ N, add_nonneg hC₁ hC₂,
    by simpa using hε₁.add hε₂, ?_⟩
  filter_upwards [h₁, h₂, hρ, hσ] with N h₁N h₂N hρN hσN
  intro _
  obtain ⟨T₁, hT₁, hc₁⟩ := h₁N
  obtain ⟨T₂, hT₂, hc₂⟩ := h₂N
  refine ⟨T₁ + T₂, ?_, hc₁.trans hc₂ hρN hσN⟩
  have hb : 1 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg N))
    linarith
  calc
    ((T₁ + T₂ : ℕ) : ℝ) ≤
        C₁ * (1 + Real.log ((N : ℝ) + 1)) ^ k₁ +
          C₂ * (1 + Real.log ((N : ℝ) + 1)) ^ k₂ := by
            push_cast
            exact add_le_add hT₁ hT₂
    _ ≤ C₁ * (1 + Real.log ((N : ℝ) + 1)) ^ max k₁ k₂ +
          C₂ * (1 + Real.log ((N : ℝ) + 1)) ^ max k₁ k₂ :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (le_max_left _ _)) hC₁)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (le_max_right _ _)) hC₂)
    _ = (C₁ + C₂) * (1 + Real.log ((N : ℝ) + 1)) ^ max k₁ k₂ := (add_mul _ _ _).symm

end IsAsymptoticLocalChannelConversion

/-- Mutual asymptotic conversion by polylogarithmic-depth local channels. -/
def IsLocalChannelPhaseEquivalent
    (ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) : Prop :=
  IsAsymptoticLocalChannelConversion ρ σ ∧ IsAsymptoticLocalChannelConversion σ ρ

namespace IsLocalChannelPhaseEquivalent

/-- Every family is locally phase equivalent to itself. -/
theorem refl (ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    IsLocalChannelPhaseEquivalent ρ ρ :=
  ⟨IsAsymptoticLocalChannelConversion.refl ρ, IsAsymptoticLocalChannelConversion.refl ρ⟩

/-- Mutual conversion is symmetric. -/
theorem symm
    {ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsLocalChannelPhaseEquivalent ρ σ) : IsLocalChannelPhaseEquivalent σ ρ := ⟨h.2, h.1⟩

/-- Local phase equivalence is transitive on eventually Hermitian families. -/
theorem trans
    {ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {σ : (N : ℕ) → Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    {τ : (N : ℕ) → Matrix (Fin N → Fin f) (Fin N → Fin f) ℂ}
    (h₁ : IsLocalChannelPhaseEquivalent ρ σ) (h₂ : IsLocalChannelPhaseEquivalent σ τ)
    (hρ : ∀ᶠ N in atTop, (ρ N).IsHermitian)
    (hσ : ∀ᶠ N in atTop, (σ N).IsHermitian)
    (hτ : ∀ᶠ N in atTop, (τ N).IsHermitian) : IsLocalChannelPhaseEquivalent ρ τ :=
  ⟨h₁.1.trans h₂.1 hρ hσ, h₂.2.trans h₁.2 hτ hσ⟩

/-- Mutual polylogarithmic-depth local conversion is an equivalence relation on families
that are eventually Hermitian. Density-matrix families satisfy this condition. -/
theorem equivalence : Equivalence (fun
    (ρ σ : {ρ : (N : ℕ) → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ //
      ∀ᶠ N in atTop, (ρ N).IsHermitian}) ↦ IsLocalChannelPhaseEquivalent ρ.1 σ.1) :=
  ⟨fun ρ ↦ refl ρ.1, fun h ↦ h.symm,
    fun {ρ σ τ} h₁ h₂ ↦ h₁.trans h₂ ρ.2 σ.2 τ.2⟩

end IsLocalChannelPhaseEquivalent

end QuantumCircuit
