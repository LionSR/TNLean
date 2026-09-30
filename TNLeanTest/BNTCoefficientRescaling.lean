/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTCoefficientRescaling

/-!
# Signature and axiom checks for representative rescaling

The signatures check unchanged multiplicities, the entry and coefficient formulas,
all natural lengths, positivity for positive real scales, and the equivalence of
the length-one idempotent coefficient equation for nonzero complex scales.
-/

open scoped BigOperators ComplexOrder
open MPOTensor

variable {Λ : Type*}

example (χ : DiagonalChiFamily Λ) (s : Λ → ℂ) (α β γ : Λ) :
    (χ.rescale s).dim α β γ = χ.dim α β γ :=
  χ.rescale_dim s α β γ

example (χ : DiagonalChiFamily Λ) (s : Λ → ℂ) (α β γ : Λ)
    (k : Fin (χ.dim α β γ)) :
    (χ.rescale s).entry α β γ k = (s α * s β / s γ) * χ.entry α β γ k :=
  χ.rescale_entry s α β γ k

example (χ : DiagonalChiFamily Λ) (s : Λ → ℂ) (α β γ : Λ) (L : ℕ) :
    (χ.rescale s).tracePowerCoeff α β γ L =
      (s α * s β / s γ) ^ L * χ.tracePowerCoeff α β γ L :=
  χ.tracePowerCoeff_rescale s α β γ L

example {χ : DiagonalChiFamily Λ} (hχ : χ.PosEntries)
    (s : Λ → ℝ) (hs : ∀ α, 0 < s α) :
    (χ.rescale (fun α => (s α : ℂ))).PosEntries :=
  hχ.rescale s hs

example (c : BNTLabelCoefficientFamily Λ) (s : Λ → ℂ) (L : ℕ) (α β γ : Λ) :
    (c.rescale s).coeff L α β γ = (s α * s β / s γ) ^ L * c.coeff L α β γ :=
  c.rescale_coeff s L α β γ

example (χ : DiagonalChiFamily Λ) (s : Λ → ℂ) :
    BNTLabelCoefficientFamily.ofChi (χ.rescale s) =
      (BNTLabelCoefficientFamily.ofChi χ).rescale s :=
  BNTLabelCoefficientFamily.ofChi_rescale χ s

example (m : BNTLabelTraceScalarFamily Λ) (s : Λ → ℂ) (α : Λ) :
    (m.rescale s).traceScalar α = m.traceScalar α / s α :=
  m.rescale_traceScalar s α

example [Fintype Λ] (m : BNTLabelTraceScalarFamily Λ)
    (c : BNTLabelCoefficientFamily Λ) (s : Λ → ℂ) (hs : ∀ α, s α ≠ 0) (γ : Λ) :
    (∑ α, ∑ β, (c.rescale s).coeff 1 α β γ *
      ((m.rescale s).traceScalar α * (m.rescale s).traceScalar β)) =
      (∑ α, ∑ β, c.coeff 1 α β γ * (m.traceScalar α * m.traceScalar β)) / s γ :=
  m.rescale_coefficient_sum c s hs γ

example [Fintype Λ] (m : BNTLabelTraceScalarFamily Λ)
    (c : BNTLabelCoefficientFamily Λ) (s : Λ → ℂ) (hs : ∀ α, s α ≠ 0) :
    (m.rescale s).HasIdempotentCoefficientForm (c.rescale s) ↔
      m.HasIdempotentCoefficientForm c :=
  m.hasIdempotentCoefficientForm_rescale_iff c s hs

-- Length zero remains valid even for zero scales.
example (χ : DiagonalChiFamily Λ) (α β γ : Λ) :
    (χ.rescale (fun _ => 0)).tracePowerCoeff α β γ 0 = χ.tracePowerCoeff α β γ 0 := by
  simpa using χ.tracePowerCoeff_rescale (fun _ => 0) α β γ 0

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'MPOTensor.DiagonalChiFamily.tracePowerCoeff_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPOTensor.DiagonalChiFamily.tracePowerCoeff_rescale

/-- info: 'MPOTensor.DiagonalChiFamily.PosEntries.rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPOTensor.DiagonalChiFamily.PosEntries.rescale

/-- info: 'MPOTensor.BNTLabelCoefficientFamily.ofChi_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPOTensor.BNTLabelCoefficientFamily.ofChi_rescale

/-- info: 'MPOTensor.BNTLabelTraceScalarFamily.rescale_coefficient_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPOTensor.BNTLabelTraceScalarFamily.rescale_coefficient_sum

/-- info: 'MPOTensor.BNTLabelTraceScalarFamily.hasIdempotentCoefficientForm_rescale_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MPOTensor.BNTLabelTraceScalarFamily.hasIdempotentCoefficientForm_rescale_iff

end AxiomChecks
