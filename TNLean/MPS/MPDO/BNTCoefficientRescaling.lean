/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTCoefficients

/-!
# Representative rescaling of BNT coefficients

For label scales `s α`, the changes are
`χ'_{αβγ,k} = (s α * s β / s γ) * χ_{αβγ,k}`,
`c'^{(L)}_{αβγ} = (s α * s β / s γ)^L * c^{(L)}_{αβγ}`, and
`m' α = m α / s α`. Multiplicities do not change. Nonzero scales preserve
exactly the equation `m γ = ∑ α, ∑ β, c^{(1)}_{αβγ} * (m α * m β)`.

These are coefficient identities, not a construction of normalized BNTs or RFPs.
Non-unit positive rescaling leaves the spectral-radius-one NT convention.

Source: `Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/rfp_symmetry_bridge.tex`,
equation `bridge:rescaling`, using the coefficients of arXiv:1606.00608,
Theorem IV.13(ii).
-/

open scoped BigOperators ComplexOrder

namespace MPOTensor

variable {Λ : Type*}

namespace DiagonalChiFamily

/-- Rescale every diagonal entry by `s α * s β / s γ`, keeping its index set. -/
noncomputable def rescale (χ : DiagonalChiFamily Λ) (s : Λ → ℂ) :
    DiagonalChiFamily Λ where
  dim := χ.dim
  entry α β γ k := (s α * s β / s γ) * χ.entry α β γ k

@[simp] theorem rescale_dim (χ : DiagonalChiFamily Λ) (s : Λ → ℂ) (α β γ : Λ) :
    (χ.rescale s).dim α β γ = χ.dim α β γ := rfl

@[simp] theorem rescale_entry (χ : DiagonalChiFamily Λ) (s : Λ → ℂ)
    (α β γ : Λ) (k : Fin (χ.dim α β γ)) :
    (χ.rescale s).entry α β γ k = (s α * s β / s γ) * χ.entry α β γ k := rfl

/-- The trace-power rescaling formula holds at every natural length, including zero. -/
theorem tracePowerCoeff_rescale (χ : DiagonalChiFamily Λ) (s : Λ → ℂ)
    (α β γ : Λ) (L : ℕ) :
    (χ.rescale s).tracePowerCoeff α β γ L =
      (s α * s β / s γ) ^ L * χ.tracePowerCoeff α β γ L := by
  simp only [tracePowerCoeff, rescale, mul_pow, Finset.mul_sum]
  rfl

/-- Positive real representative scales preserve positivity of the diagonal entries. -/
theorem PosEntries.rescale {χ : DiagonalChiFamily Λ} (hχ : χ.PosEntries)
    (s : Λ → ℝ) (hs : ∀ α, 0 < s α) :
    (χ.rescale (fun α => (s α : ℂ))).PosEntries := by
  intro α β γ k
  change 0 < ((s α : ℂ) * (s β : ℂ) / (s γ : ℂ)) * χ.entry α β γ k
  apply mul_pos _ (hχ α β γ k)
  exact_mod_cast (div_pos (mul_pos (hs α) (hs β)) (hs γ))

end DiagonalChiFamily

namespace BNTLabelCoefficientFamily

/-- Coefficients after multiplying representative `α` by `s α`. -/
noncomputable def rescale (c : BNTLabelCoefficientFamily Λ) (s : Λ → ℂ) :
    BNTLabelCoefficientFamily Λ where
  coeff L α β γ := (s α * s β / s γ) ^ L * c.coeff L α β γ

@[simp] theorem rescale_coeff (c : BNTLabelCoefficientFamily Λ) (s : Λ → ℂ)
    (L : ℕ) (α β γ : Λ) :
    (c.rescale s).coeff L α β γ =
      (s α * s β / s γ) ^ L * c.coeff L α β γ := rfl

/-- Taking trace-power coefficients commutes with representative rescaling. -/
theorem ofChi_rescale (χ : DiagonalChiFamily Λ) (s : Λ → ℂ) :
    ofChi (χ.rescale s) = (ofChi χ).rescale s := by
  unfold ofChi rescale
  congr 1
  funext L α β γ
  exact χ.tracePowerCoeff_rescale s α β γ L

end BNTLabelCoefficientFamily

namespace BNTLabelTraceScalarFamily

/-- The trace scalars change inversely to their representatives. -/
noncomputable def rescale (m : BNTLabelTraceScalarFamily Λ) (s : Λ → ℂ) :
    BNTLabelTraceScalarFamily Λ where
  traceScalar α := m.traceScalar α / s α

@[simp] theorem rescale_traceScalar (m : BNTLabelTraceScalarFamily Λ) (s : Λ → ℂ)
    (α : Λ) : (m.rescale s).traceScalar α = m.traceScalar α / s α := rfl

/-- The rescaled quadratic coefficient sum is the original sum divided by `s γ`. -/
theorem rescale_coefficient_sum [Fintype Λ]
    (m : BNTLabelTraceScalarFamily Λ) (c : BNTLabelCoefficientFamily Λ)
    (s : Λ → ℂ) (hs : ∀ α, s α ≠ 0) (γ : Λ) :
    (∑ α, ∑ β, (c.rescale s).coeff 1 α β γ *
      ((m.rescale s).traceScalar α * (m.rescale s).traceScalar β)) =
      (∑ α, ∑ β, c.coeff 1 α β γ * (m.traceScalar α * m.traceScalar β)) / s γ := by
  simp only [BNTLabelCoefficientFamily.rescale_coeff, rescale_traceScalar, pow_one,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  field_simp [hs α, hs β, hs γ]

/-- For nonzero scales, the length-one idempotent coefficient equation is equivalent
before and after rescaling. No NT normalization is asserted. -/
theorem hasIdempotentCoefficientForm_rescale_iff [Fintype Λ]
    (m : BNTLabelTraceScalarFamily Λ) (c : BNTLabelCoefficientFamily Λ)
    (s : Λ → ℂ) (hs : ∀ α, s α ≠ 0) :
    (m.rescale s).HasIdempotentCoefficientForm (c.rescale s) ↔
      m.HasIdempotentCoefficientForm c := by
  unfold HasIdempotentCoefficientForm
  simp only [rescale_coefficient_sum m c s hs]
  simp only [rescale_traceScalar, div_left_inj' (hs _)]

end BNTLabelTraceScalarFamily

end MPOTensor
