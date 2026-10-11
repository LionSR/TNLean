/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPO

/-!
# Matching-sector maps on three virtual legs

Composing two mixed endpoint maps retains only the two sectors in which
all three incoming legs agree. The analysis-synthesis product is the direct
sum of its endpoint products. The normalized trace is their
dimension-weighted normalized trace, including empty endpoint bonds.

These elementary contractions serve the actual action and fusion trees in
GLM23, `REsubmission.tex`, lines 1667--1685. They do not assume a comparison
matrix, scalarity, injectivity, or equality of endpoint symbols.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ e₀ e₁ : ℕ}

/-- Flatten the three direct-sum virtual registers in left-associated order.
Source: GLM23, `Agammasym` and lines 1667--1685. -/
def mixedEndpointTripleEquiv (a₀ a₁ b₀ b₁ c₀ c₁ : ℕ) :
    (((Fin a₀ ⊕ Fin a₁) × (Fin b₀ ⊕ Fin b₁)) × (Fin c₀ ⊕ Fin c₁)) ≃
      Fin ((a₀ + a₁) * (b₀ + b₁) * (c₀ + c₁)) :=
  (Equiv.prodCongr (mixedEndpointActedEquiv a₀ a₁ b₀ b₁) finSumFinEquiv).trans
    finProdFinEquiv

/-- Embed a three-leg analysis on the two matching endpoint sectors.
The incoming coordinates use the source's left-associated order.
Source: GLM23, `Agammasym` and lines 1667--1685. -/
def mixedEndpointTripleAnalysis
    (H₀ : Matrix (Fin d₀) ((Fin a₀ × Fin b₀) × Fin c₀) ℂ)
    (H₁ : Matrix (Fin d₁) ((Fin a₁ × Fin b₁) × Fin c₁) ℂ) :
    Matrix (Fin d₀ ⊕ Fin d₁)
      (((Fin a₀ ⊕ Fin a₁) × (Fin b₀ ⊕ Fin b₁)) × (Fin c₀ ⊕ Fin c₁)) ℂ :=
  fun z ((a, b), c) ↦ match z, a, b, c with
  | .inl z, .inl a, .inl b, .inl c => H₀ z ((a, b), c)
  | .inr z, .inr a, .inr b, .inr c => H₁ z ((a, b), c)
  | _, _, _, _ => 0

/-- Embed a three-leg synthesis on the matching endpoint sectors.
Source: GLM23, `Agammasym` and lines 1667--1685. -/
def mixedEndpointTripleSynthesis
    (S₀ : Matrix ((Fin a₀ × Fin b₀) × Fin c₀) (Fin d₀) ℂ)
    (S₁ : Matrix ((Fin a₁ × Fin b₁) × Fin c₁) (Fin d₁) ℂ) :
    Matrix (((Fin a₀ ⊕ Fin a₁) × (Fin b₀ ⊕ Fin b₁)) × (Fin c₀ ⊕ Fin c₁))
      (Fin d₀ ⊕ Fin d₁) ℂ :=
  fun ((a, b), c) z ↦ match a, b, c, z with
  | .inl a, .inl b, .inl c, .inl z => S₀ ((a, b), c) z
  | .inr a, .inr b, .inr c, .inr z => S₁ ((a, b), c) z
  | _, _, _, _ => 0

/-- Matching-sector tree contraction is block diagonal, even for
rectangular final bonds. Source: GLM23, lines 1667--1685. -/
theorem mixedEndpointTripleAnalysis_mul_synthesis
    (H₀ : Matrix (Fin d₀) ((Fin a₀ × Fin b₀) × Fin c₀) ℂ)
    (H₁ : Matrix (Fin d₁) ((Fin a₁ × Fin b₁) × Fin c₁) ℂ)
    (S₀ : Matrix ((Fin a₀ × Fin b₀) × Fin c₀) (Fin e₀) ℂ)
    (S₁ : Matrix ((Fin a₁ × Fin b₁) × Fin c₁) (Fin e₁) ℂ) :
    mixedEndpointTripleAnalysis H₀ H₁ * mixedEndpointTripleSynthesis S₀ S₁ =
      Matrix.fromBlocks (H₀ * S₀) 0 0 (H₁ * S₁) := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
      mixedEndpointTripleAnalysis, mixedEndpointTripleSynthesis,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]

/-- The two matching endpoint sectors contribute additively to the trace.
Source: GLM23, lines 1667--1685. -/
theorem mixedEndpointTripleAnalysis_trace_mul_synthesis
    (H₀ : Matrix (Fin d₀) ((Fin a₀ × Fin b₀) × Fin c₀) ℂ)
    (H₁ : Matrix (Fin d₁) ((Fin a₁ × Fin b₁) × Fin c₁) ℂ)
    (S₀ : Matrix ((Fin a₀ × Fin b₀) × Fin c₀) (Fin d₀) ℂ)
    (S₁ : Matrix ((Fin a₁ × Fin b₁) × Fin c₁) (Fin d₁) ℂ) :
    Matrix.trace (mixedEndpointTripleAnalysis H₀ H₁ *
        mixedEndpointTripleSynthesis S₀ S₁) =
      Matrix.trace (H₀ * S₀) + Matrix.trace (H₁ * S₁) := by
  rw [mixedEndpointTripleAnalysis_mul_synthesis]
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- Multiplying a normalized final-bond trace by its dimension recovers
the trace, including an empty bond. -/
theorem finDimension_mul_normalizedTrace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (d : ℂ) * ((d : ℂ)⁻¹ * Matrix.trace A) = Matrix.trace A := by
  by_cases hd : d = 0
  · subst d
    simp
  · rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hd), one_mul]

/-- Normalized trace of the actual matching-sector contraction is the
bond-dimension-weighted mean of its endpoint normalized traces. Empty
endpoint bonds contribute zero, so no positivity is required here.
Source: GLM23, lines 1667--1685. -/
theorem mixedEndpointTripleAnalysis_normalizedTrace_mul_synthesis
    (H₀ : Matrix (Fin d₀) ((Fin a₀ × Fin b₀) × Fin c₀) ℂ)
    (H₁ : Matrix (Fin d₁) ((Fin a₁ × Fin b₁) × Fin c₁) ℂ)
    (S₀ : Matrix ((Fin a₀ × Fin b₀) × Fin c₀) (Fin d₀) ℂ)
    (S₁ : Matrix ((Fin a₁ × Fin b₁) × Fin c₁) (Fin d₁) ℂ) :
    ((d₀ + d₁ : ℕ) : ℂ)⁻¹ *
        Matrix.trace (mixedEndpointTripleAnalysis H₀ H₁ *
          mixedEndpointTripleSynthesis S₀ S₁) =
      ((d₀ + d₁ : ℕ) : ℂ)⁻¹ *
        ((d₀ : ℂ) * ((d₀ : ℂ)⁻¹ * Matrix.trace (H₀ * S₀)) +
          (d₁ : ℂ) * ((d₁ : ℂ)⁻¹ * Matrix.trace (H₁ * S₁))) := by
  rw [mixedEndpointTripleAnalysis_trace_mul_synthesis,
    finDimension_mul_normalizedTrace, finDimension_mul_normalizedTrace]

end MPSTensor.MPOSymmetry
