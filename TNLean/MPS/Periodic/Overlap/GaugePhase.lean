/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexPhasePositivity
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.Periodic.Defs

/-!
# Gauge-phase identities for periodic tensors

The general gauge-phase normalization theorem gives the repeated-block
relations used in the periodic-overlap argument of arXiv:1708.00029,
Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A unit-modulus gauge-phase relation gives a repeated-block relation.

If \(B^i=\zeta X A^i X^{-1}\) and \(|\zeta|=1\), then
\(A^i=\zeta^{-1}X^{-1}B^iX\), which is the `RepeatedBlocks A B`
relation. This is the final algebraic conversion used after the phase
normalization step in arXiv:1708.00029, Appendix A, lines 1082--1117. -/
theorem repeatedBlocks_of_gaugePhaseData_norm_one
    {A B : MPSTensor d D} (X : GL (Fin D) ℂ) {ζ : ℂ}
    (hζ_norm : ‖ζ‖ = 1)
    (hB :
      ∀ i : Fin d,
        B i =
          ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    RepeatedBlocks A B := by
  have hζ_ne : ζ ≠ 0 := Complex.ne_zero_of_norm_eq_one hζ_norm
  refine ⟨ζ⁻¹, X⁻¹, by rw [norm_inv, hζ_norm, inv_one], ?_⟩
  intro i
  simp only [inv_inv]
  have hconj :
      X⁻¹.val * B i * X.val = ζ • A i := by
    rw [hB i, mul_smul_comm, smul_mul_assoc]
    congr 1
    calc
      X⁻¹.val * (X.val * A i * X⁻¹.val) * X.val
          = X⁻¹.val * X.val * A i * (X⁻¹.val * X.val) := by
              simp only [Matrix.mul_assoc]
      _ = 1 * A i * 1 := by rw [Units.inv_mul]
      _ = A i := by simp
  rw [hconj, smul_smul, inv_mul_cancel₀ hζ_ne, one_smul]

/-- A gauge-phase equivalence between left-canonical irreducible blocks is a
repeated-block relation.

The scalar has unit modulus by the Perron--Frobenius normalization theorem; the
remaining conversion is purely algebraic. -/
theorem gaugePhaseEquiv_to_repeatedBlocks_of_leftCanonical_irreducible
    [NeZero D] {A B : MPSTensor d D}
    (h : GaugePhaseEquiv A B)
    (hA_left : IsLeftCanonical A) (hB_left : IsLeftCanonical B)
    (hB_irr : IsIrreducibleTensor B) :
    RepeatedBlocks A B := by
  obtain ⟨X, ζ, hζ_ne, hB⟩ := h
  exact repeatedBlocks_of_gaugePhaseData_norm_one X
    (gaugePhase_scalar_norm_eq_one_of_leftCanonical_irreducible
      hA_left hB_left hB_irr hζ_ne hB)
    hB

end MPSTensor
