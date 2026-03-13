/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.ClosureFixedPoint

/-!
# Legacy peripheral-spectrum closure wrapper

This file retains the older compatibility API for the special case where the
Kraus family is both unital and trace-preserving.

The live library route now goes through
`TNLean.Channel.PeripheralClosureFixedPoint`, which works with a positive
definite fixed point of the adjoint map and is the version used by the active
blocking pipeline. Accordingly, this legacy wrapper is intentionally excluded
from `TNLean.lean`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace MPSTensor

/-- The MPS transfer map is exactly the Kraus map packaged as a `ℂ`-linear map. -/
theorem transferMap_eq_krausMapL {d D : ℕ}
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    MPSTensor.transferMap (d := d) (D := D) K
      = KadisonSchwarz.krausMapL (d := d) (D := D) K := by
  ext X
  simp [MPSTensor.transferMap_apply, KadisonSchwarz.krausMapL_apply, KadisonSchwarz.krausMap]

/-- Legacy compatibility theorem for the older unital + trace-preserving
hypotheses.

New code should use
`peripheralEigenvalues_pow_mem_of_irreducible_unital_of_adjoint_fixedPoint`. -/
theorem peripheralEigenvalues_pow_mem_of_irreducible_biCanonical
    {d D : ℕ} [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus K)
    (h_tp : KadisonSchwarz.IsTPKraus K)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := d) (D := D) K)) :
    ∀ μ : ℂ,
      μ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) →
        ∀ n : ℕ,
          μ ^ n ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) := by
  have hOnePosDef : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))
  have hfixOne : Kraus.adjointMap K (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    simpa [Kraus.adjointMap, KadisonSchwarz.IsTPKraus, Matrix.one_mul, Matrix.mul_assoc] using h_tp
  simpa using
    peripheralEigenvalues_pow_mem_of_irreducible_unital_of_adjoint_fixedPoint
      (K := K) (d := d) (D := D) h_unital 1 hOnePosDef hfixOne hIrr

/-- Legacy compatibility wrapper for the older unital + trace-preserving
hypotheses.

New code should use
`peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint`. -/
theorem peripheral_isRootOfUnity_of_irreducible_biCanonical
    {d D : ℕ} [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus K)
    (h_tp : KadisonSchwarz.IsTPKraus K)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := d) (D := D) K)) :
    ∀ μ : ℂ,
      μ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) →
        ∃ p : ℕ, 0 < p ∧ μ ^ p = 1 := by
  have hOnePosDef : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))
  have hfixOne : Kraus.adjointMap K (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    simpa [Kraus.adjointMap, KadisonSchwarz.IsTPKraus, Matrix.one_mul, Matrix.mul_assoc] using h_tp
  simpa using
    peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint
      (K := K) (d := d) (D := D) h_unital 1 hOnePosDef hfixOne hIrr

end MPSTensor
