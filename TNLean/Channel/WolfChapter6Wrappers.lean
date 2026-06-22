/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Cesaro
import TNLean.Channel.FixedPoint.ConditionalExpectation
import TNLean.Channel.Irreducible.Similarity

/-!
# Wolf Chapter 6: numbered theorem statements

This module provides stable theorem names that mirror Wolf's numbering for
results already formalized elsewhere:

* Proposition 6.6 (`isIrreducibleMap_full_similarity`)
* Proposition 6.8 (`IsChannel.posSemidef_parts_of_hermitian_fixedPoint`)
* Theorem 6.15 (`scalarConditionalExpectation_isConditionalExpectation`)
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Wolf Proposition 6.6: full similarity preserves irreducibility. -/
theorem wolf_prop_6_6
    [NeZero D]
    (E : Mat →ₗ[ℂ] Mat)
    {c : ℝ} (hc : 0 < c)
    {C : Mat} (hC : C.det ≠ 0)
    (hIrr : IsIrreducibleMap E) :
    IsIrreducibleMap ((c : ℂ) • similarityMap (D := D) C E) :=
  isIrreducibleMap_full_similarity (D := D) hc hC hIrr

/-- Wolf Theorem 6.15: scalar fixed-point conditional expectation. -/
theorem wolf_theorem_6_15_scalar
    [NeZero D]
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)
    (h_scalar : ∀ X : Mat, X ∈ adjointFixedPoints K →
      ∃ c : ℂ, X = c • (1 : Mat)) :
    IsConditionalExpectation
      (scalarConditionalExpectation ρ)
      (adjointFixedPointsStarSubalgebra K h_tp hρ hρ_fix) :=
  scalarConditionalExpectation_isConditionalExpectation K h_tp hρ hρ_fix h_scalar

end Kraus

namespace IsChannel

variable {d : ℕ}

/-- Wolf Proposition 6.8: Hermitian fixed points decompose into
positive-semidefinite fixed points. -/
theorem wolf_prop_6_8
    [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsChannel T)
    {X : Matrix (Fin d) (Fin d) ℂ}
    (hXh : X.IsHermitian)
    (hXfix : T X = X) :
    ∃ A B : Matrix (Fin d) (Fin d) ℂ,
      A.PosSemidef ∧ B.PosSemidef ∧ X = A - B ∧ T A = A ∧ T B = B :=
  IsChannel.posSemidef_parts_of_hermitian_fixedPoint T hT hXh hXfix

end IsChannel
