/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.Cesaro
import TNLean.Channel.Irreducible.Similarity

/-!
# Wolf Chapter 6: numbered theorem statements

This module provides stable theorem names that mirror Wolf's numbering for
results already formalized elsewhere:

* Proposition 6.6 (`isIrreducibleMap_full_similarity`)
* Proposition 6.8 (`IsPositiveMap.wolf_prop_6_8`)
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {D : ℕ}
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

end Kraus

namespace IsPositiveMap

variable {d : ℕ}

/-- Wolf Proposition 6.8: every fixed point is a fixed complex linear combination
of four positive-semidefinite fixed points. -/
theorem wolf_prop_6_8
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    {X : Matrix (Fin d) (Fin d) ℂ}
    (hXfix : T X = X) :
    ∃ P₁ P₂ P₃ P₄ : Matrix (Fin d) (Fin d) ℂ,
      P₁.PosSemidef ∧ P₂.PosSemidef ∧ P₃.PosSemidef ∧ P₄.PosSemidef ∧
      T P₁ = P₁ ∧ T P₂ = P₂ ∧ T P₃ = P₃ ∧ T P₄ = P₄ ∧
      X = (2⁻¹ : ℂ) • (P₁ - P₂) - ((2⁻¹ : ℂ) * Complex.I) • (P₃ - P₄) :=
  IsPositiveMap.exists_posSemidef_fixedPoints_decomposition
    T hT hTP hXfix

end IsPositiveMap
