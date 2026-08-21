/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Quantitative
import TNLean.Wielandt.RectangularSpan.Basic

/-!
# Rectangular span quantitative ceiling for matrix product tensors

This module states the finite-matrix-family dimension bound for matrix product tensors.
-/

open scoped Matrix

namespace MPSTensor

open Module

variable {d D : ℕ}

/-- The rectangular span has dimension at most `D * rank(P)`.

This improves the general bound `≤ D²` when `rank(P) < D`. -/
theorem rectSpan_finrank_le_rank_mul_D (P : Matrix (Fin D) (Fin D) ℂ)
    (A : MPSTensor d D) (n : ℕ) :
    finrank ℂ (rectSpan P A n) ≤ D * P.rank :=
  Kraus.rectSpan_finrank_le_rank_mul_D P A n

end MPSTensor
