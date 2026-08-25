/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint
import QICLean.Kraus.Transfer

/-!
# MPS vocabulary for primitive fixed points

This module exposes the finite-Kraus complementary fixed-point-gap certificates from
QICLean under the established matrix-product-state vocabulary. The abbreviations are
reducible, so the QIC fields and generic methods remain available definitionally, without
a separate MPS-facing forwarding declaration or conversion theorem.

## Main definitions

* `IsPrimitiveMPS`: MPS-facing name for `Kraus.HasComplementaryFixedPointGap`.
* `HasPrimitiveFixedPoint`: MPS-facing name for `Kraus.HasPrimitiveFixedPoint`.
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators Kraus

namespace MPSTensor

/-- An MPS tensor is **primitive** (with witness `ρ`) when its finite Kraus family has a
complementary fixed-point gap at `ρ`.

This reducible abbreviation preserves the public MPS vocabulary while exposing
`Kraus.HasComplementaryFixedPointGap` and all of its field projections definitionally. -/
abbrev IsPrimitiveMPS {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  Kraus.HasComplementaryFixedPointGap A ρ

/-- An MPS tensor **has a primitive fixed point** when its finite Kraus family has one.

This reducible abbreviation preserves the existential MPS vocabulary while reusing
`Kraus.HasPrimitiveFixedPoint` directly. -/
abbrev HasPrimitiveFixedPoint {d D : ℕ} [NeZero D] (A : MPSTensor d D) : Prop :=
  Kraus.HasPrimitiveFixedPoint A

end MPSTensor
