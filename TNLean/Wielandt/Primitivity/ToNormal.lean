/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint
import TNLean.MPS.Structure.PrimitiveFixedPoint

/-!
# Primitive fixed-point consequences used by TN Wielandt theory

The complementary transfer-map gap and its generic consequences are owned by QICLean.
Because `MPSTensor.IsPrimitiveMPS` is a reducible abbreviation for
`Kraus.HasComplementaryFixedPointGap`, tensor-specific consumers can use the following
QIC methods directly:

* `Kraus.HasComplementaryFixedPointGap.trace_ne_zero`
* `Kraus.HasComplementaryFixedPointGap.fixedPoint_unique`
* `Kraus.HasComplementaryFixedPointGap.complement_pow_tendsto_zero`
* `Kraus.HasComplementaryFixedPointGap.posDef_of_isIrreducibleMap`
* `Kraus.HasComplementaryFixedPointGap.posDef_of_isIrreducibleFamily`

This module remains as a lightweight import waypoint for the TN Wielandt module graph; it
introduces no replacement forwarding declarations around the generic QIC methods.
-/
