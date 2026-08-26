/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint
import QICLean.Kraus.Transfer
import TNLean.MPS.Structure.PrimitiveFixedPoint
import TNLean.Wielandt.Primitivity.Definitions
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral

/-!
# Connecting results for primitive MPS and complementary transfer-map gaps

This module collects the connection between the transfer-map
condition `IsStronglyIrreduciblePaper` and the complementary-gap predicate
`IsPrimitiveMPS`.  These results are used by the Proposition 3(c)→(b) proof in
`TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank` and by downstream
normality/canonical-form reductions.

## Main results

* `isPrimitiveMPS_of_isStronglyIrreduciblePaper` — strong irreducibility gives
  complementary transfer-map gap primitivity for a positive-definite fixed point.
* `isStronglyIrreduciblePaper_of_isPrimitiveMPS_of_posDef` — the reverse
  paper-vocabulary implication under a positive-definite fixed-point hypothesis.

## References

- [Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347], Proposition 3
- [Wolf, *Quantum Channels & Operations: Guided Tour*], Sections 6.2--6.4
-/

open scoped Matrix BigOperators ComplexOrder Kraus
open Matrix Filter

namespace MPSTensor

variable {d D : ℕ}

/-! ## Strong irreducibility and primitive complementary-gap data -/

/-- **Primitivity implication**: strong irreducibility implies the complementary-gap
predicate `IsPrimitiveMPS A ρ` for some positive-definite `ρ`.

This is the structural step in Proposition 3(c)→(b): it connects the paper's
spectral characterization (peripheral eigenvalues = {1}, irreducibility, and a
positive-definite fixed point) to the operational complementary transfer-map gap used
by the transfer-map convergence theory.

The proof chains:
1. `IsIrreducibleMap E → Kraus.IsIrreducibleFamily A`
2. `Kraus.IsIrreducibleFamily + IsPeripherallyPrimitive + hNorm`
   → `HasPrimitiveFixedPoint A`
   via `Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible`
3. every nonzero PSD fixed point of an irreducible transfer map is PosDef, via
   `Kraus.HasComplementaryFixedPointGap.posDef_of_isIrreducibleMap`
-/
theorem isPrimitiveMPS_of_isStronglyIrreduciblePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hSI : IsStronglyIrreduciblePaper A) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, IsPrimitiveMPS A ρ ∧ ρ.PosDef := by
  obtain ⟨_, _, _, hPrim, hIrrMap⟩ := hSI
  have hIrrT : Kraus.IsIrreducibleFamily A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hIrrMap
  obtain ⟨ρ', hPrimMPS⟩ :=
    Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrrT hNorm hPrim
  have hρ'PD : ρ'.PosDef :=
    hPrimMPS.posDef_of_isIrreducibleMap hIrrMap
  exact ⟨ρ', hPrimMPS, hρ'PD⟩

/-- Primitive complementary-gap data plus a positive-definite fixed point imply
paper strong irreducibility. -/
theorem isStronglyIrreduciblePaper_of_isPrimitiveMPS_of_posDef [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ)
    (hρ_pd : ρ.PosDef) :
    IsStronglyIrreduciblePaper A := by
  exact isStronglyIrreduciblePaper_of ρ hρ_pd hP.fixedPoint_is_fixed
    hP.isPrimitive
    (hP.isIrreducibleMap_of_posDef hρ_pd)

end MPSTensor
