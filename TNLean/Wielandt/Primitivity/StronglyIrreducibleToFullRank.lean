/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.WolfTheorem68
import QICLean.Kraus.InvariantProjection
import TNLean.Wielandt.Primitivity.PrimitiveBridge

/-!
# MPS reformulations of eventual full Kraus rank and irreducibility

The channel-generic proof is in
`QICLean.Kraus.Wielandt.Primitivity.StronglyIrreducibleToFullWordSpan`. This file
retains the established MPS statements used by canonical-form developments.

## Main results

* `hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper`: Proposition 3(c)
  to (b) of Sanz, Pérez-García, Wolf, and Cirac, arXiv:0909.5347.
* `isIrreducibleTensor_of_isPrimitiveMPS_of_posDef`:
  `IsPrimitiveMPS A ρ → ρ.PosDef → Kraus.IsIrreducibleFamily A`, the
  irreducibility half of the primitive-to-normal implication; the
  complementary aperiodicity input is recovered from strong irreducibility
  below.
* `isNormal_of_isPrimitiveMPS_with_posDef`: `IsPrimitiveMPS` plus a
  positive-definite fixed point implies normality.

## References

- Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Proposition 3.
- Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, Section 2.3.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **Proposition 3(c) to (b)**: strong irreducibility implies eventually full
Kraus rank. This is the MPS form of the channel-native Kraus theorem. -/
theorem hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hSI : IsStronglyIrreduciblePaper A) :
    HasEventuallyFullKrausRank A := by
  obtain ⟨_, _, _, hPrim, hIrr⟩ := hSI
  have hTP : Kraus.IsTP A := hNorm
  exact (Kraus.hasEventuallyFullWordSpan_iff_exists_pos_of_isTP A hTP).mp
    (Kraus.hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive
      A hTP hIrr hPrim)

/-- A primitive MPS tensor with a positive-definite fixed point has eventually
full Kraus rank. -/
theorem hasEventuallyFullKrausRank_of_isPrimitiveMPS_of_posDef [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ)
    (hρ_pd : ρ.PosDef) :
    HasEventuallyFullKrausRank A := by
  exact hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper A hP.norm
    (isStronglyIrreduciblePaper_of_isPrimitiveMPS_of_posDef hP hρ_pd)

/-- A primitive MPS tensor with a positive-definite fixed point is irreducible.

This is the irreducibility implication in Proposition 3 of Sanz,
Pérez-García, Wolf, and Cirac, arXiv:0909.5347. -/
theorem isIrreducibleTensor_of_isPrimitiveMPS_of_posDef [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef) :
    Kraus.IsIrreducibleFamily A :=
  Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
    (hPrim.isIrreducibleMap_of_posDef hPD)

/-- `IsPrimitiveMPS` plus a positive-definite fixed point implies normality. -/
theorem isNormal_of_isPrimitiveMPS_with_posDef [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ)
    (hρ_pd : ρ.PosDef) :
    Kraus.IsNormal A := by
  exact (hasEventuallyFullKrausRank_iff_isNormal A).mp
    (hasEventuallyFullKrausRank_of_isPrimitiveMPS_of_posDef hP hρ_pd)

end MPSTensor
