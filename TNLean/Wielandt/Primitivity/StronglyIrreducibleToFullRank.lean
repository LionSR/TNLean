/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.PrimitiveCriterion
import QICLean.Channel.Irreducible.InvariantProjection
import QICLean.Kraus.PrimitiveFixedPoint
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral
import QICLean.Kraus.Transfer
import TNLean.MPS.Structure.PrimitiveFixedPoint
import TNLean.Wielandt.Primitivity.Definitions
import TNLean.MPS.Tensor

/-!
# Normality from an irreducible transfer map without peripheral spectrum

The channel-generic proof is in
`QICLean.Kraus.Wielandt.Primitivity.StronglyIrreducibleToFullWordSpan`. This file
states its consequences for a left-canonical MPS tensor, in the three kept
notions: `Kraus.IsNormal`, `IsPrimitive` of the transfer map, and the
complementary fixed-point gap `Kraus.HasComplementaryFixedPointGap`.

## Main results

* `isNormal_of_isIrreducibleMap_of_isPrimitive`: an irreducible transfer map with
  peripheral spectrum `{1}` gives normality. This is the direction (c) to (b)
  of Proposition 3 of Sanz, Pérez-García, Wolf, and Cirac, arXiv:0909.5347.
* `exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive`: the same
  hypotheses give a complementary fixed-point gap at a positive-definite fixed
  matrix.
* `isNormal_of_hasComplementaryFixedPointGap_with_posDef`: `Kraus.HasComplementaryFixedPointGap`
  plus a positive-definite fixed point implies normality.

## References

- Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Proposition 3.
- Wolf, *Quantum Channels & Operations: Guided Tour*, Sections 6.2--6.4.
- Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, Section 2.3.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **Proposition 3(c) to (b)**: a left-canonical tensor whose transfer map is
irreducible and has no eigenvalue of modulus one other than one is normal. This
is the MPS form of the channel-native Kraus theorem.

Source: arXiv:0909.5347, Proposition 3, proof of (c)⟹(b). -/
theorem isNormal_of_isIrreducibleMap_of_isPrimitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) A))
    (hPrim : IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin D) A)) :
    Kraus.IsNormal A := by
  have hTP : Kraus.IsTP A := hNorm
  exact (Kraus.hasEventuallyFullWordSpan_iff_exists_pos_of_isTP A hTP).mp
    (Kraus.hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive
      A hTP hIrr hPrim)

/-- A left-canonical tensor whose transfer map is irreducible and has no
eigenvalue of modulus one other than one has a complementary fixed-point gap
at a positive-definite fixed matrix.

This connects the spectral characterization of Proposition 3(c) of
arXiv:0909.5347 to the complementary transfer-map gap used by the transfer-map
convergence theory. The proof chains:

1. `IsIrreducibleMap E → Kraus.IsIrreducibleFamily A`
2. `Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible`
3. every nonzero positive semidefinite fixed point of an irreducible transfer
   map is positive definite, via
   `Kraus.HasComplementaryFixedPointGap.posDef_of_isIrreducibleMap`. -/
theorem exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) A))
    (hPrim : IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin D) A)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.HasComplementaryFixedPointGap A ρ ∧ ρ.PosDef := by
  have hIrrT : Kraus.IsIrreducibleFamily A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hIrr
  obtain ⟨ρ, hP⟩ :=
    Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrrT hNorm hPrim
  exact ⟨ρ, hP, hP.posDef_of_isIrreducibleMap hIrr⟩

/-- `Kraus.HasComplementaryFixedPointGap` plus a positive-definite fixed point implies normality. -/
theorem isNormal_of_hasComplementaryFixedPointGap_with_posDef [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ)
    (hρ_pd : ρ.PosDef) :
    Kraus.IsNormal A :=
  isNormal_of_isIrreducibleMap_of_isPrimitive A hP.norm
    (hP.isIrreducibleMap_of_posDef hρ_pd) hP.isPrimitive

end MPSTensor
