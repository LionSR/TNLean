/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Semigroup.Primitivity.Helpers
import QICLean.Kraus.CPPrimitive
import QICLean.Kraus.TransferChannel
import TNLean.MPS.Structure.PrimitiveFixedPoint
import TNLean.Spectral.TransferOperatorGap

/-!
# Peripheral primitivity implies a complementary transfer-map gap

This file specializes channel-level peripheral-spectrum results to matrix-product-state
transfer maps. For an injective or irreducible normalized tensor, peripheral primitivity
implies that the transfer map minus its fixed-point projection has spectral radius less
than one. Consequently, the tensor has a primitive fixed point in the complementary-gap
sense.

The matrix-product-vector overlap consequence is stated in
`TNLean.MPS.Overlap.PeripheralToTransferMapGap`.
-/

open scoped Matrix ComplexOrder BigOperators Kraus
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The transfer map commutes with conjugate transpose: `E(Xᴴ) = (E X)ᴴ`. -/
lemma transferMap_conjTranspose (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.transferMap (d := d) (D := D) A Xᴴ = (Kraus.transferMap (d := d) (D := D) A X)ᴴ := by
  simpa only [Kraus.transferMap_apply, Kraus.map_apply] using (Kraus.map_conjTranspose A X).symm

/-- For the transfer map of an injective normalized tensor, any fixed point with trace
zero is the zero matrix. -/
theorem transferMap_fixedPoint_eq_zero_of_trace_eq_zero
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hInj : Kraus.IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hXfix : Kraus.transferMap (d := d) (D := D) A X = X)
    (htrX : Matrix.trace X = 0) :
    X = 0 :=
  fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
    (Kraus.isChannel_transferMap A hNorm) (Kraus.injective_implies_irreducibleCP A hInj)
    X hXfix htrX

/-- For the transfer map of an irreducible normalized tensor, any fixed point with trace
zero is the zero matrix. -/
theorem transferMap_fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hXfix : Kraus.transferMap (d := d) (D := D) A X = X)
    (htrX : Matrix.trace X = 0) :
    X = 0 :=
  fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
    (Kraus.isChannel_transferMap A hNorm)
    (Kraus.isIrreducibleMap_transferMap_of_isIrreducibleFamily A hIrr) X hXfix htrX

/-- Peripheral primitivity of the transfer map of an irreducible normalized tensor implies
a complementary transfer-map gap for `E - P`, where `P` projects onto a fixed point. -/
theorem spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (d := d) (D := D) A)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ Kraus.transferMap (d := d) (D := D) A ρ = ρ ∧
        ∃ htr : Matrix.trace ρ ≠ 0,
          spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              ((Kraus.transferMap (d := d) (D := D) A) - fixedPointProj (D := D) ρ htr))
            < 1 := by
  let E := Kraus.transferMap (d := d) (D := D) A
  have hCh : IsChannel E := Kraus.isChannel_transferMap A hNorm
  have hIrrMap : IsIrreducibleMap E :=
    Kraus.isIrreducibleMap_transferMap_of_isIrreducibleFamily A hIrr
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ := hCh.exists_posSemidef_fixedPoint (E := E) hDpos
  obtain ⟨htr, hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      E hCh hIrrMap hPrim ρ hρ_psd hρ_ne hρ_fix
  exact ⟨ρ, hρ_psd, hρ_ne, by simpa only [E] using hρ_fix,
    htr, by simpa only [E] using hgap⟩

/-- Peripheral primitivity of an irreducible left-canonical tensor implies
`MPSTensor.HasPrimitiveFixedPoint`. -/
theorem hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (d := d) (D := D) A)) :
    MPSTensor.HasPrimitiveFixedPoint A := by
  rcases spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
      (A := A) hIrr hNorm hPrim with
    ⟨ρ, hρ_psd, hρ_ne, hρ_fix, htr, hgap⟩
  exact ⟨ρ, hNorm, hρ_ne, hρ_psd, hρ_fix, by simpa only [map_sub] using hgap⟩

/-- Peripheral primitivity of the transfer map of an injective normalized tensor implies
a complementary transfer-map gap for `E - P`, where `P` projects onto a fixed point. -/
theorem spectralRadius_compl_lt_one_of_peripheralPrimitive
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hInj : Kraus.IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (d := d) (D := D) A)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ Kraus.transferMap (d := d) (D := D) A ρ = ρ ∧
        ∃ htr : Matrix.trace ρ ≠ 0,
          spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              ((Kraus.transferMap (d := d) (D := D) A) - fixedPointProj (D := D) ρ htr))
            < 1 := by
  have hIrr : Kraus.IsIrreducibleFamily A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_transferMap A
      (Kraus.injective_implies_irreducibleCP A hInj)
  exact spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
    (A := A) hIrr hNorm hPrim

/-- Peripheral primitivity of the transfer map of an injective normalized tensor implies
`MPSTensor.HasPrimitiveFixedPoint`. -/
theorem hasPrimitiveFixedPoint_of_peripheralPrimitive
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hInj : Kraus.IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (d := d) (D := D) A)) :
    MPSTensor.HasPrimitiveFixedPoint A := by
  have hIrr : Kraus.IsIrreducibleFamily A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_transferMap A
      (Kraus.injective_implies_irreducibleCP A hInj)
  exact hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible
    (A := A) hIrr hNorm hPrim

end MPSTensor
