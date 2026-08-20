/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Semigroup.Primitivity.Helpers
import TNLean.MPS.Core.CPPrimitive
import TNLean.MPS.Core.TransferChannel
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

open scoped Matrix ComplexOrder BigOperators TNOperatorSpace
open Matrix

/-- A primitive irreducible channel has spectral radius less than one after subtracting
the projection onto any nonzero positive semidefinite fixed point. -/
theorem spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
    {D : ℕ} [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : IsChannel E)
    (hIrr : IsIrreducibleMap E)
    (hPrim : IsPrimitive E)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_ne : ρ ≠ 0)
    (hρ_fix : E ρ = ρ) :
    ∃ htr : Matrix.trace ρ ≠ 0,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (E - fixedPointProj (D := D) ρ htr)) < 1 := by
  have htr : Matrix.trace ρ ≠ 0 := by
    intro htr0
    exact hρ_ne ((Matrix.PosSemidef.trace_eq_zero_iff hρ_psd).1 htr0)
  refine ⟨htr, spectralRadius_lt_one_of_eigenvalues_lt_one (D := D)
    (E - fixedPointProj (D := D) ρ htr) ?_⟩
  intro ν hν
  exact compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel
    E hE hIrr ρ hρ_fix hρ_ne htr hPrim ν hν

namespace MPSTensor

variable {d D : ℕ}

/-- The transfer map commutes with conjugate transpose: `E(Xᴴ) = (E X)ᴴ`. -/
lemma transferMap_conjTranspose (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (d := d) (D := D) A Xᴴ = (transferMap (d := d) (D := D) A X)ᴴ := by
  simpa only [transferMap_apply, Kraus.map_apply] using (Kraus.map_conjTranspose A X).symm

/-- For the transfer map of an injective normalized tensor, any fixed point with trace
zero is the zero matrix. -/
theorem transferMap_fixedPoint_eq_zero_of_trace_eq_zero
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hInj : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hXfix : transferMap (d := d) (D := D) A X = X)
    (htrX : Matrix.trace X = 0) :
    X = 0 :=
  fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
    (transferMap_isChannel (A := A) hNorm) (injective_implies_irreducibleCP A hInj)
    X hXfix htrX

/-- For the transfer map of an irreducible normalized tensor, any fixed point with trace
zero is the zero matrix. -/
theorem transferMap_fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hXfix : transferMap (d := d) (D := D) A X = X)
    (htrX : Matrix.trace X = 0) :
    X = 0 :=
  fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
    (transferMap_isChannel (A := A) hNorm)
    (Kraus.isIrreducibleMap_transferMap_of_isIrreducibleTensor A hIrr) X hXfix htrX

/-- Peripheral primitivity of the transfer map of an irreducible normalized tensor implies
a complementary transfer-map gap for `E - P`, where `P` projects onto a fixed point. -/
theorem spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ transferMap (d := d) (D := D) A ρ = ρ ∧
        ∃ htr : Matrix.trace ρ ≠ 0,
          spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              ((transferMap (d := d) (D := D) A) - fixedPointProj (D := D) ρ htr))
            < 1 := by
  let E := transferMap (d := d) (D := D) A
  have hCh : IsChannel E := transferMap_isChannel (A := A) hNorm
  have hIrrMap : IsIrreducibleMap E :=
    Kraus.isIrreducibleMap_transferMap_of_isIrreducibleTensor A hIrr
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
    (hIrr : IsIrreducibleTensor A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A)) :
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
    (hInj : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ transferMap (d := d) (D := D) A ρ = ρ ∧
        ∃ htr : Matrix.trace ρ ≠ 0,
          spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              ((transferMap (d := d) (D := D) A) - fixedPointProj (D := D) ρ htr))
            < 1 := by
  have hIrr : IsIrreducibleTensor A :=
    Kraus.isIrreducibleTensor_of_isIrreducibleMap_transferMap A
      (injective_implies_irreducibleCP A hInj)
  exact spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
    (A := A) hIrr hNorm hPrim

/-- Peripheral primitivity of the transfer map of an injective normalized tensor implies
`MPSTensor.HasPrimitiveFixedPoint`. -/
theorem hasPrimitiveFixedPoint_of_peripheralPrimitive
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hInj : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A)) :
    MPSTensor.HasPrimitiveFixedPoint A := by
  have hIrr : IsIrreducibleTensor A :=
    Kraus.isIrreducibleTensor_of_isIrreducibleMap_transferMap A
      (injective_implies_irreducibleCP A hInj)
  exact hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible
    (A := A) hIrr hNorm hPrim

end MPSTensor
