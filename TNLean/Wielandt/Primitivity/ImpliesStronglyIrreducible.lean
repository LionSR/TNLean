/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity
import QICLean.MPS.Core.TransferChannel
import TNLean.Wielandt.Primitivity.Definitions

/-!
# Fixed-length vector spreading: MPS formulations

This file states the positivity and irreducibility consequences of fixed-length
vector spreading in transfer-map notation. Their finite-Kraus proofs are provided
by `TNLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity`.

These results form the first part of Proposition 3, direction (a) to (c), of
Sanz, Pérez-García, Wolf, and Cirac, arXiv:0909.5347.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Module

namespace MPSTensor

variable {d D : ℕ}

/-- Sandwiching a rank-one matrix gives the rank-one matrix of the image vector. -/
theorem sandwich_vecMulVec
    (M : Matrix (Fin D) (Fin D) ℂ) (φ : Fin D → ℂ) :
    M * vecMulVec φ (star φ) * Mᴴ =
      vecMulVec (M *ᵥ φ) (star (M *ᵥ φ)) := by
  rw [Matrix.mul_assoc, vecMulVec_mul, ← star_mulVec M φ, mul_vecMulVec]

/-- The transfer-map power of a rank-one matrix is the sum over words of that length. -/
theorem transferMap_pow_rankOne_eq_sum
    (A : MPSTensor d D) (q : ℕ) (φ : Fin D → ℂ) :
    ((transferMap (d := d) (D := D) A) ^ q) (vecMulVec φ (star φ)) =
      ∑ σ : Fin q → Fin d,
        vecMulVec (evalWord A (List.ofFn σ) *ᵥ φ)
          (star (evalWord A (List.ofFn σ) *ᵥ φ)) := by
  simpa only [Kraus.mapLM_eq_transferMap] using
    Kraus.mapLM_pow_rankOne_eq_sum A q φ

/-- A spanning finite family has a positive-definite frame operator. -/
theorem posDef_sum_vecMulVec_of_span_eq_top {ι : Type*} [Fintype ι]
    (v : ι → (Fin D → ℂ))
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    (∑ i : ι, vecMulVec (v i) (star (v i))).PosDef :=
  (Matrix.posDef_sum_vecMulVec_iff_span_eq_top v).2 hspan

/-- Fixed-length full vector spreading makes the corresponding rank-one image
positive definite. -/
theorem transferMap_pow_rankOne_posDef
    (A : MPSTensor d D) {q : ℕ}
    (hq : ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan A φ q = ⊤)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0) :
    (((transferMap (d := d) (D := D) A) ^ q) (vecMulVec φ (star φ))).PosDef := by
  simpa only [Kraus.mapLM_eq_transferMap] using
    Kraus.mapLM_pow_rankOne_posDef_of_vectorSpreadSpan_eq_top A hq φ hφ

/-- Under fixed-length full vector spreading, a nonzero positive-semidefinite
fixed point of the transfer map is positive definite. -/
theorem posDef_fixedPoint_of_isPrimitivePaper
    (A : MPSTensor d D)
    {q : ℕ} (hq : ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan A φ q = ⊤)
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hpsd : ρ.PosSemidef) (hne : ρ ≠ 0)
    (hfix : transferMap (d := d) (D := D) A ρ = ρ) :
    ρ.PosDef := by
  rw [← Kraus.mapLM_eq_transferMap] at hfix
  exact Kraus.posDef_fixedPoint_of_vectorSpreadSpan_eq_top A hq hpsd hne hfix

/-- Every power of the transfer map preserves positive semidefiniteness. -/
theorem transferMap_pow_posSemidef
    (A : MPSTensor d D) (n : ℕ)
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hpsd : ρ.PosSemidef) :
    (((transferMap (d := d) (D := D) A) ^ n) ρ).PosSemidef := by
  simpa only [Kraus.mapLM_eq_transferMap] using
    Kraus.mapLM_pow_posSemidef A n hpsd

/-- Fixed-length full vector spreading makes the corresponding transfer-map
power positivity improving. -/
theorem transferMap_pow_positivity_improving
    (A : MPSTensor d D)
    {q : ℕ} (hq : ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan A φ q = ⊤)
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hpsd : ρ.PosSemidef) (hne : ρ ≠ 0) :
    (((transferMap (d := d) (D := D) A) ^ q) ρ).PosDef := by
  simpa only [Kraus.mapLM_eq_transferMap] using
    Kraus.mapLM_pow_positivityImproving_of_vectorSpreadSpan_eq_top A hq hpsd hne

/-- A rank-deficient nonzero positive-semidefinite fixed point contradicts
paper-primitivity. -/
theorem not_isPrimitivePaper_of_posSemidef_fixedPoint_not_posDef
    (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hpsd : ρ.PosSemidef) (hne : ρ ≠ 0)
    (hfix : transferMap (d := d) (D := D) A ρ = ρ)
    (hnotpd : ¬ρ.PosDef) :
    ¬IsPrimitivePaper A :=
  fun ⟨_, _, hq⟩ => hnotpd (posDef_fixedPoint_of_isPrimitivePaper A hq hpsd hne hfix)

/-- Under fixed-length full vector spreading, every nonzero positive-semidefinite
fixed point of a positive transfer-map power is positive definite. -/
theorem posDef_fixedPoint_of_pow_of_isPrimitivePaper
    (A : MPSTensor d D)
    {q : ℕ} (hq : ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan A φ q = ⊤)
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hpsd : ρ.PosSemidef) (hne : ρ ≠ 0)
    {p : ℕ} (hp : 0 < p)
    (hfix : ((transferMap (d := d) (D := D) A) ^ p) ρ = ρ) :
    ρ.PosDef := by
  rw [← Kraus.mapLM_eq_transferMap] at hfix
  exact Kraus.posDef_pow_fixedPoint_of_vectorSpreadSpan_eq_top A hq hpsd hne hp hfix

/-- A rank-deficient nonzero positive-semidefinite fixed point of a positive
transfer-map power contradicts paper-primitivity. -/
theorem not_isPrimitivePaper_of_posSemidef_pow_fixedPoint_not_posDef
    (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hpsd : ρ.PosSemidef) (hne : ρ ≠ 0)
    {p : ℕ} (hp : 0 < p)
    (hfix : ((transferMap (d := d) (D := D) A) ^ p) ρ = ρ)
    (hnotpd : ¬ρ.PosDef) :
    ¬IsPrimitivePaper A :=
  fun ⟨_, _, hq⟩ =>
    hnotpd (posDef_fixedPoint_of_pow_of_isPrimitivePaper A hq hpsd hne hp hfix)

/-- Paper-primitivity implies that the tensor has no nontrivial invariant
orthogonal projection. -/
theorem isIrreducibleTensor_of_isPrimitivePaper
    (A : MPSTensor d D)
    (hPrim : IsPrimitivePaper A) :
    IsIrreducibleTensor A := by
  obtain ⟨q, _, hq⟩ := hPrim
  exact Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
    (Kraus.isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top A hq)

end MPSTensor
