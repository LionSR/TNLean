/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalCommutant
import TNLean.MPS.MPDO.GroupedFigure8

/-!
# Gram and unitary normalization of grouped vertical sectors

This file applies normal-tensor rigidity to the grouped Figure 8 comparison
constructed from normalized BNT-refined horizontal form, which is stronger
than literal CPSV canonical form.

## Main results

* `IsMPDO.grouped_sector_gram_eq_pos_smul_one`: each grouped gauge has Gram
  matrix equal to a positive real multiple of the identity.
* `IsMPDO.grouped_sector_exists_unitary_normalization`: rescaling the grouped
  gauge by the inverse square root of that scalar makes it unitary.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1903--1921.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- The Gram matrix of an actual grouped vertical-sector gauge is a positive
real multiple of the identity.

All hypotheses are clauses furnished by
`IsHorizontalCF.exists_verticalBNTGrouping_with_isometry`.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is the
normalized BNT-refined horizontal form, stronger than the literal CPSV
canonical form; see `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem IsMPDO.grouped_sector_gram_eq_pos_smul_one
    {M : MPOTensor d D} (hM : IsMPDO M)
    (hHorizontal : IsHorizontalCF M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hDimPos : ∀ k, 0 < dim k)
    (hNormal : ∀ k, MPSTensor.IsNormalTensor (blocks k))
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (X : (j : Fin (C).g) → (q : Fin ((C).copies j)) →
      GL (Fin (dim ((C).enum j q))) ℂ)
    (ζ : (j : Fin (C).g) → Fin ((C).copies j) → ℂ)
    (hXDist : ∀ j, X j ⟨0, (C).copies_pos j⟩ = 1)
    (hCoeffPos : ∀ j q, (0 : ℂ) < μ ((C).enum j q) * ζ j q)
    (hCorner : ∀ j q v,
      (μ ((C).enum j q) * ζ j q) •
          ((X j q : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      (X j q : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q = (ω : ℂ) • 1 := by
  letI : NeZero (dim ((C).enum j q)) := ⟨(hDimPos _).ne'⟩
  let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
    (blocks ((C).repr j))
  have hNormalA : MPSTensor.IsNormal A :=
    ((MPSTensor.isNormalTensor_cast_iff (hdim j q)
      (blocks ((C).repr j))).2 (hNormal ((C).repr j))).isNormal
  have hXdet : IsUnit
      (X j q : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ).det :=
    Matrix.isUnits_det_units (X j q)
  have hOneDet : IsUnit
      (1 : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ).det := by
    simp
  have hGramConj : ∀ v,
      (X j q : Matrix (Fin (dim ((C).enum j q)))
          (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q * A v *
          (((X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q)⁻¹) =
        (1 : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ)ᴴ * 1 * A v *
          (((1 : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ)ᴴ * 1)⁻¹) := by
    intro v
    simpa [A] using IsMPDO.grouped_sector_gram_conj_eq blocks hM hHorizontal
      μ V hdim X ζ hXDist hCoeffPos hCorner j q v
  obtain ⟨ω, hω, hGram⟩ :=
    hNormalA.gram_eq_pos_smul_gram_of_gram_conj_eq hXdet hOneDet hGramConj
  refine ⟨ω, hω, ?_⟩
  simpa using hGram

/-- Every actual grouped vertical-sector gauge becomes unitary after division
by the square root of its positive Gram scalar.

All hypotheses are clauses furnished by
`IsHorizontalCF.exists_verticalBNTGrouping_with_isometry`.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is the
normalized BNT-refined horizontal form, stronger than the literal CPSV
canonical form; see `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem IsMPDO.grouped_sector_exists_unitary_normalization
    {M : MPOTensor d D} (hM : IsMPDO M)
    (hHorizontal : IsHorizontalCF M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hDimPos : ∀ k, 0 < dim k)
    (hNormal : ∀ k, MPSTensor.IsNormalTensor (blocks k))
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (X : (j : Fin (C).g) → (q : Fin ((C).copies j)) →
      GL (Fin (dim ((C).enum j q))) ℂ)
    (ζ : (j : Fin (C).g) → Fin ((C).copies j) → ℂ)
    (hXDist : ∀ j, X j ⟨0, (C).copies_pos j⟩ = 1)
    (hCoeffPos : ∀ j q, (0 : ℂ) < μ ((C).enum j q) * ζ j q)
    (hCorner : ∀ j q v,
      (μ ((C).enum j q) * ζ j q) •
          ((X j q : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ •
          (X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ) ∈
        Matrix.unitaryGroup (Fin (dim ((C).enum j q))) ℂ := by
  obtain ⟨ω, hω, hGram⟩ :=
    IsMPDO.grouped_sector_gram_eq_pos_smul_one blocks hM hHorizontal μ V
      hDimPos hNormal hdim X ζ hXDist hCoeffPos hCorner j q
  have hOneDet : IsUnit
      (1 : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ).det := by
    simp
  have hUnit := Matrix.smul_mul_nonsing_inv_mem_unitaryGroup_of_gram_eq_smul
    (X := (X j q : Matrix (Fin (dim ((C).enum j q)))
      (Fin (dim ((C).enum j q))) ℂ))
    (Y := (1 : Matrix (Fin (dim ((C).enum j q)))
      (Fin (dim ((C).enum j q))) ℂ)) hOneDet hω (by simpa using hGram)
  refine ⟨ω, hω, ?_⟩
  simpa using hUnit

end GroupedSectors

end MPOTensor
