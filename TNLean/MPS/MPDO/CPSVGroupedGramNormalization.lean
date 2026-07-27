/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalCommutant
import TNLean.MPS.MPDO.CPSVGroupedFigure8

/-!
# Gram and unitary normalization of literal grouped vertical sectors

This file applies normal-tensor rigidity to the actual-grouped Figure 8
comparison constructed directly from literal CPSV canonical form.

## Main results

* `MPSTensor.IsCPSVCanonicalForm.grouped_sector_gram_eq_pos_smul_one`: each grouped gauge has Gram
  matrix equal to a positive real multiple of the identity.
* `MPSTensor.IsCPSVCanonicalForm.grouped_sector_exists_unitary_normalization`: rescaling the grouped
  gauge by the inverse square root of that scalar makes it unitary.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1903--1921.
-/

open scoped Matrix ComplexOrder

open MPOTensor

namespace MPSTensor.IsCPSVCanonicalForm

variable {d D : ℕ}

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- The Gram matrix of an actual grouped vertical-sector gauge is a positive
real multiple of the identity.

All hypotheses after `hM` are clauses furnished by
`IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem grouped_sector_gram_eq_pos_smul_one
    {M : MPOTensor d D} (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
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
  have hGramConj : ∀ v,
      (X j q : Matrix (Fin (dim ((C).enum j q)))
          (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q * A v *
          (((X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q)⁻¹) = A v := by
    intro v
    simpa [A] using hCanonical.grouped_sector_gram_conj_eq blocks hM
      μ V hdim X ζ hXDist hCoeffPos hCorner j q v
  exact hNormalA.gram_eq_pos_smul_one_of_gram_conj_eq
    (Matrix.isUnits_det_units (X j q)) hGramConj

/-- Every actual grouped vertical-sector gauge becomes unitary after division
by the square root of its positive Gram scalar.

All hypotheses after `hM` are clauses furnished by
`IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem grouped_sector_exists_unitary_normalization
    {M : MPOTensor d D} (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
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
    hCanonical.grouped_sector_gram_eq_pos_smul_one blocks hM μ V
      hDimPos hNormal hdim X ζ hXDist hCoeffPos hCorner j q
  exact ⟨ω, hω,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      hω hGram⟩

end GroupedSectors

end MPSTensor.IsCPSVCanonicalForm
