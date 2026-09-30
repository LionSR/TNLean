/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixGramUnitary
import TNLean.MPS.MPDO.GroupedSectorGram

/-!
# Unitary normalization of grouped vertical sectors

The grouped-corner Gram-dressing hypothesis makes the Gram matrix of every
grouped gauge a positive multiple of the identity. Dividing the gauge by the
square root of that scalar makes it unitary. The argument uses no
canonical-form hypothesis: literal CPSV canonical form and normalized
BNT-refined horizontal form each supply the Gram dressing independently.

## Main result

* `MPOTensor.grouped_sector_exists_unitary_normalization_of_dressing`:
  rescaling a grouped gauge by the inverse square root of its Gram scalar
  makes it unitary.

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

/-- Every grouped vertical-sector gauge becomes unitary after division by the
square root of its positive Gram scalar.

The hypotheses are those of
`grouped_sector_gram_eq_pos_smul_one_of_dressing`: the grouped-corner Gram
dressing together with the clauses of `HasVerticalBNTGroupingWithIsometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem grouped_sector_exists_unitary_normalization_of_dressing
    {M : MPOTensor d D} (hDressing : HasGroupedCornerGramDressing M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hDimPos : ∀ k, 0 < dim k)
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (hNormal : ∀ j q, Kraus.IsNormal
      (cast (congrArg (MPSTensor (D * D)) (hdim j q))
        (blocks ((C).repr j))))
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
    grouped_sector_gram_eq_pos_smul_one_of_dressing blocks hDressing μ V
      hDimPos hdim hNormal X ζ hXDist hCoeffPos hCorner j q
  exact ⟨ω, hω,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      hω hGram⟩

end GroupedSectors

end MPOTensor
