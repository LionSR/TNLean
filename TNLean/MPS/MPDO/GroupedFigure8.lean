/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.GroupedSectorGram
import TNLean.MPS.MPDO.VerticalBNT

/-!
# Figure 8 for grouped vertical sectors

This file applies the pairwise reflected form of Lemma L to the actual
vertical corners and gauges furnished by the grouped vertical decomposition
under normalized BNT-refined horizontal form.

## Main result

* `IsMPDO.grouped_sector_gram_conj_eq`: the Gram conjugation of each grouped
  copy fixes the transported representative tensor.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, Figures 7--8 and lines 1909--1919.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- **Figure 8 for an actual grouped sector and its distinguished copy.**

Assume the phase-class gauges, positive coefficients, and physical corner
identities furnished by `exists_verticalBNTGrouping_with_isometry`.  For each
copy `q`, transport the distinguished physical corner to the bond dimension
of `q` and apply the pairwise reflected form of Lemma L.  The resulting Gram
conjugation fixes the transported representative tensor.

No identity between an individual dressed tensor and its raw reflected
adjoint is used or asserted.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
theorem IsMPDO.grouped_sector_gram_conj_eq
    {M : MPOTensor d D} (hM : IsMPDO M)
    (hHorizontal : IsHorizontalCF M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
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
    (j : Fin (C).g) (q : Fin ((C).copies j))
    (v : Fin (D * D)) :
    let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
      (blocks ((C).repr j))
    let G := (X j q : Matrix (Fin (dim ((C).enum j q)))
      (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q
    G * A v * G⁻¹ = A v := by
  apply grouped_sector_gram_conj_eq_of_dressing blocks
    (M := M) (μ := μ) (V := V) (hdim := hdim) (X := X) (ζ := ζ)
      (hXDist := hXDist) (hCoeffPos := hCoeffPos) (hCorner := hCorner)
  intro n A VX VY X' Y cX cY hcX hcY hcornerX hcornerY
  exact hHorizontal.gramDressing_eq_of_two_grouped_corners M hM
    A VX VY X' Y cX cY hcX hcY hcornerX hcornerY

end GroupedSectors

end MPOTensor
