/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVFigureEight
import TNLean.MPS.MPDO.CPSVVerticalBNT
import TNLean.MPS.MPDO.GroupedReferenceCorner

/-!
# Figure 8 for actual grouped sectors under literal CPSV canonical form

The literal vertical BNT grouping supplies positive corner equations for every
copy of each phase-class representative.  Comparing a copy with its
identity-gauge distinguished reference corner gives the actual-grouped Figure
8 identity under literal CPSV canonical form.

## Main result

* `MPSTensor.IsCPSVCanonicalForm.grouped_sector_gram_conj_eq`: each actual
  grouped gauge fixes the transported representative by Gram conjugation.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, Figures 7--8 and lines 1909--1919.
-/

open scoped Matrix ComplexOrder
open MPOTensor

namespace MPSTensor.IsCPSVCanonicalForm

variable {d D : ℕ}

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- **Figure 8 for an actual grouped sector under literal CPSV canonical form.**

The distinguished corner is transported to the copy's bond dimension and has
identity gauge.  The literal pairwise Figure 8 theorem compares it with the
chosen copy, so conjugation by the copy's Gram matrix fixes every letter of the
transported representative.

All hypotheses after `hM` are clauses of
`IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1903--1919. -/
theorem grouped_sector_gram_conj_eq
    {M : MPOTensor d D} (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
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
  classical
  let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
    (blocks ((C).repr j))
  let cq := μ ((C).enum j q) * ζ j q
  obtain ⟨W, c0, hc0, hCorner0⟩ :=
    exists_distinguished_grouped_reference_corner blocks μ V hdim X ζ
      hXDist hCoeffPos hCorner j q
  have hCornerq : ∀ w,
      (V ((C).enum j q))ᴴ * verticalTensor M w * V ((C).enum j q) =
        cq • ((X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ) * A w *
          (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ)) := by
    intro w
    simpa [cq, A] using (hCorner j q w).symm
  have hGram := hCanonical.gramDressing_eq_of_two_grouped_corners
    M hM A (V ((C).enum j q)) W (X j q) 1 cq c0
    (hCoeffPos j q) hc0 hCornerq (by intro w; simpa [A] using hCorner0 w)
  simpa [gramDressing, A] using congrFun hGram v

end GroupedSectors

end MPSTensor.IsCPSVCanonicalForm
