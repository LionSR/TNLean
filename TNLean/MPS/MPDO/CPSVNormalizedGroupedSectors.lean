/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVGroupedGramNormalization
import TNLean.MPS.MPDO.NormalizedGroupedSectorMaps

/-!
# Normalized physical maps from literal CPSV canonical form

The literal grouped Figure 8 identity supplies a positive Gram scalar for each
grouped gauge.  Absorbing the corresponding normalized unitary into the
physical isometry gives orthogonal representative-sector maps and preserves
the exact vertical reconstruction.

## Main result

* `MPSTensor.IsCPSVCanonicalForm.exists_normalized_grouped_sector_maps`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1903--1921.
-/

open scoped Matrix BigOperators ComplexOrder

open MPOTensor

namespace MPSTensor.IsCPSVCanonicalForm

variable {d D : ℕ}

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- The normalized grouped gauges can be absorbed into the physical sector
maps without changing the literal vertical decomposition.

The new map for the copy $(j,q)$ is
$W_{j,q}=V_{j,q}\omega_{j,q}^{-1/2}X_{j,q}$, with its columns transported
from the copy bond space to the representative bond space.  These maps are
isometries with mutually orthogonal ranges and intertwine the vertical tensor
with the undressed representative tensors.

All hypotheses are clauses furnished by
`IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1895--1921. -/
theorem exists_normalized_grouped_sector_maps
    {M : MPOTensor d D} (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
    (mu : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hDimPos : ∀ k, 0 < dim k)
    (hNormal : ∀ k, MPSTensor.IsNormalTensor (blocks k))
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (X : (j : Fin (C).g) → (q : Fin ((C).copies j)) →
      GL (Fin (dim ((C).enum j q))) ℂ)
    (zeta : (j : Fin (C).g) → Fin ((C).copies j) → ℂ)
    (hXDist : ∀ j, X j ⟨0, (C).copies_pos j⟩ = 1)
    (hCoeffPos : ∀ j q, (0 : ℂ) < mu ((C).enum j q) * zeta j q)
    (hIso : ∀ j q, (V ((C).enum j q))ᴴ * V ((C).enum j q) = 1)
    (hOrth : ∀ j q l p, (C).enum j q ≠ (C).enum l p →
      (V ((C).enum j q))ᴴ * V ((C).enum l p) = 0)
    (hInter : ∀ j q v, verticalTensor M v * V ((C).enum j q) =
      V ((C).enum j q) *
        ((mu ((C).enum j q) * zeta j q) •
          ((X j q : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ))))
    (hCorner : ∀ j q v,
      (mu ((C).enum j q) * zeta j q) •
          ((X j q : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (hReconstruct : ∀ v, verticalTensor M v =
      ∑ j : Fin (C).g, ∑ q : Fin ((C).copies j),
        V ((C).enum j q) *
          ((mu ((C).enum j q) * zeta j q) •
            ((X j q : Matrix (Fin (dim ((C).enum j q)))
                (Fin (dim ((C).enum j q))) ℂ) *
              (cast (congrArg (MPSTensor (D * D)) (hdim j q))
                (blocks ((C).repr j))) v *
              (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
                (Fin (dim ((C).enum j q))) ℂ))) *
          (V ((C).enum j q))ᴴ) :
    ∃ (omega : (j : Fin (C).g) → Fin ((C).copies j) → ℝ)
      (W : (p : (j : Fin (C).g) × Fin ((C).copies j)) →
        Matrix (Fin d) (Fin (dim ((C).repr p.1))) ℂ),
      (∀ j q, 0 < omega j q) ∧
      (∀ p, (W p)ᴴ * W p = 1) ∧
      (∀ p q, p ≠ q → (W p)ᴴ * W q = 0) ∧
      (∀ p v, verticalTensor M v * W p =
        W p * ((mu ((C).enum p.1 p.2) * zeta p.1 p.2) •
          blocks ((C).repr p.1) v)) ∧
      ∀ v, verticalTensor M v =
        ∑ j : Fin (C).g, ∑ q : Fin ((C).copies j),
          W ⟨j, q⟩ *
            ((mu ((C).enum j q) * zeta j q) • blocks ((C).repr j) v) *
            (W ⟨j, q⟩)ᴴ := by
  apply MPOTensor.exists_normalized_grouped_sector_maps_of_gram blocks mu V hdim X zeta
  · intro j q
    exact hCanonical.grouped_sector_gram_eq_pos_smul_one blocks hM mu V
      hDimPos hNormal hdim X zeta hXDist hCoeffPos hCorner j q
  · exact hIso
  · exact hOrth
  · exact hInter
  · exact hReconstruct

end GroupedSectors

end MPSTensor.IsCPSVCanonicalForm
