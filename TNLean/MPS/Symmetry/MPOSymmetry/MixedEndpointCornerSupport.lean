/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointEmbedding
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointSectors

/-!
# The first endpoint support as the physical corner of the extended support

Selecting both outer first-sector registers of the actual extended
zero-parameter support gives precisely the canonical two-site support of
the embedded first endpoint. Together with the inner-sector constraints,
this identifies its all-first-sector physical corner.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped Matrix

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- The image of the actual extended endpoint support under both outer
sector projections is exactly the canonical support of the embedded
first endpoint. Source: arXiv:2203.12563, Section 5, lines 1690–1692.
The support identity is derived by compressing the boundary matrix. -/
theorem mixedEndpoint_extendedSupport_outerCorner_eq_groundSpaceES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range.map
      ((mixedEndpointRowSector D₀ D₁ 0).comp (mixedEndpointColumnSector D₀ D₁ 1)) =
      groundSpaceES (mixedEndpointLeftTensor A₀ D₁) 2 := by
  let V := Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁))
  let P := bondInterpolationMatrix D₀ D₁ 0
  have hP : P = V * Vᴴ := coordinateInclusion_first_projection_eq_bondWeight.symm
  have hV : Vᴴ * V = 1 := Matrix.coordinateInclusion_isometry _
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    let X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ := fun a b => v (a, b)
    have hv : WithLp.toLp 2 (fun p : Fin (D₀ + D₁) × Fin (D₀ + D₁) => X p.1 p.2) = v := by
      apply PiLp.ext
      rintro ⟨a, b⟩
      rfl
    change mixedEndpointRowSector D₀ D₁ 0
      (mixedEndpointColumnSector D₀ D₁ 1
        (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) P v)) ∈ _
    rw [← hv, mixedEndpointColumnSector_insertedTwoSiteMap,
      mixedEndpointRowSector_insertedTwoSiteMap]
    have hcorner : P * X * P = V * (Vᴴ * X * V) * Vᴴ := by
      rw [hP]
      simp only [Matrix.mul_assoc]
    change insertedTwoSiteMap (mixedEndpointBase A₀ A₁) P
      (WithLp.toLp 2 (fun p => (P * X * P) p.1 p.2)) ∈ _
    rw [hcorner]
    rw [insertedTwoSiteMap_first_boundary]
    exact ⟨_, ⟨Vᴴ * X * V, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨X, rfl⟩, rfl⟩
    refine ⟨insertedTwoSiteMap (mixedEndpointBase A₀ A₁) P
      (WithLp.toLp 2 (fun p => (V * X * Vᴴ) p.1 p.2)), ⟨_, rfl⟩, ?_⟩
    change mixedEndpointRowSector D₀ D₁ 0
      (mixedEndpointColumnSector D₀ D₁ 1
        (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) P
          (WithLp.toLp 2 (fun p => (V * X * Vᴴ) p.1 p.2)))) = _
    rw [mixedEndpointColumnSector_insertedTwoSiteMap,
      mixedEndpointRowSector_insertedTwoSiteMap]
    have hPV : P * V = V := by rw [hP, Matrix.mul_assoc, hV, Matrix.mul_one]
    have hVP : Vᴴ * P = Vᴴ := by rw [hP, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    have hcorner : P * (V * X * Vᴴ) * P = V * X * Vᴴ := by
      calc
        P * (V * X * Vᴴ) * P = (P * V) * X * (Vᴴ * P) := by
          simp only [Matrix.mul_assoc]
        _ = V * X * Vᴴ := by rw [hPV, hVP]
    change insertedTwoSiteMap (mixedEndpointBase A₀ A₁) P
      (WithLp.toLp 2 (fun p => (P * (V * X * Vᴴ) * P) p.1 p.2)) = _
    rw [hcorner]
    exact insertedTwoSiteMap_first_boundary A₀ A₁ X

end MPOSymmetry
end MPSTensor
