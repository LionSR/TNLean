/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Restricting a gap to a reducing isometric image

If the range projection of a rectangular isometry commutes with an operator,
compression intertwines with that operator in both directions. The adjoint
therefore maps the original kernel into the compressed kernel, and the
isometry maps its orthogonal complement into the original kernel complement.
Every norm-gap bound restricts with exactly the same constant.

This is the boundary-coordinate restriction used in GLM23,
arXiv:2203.12563v3, Section 5, lines 1695–1777. It does not require the
isometry to be surjective onto the full physical alphabet, nor a lower bound
on the dimensions. The physical application must establish the reducing
range projection separately.
-/

open scoped InnerProductSpace

namespace LinearIsometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Compress an operator to the domain of an isometry by its adjoint. -/
noncomputable def compression (U : E →ₗᵢ[ℂ] F) (H : F →ₗ[ℂ] F) : E →ₗ[ℂ] E :=
  U.toLinearMap.adjoint ∘ₗ H ∘ₗ U.toLinearMap

private theorem adjoint_apply_apply (U : E →ₗᵢ[ℂ] F) (v : E) :
    U.toLinearMap.adjoint (U v) = v :=
  LinearMap.congr_fun U.adjoint_comp_self' v

/-- Compression intertwines with the original operator when the isometric
range projection commutes with that operator. -/
theorem apply_compression_of_commute (U : E →ₗᵢ[ℂ] F) (H : F →ₗ[ℂ] F)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint) H) (v : E) :
    U (U.compression H v) = H (U v) := by
  have h := LinearMap.congr_fun hComm.eq (U v)
  change U (U.toLinearMap.adjoint (H (U v))) =
    H (U (U.toLinearMap.adjoint (U v))) at h
  simpa only [compression, LinearMap.comp_apply, coe_toLinearMap, adjoint_apply_apply] using h

/-- The adjoint also intertwines the original operator with compression.
Surjectivity of the rectangular isometry is unnecessary. -/
theorem compression_adjoint_apply_of_commute (U : E →ₗᵢ[ℂ] F) (H : F →ₗ[ℂ] F)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint) H) (w : F) :
    U.compression H (U.toLinearMap.adjoint w) = U.toLinearMap.adjoint (H w) := by
  have h := LinearMap.congr_fun hComm.eq w
  change U (U.toLinearMap.adjoint (H w)) =
    H (U (U.toLinearMap.adjoint w)) at h
  change U.toLinearMap.adjoint (H (U (U.toLinearMap.adjoint w))) = _
  rw [← h, adjoint_apply_apply]

/-- The compressed kernel is the inverse image of the original kernel. -/
theorem ker_compression_of_commute (U : E →ₗᵢ[ℂ] F) (H : F →ₗ[ℂ] F)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint) H) :
    LinearMap.ker (U.compression H) = (LinearMap.ker H).comap U.toLinearMap := by
  ext v
  change U.compression H v = 0 ↔ H (U v) = 0
  rw [← U.apply_compression_of_commute H hComm]
  constructor
  · intro hv
    rw [hv, map_zero]
  · intro hv
    exact U.injective (by simpa only [map_zero] using hv)

/-- The adjoint maps the entire original kernel onto the compressed kernel.
This includes original zero modes outside the isometric image. -/
theorem ker_compression_eq_map_adjoint_of_commute
    (U : E →ₗᵢ[ℂ] F) (H : F →ₗ[ℂ] F)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint) H) :
    LinearMap.ker (U.compression H) = (LinearMap.ker H).map U.toLinearMap.adjoint := by
  apply le_antisymm
  · intro v hv
    refine ⟨U v, ?_, U.adjoint_apply_apply v⟩
    change H (U v) = 0
    rw [← U.apply_compression_of_commute H hComm, LinearMap.mem_ker.mp hv, map_zero]
  · rintro v ⟨w, hw, rfl⟩
    change U.compression H (U.toLinearMap.adjoint w) = 0
    rw [U.compression_adjoint_apply_of_commute H hComm, LinearMap.mem_ker.mp hw, map_zero]

/-- A reducing rectangular isometry maps the compressed kernel complement
into the original kernel complement. -/
theorem map_mem_orthogonal_ker_compression_of_commute
    (U : E →ₗᵢ[ℂ] F) (H : F →ₗ[ℂ] F)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint) H)
    {v : E} (hv : v ∈ (LinearMap.ker (U.compression H))ᗮ) :
    U v ∈ (LinearMap.ker H)ᗮ := by
  apply ((LinearMap.ker H).mem_orthogonal (U v)).mpr
  intro w hw
  have hadj : U.toLinearMap.adjoint w ∈ LinearMap.ker (U.compression H) := by
    rw [U.ker_compression_eq_map_adjoint_of_commute H hComm]
    exact ⟨w, hw, rfl⟩
  change ⟪w, U.toLinearMap v⟫_ℂ = 0
  rw [← LinearMap.adjoint_inner_left U.toLinearMap]
  exact ((LinearMap.ker (U.compression H)).mem_orthogonal v).mp hv _ hadj

/-- Compression to a reducing isometric image preserves every norm-gap
lower bound, with no loss and no ambient-surjectivity assumption.
Source: GLM23, arXiv:2203.12563v3, Section 5, lines 1695–1777. -/
theorem norm_gap_compression_of_commute (U : E →ₗᵢ[ℂ] F) (H : F →ₗ[ℂ] F)
    (hComm : Commute (U.toLinearMap ∘ₗ U.toLinearMap.adjoint) H) {δ : ℝ}
    (hGap : ∀ w ∈ (LinearMap.ker H)ᗮ, δ * ‖w‖ ≤ ‖H w‖) :
    ∀ v ∈ (LinearMap.ker (U.compression H))ᗮ,
      δ * ‖v‖ ≤ ‖U.compression H v‖ := by
  intro v hv
  have h := hGap (U v) (U.map_mem_orthogonal_ker_compression_of_commute H hComm hv)
  simpa only [← U.apply_compression_of_commute H hComm, U.norm_map] using h

end LinearIsometry
