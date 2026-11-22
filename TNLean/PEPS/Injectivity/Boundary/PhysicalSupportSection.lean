/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The right inverse after restriction to the physical support

For a finite-dimensional virtual Hilbert space, the tensor map becomes
surjective when its physical codomain is restricted to its range. It has a
unique section taking values in the orthogonal complement of its kernel.
The reverse composition is the orthogonal projector onto that initial space.
The range embeds isometrically into the original physical Hilbert space.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Observation 2.4,
`Papers/1001.3807/paper_v3.tex`, lines 530–554. The initial virtual space is
stated intrinsically as the orthogonal complement of the tensor-map kernel;
no equality with a row span under a different vectorization is assumed.
-/

namespace TNLean.PEPS

variable {W P : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable [FiniteDimensional ℂ W] [AddCommGroup P] [Module ℂ P]

/-- Restriction to the physical range admits a right inverse whose reverse
composition is the orthogonal projector onto the initial virtual support.
Source: SCP10, Observation 2.4, lines 530–554. -/
theorem exists_physicalSupport_section (T : W →ₗ[ℂ] P) :
    ∃ L : T.range →ₗ[ℂ] W,
      T ∘ₗ L = T.range.subtype ∧
      L ∘ₗ T.rangeRestrict = LinearMap.id - T.ker.starProjection.toLinearMap ∧
      L.range = T.kerᗮ := by
  obtain ⟨L₀, hL₀⟩ := T.rangeRestrict.exists_rightInverse_of_surjective
    T.range_rangeRestrict
  let K := T.ker
  let P₀ := K.starProjection.toLinearMap
  let L := (LinearMap.id - P₀) ∘ₗ L₀
  have hzero (x : W) : T (P₀ x) = 0 :=
    K.starProjection_apply_mem x
  have hright (y : T.range) : T (L₀ y) = y :=
    congrArg Subtype.val (LinearMap.congr_fun hL₀ y)
  have hsection : T ∘ₗ L = T.range.subtype := by
    ext y
    change T (L₀ y - P₀ (L₀ y)) = y
    rw [map_sub, hzero, sub_zero, hright]
  have hreverse : L ∘ₗ T.rangeRestrict = LinearMap.id - P₀ := by
    ext x
    have hmem : x - L₀ (T.rangeRestrict x) ∈ K := by
      change T (x - L₀ (T.rangeRestrict x)) = 0
      rw [map_sub, hright]
      exact sub_self _
    have hproj := K.starProjection_eq_self_iff.mpr hmem
    change P₀ (x - L₀ (T.rangeRestrict x)) = x - L₀ (T.rangeRestrict x) at hproj
    rw [map_sub] at hproj
    change L₀ (T.rangeRestrict x) - P₀ (L₀ (T.rangeRestrict x)) = x - P₀ x
    exact (sub_eq_sub_iff_add_eq_add.mpr
      (by simpa [add_comm] using sub_eq_sub_iff_add_eq_add.mp hproj))
  refine ⟨L, hsection, hreverse, ?_⟩
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, rfl⟩
    exact K.sub_starProjection_mem_orthogonal (L₀ z)
  · intro x hx
    refine ⟨T.rangeRestrict x, ?_⟩
    have hx₀ : P₀ x = 0 := K.starProjection_apply_eq_zero_iff.mpr hx
    have h := LinearMap.congr_fun hreverse x
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      hx₀, sub_zero] using h

omit [FiniteDimensional ℂ W] in
/-- The section into the orthogonal initial support is unique.
Source: the right-inverse construction of SCP10, Observation 2.4, lines 541–554. -/
theorem physicalSupport_section_unique (T : W →ₗ[ℂ] P)
    (L L' : T.range →ₗ[ℂ] W)
    (hL : T ∘ₗ L = T.range.subtype) (hL' : T ∘ₗ L' = T.range.subtype)
    (hrL : L.range ≤ T.kerᗮ) (hrL' : L'.range ≤ T.kerᗮ) : L = L' := by
  ext y
  have hk : L y - L' y ∈ T.ker := by
    change T (L y - L' y) = 0
    have hLy : T (L y) = y := LinearMap.congr_fun hL y
    have hLy' : T (L' y) = y := LinearMap.congr_fun hL' y
    rw [map_sub, hLy, hLy', sub_self]
  have ho : L y - L' y ∈ T.kerᗮ :=
    T.kerᗮ.sub_mem (hrL (LinearMap.mem_range_self L y))
      (hrL' (LinearMap.mem_range_self L' y))
  have hz : L y - L' y ∈ T.ker ⊓ T.kerᗮ := ⟨hk, ho⟩
  rw [T.ker.inf_orthogonal_eq_bot] at hz
  exact sub_eq_zero.mp (by simpa using hz)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A tensor map factors through an isometric inclusion of its physical support;
the reduced tensor is onto and its right inverse recovers the initial orthogonal
support. Source: SCP10, Observation 2.4, lines 530–554. -/
theorem exists_physicalSupport_isometry_section (T : W →ₗ[ℂ] H) :
    ∃ (I : T.range →ₗᵢ[ℂ] H) (L : T.range →ₗ[ℂ] W),
      I.toLinearMap ∘ₗ T.rangeRestrict = T ∧
      T.rangeRestrict ∘ₗ L = LinearMap.id ∧
      L ∘ₗ T.rangeRestrict = LinearMap.id - T.ker.starProjection.toLinearMap ∧
      L.range = T.kerᗮ := by
  obtain ⟨L, hright, hreverse, hrange⟩ := exists_physicalSupport_section T
  refine ⟨T.range.subtypeₗᵢ, L, rfl, ?_, hreverse, hrange⟩
  ext y
  change T (L y) = y
  exact LinearMap.congr_fun hright y

end TNLean.PEPS
