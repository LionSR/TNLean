/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointActiveConfigEquiv
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointEdgeBoundaryTransport

/-!
# The actual mixed endpoint Hamiltonian in active coordinates

The explicit active-coordinate isometry is used to compress every actual
nonwrapping extended interaction. Each interaction commutes with the active
projection: this follows from its individual physical-register symmetries,
then commutation with the inner-sector penalty and invariance of its kernel.
Consequently every compressed interaction is an orthogonal projection. Its
kernel is the inverse image of the actual local kernel, and the sum of these
projections is exactly the compression of the actual open Hamiltonian.

The local kernel is also described by the actual two-site boundary ranges on
every spectator fiber. These statements allow arbitrary endpoint tensors,
including zero-dimensional sectors. They do not assert a strict-window gap or
identify a normalized edge Hamiltonian with a canonical parent Hamiltonian.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.

## Passing from the active endpoint block to the actual open chain

The actual endpoint Hamiltonian reduces the explicitly constructed active
subspace. On its orthogonal complement the derived inner-sector penalty
gives energy at least one half. A gap of the actual compressed block
therefore gives the minimum of that gap and one half for the full open
Hamiltonian. This is the final sector-gluing step; its active-block input
still has to be supplied by the boundary-normalization comparison.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

section

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

open ManyBody.Interaction (translationInvariant chainTranslates)

variable {D₀ D₁ N : ℕ}

/-- Every chain row selector commutes with each actual translated local
interaction, before summing the open Hamiltonian. -/
theorem mixedEndpointChainRowSector_commute_localInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i k : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (mixedEndpointChainRowSector D₀ D₁ k)
      (Matrix.toEuclideanLin ((translationInvariant N
          (mixedEndpointParentInteraction A₀ A₁ 0)).term i)) :=
  have : NeZero N := ⟨by omega⟩
  ManyBody.Interaction.toEuclideanLin_translationInvariant_term_commute_siteDiagonal _ hN
    (fun p => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).1)
    (mixedEndpointRowSector_commute_parentInteraction_zero A₀ A₁) i k

/-- Every chain column selector commutes with each actual translated local
interaction, including when the selected site is outside its window. -/
theorem mixedEndpointChainColumnSector_commute_localInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i k : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (mixedEndpointChainColumnSector D₀ D₁ k)
      (Matrix.toEuclideanLin ((translationInvariant N
          (mixedEndpointParentInteraction A₀ A₁ 0)).term i)) :=
  have : NeZero N := ⟨by omega⟩
  ManyBody.Interaction.toEuclideanLin_translationInvariant_term_commute_siteDiagonal _ hN
    (fun p => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).2)
    (mixedEndpointColumnSector_commute_parentInteraction_zero A₀ A₁) i k

/-- The entire inner-sector penalty commutes with each actual translated
local interaction. This is a termwise reduction statement. -/
theorem mixedEndpointOpenInnerPenalty_commute_localInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (mixedEndpointOpenInnerPenalty D₀ D₁ N)
      (Matrix.toEuclideanLin ((translationInvariant N
          (mixedEndpointParentInteraction A₀ A₁ 0)).term i)) := by
  apply Commute.sum_left
  intro j _
  exact ((Commute.one_left _).sub_left
    (mixedEndpointChainColumnSector_commute_localInteraction A₀ A₁ hN i j.1)).add_left
      ((Commute.one_left _).sub_left
        (mixedEndpointChainRowSector_commute_localInteraction A₀ A₁ hN i _))

/-- The active projection commutes with each actual translated extended
interaction. Neither a reducing-subspace assumption nor injectivity is used. -/
theorem mixedEndpointOpenActiveProjection_commute_localInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (mixedEndpointOpenActiveProjection D₀ D₁ N)
      (Matrix.toEuclideanLin ((translationInvariant N
          (mixedEndpointParentInteraction A₀ A₁ 0)).term i)) := by
  have : NeZero N := ⟨by omega⟩
  let T := Matrix.toEuclideanLin ((translationInvariant N
      (mixedEndpointParentInteraction A₀ A₁ 0)).term i)
  let S := LinearMap.ker (mixedEndpointOpenInnerPenalty D₀ D₁ N)
  have hT : T.IsSymmetric := (Matrix.isPositive_toEuclideanLin_iff.mpr
    (Matrix.nonneg_iff_posSemidef.mp (ManyBody.Interaction.translationInvariant_term_nonneg
      (Matrix.nonneg_iff_posSemidef.mpr
        (posSemidef_mixedEndpointParentInteraction A₀ A₁ 0)) i))).isSymmetric
  have hS (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N))
      (hv : v ∈ S) : T v ∈ S := by
    have hc := congrArg (fun L => L v)
      (mixedEndpointOpenInnerPenalty_commute_localInteraction A₀ A₁ hN i).eq
    change mixedEndpointOpenInnerPenalty D₀ D₁ N (T v) =
      T (mixedEndpointOpenInnerPenalty D₀ D₁ N v) at hc
    rw [LinearMap.mem_ker.mp hv, map_zero] at hc
    exact hc
  rw [mixedEndpointOpenActiveProjection_eq_starProjection]
  apply (commute_iff_eq _ _).mpr
  apply LinearMap.ext
  intro v
  change S.starProjection (T v) = T (S.starProjection v)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := S)
  · exact hS _ (S.starProjection_apply_mem v)
  · intro w hw
    rw [← map_sub, hT]
    exact S.starProjection_inner_eq_zero v (T w) (hS w hw)

private theorem localExtension_isSymmetricProjection {d R L : ℕ}
    {h : Matrix (Cfg d R) (Cfg d R) ℂ}
    (hh : (Matrix.toEuclideanLin h).IsSymmetricProjection) (hRL : R ≤ L) (i : Fin L) :
    haveI : NeZero L := NeZero.of_pos i.pos;
    (Matrix.toEuclideanLin
      ((translationInvariant L h).term i)).IsSymmetricProjection := by
  have : NeZero L := NeZero.of_pos i.pos
  refine ⟨?_, (Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.nonneg_iff_posSemidef.mp
    (ManyBody.Interaction.translationInvariant_term_nonneg (Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.isPositive_toEuclideanLin_iff.mp hh.isPositive)) i))).isSymmetric⟩
  let T := Matrix.toEuclideanLin ((translationInvariant L h).term i)
  ext v σ
  let e := cyclicActiveBlockConfigEquiv d R hRL i
  let w : EuclideanSpace ℂ (Cfg d R) :=
    WithLp.toLp 2 fun ω => v (e.symm (ω, (e σ).2))
  have hfiber : (WithLp.toLp 2 fun ω =>
      T v (e.symm (ω, (e σ).2))) = Matrix.toEuclideanLin h w := by
    ext ω
    change T v (e.symm (ω, (e σ).2)) = Matrix.toEuclideanLin h w ω
    simpa only [e, w, Equiv.apply_symm_apply] using
      (toEuclideanLin_translationInvariant_term_apply_fiber h hRL i v (e.symm (ω, (e σ).2)))
  change T (T v) σ = T v σ
  rw [toEuclideanLin_translationInvariant_term_apply_fiber h hRL]
  change Matrix.toEuclideanLin h (WithLp.toLp 2 fun ω =>
      T v (e.symm (ω, (e σ).2))) (e σ).1 = _
  rw [hfiber, toEuclideanLin_translationInvariant_term_apply_fiber h hRL]
  exact congrArg (fun L => L w (e σ).1) hh.isIdempotentElem.eq

/-- Every actual extended local term on the full chain is an orthogonal
projection. Its local support projection and its fiberwise extension are
both derived from the actual interaction. -/
theorem mixedEndpointLocalInteraction_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    (Matrix.toEuclideanLin ((translationInvariant N
        (mixedEndpointParentInteraction A₀ A₁ 0)).term i)).IsSymmetricProjection := by
  have : NeZero N := ⟨by omega⟩
  apply localExtension_isSymmetricProjection (hRL := hN)
  exact isSymmetricProjection_toEuclideanLin_mixedEndpointParentInteraction A₀ A₁ 0

/-- The Hilbert space of the explicit active coordinates: two unrestricted
exterior registers and the first-sector interior chain. -/
abbrev mixedEndpointActiveSpace (D₀ D₁ N : ℕ) :=
  EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N)

/-- The adjoint of the concrete active inclusion reads the coefficient at
its encoded physical configuration. -/
theorem mixedEndpointActiveLinearIsometry_adjoint_apply
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1)))
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :
    (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint v ξ =
      v (mixedEndpointActivePhysicalCfg ξ) := by
  classical
  rw [mixedEndpointActiveLinearIsometry_toLinearMap, mixedEndpointActiveInclusion,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Matrix.coordinateInclusion,
    mixedEndpointActiveConfigEmbedding]

/-- The adjoint is a left inverse to the genuine active-coordinate isometry. -/
theorem mixedEndpointActiveLinearIsometry_adjoint_comp :
    (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint ∘ₗ
        (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap = LinearMap.id := by
  ext v ξ
  rw [LinearMap.comp_apply, mixedEndpointActiveLinearIsometry_adjoint_apply]
  exact mixedEndpointActiveInclusion_apply_active v ξ

/-- The isometry followed by its adjoint is precisely the actual active
projection, not an unspecified projection with the same intended range. -/
theorem mixedEndpointActiveLinearIsometry_comp_adjoint :
    (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap ∘ₗ
        (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint =
      mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1) := by
  classical
  ext v σ
  change mixedEndpointActiveInclusion D₀ D₁ N
      ((mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint v) σ =
    mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1) v σ
  by_cases hσ : MixedEndpointOpenInnerActive σ
  · obtain ⟨ξ, rfl⟩ := (mem_range_mixedEndpointActivePhysicalCfg_iff σ).mpr hσ
    rw [mixedEndpointActiveInclusion_apply_active,
      mixedEndpointActiveLinearIsometry_adjoint_apply,
      mixedEndpointOpenActiveProjection_apply, ite_eq_left hσ]
  · rw [mixedEndpointActiveInclusion_apply_inactive _ _ hσ,
      mixedEndpointOpenActiveProjection_apply, ite_eq_right hσ]

/-- The actual active projection fixes the concrete inclusion pointwise. -/
theorem mixedEndpointOpenActiveProjection_activeLinearIsometry
    (v : mixedEndpointActiveSpace D₀ D₁ N) :
    mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1)
        (mixedEndpointActiveLinearIsometry D₀ D₁ N v) =
      mixedEndpointActiveLinearIsometry D₀ D₁ N v := by
  rw [← mixedEndpointActiveLinearIsometry_comp_adjoint]
  change mixedEndpointActiveLinearIsometry D₀ D₁ N
    (((mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint ∘ₗ
      (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap) v) = _
  rw [mixedEndpointActiveLinearIsometry_adjoint_comp, LinearMap.id_apply]

/-- Compression into the explicit active Hilbert space, using the genuine
configuration isometry and its Hilbert adjoint. -/
def mixedEndpointActiveCompression
    (T : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1)) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1))) :
    mixedEndpointActiveSpace D₀ D₁ N →ₗ[ℂ] mixedEndpointActiveSpace D₀ D₁ N :=
  (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint ∘ₗ T ∘ₗ
    (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap

private theorem activeCompression_intertwines
    (T : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1)) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1)))
    (hT : Commute (mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1)) T)
    (v : mixedEndpointActiveSpace D₀ D₁ N) :
    mixedEndpointActiveLinearIsometry D₀ D₁ N (mixedEndpointActiveCompression T v) =
      T (mixedEndpointActiveLinearIsometry D₀ D₁ N v) := by
  change ((mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap ∘ₗ
    (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint)
      (T (mixedEndpointActiveLinearIsometry D₀ D₁ N v)) = _
  rw [mixedEndpointActiveLinearIsometry_comp_adjoint]
  have hc := congrArg (fun L => L (mixedEndpointActiveLinearIsometry D₀ D₁ N v)) hT.eq
  change mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1)
      (T (mixedEndpointActiveLinearIsometry D₀ D₁ N v)) =
    T (mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1)
      (mixedEndpointActiveLinearIsometry D₀ D₁ N v)) at hc
  simpa only [mixedEndpointOpenActiveProjection_activeLinearIsometry] using hc

/-- The actual nonwrapping local interaction compressed to active
coordinates. No replacement interaction or kernel is postulated. -/
def mixedEndpointActiveLocalInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) :
    mixedEndpointActiveSpace D₀ D₁ N →ₗ[ℂ] mixedEndpointActiveSpace D₀ D₁ N :=
  mixedEndpointActiveCompression
    (Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
        (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1))

/-- In the explicit active coordinates, a compressed term is the original
physical term evaluated on the encoded configuration after zero extension. -/
theorem mixedEndpointActiveLocalInteraction_apply
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) (v : mixedEndpointActiveSpace D₀ D₁ N)
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :
    mixedEndpointActiveLocalInteraction A₀ A₁ i v ξ =
      Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
          (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1)
        (mixedEndpointActiveLinearIsometry D₀ D₁ N v) (mixedEndpointActivePhysicalCfg ξ) :=
  mixedEndpointActiveLinearIsometry_adjoint_apply _ ξ

/-- The actual compressed term intertwines with the original physical term. -/
theorem mixedEndpointActiveLocalInteraction_intertwines
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) (v : mixedEndpointActiveSpace D₀ D₁ N) :
    mixedEndpointActiveLinearIsometry D₀ D₁ N
        (mixedEndpointActiveLocalInteraction A₀ A₁ i v) =
      Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
          (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1)
        (mixedEndpointActiveLinearIsometry D₀ D₁ N v) :=
  activeCompression_intertwines _
    (mixedEndpointOpenActiveProjection_commute_localInteraction A₀ A₁ (by omega) i.1) v

/-- Each actual compressed local term is an orthogonal projection. -/
theorem mixedEndpointActiveLocalInteraction_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) :
    (mixedEndpointActiveLocalInteraction A₀ A₁ i).IsSymmetricProjection := by
  have hlocal := mixedEndpointLocalInteraction_isSymmetricProjection A₀ A₁ (by omega) i.1
  constructor
  · apply LinearMap.ext
    intro v
    apply (mixedEndpointActiveLinearIsometry D₀ D₁ N).injective
    simp only [Module.End.mul_apply, mixedEndpointActiveLocalInteraction_intertwines]
    exact LinearMap.congr_fun hlocal.isIdempotentElem.eq
      (mixedEndpointActiveLinearIsometry D₀ D₁ N v)
  · exact (hlocal.isPositive.adjoint_conj
      (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap).isSymmetric

/-- The compressed local kernel is exactly the inverse image of the actual
physical local kernel under the explicitly constructed isometry. -/
theorem ker_mixedEndpointActiveLocalInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) :
    LinearMap.ker (mixedEndpointActiveLocalInteraction A₀ A₁ i) =
      (LinearMap.ker (Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
          (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1))).comap
          (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap := by
  ext v
  change mixedEndpointActiveLocalInteraction A₀ A₁ i v = 0 ↔
    Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
        (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1)
      (mixedEndpointActiveLinearIsometry D₀ D₁ N v) = 0
  rw [← mixedEndpointActiveLocalInteraction_intertwines]
  constructor
  · intro hv
    rw [hv, map_zero]
  · intro hv
    apply (mixedEndpointActiveLinearIsometry D₀ D₁ N).injective
    simpa only [map_zero] using hv

/-- Restricting the actual physical local kernel gives exactly the
compressed kernel. The reverse inclusion uses the derived local reduction;
it would fail for an arbitrary nonreducing coordinate restriction. -/
theorem ker_mixedEndpointActiveLocalInteraction_eq_map_adjoint
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) :
    LinearMap.ker (mixedEndpointActiveLocalInteraction A₀ A₁ i) =
      (LinearMap.ker (Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
          (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1))).map
          (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint := by
  rw [ker_mixedEndpointActiveLocalInteraction]
  ext v
  constructor
  · intro hv
    refine ⟨mixedEndpointActiveLinearIsometry D₀ D₁ N v, hv, ?_⟩
    exact LinearMap.congr_fun mixedEndpointActiveLinearIsometry_adjoint_comp v
  · rintro ⟨w, hw, rfl⟩
    let T := Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
        (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1)
    change T (((mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap ∘ₗ
      (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint) w) = 0
    rw [mixedEndpointActiveLinearIsometry_comp_adjoint]
    have hc := congrArg (fun L => L w)
      (mixedEndpointOpenActiveProjection_commute_localInteraction
        A₀ A₁ (by omega) i.1).eq.symm
    change T (mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1) w) =
      mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1) (T w) at hc
    rw [hc, LinearMap.mem_ker.mp hw, map_zero]

/-- The compressed actual interaction is the canonical orthogonal
constraint projection for the actual restricted local kernel. -/
theorem mixedEndpointActiveLocalInteraction_eq_restrictedKernel_projection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) :
    mixedEndpointActiveLocalInteraction A₀ A₁ i =
      (Submodule.starProjection
        (((LinearMap.ker (Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
            (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1))).map
            (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint)ᗮ)).toLinearMap := by
  let P := mixedEndpointActiveLocalInteraction A₀ A₁ i
  have hP := mixedEndpointActiveLocalInteraction_isSymmetricProjection A₀ A₁ i
  have hrange : LinearMap.range P = (LinearMap.ker P)ᗮ := by
    rw [← hP.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  obtain ⟨_, h⟩ := P.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hP
  simpa only [hrange, P, ker_mixedEndpointActiveLocalInteraction_eq_map_adjoint] using h

/-- Sum the actual compressed nonwrapping terms over the active chain. -/
def mixedEndpointActiveHamiltonian
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    mixedEndpointActiveSpace D₀ D₁ N →ₗ[ℂ] mixedEndpointActiveSpace D₀ D₁ N :=
  ∑ i : NonwrappingStart 2 (N + 1 + 1), mixedEndpointActiveLocalInteraction A₀ A₁ i

/-- The sum of the compressed actual terms is the compression of the actual
open Hamiltonian. The identity includes every nonwrapping bond once. -/
theorem mixedEndpointActiveHamiltonian_eq_compression
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    mixedEndpointActiveHamiltonian A₀ A₁ N =
      mixedEndpointActiveCompression (Matrix.toEuclideanLin (chainTranslates 2 (N + 1 + 1)
          (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) := by
  apply LinearMap.ext
  intro v
  simp [mixedEndpointActiveHamiltonian, mixedEndpointActiveLocalInteraction,
    mixedEndpointActiveCompression,
    ManyBody.Interaction.hamiltonian_chainTranslates_eq_sum_nonwrappingStart,
    LinearMap.sum_apply, map_sum]

/-- The active Hamiltonian is positive as a sum of the actual compressed
orthogonal projections. -/
theorem mixedEndpointActiveHamiltonian_isPositive
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    (mixedEndpointActiveHamiltonian A₀ A₁ N).IsPositive := by
  apply LinearMap.nonneg_iff_isPositive.mp
  exact Finset.sum_nonneg fun i _ => LinearMap.nonneg_iff_isPositive.mpr
    (mixedEndpointActiveLocalInteraction_isSymmetricProjection A₀ A₁ i).isPositive

/-- The compressed sum intertwines with the actual full-space open sum. -/
theorem mixedEndpointActiveHamiltonian_intertwines
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ)
    (v : mixedEndpointActiveSpace D₀ D₁ N) :
    mixedEndpointActiveLinearIsometry D₀ D₁ N (mixedEndpointActiveHamiltonian A₀ A₁ N v) =
      Matrix.toEuclideanLin (chainTranslates 2 (N + 1 + 1)
          (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian
          (mixedEndpointActiveLinearIsometry D₀ D₁ N v) := by
  rw [mixedEndpointActiveHamiltonian_eq_compression]
  exact activeCompression_intertwines _
    (mixedEndpointOpenActiveProjection_commute_hamiltonian_chainTranslates
      A₀ A₁ (by omega)) v

/-- The exact kernel of the actual compressed sum, with no assumed global
kernel identification or spectral estimate. -/
theorem ker_mixedEndpointActiveHamiltonian
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N) =
      (LinearMap.ker (Matrix.toEuclideanLin (chainTranslates 2 (N + 1 + 1)
          (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian)).comap
          (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap := by
  ext v
  change mixedEndpointActiveHamiltonian A₀ A₁ N v = 0 ↔
    Matrix.toEuclideanLin (chainTranslates 2 (N + 1 + 1)
        (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian
        (mixedEndpointActiveLinearIsometry D₀ D₁ N v) = 0
  rw [← mixedEndpointActiveHamiltonian_intertwines]
  constructor
  · intro hv
    rw [hv, map_zero]
  · intro hv
    apply (mixedEndpointActiveLinearIsometry D₀ D₁ N).injective
    simpa only [map_zero] using hv

/-- Every ground vector of the actual open Hamiltonian is active. The
inactive energy bound and the already derived commutation exclude an
inactive component, without any injectivity hypothesis. -/
theorem mixedEndpointOpenActiveProjection_eq_self_of_mem_kernel
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N))
    (hv : v ∈ LinearMap.ker (Matrix.toEuclideanLin (chainTranslates 2 N
        (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian)) :
    mixedEndpointOpenActiveProjection D₀ D₁ N v = v := by
  let Q := mixedEndpointOpenActiveProjection D₀ D₁ N
  let H := Matrix.toEuclideanLin (chainTranslates 2 N
      (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian
  have hQ : Q (Q v) = Q v := LinearMap.congr_fun
    mixedEndpointOpenActiveProjection_isSymmetricProjection.isIdempotentElem.eq v
  have hcomm : H (Q v) = Q (H v) := congrArg (fun T => T v)
    (mixedEndpointOpenActiveProjection_commute_hamiltonian_chainTranslates
      A₀ A₁ hN).eq.symm
  have hQz : Q (v - Q v) = 0 := by rw [map_sub, hQ, sub_self]
  have hHz : H (v - Q v) = 0 := by
    rw [map_sub, hcomm, LinearMap.mem_ker.mp hv, map_zero, sub_self]
  have henergy := mixedEndpointOpen_inactive_energy_lower_bound A₀ A₁ hN
    (v - Q v) hQz
  change (1 / 2 : ℝ) * ‖v - Q v‖ ^ 2 ≤ (inner ℂ (v - Q v) (H (v - Q v))).re
    at henergy
  rw [hHz, inner_zero_right, Complex.zero_re] at henergy
  have hz : v - Q v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v - Q v)])
  exact (sub_eq_zero.mp hz).symm

/-- The genuine isometry maps the compressed ground space onto the entire
actual open-chain ground space. No inactive ground vectors are discarded. -/
theorem map_ker_mixedEndpointActiveHamiltonian
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    (LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N)).map
        (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap =
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates 2 (N + 1 + 1)
          (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change Matrix.toEuclideanLin (chainTranslates 2 (N + 1 + 1)
        (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian
        (mixedEndpointActiveLinearIsometry D₀ D₁ N v) = 0
    rw [← mixedEndpointActiveHamiltonian_intertwines, LinearMap.mem_ker.mp hv, map_zero]
  · intro hw
    have hactive : w ∈ LinearMap.range
        (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap := by
      rw [range_mixedEndpointActiveLinearIsometry]
      exact ⟨w, mixedEndpointOpenActiveProjection_eq_self_of_mem_kernel
        A₀ A₁ (by omega) w hw⟩
    obtain ⟨v, rfl⟩ := hactive
    refine ⟨v, ?_, rfl⟩
    rw [ker_mixedEndpointActiveHamiltonian]
    exact hw

/-- Positivity identifies the active Hamiltonian kernel with all of its
actual local kernels. -/
theorem ker_mixedEndpointActiveHamiltonian_eq_iInf
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N) =
      ⨅ i : NonwrappingStart 2 (N + 1 + 1),
        LinearMap.ker (mixedEndpointActiveLocalInteraction A₀ A₁ i) :=
  WeightedPositiveKernel.ker_sum_eq_iInf fun i =>
    (mixedEndpointActiveLocalInteraction_isSymmetricProjection A₀ A₁ i).isPositive

/-- A two-site spectator fiber of an active-coordinate vector, evaluated
in the original physical coordinates and extended by zero outside the
actual active sector. -/
def mixedEndpointActiveWindowFiber
    (i : NonwrappingStart 2 (N + 1 + 1))
    (s : Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1 - 2))
    (v : mixedEndpointActiveSpace D₀ D₁ N) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) :=
  WithLp.toLp 2 fun ω => mixedEndpointActiveLinearIsometry D₀ D₁ N v
    ((cyclicActiveBlockConfigEquiv _ 2 (by omega) i.1).symm (ω, s))

/-- The compressed local kernel consists precisely of vectors whose
original physical two-site spectator fibers lie in the actual extended
boundary range. This formulation also covers empty physical alphabets. -/
theorem mem_ker_mixedEndpointActiveLocalInteraction_iff_fibers
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) (v : mixedEndpointActiveSpace D₀ D₁ N) :
    v ∈ LinearMap.ker (mixedEndpointActiveLocalInteraction A₀ A₁ i) ↔
      ∀ s, mixedEndpointActiveWindowFiber i s v ∈
        (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
          (bondInterpolationMatrix D₀ D₁ 0)).range := by
  rw [ker_mixedEndpointActiveLocalInteraction]
  change Matrix.toEuclideanLin ((translationInvariant (N + 1 + 1)
      (mixedEndpointParentInteraction A₀ A₁ 0)).term i.1)
      (mixedEndpointActiveLinearIsometry D₀ D₁ N v) = 0 ↔ _
  simp_rw [← mem_ker_insertedParentInteraction_iff,
    ← toEuclideanLin_mixedEndpointParentInteraction A₀ A₁ 0]
  let e := cyclicActiveBlockConfigEquiv ((D₀ + D₁) * (D₀ + D₁)) 2 (by omega) i.1
  constructor
  · intro hv s
    apply PiLp.ext
    intro ω
    have h := congrArg (fun w => w (e.symm (ω, s))) hv
    rw [toEuclideanLin_translationInvariant_term_apply_fiber _ (by omega)] at h
    simpa only [e, Equiv.apply_symm_apply, PiLp.zero_apply,
      mixedEndpointActiveWindowFiber] using h
  · intro hv
    apply PiLp.ext
    intro σ
    have h := congrArg (fun w => w (e σ).1) (hv (e σ).2)
    rw [toEuclideanLin_translationInvariant_term_apply_fiber _ (by omega)]
    exact h

/-- All coordinate constraints for the actual active Hamiltonian, expressed
using the actual extended two-site support on each physical spectator fiber. -/
theorem mem_ker_mixedEndpointActiveHamiltonian_iff_fibers
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ)
    (v : mixedEndpointActiveSpace D₀ D₁ N) :
    v ∈ LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N) ↔
      ∀ i : NonwrappingStart 2 (N + 1 + 1), ∀ s,
        mixedEndpointActiveWindowFiber i s v ∈
          (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
            (bondInterpolationMatrix D₀ D₁ 0)).range := by
  rw [ker_mixedEndpointActiveHamiltonian_eq_iInf]
  simp only [Submodule.mem_iInf,
    mem_ker_mixedEndpointActiveLocalInteraction_iff_fibers]

end

end MPOSymmetry
end MPSTensor

end

section

open scoped InnerProductSpace ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

open ManyBody.Interaction (chainTranslates)

variable {D₀ D₁ N : ℕ}

/-- A gap of the actual compressed endpoint block transfers to the full
actual open-chain Hamiltonian, as a lower bound on its nonzero eigenvalues.
The inactive energy bound and exact kernel
transport are derived, rather than supplied as hypotheses. -/
theorem mixedEndpoint_open_gap_of_active_norm_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ x ∈ (LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N))ᗮ,
      δ * ‖x‖ ≤ ‖mixedEndpointActiveHamiltonian A₀ A₁ N x‖) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin (chainTranslates 2 (N + 1 + 1)
        (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) μ →
      μ = 0 ∨ ((min δ (1 / 2) : ℝ) : ℂ) ≤ μ := by
  refine (ManyBody.forall_hasEigenvalue_iff_norm
    (ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 0) (N + 1 + 1))).mpr ?_
  let H := Matrix.toEuclideanLin (chainTranslates 2 (N + 1 + 1)
      (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian
  let K := mixedEndpointActiveHamiltonian A₀ A₁ N
  let U := mixedEndpointActiveLinearIsometry D₀ D₁ N
  let Q := mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1)
  have hH : H.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr
    (ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 0) (N + 1 + 1))
  have hK : K.IsPositive := mixedEndpointActiveHamiltonian_isPositive A₀ A₁ N
  have hleft (x : mixedEndpointActiveSpace D₀ D₁ N) : U.toLinearMap.adjoint (U x) = x :=
    LinearMap.congr_fun mixedEndpointActiveLinearIsometry_adjoint_comp x
  have hright (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1))) :
      U (U.toLinearMap.adjoint v) = Q v :=
    LinearMap.congr_fun mixedEndpointActiveLinearIsometry_comp_adjoint v
  have hintertwine (x : mixedEndpointActiveSpace D₀ D₁ N) : U (K x) = H (U x) :=
    mixedEndpointActiveHamiltonian_intertwines A₀ A₁ N x
  intro v hv
  let x := U.toLinearMap.adjoint v
  let y := v - U x
  have hsum : U x + y = v := by dsimp [y]; abel
  have hadj : U.toLinearMap.adjoint y = 0 := by
    change U.toLinearMap.adjoint (v - U x) = 0
    rw [map_sub, hleft]
    exact sub_self x
  have horth (z : mixedEndpointActiveSpace D₀ D₁ N) : ⟪U z, y⟫_ℂ = 0 := by
    calc
      ⟪U z, y⟫_ℂ = ⟪z, U.toLinearMap.adjoint y⟫_ℂ :=
        (LinearMap.adjoint_inner_right U.toLinearMap z y).symm
      _ = 0 := by rw [hadj, inner_zero_right]
  have hx : x ∈ (LinearMap.ker K)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    change ⟪z, U.toLinearMap.adjoint v⟫_ℂ = 0
    rw [LinearMap.adjoint_inner_right]
    apply Submodule.inner_right_of_mem_orthogonal _ hv
    change H (U z) = 0
    rw [← hintertwine, LinearMap.mem_ker.mp hz, map_zero]
  have hactive := hK.re_inner_ge_of_norm_gap hδ hGap x hx
  have hQy : Q y = 0 := by rw [← hright, hadj, map_zero]
  have hinactive := mixedEndpointOpen_inactive_energy_lower_bound A₀ A₁ (by omega) y hQy
  have hcross : ⟪H y, U x⟫_ℂ = 0 := by
    rw [hH.isSymmetric, ← hintertwine]
    exact inner_eq_zero_symm.mpr (horth (K x))
  have henergy : (⟪H v, v⟫_ℂ).re =
      (⟪K x, x⟫_ℂ).re + (⟪H y, y⟫_ℂ).re := by
    calc
      _ = (⟪H (U x + y), U x + y⟫_ℂ).re := by rw [hsum]
      _ = (⟪K x, x⟫_ℂ).re + (⟪H y, y⟫_ℂ).re := by
        rw [map_add, inner_add_left, inner_add_right, inner_add_right,
          ← hintertwine, U.inner_map_map, horth, hcross]
        simp
  have hnorm : ‖v‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    calc
      _ = ‖U x + y‖ ^ 2 := by rw [hsum]
      _ = ‖U x‖ ^ 2 + ‖y‖ ^ 2 := by
        simpa only [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (horth x)
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by rw [U.norm_map]
  have hquadratic : min δ (1 / 2) * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re := by
    rw [hnorm, henergy, mul_add]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans hactive
    · have hi : (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤ (⟪H y, y⟫_ℂ).re := by
        calc
          _ ≤ (⟪y, H y⟫_ℂ).re := hinactive
          _ = _ := inner_re_symm (𝕜 := ℂ) y (H y)
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans hi
  have hbound := hquadratic.trans (re_inner_le_norm (𝕜 := ℂ) (H v) v)
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact le_of_mul_le_mul_right
      (by simpa only [pow_two, mul_assoc] using hbound) (norm_pos_iff.mpr hv0)

end
end MPOSymmetry
end MPSTensor

end
