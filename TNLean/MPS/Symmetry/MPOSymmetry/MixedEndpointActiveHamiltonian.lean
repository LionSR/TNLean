/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveConfigEquiv
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointEdgeBoundaryTransport

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
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ N : ℕ}

private theorem diagonal_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    Matrix.toEuclideanLin (Matrix.diagonal f) v i = f i * v i := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

/-- Every chain row selector commutes with each actual translated local
interaction, before summing the open Hamiltonian. -/
theorem mixedEndpointChainRowSector_commute_localInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i k : Fin N) :
    Commute (mixedEndpointChainRowSector D₀ D₁ k)
      (periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i) :=
  periodicLocalInteractionES_commute_siteDiagonal _ hN
    (fun p => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).1)
    (mixedEndpointRowSector_commute_parentInteraction_zero A₀ A₁) i k

/-- Every chain column selector commutes with each actual translated local
interaction, including when the selected site is outside its window. -/
theorem mixedEndpointChainColumnSector_commute_localInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i k : Fin N) :
    Commute (mixedEndpointChainColumnSector D₀ D₁ k)
      (periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i) :=
  periodicLocalInteractionES_commute_siteDiagonal _ hN
    (fun p => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).2)
    (mixedEndpointColumnSector_commute_parentInteraction_zero A₀ A₁) i k

/-- The entire inner-sector penalty commutes with each actual translated
local interaction. This is a termwise reduction statement. -/
theorem mixedEndpointOpenInnerPenalty_commute_localInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    Commute (mixedEndpointOpenInnerPenalty D₀ D₁ N)
      (periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i) := by
  apply Commute.sum_left
  intro j _
  have hcol : periodicLocalInteractionES (mixedEndpointColumnSector D₀ D₁ 0) j.1 =
      mixedEndpointChainColumnSector D₀ D₁ j.1 := by
    apply LinearMap.ext
    intro v
    apply PiLp.ext
    intro σ
    simp [mixedEndpointColumnSector, mixedEndpointChainColumnSector,
      periodicLocalInteractionES_diagonal_apply hN, diagonal_apply,
      extractWindow, Nat.mod_eq_of_lt j.1.isLt]
  have hrow : periodicLocalInteractionES (mixedEndpointRowSector D₀ D₁ 1) j.1 =
      mixedEndpointChainRowSector D₀ D₁ (cyclicForwardSite j.1 1) := by
    apply LinearMap.ext
    intro v
    apply PiLp.ext
    intro σ
    simp [mixedEndpointRowSector, mixedEndpointChainRowSector,
      periodicLocalInteractionES_diagonal_apply hN, diagonal_apply,
      extractWindow, cyclicForwardSite]
  rw [hcol, hrow]
  exact ((Commute.one_left _).sub_left
    (mixedEndpointChainColumnSector_commute_localInteraction A₀ A₁ hN i j.1)).add_left
      ((Commute.one_left _).sub_left
        (mixedEndpointChainRowSector_commute_localInteraction A₀ A₁ hN i _))

/-- The active projection commutes with each actual translated extended
interaction. Neither a reducing-subspace assumption nor injectivity is used. -/
theorem mixedEndpointOpenActiveProjection_commute_localInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    Commute (mixedEndpointOpenActiveProjection D₀ D₁ N)
      (periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i) := by
  let T := periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i
  let S := LinearMap.ker (mixedEndpointOpenInnerPenalty D₀ D₁ N)
  have hT : T.IsSymmetric :=
    (periodicLocalInteractionES_isPositive
      (mixedEndpointParentInteraction_isPositive A₀ A₁ 0) i).isSymmetric
  have hS (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N))
      (hv : v ∈ S) : T v ∈ S := by
    have hc := congrArg (fun L => L v)
      (mixedEndpointOpenInnerPenalty_commute_localInteraction A₀ A₁ hN i).eq
    change mixedEndpointOpenInnerPenalty D₀ D₁ N (T v) =
      T (mixedEndpointOpenInnerPenalty D₀ D₁ N v) at hc
    rw [LinearMap.mem_ker.mp hv, map_zero] at hc
    exact hc
  rw [mixedEndpointOpenActiveProjection_eq_starProjection hN]
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
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : h.IsSymmetricProjection) (hRL : R ≤ L) (i : Fin L) :
    (periodicLocalInteractionES h i).IsSymmetricProjection := by
  refine ⟨?_, (periodicLocalInteractionES_isPositive hh.isPositive i).isSymmetric⟩
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  let e := cyclicActiveBlockConfigEquiv d R hRL i
  let w : EuclideanSpace ℂ (Cfg d R) :=
    WithLp.toLp 2 fun ω => v (e.symm (ω, (e σ).2))
  have hfiber : (WithLp.toLp 2 fun ω =>
      periodicLocalInteractionES h i v (e.symm (ω, (e σ).2))) = h w := by
    ext ω
    simp only [periodicLocalInteractionES_apply_fiber h hRL, Equiv.apply_symm_apply]
    rfl
  change periodicLocalInteractionES h i (periodicLocalInteractionES h i v) σ =
    periodicLocalInteractionES h i v σ
  rw [periodicLocalInteractionES_apply_fiber h hRL]
  change h (WithLp.toLp 2 fun ω =>
      periodicLocalInteractionES h i v (e.symm (ω, (e σ).2))) (e σ).1 = _
  rw [hfiber, periodicLocalInteractionES_apply_fiber h hRL]
  exact congrArg (fun L => L w (e σ).1) hh.isIdempotentElem.eq

/-- Every actual extended local term on the full chain is an orthogonal
projection. Its local support projection and its fiberwise extension are
both derived from the actual interaction. -/
theorem mixedEndpointLocalInteraction_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    (periodicLocalInteractionES
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i).IsSymmetricProjection := by
  apply localExtension_isSymmetricProjection (hRL := hN)
  exact ⟨(Submodule.isSymmetricProjection_starProjection _).isIdempotentElem.one_sub,
    (mixedEndpointParentInteraction_isPositive A₀ A₁ 0).isSymmetric⟩

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
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro ξ
  rw [LinearMap.comp_apply, mixedEndpointActiveLinearIsometry_adjoint_apply]
  exact mixedEndpointActiveInclusion_apply_active v ξ

/-- The isometry followed by its adjoint is precisely the actual active
projection, not an unspecified projection with the same intended range. -/
theorem mixedEndpointActiveLinearIsometry_comp_adjoint :
    (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap ∘ₗ
        (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint =
      mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1) := by
  classical
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  change mixedEndpointActiveInclusion D₀ D₁ N
      ((mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint v) σ =
    mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1) v σ
  by_cases hσ : MixedEndpointOpenInnerActive σ
  · obtain ⟨ξ, rfl⟩ := (mem_range_mixedEndpointActivePhysicalCfg_iff σ).mpr hσ
    rw [mixedEndpointActiveInclusion_apply_active,
      mixedEndpointActiveLinearIsometry_adjoint_apply,
      mixedEndpointOpenActiveProjection_apply, if_pos hσ]
  · rw [mixedEndpointActiveInclusion_apply_inactive _ _ hσ,
      mixedEndpointOpenActiveProjection_apply, if_neg hσ]

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
    (periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.1)

/-- In the explicit active coordinates, a compressed term is the original
physical term evaluated on the encoded configuration after zero extension. -/
theorem mixedEndpointActiveLocalInteraction_apply
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) (v : mixedEndpointActiveSpace D₀ D₁ N)
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :
    mixedEndpointActiveLocalInteraction A₀ A₁ i v ξ =
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.1
        (mixedEndpointActiveLinearIsometry D₀ D₁ N v) (mixedEndpointActivePhysicalCfg ξ) :=
  mixedEndpointActiveLinearIsometry_adjoint_apply _ ξ

/-- The actual compressed term intertwines with the original physical term. -/
theorem mixedEndpointActiveLocalInteraction_intertwines
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i : NonwrappingStart 2 (N + 1 + 1)) (v : mixedEndpointActiveSpace D₀ D₁ N) :
    mixedEndpointActiveLinearIsometry D₀ D₁ N
        (mixedEndpointActiveLocalInteraction A₀ A₁ i v) =
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.1
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
      (LinearMap.ker (periodicLocalInteractionES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.1)).comap
          (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap := by
  ext v
  change mixedEndpointActiveLocalInteraction A₀ A₁ i v = 0 ↔
    periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.1
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
      (LinearMap.ker (periodicLocalInteractionES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.1)).map
          (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap.adjoint := by
  rw [ker_mixedEndpointActiveLocalInteraction]
  ext v
  constructor
  · intro hv
    refine ⟨mixedEndpointActiveLinearIsometry D₀ D₁ N v, hv, ?_⟩
    exact LinearMap.congr_fun mixedEndpointActiveLinearIsometry_adjoint_comp v
  · rintro ⟨w, hw, rfl⟩
    let T := periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.1
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
        (((LinearMap.ker (periodicLocalInteractionES
          (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.1)).map
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
      mixedEndpointActiveCompression (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (N + 1 + 1)) := by
  apply LinearMap.ext
  intro v
  simp [mixedEndpointActiveHamiltonian, mixedEndpointActiveLocalInteraction,
    mixedEndpointActiveCompression, openInteractionHamiltonianES,
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
      openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
        (N + 1 + 1) (mixedEndpointActiveLinearIsometry D₀ D₁ N v) := by
  rw [mixedEndpointActiveHamiltonian_eq_compression]
  exact activeCompression_intertwines _
    (mixedEndpointOpenActiveProjection_commute_openInteractionHamiltonianES
      A₀ A₁ (by omega)) v

/-- The exact kernel of the actual compressed sum, with no assumed global
kernel identification or spectral estimate. -/
theorem ker_mixedEndpointActiveHamiltonian
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N) =
      (LinearMap.ker (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (N + 1 + 1))).comap
          (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap := by
  ext v
  change mixedEndpointActiveHamiltonian A₀ A₁ N v = 0 ↔
    openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
      (N + 1 + 1) (mixedEndpointActiveLinearIsometry D₀ D₁ N v) = 0
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
    (hv : v ∈ LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N)) :
    mixedEndpointOpenActiveProjection D₀ D₁ N v = v := by
  let Q := mixedEndpointOpenActiveProjection D₀ D₁ N
  let H := openInteractionHamiltonianES
    (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N
  have hQ : Q (Q v) = Q v := LinearMap.congr_fun
    mixedEndpointOpenActiveProjection_isSymmetricProjection.isIdempotentElem.eq v
  have hcomm : H (Q v) = Q (H v) := congrArg (fun T => T v)
    (mixedEndpointOpenActiveProjection_commute_openInteractionHamiltonianES
      A₀ A₁ hN).eq.symm
  have hQz : Q (v - Q v) = 0 := by rw [map_sub, hQ, sub_self]
  have hHz : H (v - Q v) = 0 := by
    rw [map_sub, hcomm, LinearMap.mem_ker.mp hv, map_zero, sub_self]
  have henergy := mixedEndpointOpen_inactive_energy_lower_bound A₀ A₁ hN
    (v - Q v) hQz
  change (1 / 2 : ℝ) * ‖v - Q v‖ ^ 2 ≤ (inner ℂ (v - Q v) (H (v - Q v))).re
    at henergy
  rw [hHz, inner_zero_right] at henergy
  have hz : v - Q v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v - Q v)])
  exact (sub_eq_zero.mp hz).symm

/-- The genuine isometry maps the compressed ground space onto the entire
actual open-chain ground space. No inactive ground vectors are discarded. -/
theorem map_ker_mixedEndpointActiveHamiltonian
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    (LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N)).map
        (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap =
      LinearMap.ker (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (N + 1 + 1)) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
      (N + 1 + 1) (mixedEndpointActiveLinearIsometry D₀ D₁ N v) = 0
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
  change periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
    i.1 (mixedEndpointActiveLinearIsometry D₀ D₁ N v) = 0 ↔ _
  simp_rw [← mem_ker_insertedParentInteraction_iff]
  let e := cyclicActiveBlockConfigEquiv ((D₀ + D₁) * (D₀ + D₁)) 2 (by omega) i.1
  constructor
  · intro hv s
    apply PiLp.ext
    intro ω
    have h := congrArg (fun w => w (e.symm (ω, s))) hv
    rw [periodicLocalInteractionES_apply_fiber _ (by omega)] at h
    simpa only [e, Equiv.apply_symm_apply, PiLp.zero_apply,
      mixedEndpointActiveWindowFiber] using h
  · intro hv
    apply PiLp.ext
    intro σ
    have h := congrArg (fun w => w (e σ).1) (hv (e σ).2)
    rw [periodicLocalInteractionES_apply_fiber _ (by omega)]
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
