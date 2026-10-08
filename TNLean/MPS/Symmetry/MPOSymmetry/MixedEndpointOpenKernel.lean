/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointRestriction
import TNLean.MPS.Symmetry.MPOSymmetry.RingEndpointComparison

/-!
# Exact open-chain kernels of the extended mixed interaction

The open-chain sum contains exactly the nonwrapping translates of the
extended two-site interaction. Positivity identifies its kernel with the
simultaneous local constraints. The inserted-support intersection property
then identifies that kernel with the full extended boundary range, including
at singular endpoint insertions. Thus the open ground-space dimension and
orthogonal kernel projector remain constant and continuous through both
endpoints.

Source: arXiv:2203.12563, Section 5, lines 1687–1692. These are fixed-volume
kernel assertions; they do not infer a uniform path gap from continuity.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor

variable {d R N : ℕ}

/-- Join a cyclic window with the complementary coordinates of a full
configuration. -/
theorem cyclicCfg_eq_join_cyclicActiveBlock
    (hRN : R ≤ N) (i : Fin N) (ω : Cfg d R) (τ : Cfg d N) :
    cyclicCfg (Fin.pos i) R i ω τ =
      (cyclicActiveBlockConfigEquiv d R hRN i).symm
        (ω, (cyclicActiveBlockConfigEquiv d R hRN i τ).2) := by
  funext k
  let x := (cyclicWindowIndexEquiv R N hRN i).symm k
  have hk : cyclicWindowIndexEquiv R N hRN i x = k := by simp [x]
  rcases x with r | r
  · rw [← hk, cyclicWindowIndexEquiv_inl]
    change cyclicCfg (Fin.pos i) R i ω τ (cyclicForwardSite i r.val) =
      (cyclicActiveBlockConfigEquiv d R hRN i).symm
        (ω, (cyclicActiveBlockConfigEquiv d R hRN i τ).2)
        (cyclicForwardSite i r.val)
    rw [cyclicCfg_cyclicForwardSite_apply (Fin.pos i) hRN,
      cyclicActiveBlockConfigEquiv_symm_apply_window]
  · rw [← hk, cyclicWindowIndexEquiv_inr]
    have hsite :
        (⟨(i.val + R + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) =
          cyclicForwardSite i (R + r.val) := by
      apply Fin.ext
      simp only [cyclicForwardSite, Fin.val_mk, Nat.add_assoc]
    rw [hsite, cyclicActiveBlockConfigEquiv_symm_apply_spectator]
    have hoff :
        ((cyclicForwardSite i (R + r.val)).val + N - i.val) % N = R + r.val := by
      simpa [cyclicForwardSite] using offset_mod_eq i.isLt (by omega : R + r.val < N)
    rw [cyclicCfg, dite_eq_right (by rw [hoff]; omega)]
    have h := cyclicActiveBlockConfigEquiv_symm_apply_spectator hRN i
      (cyclicActiveBlockConfigEquiv d R hRN i τ).1
      (cyclicActiveBlockConfigEquiv d R hRN i τ).2 r
    simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using h

/-- Cyclic restriction is the corresponding spectator fiber after the
active-block coordinate isometry. -/
theorem cyclicRestrictES_eq_rightFiber
    (hRN : R ≤ N) (i : Fin N) (τ : Cfg d N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    cyclicRestrictES (Fin.pos i) R i τ v =
      ContinuousLinearMap.rightFiber
        (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v)
        (cyclicActiveBlockConfigEquiv d R hRN i τ).2 := by
  apply PiLp.ext
  intro ω
  change v (cyclicCfg (Fin.pos i) R i ω τ) =
    cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v
      (ω, (cyclicActiveBlockConfigEquiv d R hRN i τ).2)
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply,
    cyclicCfg_eq_join_cyclicActiveBlock]

/-- A translated local interaction annihilates a vector precisely when
it annihilates every cyclic-window restriction. -/
theorem mem_ker_periodicLocalInteractionES_iff [NeZero d]
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) :
    v ∈ LinearMap.ker (periodicLocalInteractionES h i) ↔
      ∀ τ : Cfg d N, cyclicRestrictES (Fin.pos i) R i τ v ∈ LinearMap.ker h := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  let G := ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
    (LinearMap.toContinuousLinearMap h)
  have hconj : v ∈ LinearMap.ker (periodicLocalInteractionES h i) ↔
      U v ∈ LinearMap.ker G.toLinearMap := by
    simp only [LinearMap.mem_ker]
    rw [periodicLocalInteractionES, dite_eq_left hRN]
    change U.symm (G (U v)) = 0 ↔ G (U v) = 0
    constructor
    · intro hv
      have hv' := congrArg U hv
      simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using hv'
    · intro hv
      rw [hv, map_zero]
  rw [hconj]
  change U v ∈ LinearMap.ker
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
      (LinearMap.toContinuousLinearMap h)).toLinearMap ↔ _
  rw [ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff]
  change (∀ s, ContinuousLinearMap.rightFiber (U v) s ∈ LinearMap.ker h) ↔ _
  constructor
  · intro hv τ
    rw [cyclicRestrictES_eq_rightFiber hRN]
    exact hv _
  · intro hv s
    let ω : Cfg d R := fun _ => ⟨0, NeZero.pos d⟩
    have hs := hv ((cyclicActiveBlockConfigEquiv d R hRN i).symm (ω, s))
    rw [cyclicRestrictES_eq_rightFiber hRN] at hs
    simpa only [Equiv.apply_symm_apply] using hs

/-- Extending the zero local interaction gives zero. -/
@[simp] theorem periodicLocalInteractionES_zero (i : Fin N) :
    periodicLocalInteractionES
      (0 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) i = 0 := by
  simp [periodicLocalInteractionES]

/-- Extension to a cyclic window preserves positivity. -/
theorem periodicLocalInteractionES_isPositive
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : h.IsPositive) (i : Fin N) :
    (periodicLocalInteractionES h i).IsPositive := by
  apply LinearMap.nonneg_iff_isPositive.mp
  simpa only [periodicLocalInteractionES_zero] using
    periodicLocalInteractionES_mono (LinearMap.nonneg_iff_isPositive.mpr hh) i

/-- Positivity identifies the open-chain kernel with its individual
nonwrapping local constraints. -/
theorem mem_ker_openInteractionHamiltonianES_iff [NeZero d]
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : h.IsPositive) (hRN : R ≤ N) (v : EuclideanSpace ℂ (Cfg d N)) :
    v ∈ LinearMap.ker (openInteractionHamiltonianES h N) ↔
      ∀ i : NonwrappingStart R N, ∀ τ : Cfg d N,
        cyclicRestrictES (Fin.pos i.1) R i.1 τ v ∈ LinearMap.ker h := by
  rw [openInteractionHamiltonianES,
    WeightedPositiveKernel.ker_sum_eq_iInf
      (fun i : NonwrappingStart R N => periodicLocalInteractionES_isPositive hh i.1)]
  simp only [Submodule.mem_iInf, mem_ker_periodicLocalInteractionES_iff h hRN]

namespace MPOSymmetry

variable {D D₀ D₁ : ℕ}

/-- The complementary support projection vanishes exactly on the
extended two-site boundary range. -/
theorem mem_ker_insertedParentInteraction_iff
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) :
    v ∈ LinearMap.ker (1 - (insertedTwoSiteMap A W).range.starProjection).toLinearMap ↔
      v ∈ (insertedTwoSiteMap A W).range := by
  change v - (insertedTwoSiteMap A W).range.starProjection v = 0 ↔ _
  rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- The actual nonwrapping extended parent has the full extended boundary
range as its kernel. Singular nonzero insertions are allowed, so the theorem
covers both endpoints without identifying their free boundary indices with
the smaller canonical boundary space.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem ker_openInteractionHamiltonianES_inserted_eq
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0) (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (1 - (insertedTwoSiteMap A W).range.starProjection).toLinearMap N) =
      (insertedBoundaryMap A W N).range := by
  have hd : d ≠ 0 := by
    intro hd
    subst d
    have hrange : Set.range A = ∅ := by
      ext M
      constructor
      · rintro ⟨i, _⟩
        exact i.elim0
      · intro hM
        cases hM
    have hmem : W ∈ Submodule.span ℂ (Set.range A) := by
      rw [hA]
      exact Submodule.mem_top
    exact hW (by simpa only [hrange, Submodule.span_empty, Submodule.mem_bot] using hmem)
  let : NeZero d := ⟨hd⟩
  have hpos : (1 - (insertedTwoSiteMap A W).range.starProjection).toLinearMap.IsPositive := by
    simpa only [Submodule.starProjection_orthogonal'] using
      (Submodule.isSymmetricProjection_starProjection
        ((insertedTwoSiteMap A W).range)ᗮ).isPositive
  ext v
  rw [mem_ker_openInteractionHamiltonianES_iff hpos hN,
    mem_range_insertedBoundaryMap_iff]
  simp only [mem_ker_insertedParentInteraction_iff]
  constructor
  · intro hv
    apply contiguous_mem_of_restriction_intersection_submodules
      (insertedGroundSpace A W) (by omega : 0 < 2) hN ?_ ?_
    · intro M hM
      ext ψ
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      exact (insertedGroundSpace_iff_left_right A hA W hW (by omega)).symm
    · intro s hs τ
      have hlocal := hv ⟨⟨s, by omega⟩, hs⟩ τ
      rw [← insertedBoundaryMap_two A W, mem_range_insertedBoundaryMap_iff] at hlocal
      change cyclicRestrictₗ (by omega) 2 ⟨s, by omega⟩ τ
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d N) v) ∈ insertedGroundSpace A W 2 at hlocal
      rwa [cyclicRestrictₗ_eq_contiguousRestrictₗ _ hN hs] at hlocal
  · intro hv i τ
    rw [← insertedBoundaryMap_two A W, mem_range_insertedBoundaryMap_iff]
    change cyclicRestrictₗ (Fin.pos i.1) 2 i.1 τ
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N) v) ∈ insertedGroundSpace A W 2
    rw [cyclicRestrictₗ_eq_contiguousRestrictₗ _ hN i.2]
    exact contiguousRestrictₗ_insertedGroundSpace_mem A W (by omega) i.1.val i.2 τ hv

/-- The kernel of the actual open-chain sum has dimension `D²`, derived
from the injective extended boundary map.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem finrank_ker_openInteractionHamiltonianES_inserted
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openInteractionHamiltonianES
      (1 - (insertedTwoSiteMap A W).range.starProjection).toLinearMap N)) = D * D := by
  rw [ker_openInteractionHamiltonianES_inserted_eq A hA W hW hN]
  exact finrank_range_insertedBoundaryMap A hA W hW (by omega)

/-- Orthogonal projection onto the exact open-chain kernel is continuous
for any continuous injective tensor and nonzero insertion family.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem continuous_ker_openInteractionHamiltonianES_inserted_starProjection
    {X : Type*} [TopologicalSpace X]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (W : X → Matrix (Fin D) (Fin D) ℂ) (hW : Continuous W)
    (hInj : ∀ x, Kraus.IsInjective (A x)) (hne : ∀ x, W x ≠ 0) (hN : 2 ≤ N) :
    Continuous fun x => (LinearMap.ker (openInteractionHamiltonianES
      (1 - (insertedTwoSiteMap (A x) (W x)).range.starProjection).toLinearMap
        N)).starProjection := by
  simp_rw [ker_openInteractionHamiltonianES_inserted_eq _ (hInj _) _ (hne _) hN]
  exact continuous_range_insertedBoundaryMap_starProjection A hA W hW hInj hne (by omega)

/-- The actual mixed interaction has the extended boundary range as its
open-chain kernel at every real parameter, including both endpoints.
Source: arXiv:2203.12563, Section 5, lines 1687–1692. -/
theorem mixedEndpoint_open_ker_eq
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N) =
      (insertedBoundaryMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ γ) N).range :=
  ker_openInteractionHamiltonianES_inserted_eq _
    (isInjective_mixedEndpointBase A₀ A₁ h₀ h₁) _
    (bondInterpolationMatrix_ne_zero hD₀ hD₁ γ) hN

/-- The mixed open-chain kernel has the constant dimension `(D₀ + D₁)²`
through both endpoints. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_open_ker_finrank
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N)) =
      (D₀ + D₁) * (D₀ + D₁) := by
  rw [mixedEndpoint_open_ker_eq A₀ A₁ h₀ h₁ hD₀ hD₁ γ hN]
  exact finrank_mixedEndpoint_extendedBoundarySupport A₀ A₁ h₀ h₁ hD₀ hD₁ γ (by omega)

/-- Projection onto the kernel of the actual mixed open-chain sum is
continuous at both endpoints for every fixed chain length at least two.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem continuous_mixedEndpoint_open_ker_starProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hN : 2 ≤ N) :
    Continuous fun γ : ℝ => (LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N)).starProjection := by
  simp_rw [mixedEndpoint_open_ker_eq A₀ A₁ h₀ h₁ hD₀ hD₁ _ hN]
  exact continuous_mixedEndpoint_extendedBoundarySupport_starProjection
    A₀ A₁ h₀ h₁ hD₀ hD₁ (by omega)

end MPOSymmetry
end MPSTensor
