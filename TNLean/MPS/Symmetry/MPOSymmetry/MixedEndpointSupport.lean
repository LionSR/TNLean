/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointInterpolation
import TNLean.MPS.Core.TracePairing
import TNLean.Algebra.InjectiveRangeProjectorContinuity
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Continuous extended supports of the mixed endpoint interpolation

Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5, lines 1687–1692,
replace the two-site boundary vectors by
`tr[Aⁱ W(γ) Aʲ X]`. This removes the last factor `W(γ)` from the boundary
and extends the local support through the rank-changing endpoints.

The boundary map is proved injective from injectivity of the unweighted
mixed tensor and nonvanishing of `W(γ)`, even when `W(γ)` is singular.
Thus its range has constant dimension, and its orthogonal projector is
continuous by the inverse-Gram formula. These are finite-window results;
a uniform many-body gap and identification of endpoint ground spaces
require further proofs.
-/

open scoped Matrix

namespace MPSTensor
namespace MPOSymmetry

variable {d D D₀ D₁ : ℕ}

/-- A nonzero inserted matrix leaves the two-sided trace pairing of an
injective tensor nondegenerate. Source: arXiv:2203.12563, Section 5,
line 1690, the assertion that the extended two-site support has dimension
`D²`, including at the endpoints. -/
theorem eq_zero_of_inserted_pair_trace_eq_zero
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W X : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0)
    (hX : ∀ i j, Matrix.trace (A i * W * A j * X) = 0) : X = 0 := by
  have hspan := span_range_evalWord_mul_nonzero_mul_evalWord_eq_top
    (Kraus.isNBlkInjective_one_of_isInjective hA) hW
  let φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulRight ℂ X)
  have hφ : φ = 0 := by
    apply LinearMap.ext_on_range
      (v := fun uv : (Fin 1 → Fin d) × (Fin 1 → Fin d) =>
        Kraus.evalWord A (List.ofFn uv.1) * W * Kraus.evalWord A (List.ofFn uv.2))
      (hv := hspan)
    intro uv
    simpa [φ, List.ofFn_succ, Kraus.evalWord, Matrix.traceLinearMap_apply] using
      hX (uv.1 0) (uv.2 0)
  apply (Matrix.ext_iff_trace_mul_left (A := X) (B := 0)).2
  intro M
  simpa [φ, Matrix.traceLinearMap_apply] using congrArg (fun f => f M) hφ

/-- The extended two-site boundary map
`X ↦ (tr[Aⁱ W Aʲ X])ᵢⱼ`, with Euclidean domain and physical range.
Source: arXiv:2203.12563, Section 5, line 1690. -/
noncomputable def insertedTwoSiteMap
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Cfg d 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun σ =>
        Matrix.trace (A (σ 0) * W * A (σ 1) * Matrix.of (fun a b => v (a, b))))
      map_add' := by
        intro v w
        apply PiLp.ext
        intro σ
        change Matrix.trace (A (σ 0) * W * A (σ 1) *
          (Matrix.of (fun a b => v (a, b)) + Matrix.of (fun a b => w (a, b)))) = _
        simp only [Matrix.mul_add, Matrix.trace_add]
        rfl
      map_smul' := by
        intro c v
        apply PiLp.ext
        intro σ
        change Matrix.trace (A (σ 0) * W * A (σ 1) *
          (c • Matrix.of (fun a b => v (a, b)))) = _
        simp only [Matrix.mul_smul, Matrix.trace_smul]
        rfl }

@[simp]
theorem insertedTwoSiteMap_apply
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ)
    (v : EuclideanSpace ℂ (Fin D × Fin D)) (σ : Cfg d 2) :
    insertedTwoSiteMap A W v σ =
      Matrix.trace (A (σ 0) * W * A (σ 1) * Matrix.of (fun a b => v (a, b))) := rfl

/-- The extended boundary map is injective for any nonzero inserted matrix,
not only an invertible one. Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem insertedTwoSiteMap_injective
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0) :
    Function.Injective (insertedTwoSiteMap A W) := by
  refine (injective_iff_map_eq_zero (insertedTwoSiteMap A W)).2 fun v hv => ?_
  have hzero : Matrix.of (fun a b => v (a, b)) = (0 : Matrix (Fin D) (Fin D) ℂ) := by
    apply eq_zero_of_inserted_pair_trace_eq_zero A hA W _ hW
    intro i j
    simpa using congrArg (fun z : EuclideanSpace ℂ (Cfg d 2) => z ![i, j]) hv
  apply PiLp.ext
  rintro ⟨a, b⟩
  exact congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M a b) hzero

/-- The extended two-site support has dimension `D²` whenever the tensor is
injective and the inserted matrix is nonzero. Source: arXiv:2203.12563,
Section 5, line 1690. -/
theorem finrank_range_insertedTwoSiteMap
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0) :
    Module.finrank ℂ (insertedTwoSiteMap A W).range = D * D := by
  rw [LinearMap.finrank_range_of_inj (insertedTwoSiteMap_injective A hA W hW)]
  simp

/-- The extended boundary map is continuous in the inserted matrix.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem continuous_insertedTwoSiteMap
    {X : Type*} [TopologicalSpace X]
    (A : MPSTensor d D) (W : X → Matrix (Fin D) (Fin D) ℂ) (hW : Continuous W) :
    Continuous fun x => insertedTwoSiteMap A (W x) := by
  apply continuous_clm_apply.2
  intro v
  apply (EuclideanSpace.equiv (Cfg d 2) ℂ).symm.continuous.comp
  apply continuous_pi
  intro σ
  exact (((continuous_const.matrix_mul hW).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_trace

/-- Orthogonal projection onto the extended support is continuous for a
continuous family of nonzero inserted matrices. This includes singular
insertions. Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem continuous_range_insertedTwoSiteMap_starProjection
    {X : Type*} [TopologicalSpace X]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : X → Matrix (Fin D) (Fin D) ℂ) (hW : Continuous W) (hne : ∀ x, W x ≠ 0) :
    Continuous fun x => (insertedTwoSiteMap A (W x)).range.starProjection := by
  exact continuous_iff_continuousAt.mpr fun x =>
    ContinuousLinearMap.continuousAt_range_starProjection_of_injective
      (fun y => insertedTwoSiteMap A (W y))
      (continuous_insertedTwoSiteMap A W hW).continuousAt
      (insertedTwoSiteMap_injective A hA (W x) (hne x))

/-- For an invertible insertion, removing its final occurrence merely
reparametrizes the boundary matrix. Thus the extended support is exactly
the two-site ground space of the right-weighted tensor.
Source: arXiv:2203.12563, Section 5, line 1690, `Sγ = S′γ`. -/
theorem range_insertedTwoSiteMap_eq_groundSpaceES
    (A : MPSTensor d D) (W : Matrix (Fin D) (Fin D) ℂ) (hW : IsUnit W) :
    (insertedTwoSiteMap A W).range = groundSpaceES (fun i => A i * W) 2 := by
  obtain ⟨u, rfl⟩ := hW
  apply le_antisymm
  · rintro ψ ⟨v, rfl⟩
    rw [mem_groundSpaceES_iff]
    refine ⟨(↑u⁻¹ : Matrix (Fin D) (Fin D) ℂ) * Matrix.of (fun a b => v (a, b)), ?_⟩
    funext σ
    simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc,
      insertedTwoSiteMap_apply, WithLp.linearEquiv_apply]
  · intro ψ hψ
    rw [mem_groundSpaceES_iff] at hψ
    obtain ⟨X, hX⟩ := hψ
    refine ⟨WithLp.toLp 2 (fun p : Fin D × Fin D => ((u : Matrix (Fin D) (Fin D) ℂ) * X)
      p.1 p.2), ?_⟩
    apply PiLp.ext
    intro σ
    have hσ := congrFun hX σ
    have hη : Matrix.of (fun a b => ((u : Matrix (Fin D) (Fin D) ℂ) * X) a b) =
        (u : Matrix (Fin D) (Fin D) ℂ) * X := by
      ext a b
      rfl
    simpa [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc,
      insertedTwoSiteMap_apply, WithLp.linearEquiv_apply, hη] using hσ

/-- In the open interval, the extended support of the mixed interpolation
coincides with its canonical two-site MPS ground space.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem mixedEndpoint_extendedSupport_eq_groundSpaceES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
      (bondInterpolationMatrix D₀ D₁ γ)).range =
      groundSpaceES (mixedEndpointInterpolation A₀ A₁ γ) 2 :=
  range_insertedTwoSiteMap_eq_groundSpaceES _ _
    (isUnit_bondInterpolationMatrix_of_mem_Ioo hγ)

/-- The source mixed-tensor path has extended local support of dimension
`(D₀ + D₁)²`, including both rank-changing endpoints. Endpoint bond spaces
are positive, so the inserted block weight never vanishes.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem finrank_mixedEndpoint_extendedSupport
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (γ : ℝ) :
    Module.finrank ℂ (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
      (bondInterpolationMatrix D₀ D₁ γ)).range = (D₀ + D₁) * (D₀ + D₁) :=
  finrank_range_insertedTwoSiteMap _ (isInjective_mixedEndpointBase A₀ A₁ h₀ h₁) _
    (bondInterpolationMatrix_ne_zero hD₀ hD₁ γ)

/-- The orthogonal projectors onto the actual mixed-tensor extended supports
are continuous through both endpoints. No projector limits or constant-rank
hypotheses are supplied. Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem continuous_mixedEndpoint_extendedSupport_starProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) :
    Continuous fun γ : ℝ => (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
      (bondInterpolationMatrix D₀ D₁ γ)).range.starProjection :=
  continuous_range_insertedTwoSiteMap_starProjection _
    (isInjective_mixedEndpointBase A₀ A₁ h₀ h₁) _
    (continuous_bondInterpolationMatrix D₀ D₁)
    (bondInterpolationMatrix_ne_zero hD₀ hD₁)

/-- The continuous extension of the source two-site parent interaction,
using the extended support also at the endpoints.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
noncomputable def mixedEndpointParentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (γ : ℝ) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) →L[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) :=
  1 - (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
    (bondInterpolationMatrix D₀ D₁ γ)).range.starProjection

/-- The extended local parent interaction is continuous through the endpoints.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem continuous_mixedEndpointParentInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) :
    Continuous (mixedEndpointParentInteraction A₀ A₁) :=
  continuous_const.sub
    (continuous_mixedEndpoint_extendedSupport_starProjection A₀ A₁ h₀ h₁ hD₀ hD₁)

/-- In the interior the extended interaction is exactly the canonical
parent interaction of the mixed MPS tensor.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointParentInteraction_eq_parentInteractionES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    mixedEndpointParentInteraction A₀ A₁ γ =
      LinearMap.toContinuousLinearMap
        (parentInteractionES (mixedEndpointInterpolation A₀ A₁ γ) 2) := by
  have hproj := congrArg
    (fun S : Submodule ℂ (EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)) =>
      S.starProjection)
    (mixedEndpoint_extendedSupport_eq_groundSpaceES A₀ A₁ hγ)
  rw [mixedEndpointParentInteraction, hproj]
  ext v
  simp [parentInteractionES, Submodule.starProjection_orthogonal]

/-- Along the interior, the canonical parent terms converge to the extended
term at either endpoint (and at every interior point). The limiting term
uses the extended support, which need not be the unextended endpoint
support. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem tendsto_mixedEndpoint_parentInteractionES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (p : ℝ) :
    Filter.Tendsto (fun γ : ℝ => LinearMap.toContinuousLinearMap
      (parentInteractionES (mixedEndpointInterpolation A₀ A₁ γ) 2))
      (nhdsWithin p (Set.Ioo (0 : ℝ) 1))
      (nhds (mixedEndpointParentInteraction A₀ A₁ p)) := by
  have hlim := (continuous_mixedEndpointParentInteraction A₀ A₁ h₀ h₁ hD₀ hD₁).tendsto p
  apply (tendsto_nhdsWithin_of_tendsto_nhds hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  exact mixedEndpointParentInteraction_eq_parentInteractionES A₀ A₁ hγ

end MPOSymmetry
end MPSTensor
