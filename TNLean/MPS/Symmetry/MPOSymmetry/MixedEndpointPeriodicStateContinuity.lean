/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.RingEndpointRightComparison
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenGapContinuity
import TNLean.MPS.ParentHamiltonian.PeriodicShortGapContinuity
import TNLean.MPS.FundamentalTheorem.Reduction.AbsorbingCompression
import Mathlib.Topology.UnitInterval

/-!
# Periodic state and kernel continuity through the mixed endpoints

The periodic vector of the actual weighted mixed tensor equals the embedded
endpoint vector at each endpoint, for every positive chain length. At zero,
this follows by compression onto the right-absorbing first virtual corner;
at one, by exchanging the two physical and virtual sectors.

For every fixed periodic length at least two, the vector is nonzero throughout
the closed interpolation interval. The actual extended periodic Hamiltonian
has exactly its span as kernel. Consequently the kernel projection is
continuous through both endpoints, and the gap has a positive lower bound
on the closed parameter interval for each fixed length. This bound may depend
on the length and is not a thermodynamic uniform-gap assertion.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5,
`defAgamma`, lines 1586–1601 and 1687–1692.
-/

open scoped BigOperators Matrix Topology

namespace MPSTensor

/-- A nonzero periodic vector gives an injective scalar-to-state map, without
requiring the tensor itself to be injective. -/
theorem periodicMpvLineMap_injective_of_mpv_ne_zero
    {d D N : ℕ} (A : MPSTensor d D) (hψ : (mpv A : NSiteSpace d N) ≠ 0) :
    Function.Injective (periodicMpvLineMap A N) := by
  have hstate : (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A) ≠ 0 := by
    intro hzero
    apply hψ
    simpa using congrArg (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)) hzero
  apply (injective_iff_map_eq_zero (periodicMpvLineMap A N)).2
  intro c hc
  change c • (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A) = 0 at hc
  exact (smul_eq_zero.mp hc).resolve_right hstate

/-- The periodic sum of a continuous local interaction is continuous at every
fixed chain length. -/
theorem continuous_periodicInteractionHamiltonianES_family
    {X : Type*} [TopologicalSpace X] {d R : ℕ}
    (h : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hh : Continuous h) (N : ℕ) :
    Continuous fun x =>
      (periodicInteractionHamiltonianES (h x).toLinearMap N).toContinuousLinearMap := by
  have hsum : Continuous fun x => ∑ i : Fin N,
      (periodicLocalInteractionES (h x).toLinearMap i).toContinuousLinearMap :=
    continuous_finsetSum _ fun i _ => continuous_periodicLocalInteractionES_family h hh i
  convert hsum using 1
  funext x
  ext v
  simp [periodicInteractionHamiltonianES]

namespace MPOSymmetry

variable {D₀ D₁ N : ℕ}

/-- At parameter zero, every positive-length periodic vector of the actual
weighted mixed tensor is exactly the embedded first-endpoint vector. No
injectivity or state-equality hypothesis is needed.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
theorem mpv_mixedEndpointInterpolation_zero
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 0 < N) :
    (mpv (mixedEndpointInterpolation A₀ A₁ 0) :
      NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) N) =
      mpv (mixedEndpointLeftTensor A₀ D₁) := by
  let V := Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁))
  have hiso : Vᴴ * V = 1 := Matrix.coordinateInclusion_isometry _
  have hweight : bondInterpolationMatrix D₀ D₁ 0 = V * Vᴴ :=
    coordinateInclusion_first_projection_eq_bondWeight.symm
  have habs (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
      mixedEndpointInterpolation A₀ A₁ 0 p * (V * Vᴴ) =
        mixedEndpointInterpolation A₀ A₁ 0 p := by
    simp only [mixedEndpointInterpolation, hweight]
    calc
      mixedEndpointBase A₀ A₁ p * (V * Vᴴ) * (V * Vᴴ) =
          mixedEndpointBase A₀ A₁ p * V * (Vᴴ * V) * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = mixedEndpointBase A₀ A₁ p * (V * Vᴴ) := by
        rw [hiso, Matrix.mul_one, Matrix.mul_assoc]
  have hcompress (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
      Vᴴ * mixedEndpointInterpolation A₀ A₁ 0 p * V =
        mixedEndpointLeftTensor A₀ D₁ p := by
    simp only [mixedEndpointInterpolation, hweight]
    calc
      Vᴴ * (mixedEndpointBase A₀ A₁ p * (V * Vᴴ)) * V =
          (Vᴴ * mixedEndpointBase A₀ A₁ p * V) * (Vᴴ * V) := by
        simp only [Matrix.mul_assoc]
      _ = mixedEndpointLeftTensor A₀ D₁ p := by
        rw [hiso, Matrix.mul_one]
        exact mixedEndpointBase_first_compression A₀ A₁ p
  funext σ
  have hword : List.ofFn σ ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp only [List.length_ofFn, List.length_nil] at hlength
    omega
  have htrace := Kraus.trace_evalWord_compress_of_right_absorb
    (mixedEndpointInterpolation A₀ A₁ 0) Vᴴ V habs (List.ofFn σ) hword
  rw [show (fun p => Vᴴ * mixedEndpointInterpolation A₀ A₁ 0 p * V) =
      mixedEndpointLeftTensor A₀ D₁ from funext hcompress] at htrace
  exact htrace.symm

/-- The actual weighted letters at the second endpoint become the first
endpoint of the reversed pair under the physical and virtual exchanges.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
theorem mixedEndpointInterpolation_one_swap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mixedEndpointInterpolation A₁ A₀ 0 (mixedEndpointPhysicalSwap D₀ D₁ p) =
      Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap D₀ D₁)
        (mixedEndpointInterpolation A₀ A₁ 1 p) := by
  simp only [mixedEndpointInterpolation, mixedEndpointBase_swap,
    bondInterpolationMatrix_one_swap, map_mul]

/-- At parameter one, every positive-length periodic vector of the actual
weighted mixed tensor is exactly the embedded second-endpoint vector.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
theorem mpv_mixedEndpointInterpolation_one
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 0 < N) :
    (mpv (mixedEndpointInterpolation A₀ A₁ 1) :
      NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) N) =
      mpv (mixedEndpointRightTensor A₁ D₀) := by
  let e := mixedEndpointPhysicalSwap D₀ D₁
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap D₀ D₁)
  have hword (w : List (Fin ((D₀ + D₁) * (D₀ + D₁)))) :
      Kraus.evalWord (Kraus.reindexPhysical e (mixedEndpointInterpolation A₁ A₀ 0)) w =
        Φ (Kraus.evalWord (mixedEndpointInterpolation A₀ A₁ 1) w) := by
    induction w with
    | nil => simp only [Kraus.evalWord_nil, map_one]
    | cons p w ih =>
        rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ih]
        change mixedEndpointInterpolation A₁ A₀ 0 (e p) * _ = _
        rw [mixedEndpointInterpolation_one_swap, map_mul]
  have htrace (X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
      Matrix.trace (Φ X) = Matrix.trace X := by
    unfold Matrix.trace
    exact Fintype.sum_equiv (mixedEndpointBondSwap D₀ D₁).symm _ _ fun _ => rfl
  funext σ
  calc
    mpv (mixedEndpointInterpolation A₀ A₁ 1) σ =
        mpv (Kraus.reindexPhysical e (mixedEndpointInterpolation A₁ A₀ 0)) σ := by
      change Matrix.trace (Kraus.evalWord _ (List.ofFn σ)) =
        Matrix.trace (Kraus.evalWord _ (List.ofFn σ))
      rw [hword, htrace]
    _ = mpv (mixedEndpointRightTensor A₁ D₀) σ := by
      rw [mpv_reindexPhysical, mixedEndpointRightTensor, mpv_reindexPhysical]
      exact congrFun (mpv_mixedEndpointInterpolation_zero A₁ A₀ hN) _

/-- The actual weighted mixed periodic vector is nonzero on the closed
interpolation interval, including both rank-changing endpoints, for every
ring of length at least two. Source: arXiv:2203.12563, Section 5,
lines 1687–1692. -/
theorem mpv_mixedEndpointInterpolation_ne_zero [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) (hN : 2 ≤ N) :
    (mpv (mixedEndpointInterpolation A₀ A₁ γ) :
      NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) N) ≠ 0 := by
  by_cases hzero : (γ : ℝ) = 0
  · rw [hzero, mpv_mixedEndpointInterpolation_zero A₀ A₁ (by omega)]
    exact mpv_ne_zero_of_isNBlkInjective
      (Kraus.isNBlkInjective_one_of_isInjective
        (isInjective_mixedEndpointLeftTensor A₀ h₀ D₁)) (by norm_num) hN
  by_cases hone : (γ : ℝ) = 1
  · rw [hone, mpv_mixedEndpointInterpolation_one A₀ A₁ (by omega)]
    exact mpv_ne_zero_of_isNBlkInjective
      (Kraus.isNBlkInjective_one_of_isInjective
        (isInjective_mixedEndpointRightTensor A₁ h₁ D₀)) (by norm_num) hN
  have hγ : (γ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne γ.property.1 (Ne.symm hzero), lt_of_le_of_ne γ.property.2 hone⟩
  let : NeZero (D₀ + D₁) := ⟨by have := NeZero.ne D₀; omega⟩
  exact mpv_ne_zero_of_isNBlkInjective
    (Kraus.isNBlkInjective_one_of_isInjective
      (isInjective_mixedEndpointInterpolation A₀ A₁ h₀ h₁ hγ)) (by norm_num) hN

/-- In the open interpolation interval, the actual extended periodic
Hamiltonian is the canonical parent of the weighted mixed tensor.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem mixedEndpoint_periodicInteractionHamiltonianES_eq_of_mem_Ioo
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (N : ℕ) :
    periodicInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N =
      parentHamiltonianES (mixedEndpointInterpolation A₀ A₁ γ) 2 N := by
  rw [mixedEndpointParentInteraction_eq_parentInteractionES A₀ A₁ hγ]
  exact periodicInteractionHamiltonianES_parentInteractionES _ (by norm_num) N

/-- The kernel of the actual extended periodic Hamiltonian is the line of the
actual weighted mixed periodic vector throughout the closed interval. The
endpoint identification follows from the ring comparisons and absorbing
compression, rather than from an assumed limiting ground state.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_ker_eq_range_periodicMpvLineMap
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) (hN : 2 ≤ N) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N) =
      (periodicMpvLineMap (mixedEndpointInterpolation A₀ A₁ γ) N).range := by
  by_cases hzero : (γ : ℝ) = 0
  · rw [hzero, mixedEndpoint_periodic_ker_eq A₀ A₁ hN,
      ker_parentHamiltonianES_two_eq_range_periodicMpvLineMap _
        (isInjective_mixedEndpointLeftTensor A₀ h₀ D₁) hN]
    simp only [periodicMpvLineMap,
      mpv_mixedEndpointInterpolation_zero A₀ A₁ (by omega : 0 < N)]
  by_cases hone : (γ : ℝ) = 1
  · rw [hone, mixedEndpoint_periodic_one_ker_eq A₀ A₁ hN,
      ker_parentHamiltonianES_two_eq_range_periodicMpvLineMap _
        (isInjective_mixedEndpointRightTensor A₁ h₁ D₀) hN]
    simp only [periodicMpvLineMap,
      mpv_mixedEndpointInterpolation_one A₀ A₁ (by omega : 0 < N)]
  have hγ : (γ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne γ.property.1 (Ne.symm hzero), lt_of_le_of_ne γ.property.2 hone⟩
  let : NeZero (D₀ + D₁) := ⟨by have := NeZero.ne D₀; omega⟩
  rw [mixedEndpoint_periodicInteractionHamiltonianES_eq_of_mem_Ioo A₀ A₁ hγ]
  exact ker_parentHamiltonianES_two_eq_range_periodicMpvLineMap _
    (isInjective_mixedEndpointInterpolation A₀ A₁ h₀ h₁ hγ) hN

/-- The actual extended periodic Hamiltonian has a one-dimensional kernel
at every parameter of the closed interval. Source: arXiv:2203.12563,
Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_groundSpace_finrank_closedInterval
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N)) = 1 := by
  rw [mixedEndpoint_periodic_ker_eq_range_periodicMpvLineMap A₀ A₁ h₀ h₁ γ hN,
    LinearMap.finrank_range_of_inj (periodicMpvLineMap_injective_of_mpv_ne_zero _
      (mpv_mixedEndpointInterpolation_ne_zero A₀ A₁ h₀ h₁ γ hN))]
  simp

/-- For each fixed periodic volume, the exact kernel projector of the actual
extended mixed Hamiltonian is continuous through both endpoints. Neither
endpoint injectivity of the enlarged tensor nor kernel continuity is assumed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem continuous_mixedEndpoint_periodic_ker_starProjection
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    Continuous fun γ : unitInterval =>
      (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N)).starProjection := by
  have hT := continuous_periodicMpvLineMap_family
    (fun γ : unitInterval => mixedEndpointInterpolation A₀ A₁ γ)
    ((continuous_mixedEndpointInterpolation A₀ A₁).comp continuous_subtype_val) N
  have hTinj (γ : unitInterval) :
      Function.Injective (periodicMpvLineMap (mixedEndpointInterpolation A₀ A₁ γ) N) :=
    periodicMpvLineMap_injective_of_mpv_ne_zero _
      (mpv_mixedEndpointInterpolation_ne_zero A₀ A₁ h₀ h₁ γ hN)
  have hProj := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun γ : unitInterval => periodicMpvLineMap (mixedEndpointInterpolation A₀ A₁ γ) N)
    hT hTinj
  have heq :
      (fun γ : unitInterval => ContinuousLinearMap.injectiveRangeProjector
        (periodicMpvLineMap (mixedEndpointInterpolation A₀ A₁ γ) N) (hTinj γ)) =
      (fun γ : unitInterval => (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N)).starProjection) := by
    funext γ
    rw [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection]
    exact congrArg
      (fun S : Submodule ℂ (EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N)) =>
        S.starProjection)
      (mixedEndpoint_periodic_ker_eq_range_periodicMpvLineMap A₀ A₁ h₀ h₁ γ hN).symm
  rw [← heq]
  exact hProj

/-- At every fixed periodic length, one positive gap bound works throughout
the closed mixed interpolation, including its rank-changing endpoints. The
bound may depend on the chain length; no uniform thermodynamic gap is claimed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692; the compact finite-volume
argument is arXiv:1010.3732, Appendix A, lines 2575–2578. -/
theorem exists_uniform_mixedEndpoint_periodic_gap_fixed_volume
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval,
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ := by
  have hH := (continuous_periodicInteractionHamiltonianES_family _
    (continuous_mixedEndpointParentInteraction A₀ A₁ h₀ h₁
      (NeZero.pos D₀) (NeZero.pos D₁)) N).comp
    (continuous_subtype_val : Continuous fun γ : unitInterval => (γ : ℝ))
  obtain ⟨δ, hδ, hgap⟩ := ContinuousLinearMap.exists_uniform_norm_gap_of_compact
    (fun γ : unitInterval => (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N).toContinuousLinearMap)
    hH (continuous_mixedEndpoint_periodic_ker_starProjection A₀ A₁ h₀ h₁ hN)
    (S := Set.univ) isCompact_univ
  exact ⟨δ, hδ, fun γ => hgap γ (Set.mem_univ γ)⟩

end MPOSymmetry
end MPSTensor
