/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import QICLean.Channel.FixedPoint.StationaryStates
import QICLean.Channel.KrausMap
import TNLean.MPS.Defs

/-!
# Local continuous stationary densities of unital MPS tensors

For a continuous family of unital tensors, a one-dimensional adjoint fixed space
at one parameter value gives a local continuous choice of positive semidefinite,
trace-one adjoint fixed matrices. Their ranks may vary.

The proof augments the stationary equation by the trace normalization, making
it invertible near the initial parameter. Positivity follows from uniqueness
and the existence of a stationary state for a positive trace-preserving map
(Wolf, Theorem 6.11). The fixed-space hypothesis is an explicit finite-dimensional
assumption; no implication from a physical Hamiltonian gap is asserted here.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder Topology

namespace Matrix

private abbrev StationaryMat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

private noncomputable def stationaryNormalizationOperator {D : ℕ}
    (τ : StationaryMat D) (E : StationaryMat D →L[ℂ] StationaryMat D) :
    StationaryMat D →L[ℂ] StationaryMat D :=
  ContinuousLinearMap.id ℂ _ - E +
    ((traceLinearMap (Fin D) ℂ ℂ).toContinuousLinearMap).smulRight τ

private theorem stationaryNormalizationOperator_apply {D : ℕ}
    (τ : StationaryMat D) (E : StationaryMat D →L[ℂ] StationaryMat D) (X : StationaryMat D) :
    stationaryNormalizationOperator τ E X = X - E X + trace X • τ := by
  rfl

private theorem stationaryNormalizationOperator_isUnit {D : ℕ}
    (τ ρ : StationaryMat D) (E : StationaryMat D →L[ℂ] StationaryMat D)
    (hτ : trace τ = 1) (hρ : trace ρ = 1) (hfix : E ρ = ρ)
    (hTP : ∀ X, trace (E X) = trace X)
    (hdim : Module.finrank ℂ
      (LinearMap.ker (ContinuousLinearMap.id ℂ (StationaryMat D) - E).toLinearMap) = 1) :
    IsUnit (stationaryNormalizationOperator τ E) := by
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := StationaryMat D)
    (f := stationaryNormalizationOperator τ E)).mpr
  suffices hInject : Function.Injective (stationaryNormalizationOperator τ E) from
    ⟨hInject, (LinearMap.injective_iff_surjective
      (f := (stationaryNormalizationOperator τ E).toLinearMap)).mp hInject⟩
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm (fun X hX ↦ ?_) bot_le
  have hzero : X - E X + trace X • τ = 0 := hX
  have htr : trace X = 0 := by
    simpa [trace_add, trace_sub, trace_smul, hTP, hτ] using congrArg trace hzero
  have hXfix : X ∈ (ContinuousLinearMap.id ℂ (StationaryMat D) - E).toLinearMap.ker := by
    simpa [htr] using hzero
  have hρfix : ρ ∈ (ContinuousLinearMap.id ℂ (StationaryMat D) - E).toLinearMap.ker := by
    simp [hfix]
  have hρne : ρ ≠ 0 := fun h ↦ by simp [h] at hρ
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hρfix hρne
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hXfix)
  have hc0 : c = 0 := by simpa [← hc, trace_smul, hρ] using htr
  simp [← hc, hc0]

private theorem trace_stationaryNormalizationOperator {D : ℕ}
    (τ : StationaryMat D) (E : StationaryMat D →L[ℂ] StationaryMat D)
    (hτ : trace τ = 1) (hTP : ∀ X, trace (E X) = trace X) (X : StationaryMat D) :
    trace (stationaryNormalizationOperator τ E X) = trace X := by
  simp [stationaryNormalizationOperator_apply, trace_add, trace_sub, trace_smul, hTP, hτ]

private theorem stationaryNormalizationOperator_inverse_apply {D : ℕ}
    (τ : StationaryMat D) (E : StationaryMat D →L[ℂ] StationaryMat D)
    (hunit : IsUnit (stationaryNormalizationOperator τ E)) :
    stationaryNormalizationOperator τ E
      (Ring.inverse (stationaryNormalizationOperator τ E) τ) = τ := by
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    congrArg (fun F : StationaryMat D →L[ℂ] StationaryMat D ↦ F τ)
      (Ring.mul_inverse_cancel (stationaryNormalizationOperator τ E) hunit)

private theorem stationaryNormalizationOperator_inverse_isFixed {D : ℕ}
    (τ : StationaryMat D) (E : StationaryMat D →L[ℂ] StationaryMat D)
    (hτ : trace τ = 1) (hTP : ∀ X, trace (E X) = trace X)
    (hunit : IsUnit (stationaryNormalizationOperator τ E)) :
    trace (Ring.inverse (stationaryNormalizationOperator τ E) τ) = 1 ∧
      E (Ring.inverse (stationaryNormalizationOperator τ E) τ) =
        Ring.inverse (stationaryNormalizationOperator τ E) τ := by
  have hF := stationaryNormalizationOperator_inverse_apply τ E hunit
  have htr : trace (Ring.inverse (stationaryNormalizationOperator τ E) τ) = 1 := by
    simpa only [trace_stationaryNormalizationOperator τ E hτ hTP, hτ] using congrArg trace hF
  refine ⟨htr, (sub_eq_zero.mp ?_).symm⟩
  exact add_right_cancel (show _ + τ = 0 + τ from by
    simpa only [stationaryNormalizationOperator_apply, htr, one_smul, zero_add] using hF)

private theorem stationaryNormalizationOperator_inverse_unique {D : ℕ}
    (τ : StationaryMat D) (E : StationaryMat D →L[ℂ] StationaryMat D)
    (hunit : IsUnit (stationaryNormalizationOperator τ E))
    (X : StationaryMat D) (hfix : E X = X) (htr : trace X = 1) :
    X = Ring.inverse (stationaryNormalizationOperator τ E) τ := by
  apply ((ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := StationaryMat D)
    (f := stationaryNormalizationOperator τ E)).mp hunit).1
  change stationaryNormalizationOperator τ E X =
    stationaryNormalizationOperator τ E (Ring.inverse (stationaryNormalizationOperator τ E) τ)
  simp only [stationaryNormalizationOperator_inverse_apply τ E hunit,
    stationaryNormalizationOperator_apply, hfix, sub_self, htr, one_smul, zero_add]

private theorem exists_local_continuous_stationaryDensity {T : Type*} [TopologicalSpace T]
    {D : ℕ} [NeZero D] (E : T → StationaryMat D →L[ℂ] StationaryMat D)
    (hE : Continuous E) (hPos : ∀ t, IsPositiveMap (E t).toLinearMap)
    (hTP : ∀ t, IsTracePreservingMap (E t).toLinearMap) (t₀ : T)
    (hdim : Module.finrank ℂ
      (LinearMap.ker (ContinuousLinearMap.id ℂ (StationaryMat D) - E t₀).toLinearMap) = 1) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∃ σ : S → StationaryMat D, Continuous σ ∧ ∀ t : S,
        (σ t).PosSemidef ∧ trace (σ t) = 1 ∧ E t (σ t) = σ t ∧
          ∀ X : StationaryMat D, E t X = X → trace X = 1 → X = σ t := by
  obtain ⟨ρ, hρ, hfix⟩ :=
    IsStationaryMap.exists_stationaryState_of_linear (E t₀).toLinearMap (hPos t₀) (hTP t₀)
  let : NormedRing (StationaryMat D →L[ℂ] StationaryMat D) :=
    ContinuousLinearMap.toNormedRing (𝕜 := ℂ) (E := StationaryMat D)
  let : SequentialSpace (StationaryMat D) :=
    inferInstanceAs (SequentialSpace (Fin D → Fin D → ℂ))
  let hComplete : CompleteSpace (StationaryMat D →L[ℂ] StationaryMat D) :=
    ContinuousLinearMap.instCompleteSpace (𝕜₁ := ℂ) (𝕜₂ := ℂ)
      (σ := RingHom.id ℂ) (E := StationaryMat D) (F := StationaryMat D)
  let : HasSummableGeomSeries (StationaryMat D →L[ℂ] StationaryMat D) :=
    @instHasSummableGeomSeriesOfCompleteSpace
      (StationaryMat D →L[ℂ] StationaryMat D) _ hComplete
  have hF : Continuous (fun t ↦ stationaryNormalizationOperator ρ (E t)) :=
    (continuous_const.sub hE).add continuous_const
  refine ⟨{t | IsUnit (stationaryNormalizationOperator ρ (E t))},
    (show IsOpen {F : StationaryMat D →L[ℂ] StationaryMat D | IsUnit F} from
      Units.isOpen (R := StationaryMat D →L[ℂ] StationaryMat D)).preimage hF,
    stationaryNormalizationOperator_isUnit ρ ρ (E t₀) hρ.2 hρ.2 hfix (hTP t₀) hdim,
    (fun t ↦ Ring.inverse (stationaryNormalizationOperator ρ (E t)) ρ), ?_, ?_⟩
  · apply Continuous.clm_apply ?_ continuous_const
    refine continuous_iff_continuousAt.mpr (fun t ↦ ?_)
    obtain ⟨u, hu⟩ := t.property
    exact (NormedRing.inverse_continuousAt u).comp_of_eq
      (hF.comp continuous_subtype_val).continuousAt hu.symm
  · intro t
    obtain ⟨η, hη, hηfix⟩ :=
      IsStationaryMap.exists_stationaryState_of_linear (E t).toLinearMap (hPos t) (hTP t)
    refine ⟨?_, (stationaryNormalizationOperator_inverse_isFixed ρ (E t) hρ.2 (hTP t)
      t.property).1, (stationaryNormalizationOperator_inverse_isFixed ρ (E t) hρ.2 (hTP t)
      t.property).2, stationaryNormalizationOperator_inverse_unique ρ (E t) t.property⟩
    simpa only [← stationaryNormalizationOperator_inverse_unique
      ρ (E t) t.property η hηfix hη.2]
      using hη.1

end Matrix

namespace MPSTensor

/-- A continuous unital tensor family has a unique, locally continuous normalized
adjoint stationary density near a point with one-dimensional adjoint fixed space.

Positivity is obtained from Wolf, Theorem 6.11, using uniqueness of the normalized
fixed matrix. The resulting density is permitted to change rank. -/
theorem exists_local_continuous_adjointStationaryDensity_of_unital
    {T : Type*} [TopologicalSpace T] {d D : ℕ} [NeZero D]
    (B : T → MPSTensor d D) (hB : Continuous B)
    (hUnital : ∀ t, Kraus.IsUnital (B t)) (t₀ : T)
    (hdim : Module.finrank ℂ
      (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM (B t₀))) = 1) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∃ σ : S → Matrix (Fin D) (Fin D) ℂ, Continuous σ ∧ ∀ t : S,
        (σ t).PosSemidef ∧ Matrix.trace (σ t) = 1 ∧
          Kraus.adjointMap (B t) (σ t) = σ t ∧
            ∀ X : Matrix (Fin D) (Fin D) ℂ,
              Kraus.adjointMap (B t) X = X → Matrix.trace X = 1 → X = σ t := by
  let E : T → Matrix.StationaryMat D →L[ℂ] Matrix.StationaryMat D :=
    fun t ↦ (Kraus.adjointMapLM (B t)).toContinuousLinearMap
  have hE : Continuous E := by
    refine continuous_clm_apply.mpr (fun X ↦ ?_)
    change Continuous (fun t ↦ ∑ i : Fin d, (B t i)ᴴ * X * B t i)
    exact continuous_finsetSum _ (fun i _ ↦
      ((((continuous_apply i).comp hB).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
        ((continuous_apply i).comp hB))
  have hPos : ∀ t, IsPositiveMap (E t).toLinearMap := fun t X hX ↦ by
    simpa [E, Kraus.adjointMapLM_apply, Kraus.adjointMap, Kraus.mapLM_apply, Kraus.map]
      using Kraus.isPositiveMap_mapLM (fun i ↦ (B t i)ᴴ) X hX
  have hTPK : ∀ t, Kraus.IsTP (fun i ↦ (B t i)ᴴ) := fun t ↦ by
    simpa [Kraus.IsTP, Kraus.IsUnital] using hUnital t
  have hTP : ∀ t, IsTracePreservingMap (E t).toLinearMap := fun t X ↦ by
    simpa [E, Kraus.adjointMapLM_apply, Kraus.adjointMap, Kraus.mapLM_apply, Kraus.map]
      using Kraus.isTracePreservingMap_mapLM_of_isTP (fun i ↦ (B t i)ᴴ) (hTPK t) X
  exact Matrix.exists_local_continuous_stationaryDensity E hE hPos hTP t₀ hdim

/-- A pointwise normalized adjoint stationary family is continuous near a parameter
where the adjoint fixed space has dimension one. Local positivity and uniqueness
follow from the normalized stationary branch constructed above (Wolf, Theorem 6.11).
This supplies the local density-continuity step discussed in SPC11, Appendix C,
under the explicit one-dimensional adjoint fixed-space hypothesis. -/
theorem exists_open_continuousOn_stationaryDensity_of_unital
    {T : Type*} [TopologicalSpace T] {d D : ℕ} [NeZero D]
    (B : T → MPSTensor d D) (hB : Continuous B)
    (hUnital : ∀ t, Kraus.IsUnital (B t))
    (σ : T → Matrix (Fin D) (Fin D) ℂ)
    (hTrace : ∀ t, Matrix.trace (σ t) = 1)
    (hFix : ∀ t, Kraus.adjointMap (B t) (σ t) = σ t) (t₀ : T)
    (hdim : Module.finrank ℂ
      (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM (B t₀))) = 1) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧ ContinuousOn σ S ∧
      ∀ t ∈ S, (σ t).PosSemidef ∧
        ∀ X : Matrix (Fin D) (Fin D) ℂ,
          Kraus.adjointMap (B t) X = X → Matrix.trace X = 1 → X = σ t := by
  obtain ⟨S, hS, ht₀, τ, hτcont, hτ⟩ :=
    exists_local_continuous_adjointStationaryDensity_of_unital B hB hUnital t₀ hdim
  have heq : ∀ t : S, σ t = τ t :=
    fun t ↦ (hτ t).2.2.2 (σ t) (hFix t) (hTrace t)
  refine ⟨S, hS, ht₀, continuousOn_iff_continuous_domRestrict.mpr
    (hτcont.congr (fun t ↦ (heq t).symm)), ?_⟩
  exact fun t ht ↦
    ⟨Eq.mp (congrArg Matrix.PosSemidef (heq ⟨t, ht⟩).symm) (hτ ⟨t, ht⟩).1,
      fun X hX htr ↦ ((hτ ⟨t, ht⟩).2.2.2 X hX htr).trans (heq ⟨t, ht⟩).symm⟩

end MPSTensor
