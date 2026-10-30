/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleNormGrowth
import TNLean.Spectral.MPVOverlapDecayRect

/-!
# Gram limits for the two periodic uncle ground states

The normalized injective blocks have periodic squared norms tending to one.
Full perturbation span forces strict mixed damping, so their actual periodic
inner product tends to zero. These are the actual finite ground vectors;
no Gram, asymptotic orthogonality, or transfer-gap premise is supplied.

Source: arXiv:1210.6613, Lemma exptransferoperator and the projection against
the two periodic sectors in Lemma lowenergystates, lines 1165–1295.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open scoped InnerProductSpace
open Filter

namespace MPSTensor

variable {d a b : ℕ}

/-- The actual periodic squared norm of a normalized injective source block
tends to one. This follows from the derived canonical transfer contraction,
not a supplied state-normalization limit. Source: arXiv:1210.6613,
Lemma exptransferoperator. -/
theorem uncleMPV_norm_sq_tendsto_one
    (A : MPSTensor d a) (hIA : Kraus.IsInjective A) (hUA : Kraus.mapLM A 1 = 1)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (htr : Matrix.trace ρ = 1)
    (hF : Kraus.adjointMap A ρ = ρ) :
    Tendsto (fun N ↦ ‖mpvState A N‖ ^ 2) atTop (nhds (1 : ℝ)) := by
  classical
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp at htr
  let : NeZero a := ⟨ha⟩
  let V := Matrix (Fin a) (Fin a) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let : FiniteDimensional ℂ (V →L[ℂ] V) := Φ.toLinearEquiv.finiteDimensional
  let P : V →ₗ[ℂ] V := uncleDensityProjection ρ
  let E := Kraus.mapLM A
  let tr : (V →L[ℂ] V) →L[ℂ] ℂ :=
    ((LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap
  obtain ⟨C, r, hC, hr, hr1, hdec⟩ :=
    uncleTransfer_pow_sub_projection_bound A hIA hUA ρ htr hF
  have hsmall : Tendsto (fun N ↦ Φ (E ^ N - P)) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ ↦ C * r ^ N)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro X
      change ‖((Kraus.mapLM A) ^ N) X - Matrix.trace (ρ * X) • 1‖ ≤ C * r ^ N * ‖X‖
      exact hdec N hN X
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).const_mul C
  have htrace0 : Tendsto (fun N ↦ tr (Φ (E ^ N - P))) atTop (nhds (0 : ℂ)) := by
    simpa only [Function.comp_def, map_zero] using (tr.continuous.tendsto 0).comp hsmall
  have htrace_eq (N : ℕ) : tr (Φ (E ^ N - P)) = LinearMap.trace ℂ V (E ^ N) - 1 := by
    change LinearMap.trace ℂ V (E ^ N - P) = _
    rw [map_sub]
    change LinearMap.trace ℂ V (E ^ N) -
      LinearMap.trace ℂ V ((uncleDensityFunctional ρ).smulRight (1 : V)) = _
    rw [LinearMap.trace_smulRight]
    change LinearMap.trace ℂ V (E ^ N) - Matrix.trace (ρ * (1 : V)) = _
    rw [Matrix.mul_one, htr]
  have htrace : Tendsto (fun N ↦ LinearMap.trace ℂ V (E ^ N)) atTop (nhds (1 : ℂ)) :=
    tendsto_sub_nhds_zero_iff.mp (htrace0.congr htrace_eq)
  have hnorm (N : ℕ) : (LinearMap.trace ℂ V (E ^ N)).re = ‖mpvState A N‖ ^ 2 := by
    have htraceN : LinearMap.trace ℂ V (E ^ N) = mpvOverlap A A N := by
      change LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) ((Kraus.mapLM A) ^ N) = _
      simpa only [Kraus.mixedMapLM_self] using
        trace_mixedMapLM_rect_pow_eq_mpvOverlap A A N
    rw [htraceN]
    rw [mpvOverlap_eq_star_mpvInner, mpvInner, Complex.star_def, Complex.conj_re]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp htrace
  simpa only [Complex.one_re] using hre.congr hnorm

/-- The actual two periodic source ground vectors become orthogonal, with
both squared norms tending to one. The full perturbation witness and
normalized canonical data derive every transfer and Gram condition.
Source: arXiv:1210.6613, Lemmas exptransferoperator and lowenergystates. -/
theorem uncleGroundGram_tendsto
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L))
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef) (htrA : Matrix.trace ρA = 1)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef) (htrB : Matrix.trace ρB = 1)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB) :
    Tendsto (fun N ↦ ‖mpvState A N‖ ^ 2) atTop (nhds (1 : ℝ)) ∧
      Tendsto (fun N ↦ ‖mpvState B N‖ ^ 2) atTop (nhds (1 : ℝ)) ∧
      Tendsto (fun N ↦ ⟪mpvState A N, mpvState B N⟫_ℂ) atTop (nhds (0 : ℂ)) := by
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp at htrA
  have hb : b ≠ 0 := by
    intro hb
    subst b
    simp at htrB
  let : NeZero a := ⟨ha⟩
  let : NeZero b := ⟨hb⟩
  obtain ⟨hIA, hIB⟩ := uncleBoundaryLetter_isInjective_diagonal_blocks A B R L hPert
  refine ⟨uncleMPV_norm_sq_tendsto_one A hIA hUA ρA htrA hFA,
    uncleMPV_norm_sq_tendsto_one B hIB hUB ρB htrB hFB, ?_⟩
  have hgap := uncleBoundaryLetter_mixedMapSpectralRadius_lt_one
    A B R L hPert hUA hUB ρA hρA ρB hρB hFA hFB
  have hOverlap : Tendsto (fun N ↦ mpvOverlap A B N) atTop (nhds (0 : ℂ)) := by
    apply mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one A B
    simpa only [Kraus.mixedMapSpectralRadius, spectralRadius,
      AlgEquiv.quasispectrum_eq] using hgap
  simpa only [mpvOverlap_eq_star_mpvInner, star_star, mpvInner, star_zero] using hOverlap.star

end MPSTensor
