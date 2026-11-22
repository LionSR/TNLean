/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Uncle.UncleNormFactorization
import TNLean.MPS.ParentHamiltonian.Uncle.UncleWallGramGeneric
import TNLean.MPS.ParentHamiltonian.Uncle.UncleMixedDamping
import TNLean.MPS.CanonicalForm.FixedPointApproximation.SecondOrderOverlap
import TNLean.MPS.Transfer.Spectrum.MPVOverlapTrace

/-!
# Generic quadratic norm growth of the two-wall trial

The exact source trial has normalized squared norm converging to the product
of its two wall coefficients. Their derived generic positivity gives
both quadratic upper and lower bounds for almost every pair of walls.
The individual diagonal block injectivities and strict mixed damping are
derived from the full perturbation span and canonical normalization,
rather than supplied as extra hypotheses. The bounds read
\(c(N+1)^2\le\|\varphi_N\|^2\le C(N+1)^2\) for all large \(N\).

Source: arXiv:1210.6613, Lemma lowenergystates, first assertion,
lines 1196–1265. The ground-space overlaps and spectral variational
argument remain separate from this norm estimate.

## Gram limits for the two periodic uncle ground states

The normalized injective blocks have periodic squared norms tending to one.
Full perturbation span forces strict mixed damping, so their periodic
inner product tends to zero. These are the finite ground vectors;
no Gram, asymptotic orthogonality, or transfer-gap premise is supplied.
In formulas, \(\|\psi_A^N\|^2\to1\), \(\|\psi_B^N\|^2\to1\) and
\(\langle\psi_A^N,\psi_B^N\rangle\to0\) as \(N\to\infty\).

Source: arXiv:1210.6613, Lemma exptransferoperator and the projection against
the two periodic sectors in Lemma lowenergystates, lines 1165–1295.
-/

section

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open MeasureTheory Filter

namespace MPSTensor

variable {d a b : ℕ}

/-- Full source perturbation span implies injectivity of both diagonal
blocks, by the two surjective diagonal block projections.
Source: arXiv:1210.6613, injective perturbations and Lemma lowenergystates. -/
theorem uncleBoundaryLetter_isInjective_diagonal_blocks
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) :
    Kraus.IsInjective A ∧ Kraus.IsInjective B := by
  classical
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  let fA : Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ :=
    { toFun := fun M ↦ M.submatrix (fun i ↦ e (Sum.inl i)) (fun j ↦ e (Sum.inl j))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let fB : Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ :=
    { toFun := fun M ↦ M.submatrix (fun i ↦ e (Sum.inr i)) (fun j ↦ e (Sum.inr j))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hproj {D : ℕ}
      (f : Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
      (K : MPSTensor d D) (hf : Function.Surjective f)
      (hK : ∀ i, f (uncleBoundaryLetter A B R L i) = K i) : Kraus.IsInjective K := by
    have hmap : (Submodule.span ℂ (Set.range (uncleBoundaryLetter A B R L))).map f =
        Submodule.span ℂ (Set.range K) := by
      rw [Submodule.map_span]
      congr 1
      ext X
      constructor
      · rintro ⟨M, ⟨i, rfl⟩, hM⟩
        exact ⟨i, (hK i).symm.trans hM⟩
      · rintro ⟨i, rfl⟩
        exact ⟨uncleBoundaryLetter A B R L i, ⟨i, rfl⟩, hK i⟩
    change Submodule.span ℂ (Set.range K) = ⊤
    rw [hPert.span_eq_top, Submodule.map_top] at hmap
    rw [← hmap, LinearMap.range_eq_top]
    exact hf
  constructor
  · apply hproj fA A
    · intro X
      refine ⟨uncleBlockMatrix (a := a) (b := b) X 0 0 0, ?_⟩
      ext i j
      simp [fA, e, uncleBlockMatrix, Matrix.reindex_apply]
    · intro i
      ext j k
      simp [fA, e, uncleBoundaryLetter, uncleBlockMatrix, Matrix.reindex_apply]
  · apply hproj fB B
    · intro X
      refine ⟨uncleBlockMatrix (a := a) (b := b) 0 0 0 X, ?_⟩
      ext i j
      simp [fB, e, uncleBlockMatrix, Matrix.reindex_apply]
    · intro i
      ext j k
      simp [fB, e, uncleBoundaryLetter, uncleBlockMatrix, Matrix.reindex_apply]

/-- A positive value of the limiting coefficient product gives
quadratic upper and lower bounds on the squared norm of the source
trial. The following generic theorem derives this positivity without
assuming it. Source: arXiv:1210.6613, Lemma lowenergystates, first assertion. -/
theorem uncleTwoWallTrialSource_eventual_norm_bounds [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hIA : Kraus.IsInjective A) (hIB : Kraus.IsInjective B)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef) (htrA : Matrix.trace ρA = 1)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef) (htrB : Matrix.trace ρB = 1)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB)
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1)
    (hκ : 0 < (uncleWallNormSlope A B R ρA * uncleWallNormSlope B A L ρB).re) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      c * ((N + 1 : ℕ) : ℝ) ^ 2 ≤
        ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N)‖ ^ 2 ∧
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N)‖ ^ 2 ≤ C * ((N + 1 : ℕ) : ℝ) ^ 2 := by
  let κ := (uncleWallNormSlope A B R ρA * uncleWallNormSlope B A L ρB).re
  have hlim := uncleTwoWallTrialSource_normalized_norm_sq_tendsto
    A B R L hIA hIB hUA hUB ρA hρA htrA ρB hρB htrB hFA hFB hAB hBA
  refine ⟨κ / 2, κ + 1, by dsimp [κ]; linarith, by dsimp [κ]; linarith, ?_⟩
  have hlow := hlim.eventually (eventually_gt_nhds (show κ / 2 < κ by dsimp [κ]; linarith))
  have hupp := hlim.eventually (eventually_lt_nhds (show κ < κ + 1 by linarith))
  filter_upwards [hlow, hupp] with N hNlow hNupp
  have hden : 0 < ((N + 1 : ℕ) : ℝ) ^ 2 := by positivity
  exact ⟨(le_div_iff₀ hden).mp hNlow.le, (div_le_iff₀ hden).mp hNupp.le⟩

/-- For almost every pair of walls the source trial has quadratic
squared-norm growth. The coefficient product is positive by the derived
proper-radical exceptional-set theorem, not by a norm-growth premise.
A single additive Haar measure on the pair space is used. Source:
arXiv:1210.6613, Lemma lowenergystates, first assertion, lines 1196–1265. -/
theorem uncleTwoWallTrialSource_ae_quadratic_norm_growth
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀))
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef) (htrA : Matrix.trace ρA = 1)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef) (htrB : Matrix.trace ρB = 1)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB)
    (μ : Measure ((Fin d → Matrix (Fin a) (Fin b) ℂ) ×
      (Fin d → Matrix (Fin b) (Fin a) ℂ))) [Measure.IsAddHaarMeasure μ] :
    ∀ᵐ P ∂μ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      c * ((N + 1 : ℕ) : ℝ) ^ 2 ≤
        ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B P.1 P.2 N)‖ ^ 2 ∧
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B P.1 P.2 N)‖ ^ 2 ≤ C * ((N + 1 : ℕ) : ℝ) ^ 2 := by
  have : NeZero a := Matrix.neZero_of_trace_eq_one htrA
  have : NeZero b := Matrix.neZero_of_trace_eq_one htrB
  obtain ⟨hIA, hIB⟩ := uncleBoundaryLetter_isInjective_diagonal_blocks A B R₀ L₀ hPert
  have hAB := uncleBoundaryLetter_mixedMapSpectralRadius_lt_one
    A B R₀ L₀ hPert hUA hUB ρA hρA ρB hρB hFA hFB
  have hBA := uncleBoundaryLetter_mixedMapSpectralRadius_reverse_lt_one
    A B R₀ L₀ hPert hUA hUB ρA hρA ρB hρB hFA hFB
  have hae := uncleWallNormSlope_pair_ae_pos A B R₀ L₀ hPert
    ρA hρA ρB hρB hFA hFB hUA hUB hAB hBA μ
  filter_upwards [hae] with P hP
  have hκ : 0 < (uncleWallNormSlope A B P.1 ρA * uncleWallNormSlope B A P.2 ρB).re := by
    rw [Complex.mul_re, ← (Complex.pos_iff.mp hP.1).2, ← (Complex.pos_iff.mp hP.2).2,
      mul_zero, sub_zero]
    exact mul_pos (Complex.pos_iff.mp hP.1).1 (Complex.pos_iff.mp hP.2).1
  exact uncleTwoWallTrialSource_eventual_norm_bounds A B P.1 P.2 hIA hIB hUA hUB
    ρA hρA htrA ρB hρB htrB hFA hFB hAB hBA hκ

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open scoped InnerProductSpace
open Filter

namespace MPSTensor

variable {d a b : ℕ}

/-- The periodic squared norm of a normalized injective source block
tends to one, \(\|\psi_A^N\|^2\to1\). This follows from the derived canonical transfer contraction,
not a supplied state-normalization limit. Source: arXiv:1210.6613,
Lemma exptransferoperator. -/
theorem uncleMPV_norm_sq_tendsto_one
    (A : MPSTensor d a) (hIA : Kraus.IsInjective A) (hUA : Kraus.mapLM A 1 = 1)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (htr : Matrix.trace ρ = 1)
    (hF : Kraus.adjointMap A ρ = ρ) :
    Tendsto (fun N ↦ ‖mpvState A N‖ ^ 2) atTop (nhds (1 : ℝ)) := by
  classical
  have : NeZero a := Matrix.neZero_of_trace_eq_one htr
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

/-- The two periodic source ground vectors become orthogonal,
\(\langle\psi_A^N,\psi_B^N\rangle\to0\), with both squared norms tending
to one. The full perturbation witness and
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
  have : NeZero a := Matrix.neZero_of_trace_eq_one htrA
  have : NeZero b := Matrix.neZero_of_trace_eq_one htrB
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

end
