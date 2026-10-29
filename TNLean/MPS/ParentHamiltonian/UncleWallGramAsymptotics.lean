/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleWallGram
import QICLean.Analysis.SpectralRadiusPowerDecay
import QICLean.Kraus.MixedMap.SpectralRadius
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The linear limiting coefficient of a moving wall

The source mixed spectral-radius condition makes the genuine rectangular
correlation series converge. Its contraction defines the linear limiting
coefficient of the actual wall Gram weight. Cesàro convergence of the exact
Gram increments proves the normalized limit without assuming norm growth.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1230–1265.
Strict positivity of this coefficient for generic perturbations and the
separating-transfer estimate for the two-wall trial are separate results.
-/

open scoped Matrix BigOperators ComplexOrder TNOperatorSpace Topology
open Filter

namespace MPSTensor

variable {d a b : ℕ}

/-- The genuine mixed-transfer series entering the source wall norm
coefficient. Its convergence follows below from the source strict mixed
spectral-radius condition; arXiv:1210.6613, proof of Lemma lowenergystates. -/
noncomputable def uncleWallCorrelationLimit (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) : Matrix (Fin a) (Fin b) ℂ :=
  ∑' k : ℕ, ((Kraus.mixedMapLM A B) ^ k) (uncleWallSeed B R)

/-- The explicit linear limiting coefficient of the source one-wall Gram
weight, formed from the convergent mixed-transfer series and actual wall
contractions; arXiv:1210.6613, proof of Lemma lowenergystates. -/
noncomputable def uncleWallNormSlope (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) : ℂ :=
  Matrix.trace (ρ * ∑ i, R i * (R i)ᴴ) +
    uncleWallCrossWeight A R ρ (uncleWallCorrelationLimit A B R) +
    star (uncleWallCrossWeight A R ρ (uncleWallCorrelationLimit A B R))

private theorem mixedContinuous_pow_apply (A : MPSTensor d a) (B : MPSTensor d b)
    (n : ℕ) (X : Matrix (Fin a) (Fin b) ℂ) :
    ((Module.End.toContinuousLinearMap (Matrix (Fin a) (Fin b) ℂ)
        (Kraus.mixedMapLM A B)) ^ n) X = ((Kraus.mixedMapLM A B) ^ n) X := by
  exact congrArg (fun F : Matrix (Fin a) (Fin b) ℂ →L[ℂ]
      Matrix (Fin a) (Fin b) ℂ ↦ F X)
    (map_pow (Module.End.toContinuousLinearMap (Matrix (Fin a) (Fin b) ℂ))
      (Kraus.mixedMapLM A B) n).symm

/-- The actual mixed correlation series is summable under spectral radius
strictly below one. The proof uses geometric power decay from Gelfand's
formula, not the stronger condition that the operator norm is below one;
arXiv:1210.6613, Lemma offdiagonal-damping and the norm calculation. -/
theorem uncleWallCorrelation_summable (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    Summable (fun k : ℕ ↦ ((Kraus.mixedMapLM A B) ^ k) (uncleWallSeed B R)) := by
  let F := Module.End.toContinuousLinearMap (Matrix (Fin a) (Fin b) ℂ)
    (Kraus.mixedMapLM A B)
  obtain ⟨K, r, _, hr, hr1, hbound⟩ :=
    geometric_apply_bound_of_spectralRadius_lt_one F hSpect
  have hgeom : Summable (fun k : ℕ ↦ K * r ^ k * ‖uncleWallSeed B R‖) :=
    ((summable_geometric_of_lt_one hr.le hr1).mul_left K).mul_right ‖uncleWallSeed B R‖
  apply hgeom.of_norm_bounded
  intro k
  simpa only [F, mixedContinuous_pow_apply] using hbound k (uncleWallSeed B R)

/-- Under source unital right-block normalization and strict mixed-transfer
damping, the actual finite wall correlation converges to its mixed series;
arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallCorrelation_tendsto (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (hB : Kraus.mapLM B 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    Tendsto (fun n : ℕ ↦ uncleWallCorrelation A B R n) atTop
      (𝓝 (uncleWallCorrelationLimit A B R)) := by
  have h := (uncleWallCorrelation_summable A B R hSpect).hasSum.tendsto_sum_nat
  simpa only [← uncleWallCorrelation_eq_sum A B R hB, uncleWallCorrelationLimit] using h

private theorem uncleWallGramWeight_eq_sum_increments
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.IsHermitian)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1) (n : ℕ) :
    uncleWallGramWeight A B R ρ n = ∑ k ∈ Finset.range n,
      (Matrix.trace (ρ * ∑ i, R i * (R i)ᴴ) +
        uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R k) +
        star (uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R k))) := by
  induction n with
  | zero => simp [uncleWallGramWeight]
  | succ n ih =>
      rw [uncleWallGramWeight_succ A B R ρ hρ hA hB, ih, Finset.sum_range_succ]
      ring

/-- The actual wall Gram weight divided by its length converges to the
explicit mixed-series coefficient under the source stationary/unital
normalizations and strict mixed spectral-radius condition. This does not
assert strict positivity or a genericity statement; arXiv:1210.6613,
proof of Lemma lowenergystates, linear asymptotic of the wall coefficient. -/
theorem uncleWallGramWeight_normalized_tendsto
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.IsHermitian)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • uncleWallGramWeight A B R ρ n) atTop
      (𝓝 (uncleWallNormSlope A B R ρ)) := by
  let ℓ := (uncleWallCrossWeight A R ρ).toContinuousLinearMap
  have hcross : Tendsto (fun n : ℕ ↦
      uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R n)) atTop
      (𝓝 (uncleWallCrossWeight A R ρ (uncleWallCorrelationLimit A B R))) :=
    (ℓ.continuous.tendsto _).comp (uncleWallCorrelation_tendsto A B R hB hSpect)
  have hinc : Tendsto (fun n : ℕ ↦
      Matrix.trace (ρ * ∑ i, R i * (R i)ᴴ) +
        uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R n) +
        star (uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R n))) atTop
      (𝓝 (uncleWallNormSlope A B R ρ)) :=
    (tendsto_const_nhds.add hcross).add hcross.star
  have hmean := hinc.cesaro_smul
  simpa only [← uncleWallGramWeight_eq_sum_increments A B R ρ hρ hA hB] using hmean

end MPSTensor
