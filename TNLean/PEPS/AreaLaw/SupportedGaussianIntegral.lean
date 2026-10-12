/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.ProjectedRelativeEvolution
import TNLean.PEPS.AreaLaw.RegionOperatorLocalization
import QICLean.Analysis.GaussianFilter.MatrixIntegral

/-!
# A supported Gaussian approximation between two Hamiltonians

Project both the evolved observable and the relative-evolution generator
onto the same graph neighbourhood. The projected differential equation
constructs a unitary path on this neighbourhood. Integrating the product
against the original restricted Gaussian measure gives a supported
operator, with norm and approximation bounds uniform in the variance.

The path is chosen before the variance and time cutoff. Neither a
propagator nor an approximating operator is supplied as a hypothesis.
Only the actual supports of the input observable and Hamiltonian
difference enter. No spectral gap or information assumption is used.

## References

OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
September 24, 2026, Section 2, lines 513–562, in the proof of
eq:info-local-two-sided. Source revision:
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The common projection region is the neighbourhood of the union of the
two input supports, as in the support conclusion of that argument.
Independently formalized; no upstream Lean proof text is reused.
-/

open MeasureTheory ProbabilityTheory QuantumCircuit
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace TNLean.PEPS.AreaLaw

/-- The actual projected relative evolution constructs a supported
approximation to every truncated two-Hamiltonian Gaussian filter.
The same path works for all variances and nonnegative time cutoffs.
Source: polynomial-PEPS, Section 2, eq:info-local-two-sided,
lines 513–562. -/
theorem exists_supported_gaussian_integral (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (J : ℝ) :
    ∃ C v c : ℝ, 0 < C ∧ 0 < v ∧ 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (g : LocalHamiltonian Λ q R J)
        (H W : Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
        H.IsHermitian →
        ∀ Q Z : Finset (Site Λ),
          W ∈ supportedOperators q (Q : Set (Site Λ)) →
          g.operator - H ∈ supportedOperators q (Z : Set (Site Λ)) →
          ∀ l : ℕ,
            let B := graphNeighborhood Λ l (Q ∪ Z)
            ∃ U : ℝ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
              U 0 = 1 ∧
              (∀ t, HasDerivAt U
                ((Complex.I • siteExpectation q B
                  (heisenbergEvolution g.operator t (g.operator - H))) * U t) t) ∧
              (∀ t, U t ∈ Matrix.unitaryGroup (Configuration Λ q) ℂ) ∧
              (∀ t, U t ∈ supportedOperators q (B : Set (Site Λ))) ∧
              ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
                let M := ∫ t : ℝ in Set.Icc (-T) T,
                  siteExpectation q B (heisenbergEvolution g.operator t W) * U t
                    ∂gaussianReal 0 η
                M ∈ supportedOperators q (B : Set (Site Λ)) ∧
                ‖M‖ ≤ ‖W‖ ∧
                ‖M - GaussianFilter.gaussianIntertwinerTruncated η T g.operator H W‖ ≤
                  ‖W‖ * C * (Λ.card : ℝ) * (1 + ‖g.operator - H‖ * T) *
                    Real.exp (v * T - c * l) := by
  classical
  obtain ⟨C, v, c, hC, hv, hc, hlocal⟩ :=
    exists_quasilocal_region_localization q hq R J
  refine ⟨C, v, c, hC, hv, hc, ?_⟩
  intro Λ g H W hH Q Z hW hD l B
  have : NeZero q := ⟨by omega⟩
  obtain ⟨U, hU0, hU, hunit, hsupport, huniq, hcompare⟩ :=
    exists_supported_projected_relative_evolution q B g.operator_isHermitian hH
  refine ⟨U, hU0, hU, hunit, hsupport, fun η T hT ↦ ?_⟩
  have hnorm (t : ℝ) :
      ‖siteExpectation q B (heisenbergEvolution g.operator t W) * U t‖ ≤ ‖W‖ :=
    (CStarRing.norm_mul_mem_unitary _ (hunit t)).trans_le
      (MatrixEvolution.norm_projectedGenerator_le (siteExpectationLM q B)
        (norm_siteExpectation_le B) g.operator_isHermitian W t)
  have hcont : Continuous (fun t : ℝ ↦
      siteExpectation q B (heisenbergEvolution g.operator t W) * U t) :=
    (MatrixEvolution.contDiff_projectedGenerator (siteExpectationLM q B)
      g.operator W 0).continuous.mul
      (show Differentiable ℝ U from fun t ↦ (hU t).differentiableAt).continuous
  have hint : Integrable (fun t : ℝ ↦
      siteExpectation q B (heisenbergEvolution g.operator t W) * U t)
      (gaussianReal 0 η) :=
    (integrable_const ‖W‖).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hnorm)
  have hfix (t : ℝ) : siteExpectation q B
      (siteExpectation q B (heisenbergEvolution g.operator t W) * U t) =
      siteExpectation q B (heisenbergEvolution g.operator t W) * U t :=
    siteExpectation_of_mem_supportedOperators B
      (mul_mem_supportedOperators (siteExpectation_mem_supportedOperators B _) (hsupport t))
  have hMint : siteExpectation q B
      (∫ t : ℝ in Set.Icc (-T) T,
        siteExpectation q B (heisenbergEvolution g.operator t W) * U t ∂gaussianReal 0 η) =
      ∫ t : ℝ in Set.Icc (-T) T,
        siteExpectation q B (heisenbergEvolution g.operator t W) * U t ∂gaussianReal 0 η :=
    ((siteExpectationLM q B).toContinuousLinearMap.integral_comp_comm
      (hint.restrict (s := Set.Icc (-T) T))).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall hfix))
  refine ⟨hMint ▸ siteExpectation_mem_supportedOperators B _,
    (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
      (fun t _ ↦ hnorm t)).trans
      (mul_le_of_le_one_right (norm_nonneg W) measureReal_le_one), ?_⟩
  have hnear (A : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
      (hA : A ∈ supportedOperators q ((Q ∪ Z : Finset (Site Λ)) : Set (Site Λ)))
      (t : ℝ) (ht : |t| ≤ T) :
      ‖heisenbergEvolution g.operator t A -
        siteExpectation q B (heisenbergEvolution g.operator t A)‖ ≤
        ‖A‖ * (C * (Λ.card : ℝ) * Real.exp (v * T - c * l)) :=
    (hlocal Λ g (Q ∪ Z) A hA l t).trans
      (mul_le_mul_of_nonneg_left
        ((min_le_right _ _).trans
          (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr
              (sub_le_sub_right (mul_le_mul_of_nonneg_left ht hv.le) _))
            (mul_nonneg hC.le (Nat.cast_nonneg _))))
        (norm_nonneg A))
  have hrelative (t : ℝ) (ht : |t| ≤ T) :
      ‖Matrix.hermitianUnitaryPath g.operator t * Matrix.hermitianUnitaryPath H (-t) -
        U t‖ ≤ ‖g.operator - H‖ *
          (C * (Λ.card : ℝ) * Real.exp (v * T - c * l)) * |t| :=
    hcompare t _ (fun s hs ↦ hnear (g.operator - H)
      (supportedOperators_mono (fun _ hx ↦ Finset.mem_union_right Q hx) hD) s
      ((show |s| ≤ |t| by
        simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs).trans ht))
  have hfactor (t : ℝ) :
      heisenbergEvolution g.operator t W *
          (Matrix.hermitianUnitaryPath g.operator t * Matrix.hermitianUnitaryPath H (-t)) =
        Matrix.hermitianUnitaryPath g.operator t * W * Matrix.hermitianUnitaryPath H (-t) := by
    rw [heisenbergEvolution_eq_hermitianUnitaryPath,
      Matrix.mul_assoc (Matrix.hermitianUnitaryPath g.operator t * W),
      ← Matrix.mul_assoc (Matrix.hermitianUnitaryPath g.operator (-t))
        (Matrix.hermitianUnitaryPath g.operator t),
      ← Matrix.hermitianUnitaryPath_add, neg_add_cancel,
      Matrix.hermitianUnitaryPath_zero, Matrix.one_mul]
  have hpoint (t : ℝ) (ht : |t| ≤ T) :
      ‖siteExpectation q B (heisenbergEvolution g.operator t W) * U t -
        Matrix.hermitianUnitaryPath g.operator t * W * Matrix.hermitianUnitaryPath H (-t)‖ ≤
        ‖W‖ * C * (Λ.card : ℝ) * (1 + ‖g.operator - H‖ * T) *
          Real.exp (v * T - c * l) := by
    refine (hfactor t) ▸ (norm_sub_le_norm_sub_add_norm_sub
      (siteExpectation q B (heisenbergEvolution g.operator t W) * U t)
      (heisenbergEvolution g.operator t W * U t)
      (heisenbergEvolution g.operator t W *
        (Matrix.hermitianUnitaryPath g.operator t * Matrix.hermitianUnitaryPath H (-t)))).trans ?_
    rw [← sub_mul, ← mul_sub, CStarRing.norm_mul_mem_unitary _ (hunit t),
      norm_sub_rev (siteExpectation q B (heisenbergEvolution g.operator t W))
        (heisenbergEvolution g.operator t W)]
    refine (add_le_add
      (hnear W (supportedOperators_mono (fun _ hx ↦ Finset.mem_union_left Z hx) hW) t ht)
      (norm_mul_le_of_le
        (show ‖heisenbergEvolution g.operator t W‖ ≤ ‖W‖ from
          (SpectralFilter.norm_hermitianUnitaryPath_conj g.operator_isHermitian W t).le)
        ((norm_sub_rev (U t)
          (Matrix.hermitianUnitaryPath g.operator t * Matrix.hermitianUnitaryPath H (-t))).trans_le
            (hrelative t ht)))).trans ?_
    refine (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ht
          (mul_nonneg (norm_nonneg (g.operator - H))
            (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg Λ.card))
              (Real.exp_pos (v * T - c * l)).le)))
        (norm_nonneg W))).trans_eq ?_
    done
  done

end TNLean.PEPS.AreaLaw
