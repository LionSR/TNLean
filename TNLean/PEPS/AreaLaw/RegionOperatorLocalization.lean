/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphPropagation

/-!
# Localization of an operator on an arbitrary physical region

The normalized partial-trace expectation onto a graph neighbourhood approximates
the time evolution of every operator supported on the original region. The
constants precede the domain, Hamiltonian, region and operator. No spectral gap
or entropy hypothesis is used in this operator estimate.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `02-information.tex`, equation
  `eq:info-operator-localization`, lines 498–508, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Lemma 4.1, `eq:quasilocal-lr-ce`.
-/

open QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw

/-- The prefactor `C₀(R) = 2 e^R · 2 · 2² 2! e^{1/2} / (1 - e^{-1/2})` of the graph-ball
localization bound for interactions of range `R`. The factor `2 e^R` comes from the chain
bound and `2 · 2² 2! e^{1/2} / (1 - e^{-1/2})` from summing it over spheres of size at most
`2 (d + 1)²` with decay rate `1/2`.

Source: OpenAI area law, Lemma 4.1, `eq:quasilocal-lr-ce` (`03-quasilocal.tex`,
lines 117–128); used for the constant `C` of `eq:info-lr` (polynomial-PEPS,
`02-information.tex`, lines 486–496). -/
noncomputable def graphBallLocalizationPrefactor (R : ℕ) : ℝ :=
  2 * Real.exp R * 2 * (2 ^ 2 * Nat.factorial 2 * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2))))

/-- The velocity `2 v_R μ_R J e^{2R}` of the graph-ball localization bound for interactions
of range `R` and term-norm bound `J`, with `v_R = 1 + 2R(R + 1)` sites per support and
`μ_R = 2^{v_R - 1}` supports through a site.

Source: OpenAI area law, Lemma 4.1 (`03-quasilocal.tex`, lines 70–112), with the budget
`eq:quasilocal-budget` (lines 31–39); used for the velocity `v` of `eq:info-lr`
(polynomial-PEPS, `02-information.tex`, lines 486–496). -/
noncomputable def graphBallLocalizationVelocity (R : ℕ) (J : ℝ) : ℝ :=
  2 * (1 + 2 * R * (R + 1) : ℕ) * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J) *
    Real.exp (2 * R)

theorem graphBallLocalizationPrefactor_pos (R : ℕ) : 0 < graphBallLocalizationPrefactor R := by
  have h : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have : 0 < 1 - Real.exp (-(1 / 2)) := by linarith
  unfold graphBallLocalizationPrefactor
  positivity

theorem graphBallLocalizationVelocity_nonneg (R : ℕ) {J : ℝ} (hJ : 0 ≤ J) :
    0 ≤ graphBallLocalizationVelocity R J := by
  unfold graphBallLocalizationVelocity
  positivity

/-- **Localization on an arbitrary region, with explicit constants.** For a finite-range
Hamiltonian of range `R` and term-norm bound `J` on a finite domain `Λ`, an operator `A`
supported on `S` satisfies
`‖τ_t(A) - E_{N_l(S)}(τ_t(A))‖ ≤ ‖A‖ min(2, 2 C₀(R) |Λ| e^{v(R, J)|t| - l/2})`, where
`C₀(R)` is `graphBallLocalizationPrefactor R` and `v(R, J)` is
`graphBallLocalizationVelocity R J`. It applies the one-site graph-ball bound at negative
time and averages over sites outside the graph neighbourhood of `S`; the region may be empty.

Source: polynomial-PEPS `eq:info-operator-localization` (`02-information.tex`,
lines 498–508), with the constants of OpenAI area law, Lemma 4.1. -/
theorem quasilocal_region_localization (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J : ℝ)
    (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J) (S : Finset (Site Λ))
    (A : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
    (hA : A ∈ supportedOperators q (S : Set (Site Λ))) (l : ℕ) (t : ℝ) :
    ‖heisenbergEvolution h.operator t A -
        siteExpectation q (graphNeighborhood Λ l S) (heisenbergEvolution h.operator t A)‖ ≤
      ‖A‖ * min 2 (2 * graphBallLocalizationPrefactor R * (Λ.card : ℝ) *
        Real.exp (graphBallLocalizationVelocity R J * |t| - 1 / 2 * l)) := by
  classical
  set C := graphBallLocalizationPrefactor R
  set v := graphBallLocalizationVelocity R J
  have hC : 0 < C := graphBallLocalizationPrefactor_pos R
  have hdisj (y : Site Λ) (hy : y ∉ graphNeighborhood Λ l S) :
      Disjoint (S : Set (Site Λ)) (graphBall (domainGraph Λ) y l : Set (Site Λ)) :=
    Set.disjoint_left.mpr fun x hxS hxball =>
      hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, x, hxS,
        (exists_walk_length_le_iff_edist_le Λ l x y).mpr
          (by simpa only [SimpleGraph.edist_comm] using (mem_graphBall.mp hxball))⟩)
  have hK : Complex.I • h.operator ∈
      skewAdjoint (Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :=
    h.operator_isHermitian.isSelfAdjoint.I_smul_mem_skewAdjoint (K := ℂ)
  have hreverse (U : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :
      ‖heisenbergEvolution h.operator t A * U -
        U * heisenbergEvolution h.operator t A‖ =
      ‖A * heisenbergEvolution h.operator (-t) U -
        heisenbergEvolution h.operator (-t) U * A‖ := by
    simpa only [heisenbergEvolution_def, neg_neg] using
      norm_exp_commutator_eq (Complex.I • h.operator) hK A U t
  have : NeZero q := ⟨by omega⟩
  have hnear (y : Site Λ) (U : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
      (hU : U ∈ supportedOperators q ({y} : Set (Site Λ)))
      (hUu : U ∈ unitary (Matrix (Configuration Λ q) (Configuration Λ q) ℂ)) :
      ‖heisenbergEvolution h.operator (-t) U -
        siteExpectation q (graphBall (domainGraph Λ) y l)
          (heisenbergEvolution h.operator (-t) U)‖ ≤
        C * Real.exp (v * |t| - 1 / 2 * l) := by
    have hestimate := h.norm_sub_siteExpectation_graphBall_le
      ⟨{y}, isAdmissibleSupport_singleton Λ R y⟩ (Finset.mem_singleton_self y)
      (by simpa only [Finset.coe_singleton] using hU) l (-t)
    rw [CStarRing.norm_of_mem_unitary hUu, one_mul, abs_neg,
      show (l : ℝ) / 2 = 1 / 2 * l by ring] at hestimate
    exact hestimate.trans (min_le_right _ _)
  have hcommute (y : Site Λ) (hy : y ∉ graphNeighborhood Λ l S)
      (U : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :
      Commute A (siteExpectation q (graphBall (domainGraph Λ) y l)
        (heisenbergEvolution h.operator (-t) U)) :=
    commute_of_mem_supportedOperators (hdisj y hy) hA
      (siteExpectation_mem_supportedOperators _ _)
  have hε (y : Site Λ) (hy : y ∉ graphNeighborhood Λ l S)
      (U : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
      (hU : U ∈ supportedOperators q ({y} : Set (Site Λ)))
      (hUu : U ∈ unitary (Matrix (Configuration Λ q) (Configuration Λ q) ℂ)) :
      ‖heisenbergEvolution h.operator t A * U -
        U * heisenbergEvolution h.operator t A‖ ≤
        2 * (C * Real.exp (v * |t| - 1 / 2 * l)) * ‖A‖ := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, (hcommute y hy U).eq,
      sub_sub_sub_cancel_right, hreverse U] using
      (norm_commutator_le A (heisenbergEvolution h.operator (-t) U -
        siteExpectation q (graphBall (domainGraph Λ) y l)
          (heisenbergEvolution h.operator (-t) U))).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hnear y U hU hUu) zero_le_two) (norm_nonneg A))
  have hExp : ‖heisenbergEvolution h.operator t A -
      siteExpectation q (graphNeighborhood Λ l S) (heisenbergEvolution h.operator t A)‖ ≤
      ‖A‖ * (2 * C * (Λ.card : ℝ) * Real.exp (v * |t| - 1 / 2 * l)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      mul_assoc, mul_comm, mul_left_comm] using
      (norm_sub_siteExpectation_le (graphNeighborhood Λ l S)
        (heisenbergEvolution h.operator t A)
        (fun _ ↦ 2 * (C * Real.exp (v * |t| - 1 / 2 * l)) * ‖A‖) hε).trans
        (Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ by positivity))
  have hτnorm : ‖heisenbergEvolution h.operator t A‖ = ‖A‖ :=
    letI : NormedAlgebra ℚ (Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :=
      .restrictScalars ℚ ℝ (Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
    (CStarRing.norm_mul_mem_unitary
      (NormedSpace.exp (t • (Complex.I • h.operator)) * A)
      (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem (-t) hK))).trans
      (CStarRing.norm_mem_unitary_mul A
        (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hK)))
  have hTwo : ‖heisenbergEvolution h.operator t A -
      siteExpectation q (graphNeighborhood Λ l S) (heisenbergEvolution h.operator t A)‖ ≤
      ‖A‖ * 2 := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add le_rfl (norm_siteExpectation_le _ _)).trans ?_
    simpa only [hτnorm, mul_two] using (le_refl (‖A‖ + ‖A‖))
  rw [mul_min_of_nonneg _ _ (norm_nonneg A)]
  exact le_min hTwo hExp

/-- Localization on an arbitrary region, including an empty region or domain, with
positive constants chosen before the domain, Hamiltonian, region and operator. It is the
explicit `TNLean.PEPS.AreaLaw.quasilocal_region_localization`, with the velocity raised to
be positive.

Source: polynomial-PEPS `eq:info-operator-localization`. The displayed domain
cardinality is sufficient for its square-grid specialization. -/
theorem exists_quasilocal_region_localization (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (J : ℝ) :
    ∃ C v c : ℝ, 0 < C ∧ 0 < v ∧ 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (S : Finset (Site Λ)) (A : Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
        A ∈ supportedOperators q (S : Set (Site Λ)) → ∀ (l : ℕ) (t : ℝ),
        ‖heisenbergEvolution h.operator t A -
            siteExpectation q (graphNeighborhood Λ l S)
              (heisenbergEvolution h.operator t A)‖ ≤
          ‖A‖ * min 2 (C * (Λ.card : ℝ) * Real.exp (v * |t| - c * l)) := by
  refine ⟨2 * graphBallLocalizationPrefactor R, max (graphBallLocalizationVelocity R J) 1,
    1 / 2, mul_pos two_pos (graphBallLocalizationPrefactor_pos R),
    lt_max_of_lt_right one_pos, one_half_pos, fun Λ h S A hA l t ↦ ?_⟩
  have hP := graphBallLocalizationPrefactor_pos R
  refine (quasilocal_region_localization q hq R J Λ h S A hA l t).trans ?_
  gcongr
  exact le_max_left _ _

end TNLean.PEPS.AreaLaw
