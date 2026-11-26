/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Operators.Interactions.GraphPropagation
import QICLean.ManyBody.Dynamics.SupportedGaussianIntegral

/-!
# Localization of an operator on an arbitrary physical region

The normalized partial-trace expectation onto a graph neighbourhood approximates
the time evolution of every operator supported on the original region. The
constants precede the domain, Hamiltonian, region and operator. No spectral gap
or entropy hypothesis is used in this operator estimate.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.supported_gaussian_integral`,
  `TNLean.PEPS.AreaLaw.exists_supported_gaussian_integral`: a supported Gaussian approximation
  between two Hamiltonians.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `02-information.tex`, equation
  `eq:info-operator-localization`, lines 498–508, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Lemma 4.1, `eq:quasilocal-lr-ce`.
-/

section RegionOperatorLocalization

open QuantumCircuit
open scoped Matrix.Norms.L2Operator

open ManyBody (isAdmissibleSupport_singleton planeDomainGraph graphNeighborhood PlaneInteraction)

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
    (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ J) (S : Finset ↥Λ)
    (A : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) (l : ℕ) (t : ℝ) :
    ‖ManyBody.heisenbergEvolution h.hamiltonian t A -
        ManyBody.regionExpectation (graphNeighborhood (planeDomainGraph Λ) S l)
          (ManyBody.heisenbergEvolution h.hamiltonian t A)‖ ≤
      ‖A‖ * min 2 (2 * graphBallLocalizationPrefactor R * (Λ.card : ℝ) *
        Real.exp (graphBallLocalizationVelocity R J * |t| - 1 / 2 * l)) := by
  classical
  set C := graphBallLocalizationPrefactor R
  set v := graphBallLocalizationVelocity R J
  have hC : 0 < C := graphBallLocalizationPrefactor_pos R
  have hdisj (y : ↥Λ) (hy : y ∉ graphNeighborhood (planeDomainGraph Λ) S l) :
      Disjoint S (ManyBody.graphBall (planeDomainGraph Λ) y l) :=
    Finset.disjoint_left.mpr fun x hxS hxball =>
      (ManyBody.lt_edist_of_notMem_graphNeighborhood hy hxS).not_ge
        (by simpa only [SimpleGraph.edist_comm] using (ManyBody.mem_graphBall.mp hxball))
  have hK : Complex.I • h.hamiltonian ∈
      skewAdjoint (Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) :=
    (ManyBody.Interaction.isHermitian_hamiltonian hh).isSelfAdjoint.I_smul_mem_skewAdjoint (K := ℂ)
  have hreverse (U : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) :
      ‖ManyBody.heisenbergEvolution h.hamiltonian t A * U -
        U * ManyBody.heisenbergEvolution h.hamiltonian t A‖ =
      ‖A * ManyBody.heisenbergEvolution h.hamiltonian (-t) U -
        ManyBody.heisenbergEvolution h.hamiltonian (-t) U * A‖ := by
    simpa only [ManyBody.heisenbergEvolution_def, neg_neg] using
      norm_exp_commutator_eq (Complex.I • h.hamiltonian) hK A U t
  have : NeZero q := ⟨by omega⟩
  have hnear (y : ↥Λ) (U : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)
      (hU : U ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ({y} : Finset ↥Λ))
      (hUu : U ∈ unitary (Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)) :
      ‖ManyBody.heisenbergEvolution h.hamiltonian (-t) U -
        ManyBody.regionExpectation (ManyBody.graphBall (planeDomainGraph Λ) y l)
          (ManyBody.heisenbergEvolution h.hamiltonian (-t) U)‖ ≤
        C * Real.exp (v * |t| - 1 / 2 * l) := by
    have hestimate := h.norm_sub_regionExpectation_graphBall_le hh hhJ
      ⟨{y}, isAdmissibleSupport_singleton Λ R y⟩ (Finset.mem_singleton_self y)
      (by simpa only [Finset.coe_singleton] using hU) l (-t)
    rw [CStarRing.norm_of_mem_unitary hUu, one_mul, abs_neg,
      show (l : ℝ) / 2 = 1 / 2 * l by ring] at hestimate
    exact hestimate.trans (min_le_right _ _)
  have hcommute (y : ↥Λ) (hy : y ∉ graphNeighborhood (planeDomainGraph Λ) S l)
      (U : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) :
      Commute A (ManyBody.regionExpectation (ManyBody.graphBall (planeDomainGraph Λ) y l)
        (ManyBody.heisenbergEvolution h.hamiltonian (-t) U)) :=
    ManyBody.commute_of_mem_supportedOperators_of_disjoint hA
        (ManyBody.regionExpectation_mem_supportedOperators _ _) (hdisj y hy)
  have hε (y : ↥Λ) (hy : y ∉ graphNeighborhood (planeDomainGraph Λ) S l)
      (U : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)
      (hU : U ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ({y} : Finset ↥Λ))
      (hUu : U ∈ unitary (Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)) :
      ‖ManyBody.heisenbergEvolution h.hamiltonian t A * U -
        U * ManyBody.heisenbergEvolution h.hamiltonian t A‖ ≤
        2 * (C * Real.exp (v * |t| - 1 / 2 * l)) * ‖A‖ := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, (hcommute y hy U).eq,
      sub_sub_sub_cancel_right, hreverse U] using
      (norm_commutator_le A (ManyBody.heisenbergEvolution h.hamiltonian (-t) U -
        ManyBody.regionExpectation (ManyBody.graphBall (planeDomainGraph Λ) y l)
          (ManyBody.heisenbergEvolution h.hamiltonian (-t) U))).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hnear y U hU hUu) zero_le_two) (norm_nonneg A))
  have hExp : ‖ManyBody.heisenbergEvolution h.hamiltonian t A -
      ManyBody.regionExpectation (graphNeighborhood (planeDomainGraph Λ) S l)
          (ManyBody.heisenbergEvolution h.hamiltonian
          t A)‖ ≤
      ‖A‖ * (2 * C * (Λ.card : ℝ) * Real.exp (v * |t| - 1 / 2 * l)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      mul_assoc, mul_comm, mul_left_comm] using
      (ManyBody.norm_sub_regionExpectation_le (graphNeighborhood (planeDomainGraph Λ) S l)
        (ManyBody.heisenbergEvolution h.hamiltonian t A)
        (fun _ ↦ 2 * (C * Real.exp (v * |t| - 1 / 2 * l)) * ‖A‖) fun y hy U hU hUu ↦
          hε y hy U (by simpa using hU)
            hUu).trans
        (Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ by positivity))
  have hτnorm : ‖ManyBody.heisenbergEvolution h.hamiltonian t A‖ = ‖A‖ :=
    letI : NormedAlgebra ℚ (Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) :=
      .restrictScalars ℚ ℝ (Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)
    (CStarRing.norm_mul_mem_unitary
      (NormedSpace.exp (t • (Complex.I • h.hamiltonian)) * A)
      (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem (-t) hK))).trans
      (CStarRing.norm_mem_unitary_mul A
        (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hK)))
  have hTwo : ‖ManyBody.heisenbergEvolution h.hamiltonian t A -
      ManyBody.regionExpectation (graphNeighborhood (planeDomainGraph Λ) S l)
          (ManyBody.heisenbergEvolution h.hamiltonian
          t A)‖ ≤
      ‖A‖ * 2 := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add le_rfl (ManyBody.norm_regionExpectation_le _)).trans ?_
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
      ∀ (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J)
        (S : Finset ↥Λ) (A : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ),
        A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S → ∀ (l : ℕ) (t : ℝ),
        ‖ManyBody.heisenbergEvolution h.hamiltonian t A -
            ManyBody.regionExpectation (graphNeighborhood (planeDomainGraph Λ) S l)
              (ManyBody.heisenbergEvolution h.hamiltonian t A)‖ ≤
          ‖A‖ * min 2 (C * (Λ.card : ℝ) * Real.exp (v * |t| - c * l)) := by
  refine ⟨2 * graphBallLocalizationPrefactor R, max (graphBallLocalizationVelocity R J) 1,
    1 / 2, mul_pos two_pos (graphBallLocalizationPrefactor_pos R),
    lt_max_of_lt_right one_pos, one_half_pos, fun Λ h hh hhJ S A hA l t ↦ ?_⟩
  have hP := graphBallLocalizationPrefactor_pos R
  refine (quasilocal_region_localization q hq R J Λ h hh hhJ S A hA l t).trans ?_
  gcongr
  exact le_max_left _ _

end TNLean.PEPS.AreaLaw

end RegionOperatorLocalization

section SupportedGaussianIntegral

/-!
## A supported Gaussian approximation between two Hamiltonians

Project both the evolved observable and the relative-evolution generator
onto the same graph neighbourhood. The projected differential equation
constructs a unitary path on this neighbourhood. Integrating the product
against the original restricted Gaussian measure gives a supported
operator, with norm and approximation bounds uniform in the variance.

The path is chosen before the variance and time cutoff. Neither a
propagator nor an approximating operator is supplied as a hypothesis.
Only the actual supports of the input observable and Hamiltonian
difference enter. No spectral gap or information assumption is used.

### References

OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
September 24, 2026, Section 2, lines 513–562, in the proof of
eq:info-local-two-sided. Source revision:
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The common projection region is the neighbourhood of the union of the
two input supports, as in the support conclusion of that argument.
Independently formalized; no upstream Lean proof text is reused.
-/

open ManyBody (PlaneInteraction graphNeighborhood planeDomainGraph)

open MeasureTheory ProbabilityTheory QuantumCircuit
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace TNLean.PEPS.AreaLaw

/-- The supported Gaussian approximation from a region localization bound with constants
`C, v ≥ 0` and decay `c`, for one finite-range Hamiltonian `g`. The constants of the
localization bound pass unchanged to the approximation error. -/
private theorem supported_gaussian_integral_of_localization {q : ℕ} (hq : 1 ≤ q) {R : ℕ}
    {C v c : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v) {Λ : Finset (ℤ × ℤ)} (g : PlaneInteraction Λ q R)
        (hg : ∀ X, (g.term X).IsHermitian)
    (hlocal : ∀ (S : Finset ↥Λ) (A : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ),
      A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S → ∀ (l : ℕ) (t : ℝ),
      ‖ManyBody.heisenbergEvolution g.hamiltonian t A -
          ManyBody.regionExpectation (graphNeighborhood (planeDomainGraph Λ) S l)
            (ManyBody.heisenbergEvolution
              g.hamiltonian t
              A)‖ ≤
        ‖A‖ * min 2 (C * (Λ.card : ℝ) * Real.exp (v * |t| - c * l)))
    (H W : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) (hH : H.IsHermitian)
    (Q Z : Finset ↥Λ) (hW : W ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Q)
    (hD : g.hamiltonian - H ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Z) (l : ℕ) :
    let B := graphNeighborhood (planeDomainGraph Λ) (Q ∪ Z) l
    ∃ U : ℝ → Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ,
      U 0 = 1 ∧
      (∀ t, HasDerivAt U
        ((Complex.I • ManyBody.regionExpectation B
          (ManyBody.heisenbergEvolution g.hamiltonian t (g.hamiltonian - H))) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup (↥Λ → Fin q) ℂ) ∧
      (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B) ∧
      ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
        let M := ∫ t : ℝ in Set.Icc (-T) T,
          ManyBody.regionExpectation B (ManyBody.heisenbergEvolution g.hamiltonian t W) * U t
            ∂gaussianReal 0 η
        M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B ∧
        ‖M‖ ≤ ‖W‖ ∧
        ‖M - GaussianFilter.gaussianIntertwinerTruncated η T g.hamiltonian H W‖ ≤
          ‖W‖ * C * (Λ.card : ℝ) * (1 + ‖g.hamiltonian - H‖ * T) *
            Real.exp (v * T - c * l) := by
  classical
  intro B
  have : NeZero q := ⟨by omega⟩
  obtain ⟨U, hU0, hU, hunit, hsupport, haverage⟩ :=
    ManyBody.exists_supported_gaussian_integral_of_projection_bounds
        (ManyBody.Interaction.isHermitian_hamiltonian hg) hH B
  refine ⟨U, hU0, hU, hunit, fun t ↦ (hsupport t),
    fun η T hT ↦ ?_⟩
  have hnear (A : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)
      (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (Q ∪ Z : Finset ↥Λ))
      (t : ℝ) (ht : |t| ≤ T) :
      ‖ManyBody.heisenbergEvolution g.hamiltonian t A -
        ManyBody.regionExpectation B (ManyBody.heisenbergEvolution g.hamiltonian t A)‖ ≤
        ‖A‖ * (C * (Λ.card : ℝ) * Real.exp (v * T - c * l)) :=
    (hlocal (Q ∪ Z) A hA l t).trans
      (mul_le_mul_of_nonneg_left
        ((min_le_right _ _).trans
          (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr
              (sub_le_sub_right (mul_le_mul_of_nonneg_left ht hv) _))
            (mul_nonneg hC (Nat.cast_nonneg _))))
        (norm_nonneg A))
  obtain ⟨hMsupport, hMnorm, hMerror⟩ := haverage B B
    (fun _ hx ↦ hx) (fun _ hx ↦ hx) W η T hT
    (C * (Λ.card : ℝ) * Real.exp (v * T - c * l))
    (‖g.hamiltonian - H‖ * (C * (Λ.card : ℝ) * Real.exp (v * T - c * l)))
    (by positivity) (by positivity)
    (hnear W (ManyBody.supportedOperators_mono (fun _ hx ↦ Finset.mem_union_left Z hx) hW))
    (hnear (g.hamiltonian - H)
      (ManyBody.supportedOperators_mono (fun _ hx ↦ Finset.mem_union_right Q hx) hD))
  refine ⟨ hMsupport, hMnorm, hMerror.trans_eq ?_⟩
  ring


/-- **The supported Gaussian approximation, with explicit constants.** For a Hamiltonian of
range `R` and term-norm bound `J ≥ 0`, the approximation error of the supported Gaussian
integral is at most `‖W‖ 2 C₀(R) |Λ| (1 + ‖D‖ T) e^{v(R, J) T - l/2}`, with
`C₀(R) = graphBallLocalizationPrefactor R` and `v(R, J) = graphBallLocalizationVelocity R J`
the constants of `TNLean.PEPS.AreaLaw.quasilocal_region_localization`.
Source: polynomial-PEPS, Section 2, eq:info-local-two-sided, lines 513–562. -/
theorem supported_gaussian_integral (q : ℕ) (hq : 1 ≤ q) (R : ℕ) {J : ℝ} (hJ : 0 ≤ J)
    (Λ : Finset (ℤ × ℤ)) (g : PlaneInteraction Λ q R) (hg : ∀ X, (g.term X).IsHermitian)
        (hgJ : ∀ X, ‖g.term X‖ ≤ J)
    (H W : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) (hH : H.IsHermitian)
    (Q Z : Finset ↥Λ) (hW : W ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Q)
    (hD : g.hamiltonian - H ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Z) (l : ℕ) :
    let B := graphNeighborhood (planeDomainGraph Λ) (Q ∪ Z) l
    ∃ U : ℝ → Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ,
      U 0 = 1 ∧
      (∀ t, HasDerivAt U
        ((Complex.I • ManyBody.regionExpectation B
          (ManyBody.heisenbergEvolution g.hamiltonian t (g.hamiltonian - H))) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup (↥Λ → Fin q) ℂ) ∧
      (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B) ∧
      ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
        let M := ∫ t : ℝ in Set.Icc (-T) T,
          ManyBody.regionExpectation B (ManyBody.heisenbergEvolution g.hamiltonian t W) * U t
            ∂gaussianReal 0 η
        M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B ∧
        ‖M‖ ≤ ‖W‖ ∧
        ‖M - GaussianFilter.gaussianIntertwinerTruncated η T g.hamiltonian H W‖ ≤
          ‖W‖ * (2 * graphBallLocalizationPrefactor R) * (Λ.card : ℝ) *
            (1 + ‖g.hamiltonian - H‖ * T) *
            Real.exp (graphBallLocalizationVelocity R J * T - 1 / 2 * l) :=
  supported_gaussian_integral_of_localization hq
    (mul_pos two_pos (graphBallLocalizationPrefactor_pos R)).le
    (graphBallLocalizationVelocity_nonneg R hJ) g hg
    (quasilocal_region_localization q hq R J Λ g hg hgJ) H W hH Q Z hW hD l

/-- The actual projected relative evolution constructs a supported
approximation to every truncated two-Hamiltonian Gaussian filter.
The same path works for all variances and nonnegative time cutoffs.
Source: polynomial-PEPS, Section 2, eq:info-local-two-sided,
lines 513–562. -/
theorem exists_supported_gaussian_integral (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (J : ℝ) :
    ∃ C v c : ℝ, 0 < C ∧ 0 < v ∧ 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (g : PlaneInteraction Λ q R) (_ : ∀ X, (g.term X).IsHermitian)
          (_ : ∀ X, ‖g.term X‖ ≤ J)
        (H W : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ),
        H.IsHermitian →
        ∀ Q Z : Finset ↥Λ,
          W ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Q →
          g.hamiltonian - H ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Z →
          ∀ l : ℕ,
            let B := graphNeighborhood (planeDomainGraph Λ) (Q ∪ Z) l
            ∃ U : ℝ → Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ,
              U 0 = 1 ∧
              (∀ t, HasDerivAt U
                ((Complex.I • ManyBody.regionExpectation B
                  (ManyBody.heisenbergEvolution g.hamiltonian t (g.hamiltonian - H))) * U t) t) ∧
              (∀ t, U t ∈ Matrix.unitaryGroup (↥Λ → Fin q) ℂ) ∧
              (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B) ∧
              ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
                let M := ∫ t : ℝ in Set.Icc (-T) T,
                  ManyBody.regionExpectation B
                      (ManyBody.heisenbergEvolution g.hamiltonian t W) * U t
                    ∂gaussianReal 0 η
                M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B ∧
                ‖M‖ ≤ ‖W‖ ∧
                ‖M - GaussianFilter.gaussianIntertwinerTruncated η T g.hamiltonian H W‖ ≤
                  ‖W‖ * C * (Λ.card : ℝ) * (1 + ‖g.hamiltonian - H‖ * T) *
                    Real.exp (v * T - c * l)  := by
  obtain ⟨C, v, c, hC, hv, hc, hlocal⟩ :=
    exists_quasilocal_region_localization q hq R J
  exact ⟨C, v, c, hC, hv, hc, fun Λ g hg hgJ H W hH Q Z hW hD l ↦
    supported_gaussian_integral_of_localization hq hC.le hv.le g hg (hlocal Λ g hg hgJ) H W
        hH Q Z hW hD l⟩

end TNLean.PEPS.AreaLaw

end SupportedGaussianIntegral
