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

/-- Localization on an arbitrary region, including an empty region or domain.
The estimate follows by applying the one-site propagation bound at negative
time and averaging over sites outside the region's graph neighbourhood.

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
  obtain ⟨C, v, c, hC, hv, hc, hlocal⟩ :=
    exists_quasilocal_lieb_robinson q hq R J
  refine ⟨2 * C, v, c, by positivity, hv, hc, ?_⟩
  intro Λ h S A hA l t
  classical
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
        C * Real.exp (v * |t| - c * l) := by
    have hestimate := (hlocal Λ h ⟨{y}, isAdmissibleSupport_singleton Λ R y⟩ y
      (Finset.mem_singleton_self y) U
      (by simpa only [Finset.coe_singleton] using hU) (-t)).2 l
    rw [CStarRing.norm_of_mem_unitary hUu, one_mul, abs_neg] at hestimate
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
        2 * (C * Real.exp (v * |t| - c * l)) * ‖A‖ := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, (hcommute y hy U).eq,
      sub_sub_sub_cancel_right, hreverse U] using
      (norm_commutator_le A (heisenbergEvolution h.operator (-t) U -
        siteExpectation q (graphBall (domainGraph Λ) y l)
          (heisenbergEvolution h.operator (-t) U))).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hnear y U hU hUu) zero_le_two) (norm_nonneg A))
  done

end TNLean.PEPS.AreaLaw
