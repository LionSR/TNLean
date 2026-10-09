/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualMarginalTails

/-!
# Actual truncated marginal regressions

The same physical ground-state premise gives every cut, including complementary
cuts and negative thresholds. The original centering vector is independent of
the truncated ground vector. Budget checks cover empty and full cuts, an empty
label type, zero local dimension, and two repeated labels on a retained component
at local dimensions one and two, including zero operators.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan SpectralFilter
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
namespace TNLeanTest.ActualMarginalTails

section Budgets

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (S₀ : Finset V) (r₀ : ℕ) (a : I → V) (X : Finset V)

-- The equality itself does not require a nonzero local dimension.
example : cutBudget 0 G S₀ r₀ a X =
    Entropy.cutLogBudget
      (Entropy.crossingTerms (fun i => designatedSupport G S₀ r₀ (a i)) X)
      (Entropy.supportDim (fun _ : V => 0) ∘
        (fun i => designatedSupport G S₀ r₀ (a i))) :=
  cutBudget_eq_cutLogBudget 0 G S₀ r₀ a X

example (q : ℕ) : cutBudget q G S₀ r₀ a ∅ = 1 := cutBudget_empty q G S₀ r₀ a

example (q : ℕ) : cutBudget q G S₀ r₀ a Finset.univ = 1 := cutBudget_univ q G S₀ r₀ a

-- No containment premise is available for the complementary cut.
example (q : ℕ) : cutBudget q G S₀ r₀ a Xᶜ = cutBudget q G S₀ r₀ a X :=
  cutBudget_compl q G S₀ r₀ a X

example (q : ℕ) : 0 < cutBudget q G S₀ r₀ a X :=
  lt_of_lt_of_le zero_lt_one (one_le_cutBudget q G S₀ r₀ a X)

example (q : ℕ) (a₀ : Fin 0 → V) : cutBudget q G S₀ r₀ a₀ X = 1 := by
  simp [cutBudget, crossingLabels]

end Budgets

private theorem retained_support :
    designatedSupport (⊤ : SimpleGraph (Fin 2)) ∅ 0 0 = Finset.univ := by
  classical
  have hdist : setDist (⊤ : SimpleGraph (Fin 2)) ∅ 0 = ⊤ := by simp [setDist]
  rw [designatedSupport, hdist, if_pos rfl]
  apply Finset.eq_univ_of_forall
  intro x
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hx : (0 : Fin 2) = x
  · subst x
    exact SimpleGraph.Reachable.refl _
  · exact (show (⊤ : SimpleGraph (Fin 2)).Adj 0 x from hx).reachable

private theorem repeated_crossing_labels :
    crossingLabels (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} =
      Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro i
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [retained_support]
  exact ⟨⟨0, Finset.mem_univ _, by simp⟩, ⟨1, Finset.mem_univ _, by decide⟩⟩

-- Empty truncation sets retain components; they do not erase internal crossings.
-- Two identical anchors still contribute two terms, even at physical dimension one.
example : cutBudget 1 (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} = 3 := by
  norm_num [cutBudget, repeated_crossing_labels]

-- The geometric budget retains both labels even when both labelled operators vanish.
example : (∑ _i : Fin 2, (0 : Matrix (Fin 2 → Fin 1) (Fin 2 → Fin 1) ℂ)) = 0 ∧
    cutBudget 1 (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} = 3 := by
  norm_num [cutBudget, repeated_crossing_labels]

-- Qubit supports have dimension four: both copies of their positive logarithmic
-- contribution must survive, rather than a deduplicated single contribution.
private theorem repeated_qubit_budget :
    cutBudget 2 (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} =
      1 + 2 * Real.log (Real.exp 1 * 4) ^ 2 := by
  norm_num [cutBudget, repeated_crossing_labels, retained_support]

example : 1 < cutBudget 2 (⊤ : SimpleGraph (Fin 2)) ∅ 0
    (fun _ : Fin 2 => 0) {0} := by
  rw [repeated_qubit_budget]
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hlog : 0 < Real.log (Real.exp 1 * 4) := Real.log_pos (by linarith)
  nlinarith [sq_pos_of_pos hlog]

example : (∑ _i : Fin 2, (0 : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ)) = 0 ∧
    cutBudget 2 (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} =
      1 + 2 * Real.log (Real.exp 1 * 4) ^ 2 :=
  ⟨by simp, repeated_qubit_budget⟩

section Physical

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ} [NeZero q]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (h : LocalHamiltonian Λ q R J) (Ω Ωt : StateSpace Λ q)
    (hgraph : S.graph = domainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) (e : ℝ)
    (hgs : IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))

-- The original centering vector and the single ground vector remain separate.
example (X : Finset (Site Λ)) (u : ℝ)
    (hu : |u| ≤ Entropy.tailRadius (2 / (Δ / positiveNormalization 1 (Δ / 2) J))
      (cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X)) :
    Real.log (Entropy.surprisalMoment (reducedState_isHermitian Λ q Ωt X).eigenvalues u) ≤
      u * regionalEntropy Λ q Ωt X +
        512 * Real.exp 1 * (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
          cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X * u ^ 2 :=
  S.log_surprisalMoment_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L hgs X hu

-- One premise is reused for all cuts and all real thresholds, with no history data.
example : ∀ (X : Finset (Site Λ)) (w : ℝ),
    Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
        (regionalEntropy Λ q Ωt X) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
            cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X))))) :=
  fun X w => S.surprisalTail_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L hgs X w

-- The marginal is genuinely that of Xᶜ; only the scalar budget is complemented.
example (X : Finset (Site Λ)) :
    Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt Xᶜ).eigenvalues
        (regionalEntropy Λ q Ωt Xᶜ) (-1) ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-((-1) / (32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
            cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X))))) := by
  simpa only [cutBudget_compl] using
    S.surprisalTail_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L hgs Xᶜ (-1)

end Physical

-- Local dimension one is admitted by the physical theorem, without an extra J premise.
example {Λ : Finset (ℤ × ℤ)} {R : ℕ} {J Δ e : ℝ}
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (h : LocalHamiltonian Λ 1 R J)
    (Ω Ωt : StateSpace Λ 1) (hgraph : S.graph = domainGraph Λ)
    (hanchor : ∀ i, S.anchor i ∈ i.val) (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ)
    (hgs : IsGappedGroundState Λ 1 (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2)) (w : ℝ) :
    Entropy.surprisalTail (reducedState_isHermitian Λ 1 Ωt ∅).eigenvalues
        (regionalEntropy Λ 1 Ωt ∅) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt
          (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)))))) := by
  simpa only [cutBudget_empty, mul_one] using
    S.surprisalTail_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L hgs ∅ w

end TNLeanTest.ActualMarginalTails
