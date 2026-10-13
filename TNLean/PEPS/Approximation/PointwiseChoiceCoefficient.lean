/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NonemptyGateLabels

/-! # Coefficients of chronological choices as products over occurrences

The coefficient of a partial choice is the product of the original branch
coefficients at the touched occurrences. For the all-party expansion this is a
product over the nonempty original gate occurrences, so each factor can be
attached to the occurrence carrying its label.

Source: polynomial-PEPS, `04-compression.tex`, lines 351–381 and 565–573.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section

open scoped ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

open Classical in
/-- The actual coefficient of a partial chronological choice is the product of
the original coefficients at exactly its touched occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 565–573. -/
theorem coefficient_eq_prod_dite (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    coefficient A w ξ = ∏ g : w.gateLocations,
      if hg : w.IsTouched A g then w.branchCoefficient g (choiceAt A w ξ g hg) else 1 := by
  classical
  induction w with
  | id =>
      change 1 = ∏ _ : Empty, _
      simp only [Fintype.prod_empty]
  | comp w v ihw ihv =>
      change coefficient A w ξ.1 * coefficient A v ξ.2 =
        ∏ g : w.gateLocations ⊕ v.gateLocations, _
      rw [Fintype.prod_sum_type]
      exact congrArg₂ (· * ·) (ihw ξ.1) (ihv ξ.2)
  | localMap =>
      change 1 = ∏ _ : Empty, _
      simp only [Fintype.prod_empty]
  | @gate C ι _ _ owner a b c G tail =>
      change coefficient A (.gate owner G tail) ξ = ∏ g : Unit, _
      rw [Fintype.prod_unique]
      by_cases ht : ∃ q : C, A (owner q) = true
      · have hg := (isTouched_gate_iff A owner G tail).mpr ht
        rw [dite_eq_left hg]
        unfold coefficient
        rw [dite_eq_left ht]
        rfl
      · have hg : ¬IsTouched A (.gate owner G tail) () := by
          intro hg
          exact ht ((isTouched_gate_iff A owner G tail).mp hg)
        rw [dite_eq_right hg]
        unfold coefficient
        rw [dite_eq_right ht]
  | swap =>
      change 1 = ∏ _ : Empty, _
      simp only [Fintype.prod_empty]
  | frame r w ih => exact ih ξ

/-- The actual all-party coefficient is the product of the coefficients at
its nonempty-participant occurrences. Empty occurrences are already contained
in the aggregate residual, rather than this coefficient.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 565–573. -/
theorem coefficient_all_eq_prod_nonemptyGateLocations {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices (fun _ => true) w) :
    coefficient (fun _ => true) w ξ = ∏ g : w.nonemptyGateLocations,
      w.branchCoefficient g.1 (allChoicesNonemptyLabelsEquiv w ξ g) := by
  classical
  let F := fun g : w.gateLocations =>
    if hg : w.IsTouched (fun _ => true) g then
      w.branchCoefficient g (choiceAt (fun _ => true) w ξ g hg) else 1
  calc
    coefficient (fun _ => true) w ξ = ∏ g : w.gateLocations, F g :=
      coefficient_eq_prod_dite (fun _ => true) w ξ
    _ = ∏ g ∈ Finset.univ.filter (fun g => (w.participants g).Nonempty), F g := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro g _
      by_cases hg : (w.participants g).Nonempty
      · rw [ite_eq_left hg]
      · rw [ite_eq_right hg]
        exact dite_eq_right (fun h => hg ((isTouched_all_iff w g).mp h))
    _ = ∏ g : w.nonemptyGateLocations, F g.1 :=
      Finset.prod_subtype _ (by intro g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) F
    _ = ∏ g : w.nonemptyGateLocations,
        w.branchCoefficient g.1 (allChoicesNonemptyLabelsEquiv w ξ g) := by
      apply Finset.prod_congr rfl
      intro g _
      exact dite_eq_left ((isTouched_all_iff w g.1).mpr g.2)

/-- The mixed coefficient of two all-party choices is the product of their
mixed branch coefficients at the original nonempty gate occurrences.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381 and
565–573. -/
theorem coefficient_all_mul_conj_eq_prod_nonemptyGateLocations
    {a b : Layout P} (w : SourceCircuit a b)
    (ξ ζ : Choices (fun _ : P => true) w) :
    coefficient (fun _ : P => true) w ξ *
        conj (coefficient (fun _ : P => true) w ζ) =
      ∏ g : w.nonemptyGateLocations,
        w.branchCoefficient g.1 (allChoicesNonemptyLabelsEquiv w ξ g) *
          conj (w.branchCoefficient g.1 (allChoicesNonemptyLabelsEquiv w ζ g)) := by
  classical
  rw [coefficient_all_eq_prod_nonemptyGateLocations w ξ,
    coefficient_all_eq_prod_nonemptyGateLocations w ζ, map_prod,
    Finset.prod_mul_distrib]

/-- Reindex the two all-party choice sums by their original gate-label
functions, with the mixed coefficient written as a product over the nonempty
original gate occurrences. The matrix summand is arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381 and
565–573. -/
theorem sum_coefficient_all_mul_conj_smul_eq_sum_nonemptyGateLabels
    {a b : Layout P} (w : SourceCircuit a b) {m n : Type}
    (K : Choices (fun _ : P => true) w → Choices (fun _ : P => true) w →
      Matrix m n ℂ) :
    (∑ ξ : Choices (fun _ : P => true) w,
      ∑ ζ : Choices (fun _ : P => true) w,
        (coefficient (fun _ : P => true) w ξ *
          conj (coefficient (fun _ : P => true) w ζ)) • K ξ ζ) =
      ∑ η : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
        ∑ θ : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
          (∏ g : w.nonemptyGateLocations,
            w.branchCoefficient g.1 (η g) * conj (w.branchCoefficient g.1 (θ g))) •
              K ((allChoicesNonemptyLabelsEquiv w).symm η)
                ((allChoicesNonemptyLabelsEquiv w).symm θ) := by
  classical
  let e := allChoicesNonemptyLabelsEquiv w
  simp_rw [coefficient_all_mul_conj_eq_prod_nonemptyGateLocations]
  refine Fintype.sum_equiv e _ _ ?_
  intro ξ
  simp only [Equiv.symm_apply_apply]
  refine Fintype.sum_equiv e _ _ ?_
  intro ζ
  simp only [Equiv.symm_apply_apply]

end TNLean.PEPS.PairEffect.SourceCircuit
