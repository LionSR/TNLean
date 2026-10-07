/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedSourceComposition

/-! # Exact scalar cost of choosing only affected gate branches -/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-choice-cost.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-local-cost-sourcecircuit.sum_norm_coefficient_gate_of_touches
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_gate_of_touches

Provenance-ID: 8769-chronological-local-cost-sourcecircuit.sum_norm_coefficient_gate_of_exterior
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_gate_of_exterior

Provenance-ID: 8769-chronological-local-cost-sourcecircuit.sum_norm_coefficient_comp
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_comp

Provenance-ID: 8769-chronological-local-cost-sourcecircuit.sum_norm_coefficient_frame
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_frame

Provenance-ID: 8769-chronological-local-cost-sourcecircuit.sum_norm_coefficient_id
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_id

Provenance-ID: 8769-chronological-local-cost-sourcecircuit.sum_norm_coefficient_localmap
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_localMap

Provenance-ID: 8769-chronological-local-cost-sourcecircuit.sum_norm_coefficient_swap
Downstream declaration: TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_swap
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- An expanded gate contributes exactly the sum of the absolute values of its
original coefficients, including zero for an empty branch set.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_gate_of_touches {C ι : Type} [Fintype C] [Fintype ι]
    (A : P → Bool) (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P)
    (h : ∃ p : C, A (owner p) = true) :
    (∑ ξ : Choices A (.gate owner G tail),
      ‖coefficient A (.gate owner G tail) ξ‖) = ∑ ξ, ‖c ξ‖ := by
  classical
  let e : Choices A (.gate owner G tail) ≃ ι := Equiv.cast (by simp [Choices, h])
  apply Fintype.sum_equiv e
  intro ξ
  simp only [coefficient, dite_eq_left h]
  rfl

/-- An untouched gate has one partial choice with coefficient one, even when
its original branch type is empty.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–417. -/
theorem sum_norm_coefficient_gate_of_exterior {C ι : Type} [Fintype C] [Fintype ι]
    (A : P → Bool) (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P)
    (h : ¬ ∃ p : C, A (owner p) = true) :
    (∑ ξ : Choices A (.gate owner G tail),
      ‖coefficient A (.gate owner G tail) ξ‖) = 1 := by
  classical
  let e : Choices A (.gate owner G tail) ≃ Unit := Equiv.cast (by simp [Choices, h])
  calc
    _ = ∑ _ : Unit, (1 : ℝ) := by
      apply Fintype.sum_equiv e
      intro ξ
      simp only [coefficient, dite_eq_right h, norm_one]
    _ = 1 := by simp

/-- Independent choices in consecutive compositions multiply their exact sums
of absolute coefficients.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_comp (A : P → Bool) {a b d : Layout P}
    (w : SourceCircuit a b) (v : SourceCircuit b d) :
    (∑ ξ : Choices A (.comp w v), ‖coefficient A (.comp w v) ξ‖) =
      (∑ ξ : Choices A w, ‖coefficient A w ξ‖) *
        (∑ ξ : Choices A v, ‖coefficient A v ξ‖) := by
  change (∑ ξ : Choices A w × Choices A v,
    ‖coefficient A w ξ.1 * coefficient A v ξ.2‖) = _
  simp only [norm_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- An untouched register changes neither the choices nor their scalar weights.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_frame (A : P → Bool) (r : Reg P) {a b : Layout P}
    (w : SourceCircuit a b) :
    (∑ ξ : Choices A (.frame r w), ‖coefficient A (.frame r w) ξ‖) =
      ∑ ξ : Choices A w, ‖coefficient A w ξ‖ := rfl

/-- The identity has one choice with scalar coefficient one.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_id (A : P → Bool) (a : Layout P) :
    (∑ ξ : Choices A (.id a), ‖coefficient A (.id a) ξ‖) = 1 := by
  change (∑ _ : Unit, ‖(1 : ℂ)‖) = 1
  simp

/-- A private operation contributes no branch coefficient.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_localMap (A : P → Bool) (p : P) {a b : Layout P}
    (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
    (T : Mem a →L[ℂ] Mem b) (tail : Layout P) :
    (∑ ξ : Choices A (.localMap p ha hb T tail),
      ‖coefficient A (.localMap p ha hb T tail) ξ‖) = 1 := by
  change (∑ _ : Unit, ‖(1 : ℂ)‖) = 1
  simp

/-- A register exchange has one choice with scalar coefficient one.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_swap (A : P → Bool) (r s : Reg P) (tail : Layout P) :
    (∑ ξ : Choices A (.swap r s tail), ‖coefficient A (.swap r s tail) ξ‖) = 1 := by
  change (∑ _ : Unit, ‖(1 : ℂ)‖) = 1
  simp

end TNLean.PEPS.PairEffect.SourceCircuit
