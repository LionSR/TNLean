/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelPoissonGrowth

/-! Chronology and boundary cases for physical Poisson-word oscillations. -/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix MeasureTheory TNLean.PEPS.AreaLaw
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace GraphChannelPoissonGrowthTest

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

-- The first event acts first; no commutation of the channels is assumed.
example (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (i j : κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k
        (List.ofFn (PoissonWord.append (PoissonWord.singleton i) (PoissonWord.singleton j)).2) B =
      spectatorRootChannel (k j) (spectatorRootChannel (k i) B) := by
  simp only [spectatorRootChannelWord_ofFn_append_singleton, PoissonWord.ofFn_singleton]
  rfl

-- At time zero the actual integral is the literal initial oscillation.
example [Fintype κ] (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∫ u, siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B)
      ∂PoissonWord.measure κ 0) = siteOscillation q y B := by
  simp only [PoissonWord.measure_zero, integral_dirac, PoissonWord.nil,
    List.ofFn_zero, spectatorRootChannelWord_nil]

private theorem emptyEventsWord
    (k : Empty → Matrix (ι → Fin q) (ι → Fin q) ℂ) (u : PoissonWord.Word Empty)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k (List.ofFn u.2) B = B := by
  cases h : List.ofFn u.2 with
  | nil => rfl
  | cons i w => exact isEmptyElim i

-- An empty event alphabet has the constant physical observable at every time.
example (k : Empty → Matrix (ι → Fin q) (ι → Fin q) ℂ) (y : ι) (t : ℝ≥0)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    Integrable (fun u : PoissonWord.Word Empty =>
        siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B))
      (PoissonWord.measure Empty t) ∧
      (∫ u, siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B)
        ∂PoissonWord.measure Empty t) = siteOscillation q y B := by
  simp only [emptyEventsWord]
  exact ⟨integrable_const _, by simp⟩

-- The graph consumer accepts the empty physical site type.
example [Fintype κ] [NeZero q]
    (k : κ → Matrix (Empty → Fin q) (Empty → Fin q) ℂ)
    (B : Matrix ((Empty → Fin q) × Aux) ((Empty → Fin q) × Aux) ℂ) (t : ℝ≥0) :
    ∀ y : Empty, Integrable (fun u : PoissonWord.Word κ =>
        siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B))
      (PoissonWord.measure κ t) := by
  intro y
  exact (integrable_and_integral_siteOscillation_le_of_graph_kernel (⊥ : SimpleGraph Empty)
    k (fun _ _ => 0) (β := 1) (α := 1) (v := 0) (by norm_num) (by norm_num)
    le_rfl le_rfl (fun _ _ => le_rfl) (fun z => isEmptyElim z)
    (fun _ _ _ => rfl) (fun _ => by simp) Finset.univ B
    (fun a b => by
      simpa only [Finset.coe_univ] using
        mem_supportedOperators_univ (Matrix.of fun σ τ => B (σ, a) (τ, b)))
    t y).1

section Kernel

variable [Fintype κ] [NeZero q]
variable (G : SimpleGraph ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
  (A : ι → ι → ℝ) {β α v : ℝ}
  (hβ : 0 ≤ β) (hα : 0 < α) (hα₁ : α ≤ 1) (hv : 0 ≤ v)
  (hA : ∀ y z, 0 ≤ A y z)
  (hstep : ∀ (y : ι)
    (W : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ),
    (∑ i, (siteOscillation q y (spectatorRootChannel (k i) W) -
      siteOscillation q y W)) ≤ ∑ z, A y z * siteOscillation q z W)
  (hcomponent : ∀ y z, ¬ G.Reachable y z → A y z = 0)
  (hrow : ∀ y, (∑ z, A y z * Real.exp (β * (G.dist y z : ℝ) ^ α)) ≤ v)

-- Empty initial support gives pointwise zero, including spectator-only matrices.
example (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (hB : ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (∅ : Set ι)) (y : ι) (u : PoissonWord.Word κ) :
    siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B) = 0 := by
  have h := integrable_and_integral_siteOscillation_le_of_graph_kernel G k A
    hβ hα hα₁ hv hA hstep hcomponent hrow ∅ B
    (by simpa only [Finset.coe_empty] using hB) 0 y
  exact h.2.2 u (by simp)

-- A component disjoint from the support has zero oscillation at every word.
example (S : Finset ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (hB : ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (S : Set ι)) (y : ι)
    (hy : ∀ z ∈ S, ¬ G.Reachable y z) (u : PoissonWord.Word κ) :
    siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B) = 0 := by
  let := graphPseudoEMetricSpace G
  have hdist : Metric.infEDist y (S : Set ι) = ⊤ := by
    apply top_unique
    apply Metric.le_infEDist.mpr
    intro z hz
    exact le_of_eq ((graphPseudoEMetricSpace_edist_eq_top G y z).mpr (hy z hz)).symm
  exact (integrable_and_integral_siteOscillation_le_of_graph_kernel G k A
    hβ hα hα₁ hv hA hstep hcomponent hrow S B hB 0 y).2.2 u hdist

-- At finite distance the profile has the source's single-exponential form.
example (S : Finset ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (hB : ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (S : Set ι)) (t : ℝ≥0) (y : ι) :
    letI := graphPseudoEMetricSpace G
    Metric.infEDist y (S : Set ι) ≠ ⊤ →
      (∫ u, siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B)
        ∂PoissonWord.measure κ t) ≤
        2 * ‖B‖ * Real.exp (v * t - β * (Metric.infEDist y (S : Set ι)).toReal ^ α) := by
  let := graphPseudoEMetricSpace G
  intro hy
  have h := (integrable_and_integral_siteOscillation_le_of_graph_kernel G k A
    hβ hα hα₁ hv hA hstep hcomponent hrow S B hB t y).2.1
  refine h.trans_eq ?_
  rw [Metric.exponentialDistanceProfile_of_ne_top _ _ _ _ hy, sub_eq_add_neg,
    Real.exp_add, neg_mul]
  ring

end Kernel

-- The tail-based graph corollary requires no nonempty spectator space.
example [Fintype κ] [NeZero q]
    (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, k i ∈ supportedOperators q {x | G.Reachable (a i) x})
    {C c α v : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hv : 0 ≤ v) (N : ℕ) (hN : ∀ i, Finset.univ.sup (G.dist (a i)) ≤ N)
    (hε : ∀ i l, l ≤ N → ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (hrow : ∀ y, (∑ z,
      graphChannelEventKernel G a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
        (c / 2) α N y z *
          Real.exp (c / (4 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) ≤ v)
    (S : Finset ι) (B : Matrix ((ι → Fin q) × Empty) ((ι → Fin q) × Empty) ℂ)
    (t : ℝ≥0) (y : ι) :
    (∫ u, siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B)
      ∂PoissonWord.measure κ t) ≤ 0 := by
  have h := integrable_and_integral_siteOscillation_le_graphChannelEventKernel G a k
    hk₀ hk₁ hk hC hc hα hα₁ hv N hN hε hrow S B (fun a => isEmptyElim a) t y
  have hB : B = 0 := Subsingleton.elim _ _
  simpa only [hB, norm_zero, mul_zero, zero_mul] using h.2.1

end GraphChannelPoissonGrowthTest

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannelWord_ofFn_append_singleton'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectatorRootChannelWord_ofFn_append_singleton

/--
info: 'TNLean.PEPS.AreaLaw.integrable_and_integral_siteOscillation_le_of_graph_kernel'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrable_and_integral_siteOscillation_le_of_graph_kernel

/--
info: 'TNLean.PEPS.AreaLaw.integrable_and_integral_siteOscillation_le_graphChannelEventKernel'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrable_and_integral_siteOscillation_le_graphChannelEventKernel
