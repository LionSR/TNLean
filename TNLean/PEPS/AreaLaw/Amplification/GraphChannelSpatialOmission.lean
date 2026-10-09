/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordOmission
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelEventError
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelPoissonGrowth
import TNLean.PEPS.AreaLaw.Amplification.GraphOmittedAnchorTail

/-!
# Spatial omission bounds for actual physical channel words

The full and retained words are coupled by filtering the same finite Poisson
word. Their expected operator-norm difference has a stretched-exponential
spatial bound, uniform in the graph, event labels, local dimension, spectator,
support and cutoff. The proof derives the physical oscillation growth from
the actual effects and their localization tails, and combines it with the
omitted-prefix occupation identity and the graph anchor-tail estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–215, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- Uniform spatial decay for the expectation of the actual full/retained
operator-norm defect. Every constant is chosen before the graph, all finite
types, physical effects, retained predicate, cutoff, observable and time.
The initial observable may be non-Hermitian and the finite spectator may be
empty. The same localization constants generate the event shells, physical
oscillation kernel, retained-word growth and omitted-anchor tail.
Source: area law, `09-amplification.tex`, lines 139–215. -/
theorem exists_integrable_and_integral_channelWordOmissionDefect_le
    {C K μ c α : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hμ : 0 ≤ μ)
    (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ D v γ : ℝ, 0 ≤ D ∧ 0 < v ∧ 0 < γ ∧
      γ = min (c / 2) (c / (4 * (2 : ℝ) ^ α)) / 2 ∧
      ∀ (ι κ Aux : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
        [Fintype Aux] [DecidableEq Aux] (q : ℕ) [NeZero q]
        (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ i, k i ∈ supportedOperators q {x | G.Reachable (a i) x}) →
        (∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        ∀ (N : ℕ), (∀ i, Finset.univ.sup (G.dist (a i)) ≤ N) →
        (∀ i l, l ≤ N → ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (P : κ → Prop) [DecidablePred P] (S : Finset ι)
          (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ),
          (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
            supportedOperators q (S : Set ι)) →
          ∀ (r : ℝ), 0 ≤ r →
            (∀ i, ¬ P i → ∀ s ∈ S, ENNReal.ofReal r < (G.edist (a i) s : ℝ≥0∞)) →
            ∀ T : ℝ≥0,
              Integrable (fun w : PoissonWord.Word κ =>
                channelWordOmissionDefect k P (List.ofFn w.2) B) (PoissonWord.measure κ T) ∧
              (∫ w : PoissonWord.Word κ,
                channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ T) ≤
                D * S.card * ‖B‖ * Real.exp (v * T - γ * r ^ α) := by
  obtain ⟨v, hv, hkernel⟩ := exists_graphChannelEventKernel_bounds_of_component_support
    hC hK hμ hc hα hα₁
  have hβ : 0 < c / (4 * (2 : ℝ) ^ α) := by positivity
  obtain ⟨L, γ, hL, hγ, hγeq, htail⟩ :=
    exists_sum_omitted_graphBall_exponentialDistanceProfile_le
      hK hμ (half_pos hc) hβ hα hα₁
  let A₀ := 2 + 8 * Real.sqrt C * Real.exp (c / 2)
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  refine ⟨2 * A₀ * L, v + 1, γ, by positivity, by linarith, hγ, hγeq, ?_⟩
  intro ι κ Aux _ _ _ _ _ q _ G a k hk₀ hk₁ hk hball hfiber N hN hε
    P _ S B hB r hr hfar T
  classical
  let := graphPseudoEMetricSpace G
  let a' (i : {i // P i}) := a i
  let k' (i : {i // P i}) := k i
  have hfiber' (x : ι) :
      ((Finset.univ.filter fun i : {i // P i} => a' i = x).card : ℝ) ≤ μ :=
    (Nat.cast_le.mpr (card_anchor_fiber_subtype_le a P x)).trans (hfiber x)
  obtain ⟨hrow, _⟩ := hkernel ι {i // P i} Aux q G a' k'
    (fun i => hk₀ i) (fun i => hk₁ i) (fun i => hk i)
    hball hfiber' N (fun i => hN i) (fun i => hε i)
  let W (u : PoissonWord.Word {i // P i}) := spectatorRootChannelWord k' (List.ofFn u.2) B
  let d (u : PoissonWord.Word {i // P i}) (z : ι) := siteOscillation q z (W u)
  let F (u : PoissonWord.Word {i // P i}) (i : κ) :=
    ‖spectatorRootChannel (k i) (W u) - W u‖
  let p (z : ι) := Metric.exponentialDistanceProfile (S : Set ι)
    (c / (4 * (2 : ℝ) ^ α)) α z
  let E := Finset.univ.filter fun i => ¬ P i
  have hgrowth (t : ℝ≥0) (z : ι) :=
    integrable_and_integral_siteOscillation_le_graphChannelEventKernel
      G a' k' (fun i => hk₀ i) (fun i => hk₁ i) (fun i => hk i)
      hC hc hα hα₁ hv N (fun i => hN i) (fun i => hε i) hrow S B hB t z
  have hdint (t : ℝ≥0) (z : ι) : Integrable (fun u => d u z)
      (PoissonWord.measure {i // P i} t) := (hgrowth t z).1
  have hdbound (t : ℝ≥0) (z : ι) :
      (∫ u, d u z ∂PoissonWord.measure {i // P i} t) ≤
        Real.exp (v * t) * (2 * ‖B‖) * p z := (hgrowth t z).2.1
  have hevent (t : ℝ≥0) (i : κ) :
      (∫ u, F u i ∂PoissonWord.measure {i // P i} t) ≤
        A₀ * (Real.exp (v * t) * (2 * ‖B‖)) *
          ∑ l ∈ Finset.range (N + 1), Real.exp (-(c / 2) * (l : ℝ) ^ α) *
            ∑ z ∈ graphBall G (a i) l, p z := by
    let w (l : ℕ) := A₀ * Real.exp (-(c / 2 * (l : ℝ) ^ α))
    have hint (l : ℕ) : Integrable (fun u => w l *
        ∑ z ∈ graphBall G (a i) l, d u z) (PoissonWord.measure {i // P i} t) :=
      (integrable_finsetSum _ fun z _ => hdint t z).const_mul (w l)
    calc
      _ ≤ ∫ u, ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ graphBall G (a i) l, d u z ∂PoissonWord.measure {i // P i} t := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
          (integrable_finsetSum _ fun l _ => hint l)
        apply Filter.Eventually.of_forall
        intro u
        exact norm_spectatorRootChannel_sub_self_le_exp_of_component_support
          G (a i) (hk₀ i) (hk₁ i) (hk i) hC hc hα hα₁ N (hN i) (hε i) (W u)
      _ = ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ graphBall G (a i) l,
            ∫ u, d u z ∂PoissonWord.measure {i // P i} t := by
        rw [integral_finsetSum _ fun l _ => hint l]
        apply Finset.sum_congr rfl
        intro l _
        rw [integral_const_mul, integral_finsetSum _ fun z _ => hdint t z]
      _ ≤ ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ graphBall G (a i) l, Real.exp (v * t) * (2 * ‖B‖) * p z := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun z _ => hdbound t z) (by dsimp [w]; positivity)
      _ = _ := by
        simp only [w, Finset.mul_sum, neg_mul]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro z _
        ring
  have hspatial : (∑ i ∈ E, ∑ l ∈ Finset.range (N + 1),
      Real.exp (-(c / 2) * (l : ℝ) ^ α) * ∑ z ∈ graphBall G (a i) l, p z) ≤
      L * S.card * Real.exp (-γ * r ^ α) :=
    htail ι κ G a hball hfiber E S N r hr
      (fun i hi => hfar i (Finset.mem_filter.mp hi).2)
  have hsum (s : ℝ) (hs : s ∈ Set.Ioc 0 (T : ℝ)) :
      (∑ i ∈ E, ∫ u, F u i ∂PoissonWord.measure {i // P i} (Real.toNNReal s)) ≤
        (2 * A₀ * L) * S.card * ‖B‖ * Real.exp (v * T - γ * r ^ α) := by
    have hexp : Real.exp (v * (Real.toNNReal s : ℝ)) ≤ Real.exp (v * T) := by
      rw [Real.toNNReal_of_nonneg hs.1.le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hv)
    calc
      _ ≤ ∑ i ∈ E, A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          ∑ l ∈ Finset.range (N + 1), Real.exp (-(c / 2) * (l : ℝ) ^ α) *
            ∑ z ∈ graphBall G (a i) l, p z := Finset.sum_le_sum fun i _ => hevent _ i
      _ = A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          ∑ i ∈ E, ∑ l ∈ Finset.range (N + 1), Real.exp (-(c / 2) * (l : ℝ) ^ α) *
            ∑ z ∈ graphBall G (a i) l, p z := (Finset.mul_sum _ _ _).symm
      _ ≤ A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          (L * S.card * Real.exp (-γ * r ^ α)) :=
        mul_le_mul_of_nonneg_left hspatial (by positivity)
      _ ≤ A₀ * (Real.exp (v * T) * (2 * ‖B‖)) *
          (L * S.card * Real.exp (-γ * r ^ α)) := by gcongr
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]; ring
  obtain ⟨hi, htime⟩ := integrable_and_integral_channelWordOmissionDefect_le k hk₀ hk₁ P B T
  refine ⟨hi, htime.trans ?_⟩
  change (∫ s : ℝ in Set.Ioc 0 (T : ℝ),
    ∑ i ∈ E, ∫ u, F u i ∂PoissonWord.measure {i // P i} (Real.toNNReal s)) ≤ _
  calc
    _ ≤ ∫ _s : ℝ in Set.Ioc 0 (T : ℝ),
        (2 * A₀ * L) * S.card * ‖B‖ * Real.exp (v * T - γ * r ^ α) :=
      setIntegral_mono_of_nonneg
        (fun s _ => Finset.sum_nonneg fun i _ => integral_nonneg fun u => norm_nonneg _)
        hsum (integrable_const _)
    _ = (T : ℝ) * ((2 * A₀ * L) * S.card * ‖B‖ *
        Real.exp (v * T - γ * r ^ α)) := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le T.coe_nonneg, sub_zero, smul_eq_mul]
    _ ≤ Real.exp (T : ℝ) * ((2 * A₀ * L) * S.card * ‖B‖ *
        Real.exp (v * T - γ * r ^ α)) :=
      mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)) (by positivity)
    _ = _ := by
      rw [← mul_assoc, mul_comm (Real.exp (T : ℝ)), mul_assoc, ← Real.exp_add]
      congr 2
      ring

end TNLean.PEPS.AreaLaw
