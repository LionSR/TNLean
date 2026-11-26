/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Operators.ChannelWords.ChannelWordOmission
import TNLean.PEPS.AreaLaw.Operators.ChannelWords.GraphChannelPoissonGrowth
import TNLean.PEPS.AreaLaw.Operators.ChannelWords.GraphOmittedAnchorTail
import QICLean.Algebra.Combinatorics.FinSumPermutation
import TNLean.PEPS.AreaLaw.Operators.ChannelWords.ExponentialChannelShells
import TNLean.PEPS.AreaLaw.Operators.ChannelWords.ComponentChannelOscillation

/-!
# Spatial omission bounds for physical channel words

The full and retained words are coupled by filtering the same finite Poisson
word. Their expected operator-norm difference has a stretched-exponential
spatial bound, uniform in the graph, event labels, local dimension, spectator,
support and cutoff. The proof derives the physical oscillation growth from
the effects and their localization tails, and combines it with the
omitted-prefix occupation identity and the graph anchor-tail estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–215, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.norm_localRootChannel_sub_self_le_exp_sum_siteOscillation`,
  `TNLean.PEPS.AreaLaw.norm_spectatorRootChannel_sub_self_le_exp_of_component_support`: one-event
  errors from channel shells.
-/

section GraphChannelEventError

/-!
## One-event errors from channel shells

Summing the localized channel shells bounds the operator-norm error of
a root channel by the physical site oscillations. At a finite radius containing
the anchor component, the localized channel equals the full channel exactly.
The coefficient is the shell coefficient itself, without the extra factor two
needed when bounding a site-oscillation increment.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 101–121 and 188–191, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
  [Fintype Aux] [DecidableEq Aux]

/-- The finite shell sum controls the localized channel error in
operator norm. Source: area law, `09-amplification.tex`, lines 101–121 and 188–191. -/
theorem norm_localRootChannel_sub_self_le_exp_sum_siteOscillation
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - ManyBody.regionExpectation (regions l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannel (regions n) k B - B‖ ≤
      ∑ l ∈ Finset.range (n + 1),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
          Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
            ∑ z ∈ regions l, siteOscillation q z B := by
  revert hε
  induction n with
  | zero =>
    intro hε
    simpa only [localRootChannelShell, Nat.zero_add, Finset.sum_range_one] using
      norm_localRootChannelShell_le_exp_sum_siteOscillation
        regions hregions hk₀ hk₁ hC hc hα hα₁ 0 hε B
  | succ n ih =>
    intro hε
    have hprev := ih fun l hl => hε l (hl.trans (Nat.le_succ n))
    have hnext := norm_localRootChannelShell_le_exp_sum_siteOscillation
      regions hregions hk₀ hk₁ hC hc hα hα₁ (n + 1) hε B
    change ‖localRootChannel (regions (n + 1)) k B -
      localRootChannel (regions n) k B‖ ≤ _ at hnext
    rw [Finset.sum_range_succ]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (localRootChannel (regions n) k B) _).trans
      ((add_le_add hnext hprev).trans_eq (add_comm _ _))

open Classical in
/-- Once the graph-ball cutoff contains the anchor component, the finite shell
bound controls the full physical event error. Source: area law,
`09-amplification.tex`, lines 135–137 and 188–191. -/
theorem norm_spectatorRootChannel_sub_self_le_exp_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
        (Finset.univ.filter fun x ↦ G.Reachable a x))
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Finset.univ.sup (G.dist a) ≤ n)
    (hε : ∀ l ≤ n, ‖k - ManyBody.regionExpectation (ManyBody.graphBall G a l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorRootChannel k B - B‖ ≤
      ∑ l ∈ Finset.range (n + 1),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
          Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
            ∑ z ∈ ManyBody.graphBall G a l, siteOscillation q z B := by
  simpa only [localRootChannel_graphBall_eq_of_component_support G a hk hn] using
    norm_localRootChannel_sub_self_le_exp_sum_siteOscillation
      (ManyBody.graphBall G a) (ManyBody.graphBall_mono G a) hk₀ hk₁ hC hc hα hα₁ n hε B

end TNLean.PEPS.AreaLaw

end GraphChannelEventError

section GraphChannelSpatialOmission

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

open Classical in
/-- Localization tails at every radius force exact support on the anchor
component: beyond the largest distance in the component the graph balls stop
growing, while the tail tends to zero. Source: area law, `09-amplification.tex`,
lines 135–137. -/
theorem mem_supportedOperators_reachable_of_forall_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    {C c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hε : ∀ l : ℕ, ‖k - ManyBody.regionExpectation (ManyBody.graphBall G a l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α))) :
    k ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
        (Finset.univ.filter fun x ↦ G.Reachable a x) := by
  classical
  set n := Finset.univ.sup (G.dist a)
  have hball (l : ℕ) (hl : n ≤ l) : ManyBody.graphBall G a l = ManyBody.graphBall G a n :=
    Finset.coe_injective (by
      rw [ManyBody.coe_graphBall_eq_reachable_of_sup_dist_le G a hl,
        ManyBody.coe_graphBall_eq_reachable_of_sup_dist_le G a le_rfl])
  have htend : Filter.Tendsto (fun l : ℕ => C * Real.exp (-(c * (l : ℝ) ^ α)))
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
    simpa using (Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp h)).const_mul C
  have hzero : ‖k - ManyBody.regionExpectation (ManyBody.graphBall G a n) k‖ ≤ 0 :=
    ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨n, fun l hl => hball l hl ▸ hε l⟩)
  have hk : ManyBody.regionExpectation (ManyBody.graphBall G a n) k = k :=
    (sub_eq_zero.mp (norm_le_zero_iff.mp hzero)).symm
  rw [← hk]
  convert (ManyBody.regionExpectation_mem_supportedOperators (ManyBody.graphBall G a n) k) using 2
  apply Finset.coe_injective
  rw [ManyBody.coe_graphBall_eq_reachable_of_sup_dist_le G a le_rfl]
  ext
  simp

/-- The prefactor `2 A₀ L` of the spatial omission bound, with `A₀ = 2 + 8 √C e^{c/2}` and
`L = omittedAnchorTailConstant K μ (c / 2) (c / (4 · 2^α)) α`. Source: area law,
`09-amplification.tex`, lines 139–215. -/
noncomputable def channelOmissionPrefactor (C K μ c α : ℝ) : ℝ :=
  2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
    omittedAnchorTailConstant K μ (c / 2) (c / (4 * (2 : ℝ) ^ α)) α

/-- The time rate `v + 1` of the spatial omission bound, where `v` is the row constant
`channelEventRowConstant C K μ c α`. Source: area law, `09-amplification.tex`,
lines 139–215. -/
noncomputable def channelOmissionRate (C K μ c α : ℝ) : ℝ :=
  channelEventRowConstant C K μ c α + 1

/-- The spatial exponent `γ = min (c / 2) (c / (4 · 2^α)) / 2` of the omission bound.
Source: area law, `09-amplification.tex`, lines 188–215. -/
noncomputable def channelOmissionExponent (c α : ℝ) : ℝ :=
  min (c / 2) (c / (4 * (2 : ℝ) ^ α)) / 2

/-- The omission prefactor is nonnegative. -/
theorem channelOmissionPrefactor_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (C K c α : ℝ) :
    0 ≤ channelOmissionPrefactor C K μ c α :=
  mul_nonneg (by positivity) (omittedAnchorTailConstant_nonneg hμ _ _ _ _)

/-- The omission rate is positive. -/
theorem channelOmissionRate_pos {μ : ℝ} (hμ : 0 ≤ μ) (C K c α : ℝ) :
    0 < channelOmissionRate C K μ c α :=
  add_pos_of_nonneg_of_pos (channelEventRowConstant_nonneg hμ C K c α) one_pos

/-- The omission exponent is positive. -/
theorem channelOmissionExponent_pos {c : ℝ} (hc : 0 < c) (α : ℝ) :
    0 < channelOmissionExponent c α := by
  unfold channelOmissionExponent
  positivity

open Classical in
/-- **Uniform spatial decay of the omission defect, with explicit constants.** For every
graph, finite family of component-supported effects with localization tails `C e^{-c l^α}`,
retained predicate, spectator operator `B` on `S` and time `T`, the full/retained defect is
integrable with expectation at most `D T |S| ‖B‖ e^{v T - γ r^α}`, where
`D = channelOmissionPrefactor C K μ c α`, `v = channelOmissionRate C K μ c α` and
`γ = channelOmissionExponent c α`. Source: area law, `09-amplification.tex`, lines 139–215. -/
theorem graph_integrable_and_integral_channelWordOmissionDefect_le
    {C K μ c α : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hμ : 0 ≤ μ)
    (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∀ (ι κ Aux : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
      [Fintype Aux] [DecidableEq Aux] (q : ℕ) [NeZero q]
      (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ),
      (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
      (∀ i, k i ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
          (Finset.univ.filter fun x ↦ G.Reachable (a i) x)) →
      (∀ x l, ((ManyBody.graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
      (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
      ∀ (N : ℕ), (∀ i, Finset.univ.sup (G.dist (a i)) ≤ N) →
      (∀ i l, l ≤ N → ‖k i - ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i)‖ ≤
        C * Real.exp (-(c * (l : ℝ) ^ α))) →
      ∀ (P : κ → Prop) [DecidablePred P] (S : Finset ι)
        (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ),
        (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
          ManyBody.supportedOperators (fun _ ↦ Fin q) S) →
        ∀ (r : ℝ), 0 ≤ r →
          (∀ i, ¬ P i → ∀ s ∈ S, ENNReal.ofReal r < (G.edist (a i) s : ℝ≥0∞)) →
          ∀ T : ℝ≥0,
            Integrable (fun w : PoissonWord.Word κ =>
              channelWordOmissionDefect k P (List.ofFn w.2) B) (PoissonWord.measure κ T) ∧
            (∫ w : PoissonWord.Word κ,
              channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ T) ≤
              channelOmissionPrefactor C K μ c α * T * S.card * ‖B‖ *
                Real.exp (channelOmissionRate C K μ c α * T -
                  channelOmissionExponent c α * r ^ α) := by
  have hkernel := graphChannelEventKernel_bounds_of_component_support hC hK hμ hc hα hα₁
  have hv : 0 ≤ channelEventRowConstant C K μ c α := channelEventRowConstant_nonneg hμ C K c α
  have hβ : 0 < c / (4 * (2 : ℝ) ^ α) := by positivity
  have htail := sum_omitted_graphBall_exponentialDistanceProfile_le
    hK hμ (half_pos hc) hβ hα hα₁
  unfold channelOmissionPrefactor channelOmissionRate channelOmissionExponent
  set v := channelEventRowConstant C K μ c α
  set L := omittedAnchorTailConstant K μ (c / 2) (c / (4 * (2 : ℝ) ^ α)) α
  set γ := min (c / 2) (c / (4 * (2 : ℝ) ^ α)) / 2
  set A₀ := 2 + 8 * Real.sqrt C * Real.exp (c / 2)
  have hA₀ : 0 ≤ A₀ := by positivity
  have hL : 0 ≤ L := omittedAnchorTailConstant_nonneg hμ _ _ _ _
  intro ι κ Aux _ _ _ _ _ q _ G a k hk₀ hk₁ hk hball hfiber N hN hε
    P _ S B hB r hr hfar T
  classical
  let := ManyBody.graphPseudoEMetricSpace G
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
            ∑ z ∈ ManyBody.graphBall G (a i) l, p z := by
    let w (l : ℕ) := A₀ * Real.exp (-(c / 2 * (l : ℝ) ^ α))
    have hint (l : ℕ) : Integrable (fun u => w l *
        ∑ z ∈ ManyBody.graphBall G (a i) l, d u z) (PoissonWord.measure {i // P i} t) :=
      (integrable_finsetSum _ fun z _ => hdint t z).const_mul (w l)
    calc
      _ ≤ ∫ u, ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ ManyBody.graphBall G (a i) l, d u z ∂PoissonWord.measure {i // P i} t := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
          (integrable_finsetSum _ fun l _ => hint l)
        apply Filter.Eventually.of_forall
        intro u
        exact norm_spectatorRootChannel_sub_self_le_exp_of_component_support
          G (a i) (hk₀ i) (hk₁ i) (hk i) hC hc hα hα₁ N (hN i) (hε i) (W u)
      _ = ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ ManyBody.graphBall G (a i) l,
            ∫ u, d u z ∂PoissonWord.measure {i // P i} t := by
        rw [integral_finsetSum _ fun l _ => hint l]
        apply Finset.sum_congr rfl
        intro l _
        rw [integral_const_mul, integral_finsetSum _ fun z _ => hdint t z]
      _ ≤ ∑ l ∈ Finset.range (N + 1), w l *
          ∑ z ∈ ManyBody.graphBall G (a i) l, Real.exp (v * t) * (2 * ‖B‖) * p z := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun z _ => hdbound t z) (by dsimp [w]; positivity)
      _ = _ := by
        simp only [w, Finset.mul_sum, neg_mul]
        refine Finset.sum_congr₂ fun l _ z _ ↦ ?_
        ring
  have hspatial : (∑ i ∈ E, ∑ l ∈ Finset.range (N + 1),
      Real.exp (-(c / 2) * (l : ℝ) ^ α) * ∑ z ∈ ManyBody.graphBall G (a i) l, p z) ≤
      L * S.card * Real.exp (-γ * r ^ α) :=
    htail ι κ G a hball hfiber E S N r hr
      (fun i hi => hfar i (Finset.mem_filter.mp hi).2)
  have hsum (s : ℝ) (hs : s ∈ Set.Ioc 0 (T : ℝ)) :
      (∑ i ∈ E, ∫ u, F u i ∂PoissonWord.measure {i // P i} (Real.toNNReal s)) ≤
        (2 * A₀ * L) * S.card * ‖B‖ * Real.exp ((v + 1) * T - γ * r ^ α) := by
    have hexp : Real.exp (v * (Real.toNNReal s : ℝ)) ≤ Real.exp ((v + 1) * T) := by
      rw [Real.toNNReal_of_nonneg hs.1.le]
      have hT : (0 : ℝ) ≤ T := T.coe_nonneg
      refine Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hs.2 hv).trans ?_)
      rw [add_mul, one_mul]
      linarith
    calc
      _ ≤ ∑ i ∈ E, A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          ∑ l ∈ Finset.range (N + 1), Real.exp (-(c / 2) * (l : ℝ) ^ α) *
            ∑ z ∈ ManyBody.graphBall G (a i) l, p z := Finset.sum_le_sum fun i _ => hevent _ i
      _ = A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          ∑ i ∈ E, ∑ l ∈ Finset.range (N + 1), Real.exp (-(c / 2) * (l : ℝ) ^ α) *
            ∑ z ∈ ManyBody.graphBall G (a i) l, p z := (Finset.mul_sum _ _ _).symm
      _ ≤ A₀ * (Real.exp (v * (Real.toNNReal s : ℝ)) * (2 * ‖B‖)) *
          (L * S.card * Real.exp (-γ * r ^ α)) :=
        mul_le_mul_of_nonneg_left hspatial (by positivity)
      _ ≤ A₀ * (Real.exp ((v + 1) * T) * (2 * ‖B‖)) *
          (L * S.card * Real.exp (-γ * r ^ α)) := by gcongr
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]; ring
  obtain ⟨hi, htime⟩ := integrable_and_integral_channelWordOmissionDefect_le k hk₀ hk₁ P B T
  refine ⟨hi, htime.trans ?_⟩
  change (∫ s : ℝ in Set.Ioc 0 (T : ℝ),
    ∑ i ∈ E, ∫ u, F u i ∂PoissonWord.measure {i // P i} (Real.toNNReal s)) ≤ _
  calc
    _ ≤ ∫ _s : ℝ in Set.Ioc 0 (T : ℝ),
        (2 * A₀ * L) * S.card * ‖B‖ * Real.exp ((v + 1) * T - γ * r ^ α) :=
      setIntegral_mono_of_nonneg
        (fun s _ => Finset.sum_nonneg fun i _ => integral_nonneg fun u => norm_nonneg _)
        hsum (integrable_const _)
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le T.coe_nonneg, sub_zero, smul_eq_mul]
      ring

open Classical in
/-- Uniform spatial decay for the expectation of the full/retained
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
        (∀ i, k i ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
            (Finset.univ.filter fun x ↦ G.Reachable (a i) x)) →
        (∀ x l, ((ManyBody.graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        ∀ (N : ℕ), (∀ i, Finset.univ.sup (G.dist (a i)) ≤ N) →
        (∀ i l, l ≤ N → ‖k i - ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (P : κ → Prop) [DecidablePred P] (S : Finset ι)
          (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ),
          (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
            ManyBody.supportedOperators (fun _ ↦ Fin q) S) →
          ∀ (r : ℝ), 0 ≤ r →
            (∀ i, ¬ P i → ∀ s ∈ S, ENNReal.ofReal r < (G.edist (a i) s : ℝ≥0∞)) →
            ∀ T : ℝ≥0,
              Integrable (fun w : PoissonWord.Word κ =>
                channelWordOmissionDefect k P (List.ofFn w.2) B) (PoissonWord.measure κ T) ∧
              (∫ w : PoissonWord.Word κ,
                channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ T) ≤
                D * T * S.card * ‖B‖ * Real.exp (v * T - γ * r ^ α) :=
  ⟨_, _, _, channelOmissionPrefactor_nonneg hμ C K c α, channelOmissionRate_pos hμ C K c α,
    channelOmissionExponent_pos hc α, rfl,
    graph_integrable_and_integral_channelWordOmissionDefect_le hC hK hμ hc hα hα₁⟩

end TNLean.PEPS.AreaLaw

end GraphChannelSpatialOmission
