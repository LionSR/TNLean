/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelEventKernel
import TNLean.PEPS.AreaLaw.TruncationSeries

/-!
# Uniform weighted rows of the actual graph-ball incidence kernel

Quadratic bounds on graph balls and a uniform bound on anchor fibers imply a
weighted row estimate for the finite event kernel. The constant is chosen
before the graph, its site and label types, and the cutoff. Labels with the
same anchor remain distinct. Balls use extended graph distance, so incidences
between disconnected components vanish before natural distance is used in the
weight. The analytic estimate reuses the volume-free truncation series.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–160, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The finite kernel in the actual event-family oscillation estimate. The
cardinality counts labels, including repeated anchors. Source: area law,
`09-amplification.tex`, lines 139–146. -/
noncomputable def graphChannelEventKernel (G : SimpleGraph ι) (a : κ → ι)
    (D b α : ℝ) (N : ℕ) (y z : ι) : ℝ := by
  classical
  exact D * ∑ l ∈ Finset.range (N + 1), Real.exp (-(b * (l : ℝ) ^ α)) *
    ((Finset.univ.filter fun i : κ =>
      y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l).card : ℝ)

/-- A nonnegative prefactor gives a nonnegative graph-ball incidence kernel,
without restrictions on the decay parameters or cutoff. -/
theorem graphChannelEventKernel_nonneg (G : SimpleGraph ι) (a : κ → ι)
    {D : ℝ} (hD : 0 ≤ D) (b α : ℝ) (N : ℕ) (y z : ι) :
    0 ≤ graphChannelEventKernel G a D b α N y z := by
  classical
  unfold graphChannelEventKernel
  exact mul_nonneg hD (Finset.sum_nonneg fun l _ => by positivity)

omit [DecidableEq ι] in
private theorem edist_le_two_mul_of_mem_graphBall {G : SimpleGraph ι} {x y z : ι}
    {l : ℕ} (hy : y ∈ graphBall G x l) (hz : z ∈ graphBall G x l) :
    G.edist y z ≤ (2 * l : ℕ) := by
  calc
    G.edist y z ≤ G.edist y x + G.edist x z := G.edist_triangle
    _ ≤ (l : ℕ∞) + l := add_le_add
      (by simpa only [G.edist_comm] using mem_graphBall.mp hy) (mem_graphBall.mp hz)
    _ = (2 * l : ℕ) := by simp [two_mul]

/-- Distinct graph components have no common ball incidence. In particular,
the zero convention of natural graph distance never creates a nonzero kernel
entry between components. Source: area law, `09-amplification.tex`, lines
139–155, with graph distance interpreted componentwise. -/
theorem graphChannelEventKernel_eq_zero_of_not_reachable
    (G : SimpleGraph ι) (a : κ → ι) (D b α : ℝ) (N : ℕ) (y z : ι)
    (hyz : ¬ G.Reachable y z) : graphChannelEventKernel G a D b α N y z = 0 := by
  classical
  have hempty (l : ℕ) : (Finset.univ.filter fun i : κ =>
      y ∈ graphBall G (a i) l ∧ z ∈ graphBall G (a i) l) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hy, hz⟩ := (Finset.mem_filter.mp hi).2
    have h := edist_le_two_mul_of_mem_graphBall hy hz
    rw [G.edist_eq_top_of_not_reachable hyz] at h
    exact (not_le_of_gt (ENat.natCast_lt_top (2 * l))) h
  simp [graphChannelEventKernel, hempty]

private theorem card_graphBall_anchors_le (G : SimpleGraph ι) (a : κ → ι)
    {μ : ℝ} (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (y : ι) (l : ℕ) :
    ((Finset.univ.filter fun i : κ => y ∈ graphBall G (a i) l).card : ℝ) ≤
      μ * (graphBall G y l).card := by
  classical
  have hcount := Finset.sum_card_fiberwise_eq_card_filter Finset.univ (graphBall G y l) a
  have hsymm (i : κ) : (y ∈ graphBall G (a i) l) ↔ a i ∈ graphBall G y l := by
    simp only [mem_graphBall, G.edist_comm]
  simp_rw [hsymm]
  rw [← hcount, Nat.cast_sum]
  calc
    _ ≤ ∑ _x ∈ graphBall G y l, μ := Finset.sum_le_sum fun x _ => hfiber x
    _ = _ := by simp [mul_comm]

omit [DecidableEq ι] in
private theorem weighted_graphBall_term_le (G : SimpleGraph ι)
    {b α : ℝ} (hb : 0 < b) (hα : 0 < α) {x y z : ι} {l : ℕ}
    (hy : y ∈ graphBall G x l) (hz : z ∈ graphBall G x l) :
    Real.exp (-(b * (l : ℝ) ^ α)) *
        Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α) ≤
      Real.exp (-(b / 2 * (l : ℝ) ^ α)) := by
  have hdist : G.dist y z ≤ 2 * l := by
    exact_mod_cast G.natCast_dist_le_edist.trans (edist_le_two_mul_of_mem_graphBall hy hz)
  have hpow : (G.dist y z : ℝ) ^ α ≤ (2 : ℝ) ^ α * (l : ℝ) ^ α := by
    calc
      _ ≤ (2 * (l : ℝ)) ^ α := Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast hdist) hα.le
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  have htwo : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hweight : b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α ≤
      b / 2 * (l : ℝ) ^ α := by
    calc
      _ ≤ b / (2 * (2 : ℝ) ^ α) * ((2 : ℝ) ^ α * (l : ℝ) ^ α) := by
        gcongr
      _ = _ := by field_simp
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The finite geometric step: quadratic ball growth and bounded anchor
fibers reduce every weighted row to a fourth-power stretched-exponential
sum. Source: area law, `09-amplification.tex`, lines 146–160. -/
theorem sum_graphChannelEventKernel_mul_exp_le
    (G : SimpleGraph ι) (a : κ → ι) {D K μ b α : ℝ}
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hb : 0 < b) (hα : 0 < α)
    (hball : ∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2)
    (hfiber : ∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ)
    (N : ℕ) (y : ι) :
    (∑ z, graphChannelEventKernel G a D b α N y z *
      Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) ≤
      D * μ * K ^ 2 * ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 4 *
        Real.exp (-(b / 2 * (l : ℝ) ^ α)) := by
  classical
  let w (l : ℕ) := Real.exp (-(b * (l : ℝ) ^ α))
  let v (l : ℕ) := Real.exp (-(b / 2 * (l : ℝ) ^ α)) * K * ((l : ℝ) + 1) ^ 2
  let d (z : ι) := Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)
  have hrow : (∑ z, graphChannelEventKernel G a D b α N y z * d z) =
      D * ∑ i, ∑ l ∈ (Finset.range (N + 1)).filter
        (fun l : ℕ => G.edist (a i) y ≤ l), w l * ∑ z ∈ graphBall G (a i) l, d z := by
    rw [sum_graphBall_shell_eq_sum_card]
    simp only [graphChannelEventKernel, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hevent (i : κ) (l : ℕ) (hl : G.edist (a i) y ≤ l) :
      w l * ∑ z ∈ graphBall G (a i) l, d z ≤ v l := by
    calc
      _ = ∑ z ∈ graphBall G (a i) l, w l * d z := Finset.mul_sum ..
      _ ≤ ∑ _z ∈ graphBall G (a i) l, Real.exp (-(b / 2 * (l : ℝ) ^ α)) :=
        Finset.sum_le_sum fun z hz => weighted_graphBall_term_le G hb hα (mem_graphBall.mpr hl) hz
      _ = Real.exp (-(b / 2 * (l : ℝ) ^ α)) * (graphBall G (a i) l).card := by
        simp [mul_comm]
      _ ≤ v l := by
        dsimp [v]
        nlinarith [hball (a i) l, Real.exp_pos (-(b / 2 * (l : ℝ) ^ α))]
  have hanchors (l : ℕ) :
      ((Finset.univ.filter fun i : κ => y ∈ graphBall G (a i) l).card : ℝ) ≤
        μ * K * ((l : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ μ * (graphBall G y l).card := card_graphBall_anchors_le G a hfiber y l
      _ ≤ μ * (K * ((l : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left (hball y l) hμ
      _ = _ := by ring
  calc
    _ = D * ∑ i, ∑ l ∈ (Finset.range (N + 1)).filter
        (fun l : ℕ => G.edist (a i) y ≤ l), w l * ∑ z ∈ graphBall G (a i) l, d z := hrow
    _ ≤ D * ∑ i, ∑ l ∈ (Finset.range (N + 1)).filter
        (fun l : ℕ => G.edist (a i) y ≤ l), v l := by
      gcongr with i _ l hl
      exact hevent i l (Finset.mem_filter.mp hl).2
    _ = D * ∑ l ∈ Finset.range (N + 1), v l *
        ((Finset.univ.filter fun i : κ => y ∈ graphBall G (a i) l).card : ℝ) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.natCast_card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_graphBall]
      split_ifs <;> simp
    _ ≤ D * ∑ l ∈ Finset.range (N + 1), v l * (μ * K * ((l : ℝ) + 1) ^ 2) := by
      gcongr with l _
      exact hanchors l
    _ = _ := by
      simp only [v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

private theorem exists_sum_fourth_pow_mul_exp_neg_rpow_le {b α : ℝ}
    (hb : 0 < b) (hα : 0 < α) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 4 *
        Real.exp (-(b / 2 * (l : ℝ) ^ α)) ≤ A := by
  obtain ⟨M, hM, hMb⟩ :=
    exists_one_add_pow_mul_exp_neg_rpow_le (b := b / 4) (by positivity) hα 2
  obtain ⟨S, hS, hSb⟩ := exists_sum_shell_le (c := b / 4) (by positivity) hα
  refine ⟨M * S, mul_nonneg hM hS, fun N => ?_⟩
  have hterm (l : ℕ) :
      ((l : ℝ) + 1) ^ 4 * Real.exp (-(b / 2 * (l : ℝ) ^ α)) ≤
        M * (((l : ℝ) + 1) ^ 2 *
          Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α))) := by
    have hfloor : ((l / 2 : ℕ) : ℝ) ^ α ≤ (l : ℝ) ^ α :=
      Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast Nat.div_le_self l 2) hα.le
    have hexp : Real.exp (-(b / 4 * (l : ℝ) ^ α)) ≤
        Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left hfloor (by positivity))
    calc
      ((l : ℝ) + 1) ^ 4 * Real.exp (-(b / 2 * (l : ℝ) ^ α)) =
          (((l : ℝ) + 1) ^ 2 * Real.exp (-(b / 4 * (l : ℝ) ^ α))) *
          (((l : ℝ) + 1) ^ 2 * Real.exp (-(b / 4 * (l : ℝ) ^ α))) := by
        rw [show -(b / 2 * (l : ℝ) ^ α) =
          -(b / 4 * (l : ℝ) ^ α) + -(b / 4 * (l : ℝ) ^ α) by ring, Real.exp_add]
        ring
      _ ≤ M * (((l : ℝ) + 1) ^ 2 * Real.exp (-(b / 4 * (l : ℝ) ^ α))) :=
        mul_le_mul_of_nonneg_right (hMb l (by positivity)) (by positivity)
      _ ≤ M * (((l : ℝ) + 1) ^ 2 * Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (by positivity)) hM
  have hsum : ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 2 *
      Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α)) ≤ S := by
    simpa [Real.zero_rpow (ne_of_gt hα)] using hSb 0 (N + 1)
  calc
    _ ≤ ∑ l ∈ Finset.range (N + 1), M * (((l : ℝ) + 1) ^ 2 *
        Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α))) :=
      Finset.sum_le_sum fun l _ => hterm l
    _ = M * ∑ l ∈ Finset.range (N + 1), ((l : ℝ) + 1) ^ 2 *
        Real.exp (-(b / 4 * ((l / 2 : ℕ) : ℝ) ^ α)) := by rw [Finset.mul_sum]
    _ ≤ M * S := mul_le_mul_of_nonneg_left hsum hM

/-- A volume- and cutoff-independent weighted row bound for the actual
finite graph-ball incidence kernel. The witness depends only on
`D, K, μ, b, α`, and is chosen before both finite types, the graph, anchors,
and cutoff. No weighted row estimate is assumed. The weight exponent is
`a = b / (2 * 2 ^ α)`. Source: area law, `09-amplification.tex`, lines 146–160. -/
theorem exists_graphChannelEventKernel_weighted_row_le {D K μ b α : ℝ}
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hb : 0 < b) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
      (G : SimpleGraph ι) (a : κ → ι),
      (∀ x l, ((graphBall G x l).card : ℝ) ≤ K * ((l : ℝ) + 1) ^ 2) →
      (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
      ∀ (N : ℕ) (y : ι),
        (∑ z, graphChannelEventKernel G a D b α N y z *
          Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) ≤ C := by
  obtain ⟨A, hA, hbound⟩ := exists_sum_fourth_pow_mul_exp_neg_rpow_le hb hα
  refine ⟨D * μ * K ^ 2 * A, by positivity, ?_⟩
  intro ι κ _ _ _ G a hball hfiber N y
  exact (sum_graphChannelEventKernel_mul_exp_le G a hD hK hμ hb hα hball hfiber N y).trans
    (mul_le_mul_of_nonneg_left (hbound N) (by positivity))

variable {q : ℕ} [NeZero q] {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The actual summed full-channel oscillation increments are dominated by
the finite graph-ball event kernel. The coefficient is the one derived from
the actual localization tails, including its factor of two. This is only a
finite reordering of the event-family estimate. Source: area law,
`09-amplification.tex`, lines 139–146. -/
theorem sum_siteOscillation_spectatorRootChannel_sub_le_graphChannelEventKernel
    (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, k i ∈ supportedOperators q {x | G.Reachable (a i) x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (N : ℕ) (hN : ∀ i, Finset.univ.sup (G.dist (a i)) ≤ N)
    (hε : ∀ i l, l ≤ N → ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (∑ i, (siteOscillation q y (spectatorRootChannel (k i) B) -
      siteOscillation q y B)) ≤
      ∑ z, graphChannelEventKernel G a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
        (c / 2) α N y z * siteOscillation q z B := by
  have h := sum_siteOscillation_spectatorRootChannel_sub_le_exp_card
    G a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε y B
  convert h using 1
  simp only [graphChannelEventKernel, mul_assoc, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Uniform weighted rows and literal channel-increment domination for an
actual finite family of component-supported effects. If
`A = 2 + 8 * sqrt C * exp (c / 2)`, the kernel uses `D = 2 * A`, `b = c / 2`,
and weight exponent `c / (4 * 2 ^ α)`. The row constant is chosen before the
site, label and spectator types, local dimension, graph, effects and cutoff;
only the scalar tail, ball-growth and fiber bounds enter its choice. Source:
area law, `09-amplification.tex`, lines 139–160. -/
theorem exists_graphChannelEventKernel_bounds_of_component_support {C K μ c α : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hμ : 0 ≤ μ)
    (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ R : ℝ, 0 ≤ R ∧
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
        (∀ y, (∑ z,
          graphChannelEventKernel G a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
            (c / 2) α N y z * Real.exp (c / (4 * (2 : ℝ) ^ α) *
              (G.dist y z : ℝ) ^ α)) ≤ R) ∧
        (∀ (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ),
          (∑ i, (siteOscillation q y (spectatorRootChannel (k i) B) -
            siteOscillation q y B)) ≤
          ∑ z,
            graphChannelEventKernel G a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
              (c / 2) α N y z * siteOscillation q z B) := by
  obtain ⟨R, hR, hrows⟩ := exists_graphChannelEventKernel_weighted_row_le
    (D := 2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
    (by positivity) hK hμ (half_pos hc) hα
  refine ⟨R, hR, ?_⟩
  intro ι κ Aux _ _ _ _ _ q _ G a k hk₀ hk₁ hk hball hfiber N hN hε
  constructor
  · intro y
    convert hrows ι κ G a hball hfiber N y using 1
    congr 1
    ext z
    congr 2
    ring
  · exact sum_siteOscillation_spectatorRootChannel_sub_le_graphChannelEventKernel
      G a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε

end TNLean.PEPS.AreaLaw
