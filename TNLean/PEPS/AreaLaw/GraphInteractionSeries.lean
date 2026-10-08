/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphInteractionTarget
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential bounds for graph interaction-chain series

Target-sensitive chain coefficients have an exponential generating function. A finite
interaction budget and the graph-range indicator give its distance-decay estimate, while
every coefficient vanishes at infinite graph distance. This proves the series step of the
propagation argument, independently of the still separate physical commutator recursion.

Independently formalized from OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 4.1, `03-quasilocal.tex`, lines 96–113, at source commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. No upstream Lean proof text is reused.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

variable {V : Type*} [DecidableEq V]

private theorem exponential_chain_factor (κ μ : ℝ) (R D n : ℕ) :
    Real.exp (μ * R - μ * D) * (κ * Real.exp (μ * R)) ^ n =
      κ ^ n * Real.exp (μ * (((n + 1) * R : ℕ) - (D : ℝ))) := by
  rw [mul_pow]
  calc
    _ = κ ^ n * (Real.exp (μ * R - μ * D) * Real.exp ((n : ℝ) * (μ * R))) := by
      rw [Real.exp_nat_mul]
      ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      push_cast
      ring

/-- The graph-range indicator is bounded by an exponential spatial weight.
The finite distance is supplied exactly, and `μ = 0` is allowed. -/
theorem interactionChainTargetWeightSum_le_exponential
    (F : Finset (Finset V)) (w : Finset V → ℝ) (G : SimpleGraph V)
    (R v : ℕ) (b μ : ℝ) (hb : 0 ≤ b) (hμ : 0 ≤ μ) (hw : ∀ X ∈ F, 0 ≤ w X)
    (hcard : ∀ X ∈ F, X.card ≤ v)
    (hsite : ∀ a, (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤ b)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ z ∈ X, ∃ p : G.Walk a z, p.length ≤ R)
    (y : V) (n : ℕ) (X : Finset V) (hX : X ∈ F) (a : V) (ha : a ∈ X)
    (D : ℕ) (hD : G.edist a y = (D : ℕ∞)) :
    interactionChainTargetWeightSum F w y X n ≤
      Real.exp (μ * R - μ * D) * (((v : ℝ) * b) * Real.exp (μ * R)) ^ n := by
  rw [exponential_chain_factor]
  have hκ : 0 ≤ (v : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb
  by_cases hd : G.edist a y ≤ (((n + 1) * R : ℕ) : ℕ∞)
  · have hDn : D ≤ (n + 1) * R := by
      rw [hD] at hd
      exact ENat.natCast_le_natCast.mp hd
    have hDr : (D : ℝ) ≤ (((n + 1) * R : ℕ) : ℝ) := Nat.cast_le.mpr hDn
    have hone : 1 ≤ Real.exp (μ * (((n + 1) * R : ℕ) - (D : ℝ))) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hμ (sub_nonneg.mpr hDr))
    exact ((interactionChainTargetWeightSum_le F w hw y n X).trans
      (interactionChainWeightSum_le_pow F w v b hb hw hcard hsite n X hX)).trans
        (le_mul_of_one_le_right (pow_nonneg hκ _) hone)
  · rw [interactionChainTargetWeightSum_eq_zero_of_lt_edist F w G R hrange y n X hX a ha
      (lt_of_not_ge hd)]
    exact mul_nonneg (pow_nonneg hκ _) (Real.exp_nonneg _)

/-- Exponential generating function of target-sensitive interaction continuations.
Absolute time makes the combinatorial series identical for the two time directions. -/
noncomputable def interactionChainPropagationSeries (F : Finset (Finset V))
    (w : Finset V → ℝ) (y : V) (X : Finset V) (t : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * |t|) ^ n / n.factorial * interactionChainTargetWeightSum F w y X n

/-- The weighted chain series converges and has the distance-decay bound used in Lemma 4.1.
No physical evolution estimate is assumed: this theorem concerns the actual finite-family
chain coefficients. The prefactor for a commutator is supplied by the separate recursion. -/
theorem interactionChainPropagationSeries_summable_and_le
    (F : Finset (Finset V)) (w : Finset V → ℝ) (G : SimpleGraph V)
    (R v : ℕ) (b μ : ℝ) (hb : 0 ≤ b) (hμ : 0 ≤ μ) (hw : ∀ X ∈ F, 0 ≤ w X)
    (hcard : ∀ X ∈ F, X.card ≤ v)
    (hsite : ∀ a, (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤ b)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ z ∈ X, ∃ p : G.Walk a z, p.length ≤ R)
    (y : V) (X : Finset V) (hX : X ∈ F) (a : V) (ha : a ∈ X)
    (D : ℕ) (hD : G.edist a y = (D : ℕ∞)) (t : ℝ) :
    Summable (fun n : ℕ ↦ (2 * |t|) ^ n / n.factorial *
      interactionChainTargetWeightSum F w y X n) ∧
    interactionChainPropagationSeries F w y X t ≤
      Real.exp (μ * R - μ * D) *
        Real.exp (2 * |t| * ((v : ℝ) * b * Real.exp (μ * R))) := by
  let C := Real.exp (μ * R - μ * D)
  let A := (v : ℝ) * b * Real.exp (μ * R)
  have hsum : HasSum (fun n : ℕ ↦ C * ((2 * |t| * A) ^ n / n.factorial))
      (C * Real.exp (2 * |t| * A)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (2 * |t| * A)).mul_left C
  have hnonneg (n : ℕ) :
      0 ≤ (2 * |t|) ^ n / n.factorial * interactionChainTargetWeightSum F w y X n :=
    mul_nonneg (div_nonneg (pow_nonneg (by positivity) _) (Nat.cast_nonneg _))
      (interactionChainTargetWeightSum_nonneg F w hw y n X)
  have hle (n : ℕ) :
      (2 * |t|) ^ n / n.factorial * interactionChainTargetWeightSum F w y X n ≤
        C * ((2 * |t| * A) ^ n / n.factorial) := by
    calc
      _ ≤ (2 * |t|) ^ n / n.factorial * (C * A ^ n) :=
        mul_le_mul_of_nonneg_left
          (interactionChainTargetWeightSum_le_exponential F w G R v b μ hb hμ hw
            hcard hsite hrange y n X hX a ha D hD)
          (div_nonneg (pow_nonneg (by positivity) _) (Nat.cast_nonneg _))
      _ = _ := by rw [mul_pow]; ring
  have hconv := hsum.summable.of_nonneg_of_le hnonneg hle
  refine ⟨hconv, ?_⟩
  exact (hconv.tsum_le_tsum hle hsum.summable).trans_eq hsum.tsum_eq

/-- At infinite graph distance the complete chain series vanishes, even for signed weights. -/
theorem interactionChainPropagationSeries_eq_zero_of_edist_eq_top
    (F : Finset (Finset V)) (w : Finset V → ℝ) (G : SimpleGraph V) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ z ∈ X, ∃ p : G.Walk a z, p.length ≤ R)
    (y : V) (X : Finset V) (hX : X ∈ F) (a : V) (ha : a ∈ X)
    (hd : G.edist a y = ⊤) (t : ℝ) :
    interactionChainPropagationSeries F w y X t = 0 := by
  unfold interactionChainPropagationSeries
  simp only [interactionChainTargetWeightSum_eq_zero_of_edist_eq_top
    F w G R hrange y _ X hX a ha hd, mul_zero, tsum_zero]

end TNLean.PEPS.AreaLaw
