/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphInteractionBudget
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Interaction chains reaching a specified site

The continuation weight retains only chains whose final support contains the target site.
Its coefficients vanish exactly beyond the total graph-range allowance, including between
different connected components. A nonnegative per-site budget gives the source indicator
bound before summing the time-evolution series. This is a combinatorial statement; it does
not assume or establish a differential equation for physical commutators.

Independently written from OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 4.1, lines 96–113 in `03-quasilocal.tex`, at immutable source
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. No upstream Lean proof text is reused.
-/

open scoped BigOperators

/-!
## Declaration provenance

Provenance-ID: 8745-tnlean.peps.arealaw.interactionchaintargetweightsum
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchaintargetweightsum_nonneg
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_nonneg
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchaintargetweightsum_le
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_le
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchaintargetweightsum_eq_zero_of_no_walk
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_no_walk
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchaintargetweightsum_eq_zero_of_lt_edist
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_lt_edist
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchaintargetweightsum_eq_zero_of_edist_eq_top
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_edist_eq_top
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchaintargetweightsum_le_indicator_pow
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_le_indicator_pow
Source: September 24, 2026, lem:quasilocal-lr, eq:quasilocal-lr-recursion.
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/03-quasilocal.tex>
Independently formalized; no upstream Lean proof text reused.
This module proves graph/counting coefficients, not physical commutator dynamics.
-/

namespace TNLean.PEPS.AreaLaw

variable {V : Type*} [DecidableEq V]

/-- Weight of length-`n` interaction continuations whose last support contains `y`.
Repeated supports are allowed, and `n = 0` tests the initial support itself. -/
noncomputable def interactionChainTargetWeightSum (F : Finset (Finset V))
    (w : Finset V → ℝ) (y : V) (X : Finset V) : ℕ → ℝ
  | 0 => if y ∈ X then 1 else 0
  | n + 1 => ∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X),
      w Y * interactionChainTargetWeightSum F w y Y n

/-- Nonnegative original weights give nonnegative target-chain coefficients. -/
theorem interactionChainTargetWeightSum_nonneg (F : Finset (Finset V))
    (w : Finset V → ℝ) (hw : ∀ X ∈ F, 0 ≤ w X) (y : V) (n : ℕ) (X : Finset V) :
    0 ≤ interactionChainTargetWeightSum F w y X n := by
  induction n generalizing X with
  | zero => simp only [interactionChainTargetWeightSum]; split_ifs <;> norm_num
  | succ n ih =>
      exact Finset.sum_nonneg fun Y hY ↦
        mul_nonneg (hw Y (Finset.mem_filter.mp hY).1) (ih Y)

/-- Restricting the final support to contain a target can only decrease a nonnegative
continuation weight. -/
theorem interactionChainTargetWeightSum_le (F : Finset (Finset V))
    (w : Finset V → ℝ) (hw : ∀ X ∈ F, 0 ≤ w X) (y : V) (n : ℕ) (X : Finset V) :
    interactionChainTargetWeightSum F w y X n ≤ interactionChainWeightSum F w X n := by
  induction n generalizing X with
  | zero =>
      simp only [interactionChainTargetWeightSum, interactionChainWeightSum]
      split_ifs <;> norm_num
  | succ n ih =>
      exact Finset.sum_le_sum fun Y hY ↦
        mul_le_mul_of_nonneg_left (ih Y) (hw Y (Finset.mem_filter.mp hY).1)

/-- If no sufficiently short graph walk reaches the target, its chain coefficient is zero.
This algebraic vanishing does not need nonnegative weights. -/
theorem interactionChainTargetWeightSum_eq_zero_of_no_walk
    (F : Finset (Finset V)) (w : Finset V → ℝ) (G : SimpleGraph V) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ z ∈ X, ∃ p : G.Walk a z, p.length ≤ R)
    (y : V) (n : ℕ) (X : Finset V) (hX : X ∈ F) (a : V) (ha : a ∈ X)
    (hnone : ¬ ∃ p : G.Walk a y, p.length ≤ (n + 1) * R) :
    interactionChainTargetWeightSum F w y X n = 0 := by
  induction n generalizing X a with
  | zero =>
      have hy : y ∉ X := by
        intro hy
        obtain ⟨p, hp⟩ := hrange X hX a ha y hy
        exact hnone ⟨p, by simpa using hp⟩
      simp [interactionChainTargetWeightSum, hy]
  | succ n ih =>
      simp only [interactionChainTargetWeightSum]
      apply Finset.sum_eq_zero
      intro Y hY
      obtain ⟨hYF, hYX⟩ := Finset.mem_filter.mp hY
      obtain ⟨z, hzY, hzX⟩ := Finset.not_disjoint_iff.mp hYX
      have hnext : ¬ ∃ q : G.Walk z y, q.length ≤ (n + 1) * R := by
        rintro ⟨q, hq⟩
        obtain ⟨p, hp⟩ := hrange X hX a ha z hzX
        apply hnone
        refine ⟨p.append q, ?_⟩
        calc
          (p.append q).length = p.length + q.length := by simp
          _ ≤ R + (n + 1) * R := Nat.add_le_add hp hq
          _ = (n + 1 + 1) * R := by
            simp only [Nat.add_mul, Nat.one_mul]
            omega
      rw [ih Y hYF z hzY hnext, mul_zero]

/-- A target beyond `(n+1)R` in the induced graph has zero `n`-step coefficient. -/
theorem interactionChainTargetWeightSum_eq_zero_of_lt_edist
    (F : Finset (Finset V)) (w : Finset V → ℝ) (G : SimpleGraph V) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ z ∈ X, ∃ p : G.Walk a z, p.length ≤ R)
    (y : V) (n : ℕ) (X : Finset V) (hX : X ∈ F) (a : V) (ha : a ∈ X)
    (hd : (((n + 1) * R : ℕ) : ℕ∞) < G.edist a y) :
    interactionChainTargetWeightSum F w y X n = 0 := by
  apply interactionChainTargetWeightSum_eq_zero_of_no_walk F w G R hrange y n X hX a ha
  rintro ⟨p, hp⟩
  exact (not_le_of_gt hd) (p.edist_le.trans (ENat.natCast_le_natCast.mpr hp))

/-- Infinite graph distance forces every finite chain coefficient to vanish exactly. -/
theorem interactionChainTargetWeightSum_eq_zero_of_edist_eq_top
    (F : Finset (Finset V)) (w : Finset V → ℝ) (G : SimpleGraph V) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ z ∈ X, ∃ p : G.Walk a z, p.length ≤ R)
    (y : V) (n : ℕ) (X : Finset V) (hX : X ∈ F) (a : V) (ha : a ∈ X)
    (hd : G.edist a y = ⊤) : interactionChainTargetWeightSum F w y X n = 0 := by
  apply interactionChainTargetWeightSum_eq_zero_of_lt_edist F w G R hrange y n X hX a ha
  rw [hd]
  exact ENat.natCast_lt_top _

/-- The weighted chain indicator bound used before the exponential series in Lemma 4.1.
The constants depend on the support cardinality and site budget, not the domain size. -/
theorem interactionChainTargetWeightSum_le_indicator_pow
    (F : Finset (Finset V)) (w : Finset V → ℝ) (G : SimpleGraph V)
    (R v : ℕ) (b : ℝ) (hb : 0 ≤ b) (hw : ∀ X ∈ F, 0 ≤ w X)
    (hcard : ∀ X ∈ F, X.card ≤ v)
    (hsite : ∀ a, (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤ b)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ z ∈ X, ∃ p : G.Walk a z, p.length ≤ R)
    (y : V) (n : ℕ) (X : Finset V) (hX : X ∈ F) (a : V) (ha : a ∈ X) :
    interactionChainTargetWeightSum F w y X n ≤
      if G.edist a y ≤ (((n + 1) * R : ℕ) : ℕ∞) then ((v : ℝ) * b) ^ n else 0 := by
  classical
  split_ifs with hd
  · exact (interactionChainTargetWeightSum_le F w hw y n X).trans
      (interactionChainWeightSum_le_pow F w v b hb hw hcard hsite n X hX)
  · rw [interactionChainTargetWeightSum_eq_zero_of_lt_edist F w G R hrange y n X hX a ha
      (lt_of_not_ge hd)]

end TNLean.PEPS.AreaLaw
