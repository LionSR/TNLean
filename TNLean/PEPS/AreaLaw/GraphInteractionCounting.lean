/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphInteractionBudget
import TNLean.PEPS.AreaLaw.GraphLatticeCounting

/-!
# Uniform interaction counting in finite square-lattice domains

This file combines the bounded-walk lattice count with the one-term-per-support power-set
count. The graph is arbitrary, with an injective integer-coordinate map and nearest-neighbor
edges. Consequently the constants are independent of the finite domain, its holes, and its
connected components. Pairwise support walks remain in the full graph.

The auxiliary constants are $v = (2R+1)^2$ and $μ = 2^{v-1}$, using the containing square.
These are conservative alternatives to the manuscript's exact diamond count
$v_R = 1+2R(R+1)$ and $μ_R = 2^{v_R-1}$. This file proves counting and chain-weight bounds
only. The commutator differential inequality and conditional-expectation localization are
separate obligations for the graph-distance propagation theorem.

## References and provenance

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 2 (local counting) and Lemma 4.1 (interaction-chain iteration), pinned source
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proofs are original; no OpenAI Lean declaration or proof text is reused.
-/

open scoped BigOperators

/-!
## Declaration provenance for issue #8745

Provenance-ID: 8745-tnlean.peps.arealaw.card_support_le_square
Downstream declaration: TNLean.PEPS.AreaLaw.card_support_le_square
Provenance-ID: 8745-tnlean.peps.arealaw.card_supports_containing_le_square
Downstream declaration: TNLean.PEPS.AreaLaw.card_supports_containing_le_square
Provenance-ID: 8745-tnlean.peps.arealaw.sum_supportweights_containing_le_square
Downstream declaration: TNLean.PEPS.AreaLaw.sum_supportWeights_containing_le_square
Provenance-ID: 8745-tnlean.peps.arealaw.interactionchainweightsum_le_lattice_pow
Downstream declaration: TNLean.PEPS.AreaLaw.interactionChainWeightSum_le_lattice_pow
Source: September 24, 2026.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/01-preliminaries.tex
Labels: eq:ball-count.
Source: September 24, 2026.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/03-quasilocal.tex
Labels: eq:quasilocal-budget, lem:quasilocal-lr.
Independently formalized; no upstream Lean proof text reused.
These are auxiliary graph and counting results, not the complete propagation or area-law theorem.
-/

namespace TNLean.PEPS.AreaLaw

variable {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}

omit [Finite V] [DecidableEq V] in
/-- Every finite interaction support with graph range at most $R$ obeys the auxiliary square
cardinality bound. The empty support is included in this combinatorial statement. -/
theorem card_support_le_square (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (X : Finset V) (R : ℕ)
    (hrange : ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R) :
    X.card ≤ (2 * R + 1) ^ 2 := by
  classical
  by_cases hX : X.Nonempty
  · obtain ⟨a, ha⟩ := hX
    exact card_le_square_of_walks coord X hcoord hstep a R (hrange a ha)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hX
    simp [hX]

/-- The number of original supports containing any specified site is uniformly bounded by
$2^{(2R+1)^2-1}$, using the auxiliary square count. The family contains one copy of each
support; finite-range paths are paths in the full graph. -/
theorem card_supports_containing_le_square (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (a : V) : (F.filter (fun X => a ∈ X)).card ≤ 2 ^ ((2 * R + 1) ^ 2 - 1) := by
  classical
  let := Fintype.ofFinite V
  let B : Finset V := Finset.univ.filter (fun x => ∃ p : G.Walk a x, p.length ≤ R)
  have haB : a ∈ B := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ a, SimpleGraph.Walk.nil, by simp⟩
  have hB : B.card ≤ (2 * R + 1) ^ 2 := by
    apply card_le_square_of_walks coord B hcoord hstep a R
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hFB : ∀ X ∈ F.filter (fun X => a ∈ X), a ∈ X ∧ X ⊆ B := by
    intro X hX
    obtain ⟨hXF, haX⟩ := Finset.mem_filter.mp hX
    refine ⟨haX, ?_⟩
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hrange X hXF a haX x hx⟩
  calc
    (F.filter (fun X => a ∈ X)).card ≤ 2 ^ (B.card - 1) :=
      card_supportFamily_le_pow _ B a haB hFB
    _ ≤ 2 ^ ((2 * R + 1) ^ 2 - 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hB 1)

/-- Weights of original terms containing a site satisfy a uniform interaction budget.
For operator norms the nonnegative term-bound parameter is the source parameter $J$. -/
theorem sum_supportWeights_containing_le_square (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J) (hw : ∀ X ∈ F, w X ≤ J) (a : V) :
    (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤
      (2 ^ ((2 * R + 1) ^ 2 - 1) : ℕ) * J := by
  have hcard := card_supports_containing_le_square coord hcoord hstep F R hrange a
  calc
    (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤
        ∑ X ∈ F.filter (fun X => a ∈ X), J := by
      apply Finset.sum_le_sum
      intro X hX
      exact hw X (Finset.mem_filter.mp hX).1
    _ = ((F.filter (fun X => a ∈ X)).card : ℝ) * J := by simp
    _ ≤ (2 ^ ((2 * R + 1) ^ 2 - 1) : ℕ) * J :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hJ

/-- Interaction-chain continuations have total weight at most $κ^n$ uniformly in the
finite lattice domain, with the auxiliary constants $v=(2R+1)^2$, $μ=2^{v-1}$ and $κ=vμJ$.
No gap, Hermiticity or subsystem hypothesis is needed for this counting estimate. -/
theorem interactionChainWeightSum_le_lattice_pow (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hw0 : ∀ X ∈ F, 0 ≤ w X) (hwJ : ∀ X ∈ F, w X ≤ J)
    (n : ℕ) (X : Finset V) (hX : X ∈ F) :
    interactionChainWeightSum F w X n ≤
      (((2 * R + 1) ^ 2 : ℕ) * ((2 ^ ((2 * R + 1) ^ 2 - 1) : ℕ) * J)) ^ n := by
  apply interactionChainWeightSum_le_pow F w ((2 * R + 1) ^ 2)
    ((2 ^ ((2 * R + 1) ^ 2 - 1) : ℕ) * J)
    (mul_nonneg (Nat.cast_nonneg _) hJ) hw0 _ _ n X hX
  · intro Y hY
    exact card_support_le_square coord hcoord hstep Y R (hrange Y hY)
  · intro a
    exact sum_supportWeights_containing_le_square coord hcoord hstep F R hrange w J hJ hwJ a

end TNLean.PEPS.AreaLaw
