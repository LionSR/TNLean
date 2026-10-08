/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.SourceOnlyReduction

/-! # Coefficients and monomial counts after pair-effect elimination

The actual coefficient function of the replacement has no larger absolute sum
than the original expansion. Its actual finite label type has at most `K * m^r`
elements. The chosen stack length is bounded by `(r * S / δ)^2 + 2`.

Source: polynomial-PEPS 04-compression.tex, lines 65–67 and 199–212.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-effectreplacementcoefficients-01
TNLean.PEPS.PairEffect.card_replacementLabels_le
Provenance-ID: 8769-source-resource-effectreplacementcoefficients-02
TNLean.PEPS.PairEffect.card_replacementLabels_stackLength_le
Provenance-ID: 8769-source-resource-effectreplacementcoefficients-03
TNLean.PEPS.PairEffect.exists_prepared_effectReplacement_uniform_resources
Provenance-ID: 8769-source-resource-effectreplacementcoefficients-04
TNLean.PEPS.PairEffect.length_wordList_le
Provenance-ID: 8769-source-resource-effectreplacementcoefficients-05
TNLean.PEPS.PairEffect.stackLength_le
Provenance-ID: 8769-source-resource-effectreplacementcoefficients-06
TNLean.PEPS.PairEffect.sum_norm_coeff_wordList
Provenance-ID: 8769-source-resource-effectreplacementcoefficients-07
TNLean.PEPS.PairEffect.sum_norm_replacementCoefficients
Provenance-ID: 8769-source-resource-effectreplacementcoefficients-08
TNLean.PEPS.PairEffect.sum_norm_replacementCoefficients_le
-/

noncomputable section
namespace TNLean.PEPS.PairEffect

/-- The explicit source-only word expansion preserves the absolute coefficient sum.
Source: polynomial-PEPS 04-compression.tex, lines 65–67 and 120–124. -/
theorem sum_norm_coeff_wordList {C : Type} {a b : Layout C} {m : ℕ}
    (hm : m ≠ 0) (L : PartyGate a b) :
    ((wordList m L).map fun q => ‖q.1‖).sum = (L.map fun q => ‖q.1‖).sum := by
  have h := sum_norm_coeff_termList hm (toGate L)
  simpa only [termList_toGate, List.map_map, Function.comp_def, map_norm_toGate] using h

/-- The labels of the explicit expansion obey the source's monomial count.
Source: polynomial-PEPS 04-compression.tex, lines 65–66 and 120–124. -/
theorem length_wordList_le {C : Type} {a b : Layout C} {m r : ℕ}
    (hm : m ≠ 0) (L : PartyGate a b)
    (hr : ∀ q ∈ L, q.2.toEffectChain.effectCount ≤ r) :
    (wordList m L).length ≤ L.length * m ^ r := by
  have h := length_termList_le hm (toGate L) (fun q hq => by
    obtain ⟨p, hp, rfl⟩ := mem_toGate hq
    exact hr p hp)
  simpa only [termList_toGate, List.length_map, length_toGate] using h

private theorem sum_norm_get {α : Type*} (l : List (ℂ × α)) :
    (∑ i : Fin l.length, ‖(l.get i).1‖) = (l.map fun q => ‖q.1‖).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun q : ℂ × α => ‖q.1‖) ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- Rescaling multiplies the absolute coefficient sum by its single scalar norm.
Source: polynomial-PEPS 04-compression.tex, lines 210–212. -/
theorem sum_norm_replacementCoefficients {C : Type} {a b : Layout C} {m : ℕ}
    (hm : m ≠ 0) (δ : ℝ) (L : PartyGate a b) :
    (∑ i : Fin (wordList m L).length, ‖replacementCoefficients m δ L i‖) =
      ‖(((1 + δ)⁻¹ : ℝ) : ℂ)‖ * (L.map fun q => ‖q.1‖).sum := by
  simp only [replacementCoefficients, norm_mul, ← Finset.mul_sum, sum_norm_get,
    sum_norm_coeff_wordList hm L]

/-- The actual replacement coefficients have no greater absolute sum than the
original coefficients. The averaging expansion and the common rescaling are explicit.
Source: polynomial-PEPS 04-compression.tex, lines 65–67 and 210–212. -/
theorem sum_norm_replacementCoefficients_le {C : Type} {a b : Layout C} {m : ℕ}
    (hm : m ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ) (L : PartyGate a b) :
    (∑ i : Fin (wordList m L).length, ‖replacementCoefficients m δ L i‖) ≤
      (L.map fun q => ‖q.1‖).sum := by
  rw [sum_norm_replacementCoefficients hm δ L]
  have hscalar : ‖(((1 + δ)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hsum : 0 ≤ (L.map fun q => ‖q.1‖).sum := List.sum_nonneg fun x hx => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hscalar hsum

/-- The actual monomial label type has at most the original number of monomials
multiplied by the averaging factor. Source: polynomial-PEPS 04-compression.tex,
lines 65–66 and 120–124. -/
theorem card_replacementLabels_le {C : Type} {a b : Layout C} {m r : ℕ}
    (hm : m ≠ 0) (L : PartyGate a b)
    (hr : ∀ q ∈ L, q.2.toEffectChain.effectCount ≤ r) :
    Fintype.card (Fin (wordList m L).length) ≤ L.length * m ^ r := by
  simpa only [Fintype.card_fin] using length_wordList_le hm L hr

/-- The actual uniformly chosen source-only prepared gate has both the source's
approximation and resource bounds, derived from the original expansion.
Source: polynomial-PEPS 04-compression.tex, lines 199–212. -/
theorem exists_prepared_effectReplacement_uniform_resources {C : Type} [Finite C]
    {a b : Layout C} {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (L : PartyGate a b)
    (hL : ∀ q ∈ L, q.2.IsAllowed ∧ q.2.toEffectChain.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) (hS : (L.map fun q => ‖q.1‖).sum ≤ S) :
    ∃ G : PreparedSourceGate (replacementCoefficients (stackLength r S δ) δ L)
        a (gateOut (stackLength r S δ) L),
      ContinuousLinearMap.isoL (gateIso (stackLength r S δ) L) ∘L G.eval =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) (toGate L) ∧
      ‖G.eval - (prepGate (stackLength r S δ) L).eval ∘L gate (toGate L)‖ ≤ 2 * δ ∧
      (∑ i : Fin (wordList (stackLength r S δ) L).length,
        ‖replacementCoefficients (stackLength r S δ) δ L i‖) ≤
          (L.map fun q => ‖q.1‖).sum ∧
      Fintype.card (Fin (wordList (stackLength r S δ) L).length) ≤
        L.length * (stackLength r S δ) ^ r := by
  obtain ⟨G, he, herr⟩ := exists_prepared_effectReplacement_uniform hδ L hL hG hS
  exact ⟨G, he, herr,
    sum_norm_replacementCoefficients_le (stackLength_ne_zero r S δ) hδ.le L,
    card_replacementLabels_le (stackLength_ne_zero r S δ) L (fun q hq => (hL q hq).2)⟩

/-- The stack length chosen from the original data is bounded by a quadratic
expression before any averaging labels are introduced.
Source: polynomial-PEPS 04-compression.tex, lines 199–208. -/
theorem stackLength_le (r : ℕ) (S δ : ℝ) :
    (stackLength r S δ : ℝ) ≤ (r * S / δ) ^ 2 + 2 := by
  have h := Nat.ceil_lt_add_one (sq_nonneg ((r : ℝ) * S / δ))
  simp only [stackLength, Nat.cast_add, Nat.cast_one]
  linarith

/-- The actual expanded monomial count is polynomial in the original monomial
count and coefficient bound, and in the inverse gate-error budget for fixed `r`.
Source: polynomial-PEPS 04-compression.tex, lines 199–208. -/
theorem card_replacementLabels_stackLength_le {C : Type} {a b : Layout C}
    (r : ℕ) (S δ : ℝ) (L : PartyGate a b)
    (hr : ∀ q ∈ L, q.2.toEffectChain.effectCount ≤ r) :
    (Fintype.card (Fin (wordList (stackLength r S δ) L).length) : ℝ) ≤
      L.length * ((r * S / δ) ^ 2 + 2) ^ r := by
  have h : (Fintype.card (Fin (wordList (stackLength r S δ) L).length) : ℝ) ≤
      (L.length : ℝ) * (stackLength r S δ : ℝ) ^ r := by
    exact_mod_cast card_replacementLabels_le (stackLength_ne_zero r S δ) L hr
  refine h.trans ?_
  gcongr
  exact stackLength_le r S δ

end TNLean.PEPS.PairEffect
