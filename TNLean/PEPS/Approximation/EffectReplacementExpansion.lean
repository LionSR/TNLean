/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.EffectReplacementCoefficients

/-! # Expansion bounds of the actual source-only circuit

The original monomial count, effect bound and absolute coefficient-sum bound
imply expansion bounds at every gate of the constructed replacement. Private
operations, retained spectators and register permutations leave these bounds
unchanged.

Source: polynomial-PEPS 04-compression.tex, lines 199–212 and 229.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-effectreplacementexpansion-01
TNLean.PEPS.PairEffect.OriginalCircuit.IsMonomialBounded
Provenance-ID: 8769-source-resource-effectreplacementexpansion-02
TNLean.PEPS.PairEffect.OriginalCircuit.isExpansionBounded_replacement
Provenance-ID: 8769-source-resource-effectreplacementexpansion-03
TNLean.PEPS.PairEffect.SourceCircuit.IsExpansionBounded
Provenance-ID: 8769-source-resource-effectreplacementexpansion-04
TNLean.PEPS.PairEffect.SourceCircuit.isExpansionBounded_castLayouts
Provenance-ID: 8769-source-resource-effectreplacementexpansion-05
TNLean.PEPS.PairEffect.SourceCircuit.isExpansionBounded_exchangeBlocks
Provenance-ID: 8769-source-resource-effectreplacementexpansion-06
TNLean.PEPS.PairEffect.SourceCircuit.isExpansionBounded_frameList
Provenance-ID: 8769-source-resource-effectreplacementexpansion-07
TNLean.PEPS.PairEffect.SourceCircuit.isExpansionBounded_ofLocalWord
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

namespace SourceCircuit
/-- Each actual prepared gate obeys the specified monomial count and absolute
coefficient-sum bounds. Private maps and exchanges require no expansion.
Source: polynomial-PEPS 04-compression.tex, lines 65–67 and 199–212. -/
def IsExpansionBounded (K : ℕ) (S : ℝ) : {a b : Layout P} → SourceCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsExpansionBounded K S ∧ v.IsExpansionBounded K S
  | _, _, .localMap .. => True
  | _, _, @SourceCircuit.gate _ _ ι _ _ _ _ _ c _ _ =>
      Fintype.card ι ≤ K ∧ (∑ ξ, ‖c ξ‖) ≤ S
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsExpansionBounded K S

/-- Identifying equal register layouts does not change gate expansion bounds.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem isExpansionBounded_castLayouts {a b a' b' : Layout P}
    (w : SourceCircuit a b) (h : a = a') (h' : b = b') (K : ℕ) (S : ℝ) :
    (w.castLayouts h h').IsExpansionBounded K S ↔ w.IsExpansionBounded K S := by
  cases h
  cases h'
  rfl

/-- Retained spectators do not change gate expansion bounds.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem isExpansionBounded_frameList {K : ℕ} {S : ℝ} {a b : Layout P}
    (w : SourceCircuit a b) (hw : w.IsExpansionBounded K S) (rs : Layout P) :
    (frameList rs w).IsExpansionBounded K S := by
  induction rs with
  | nil => exact hw
  | cons r rest ih => exact ih

/-- A source-free word contains no expanded gates and hence satisfies every
expansion bound. Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
theorem isExpansionBounded_ofLocalWord {a b : Layout P} (w : Word a b)
    (h : w.sources = []) (K : ℕ) (S : ℝ) :
    (ofLocalWord w h).IsExpansionBounded K S := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      exact ⟨ihw (List.append_eq_nil_iff.mp h).2,
        ihv (List.append_eq_nil_iff.mp h).1⟩
  | localMap => trivial
  | source => cases h
  | swap => trivial
  | frame r w ih => exact ih h

/-- Inserted block exchanges introduce no monomial labels or coefficients.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem isExpansionBounded_exchangeBlocks (a b tail : Layout P) (K : ℕ) (S : ℝ) :
    (exchangeBlocks a b tail).IsExpansionBounded K S :=
  isExpansionBounded_ofLocalWord _ _ K S
end SourceCircuit

namespace OriginalCircuit
/-- The original monomial count is bounded before averaging is expanded.
Source: polynomial-PEPS 04-compression.tex, lines 199–208. -/
def IsMonomialBounded (K : ℕ) : {a b : Layout P} → OriginalCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsMonomialBounded K ∧ v.IsMonomialBounded K
  | _, _, .privateMap .. => True
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ L _ _ _ => L.length ≤ K
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsMonomialBounded K
/-- Every gate of the actual source-only replacement has at most `K m^r`
monomials and coefficient sum at most the original bound `S`. Both bounds are
derived from the original circuit data; inserted exchanges add no gate expansions.
Source: polynomial-PEPS 04-compression.tex, lines 199–212 and 229. -/
theorem isExpansionBounded_replacement {K r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    {a b : Layout P} (w : OriginalCircuit a b) (hb : w.IsExpansionBounded r S)
    (hK : w.IsMonomialBounded K) :
    (w.produce.replacement hδ w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).IsExpansionBounded
        (K * (stackLength r S δ) ^ r) S := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      exact (SourceCircuit.isExpansionBounded_castLayouts _ _ _ _ _).mpr
        ⟨ihw hb.1 hK.1,
          SourceCircuit.isExpansionBounded_frameList _ (ihv hb.2 hK.2) _⟩
  | privateMap => trivial
  | @nonprivateGate C _ owner hC a b L hL hG tail =>
      simp only [produce, EffectCircuit.replacement,
        SourceCircuit.isExpansionBounded_castLayouts]
      change Fintype.card (Fin (wordList (stackLength r S δ) L).length) ≤
        K * (stackLength r S δ) ^ r ∧
        (∑ i, ‖replacementCoefficients (stackLength r S δ) δ L i‖) ≤ S
      exact ⟨(card_replacementLabels_le (stackLength_ne_zero r S δ) L hb.1).trans
        (Nat.mul_le_mul_right _ hK),
        (sum_norm_replacementCoefficients_le (stackLength_ne_zero r S δ) hδ.le L).trans hb.2⟩
  | swap => trivial
  | frame t w ih =>
      exact ⟨ih hb hK, SourceCircuit.isExpansionBounded_exchangeBlocks _ _ _ _ _⟩
end OriginalCircuit
end TNLean.PEPS.PairEffect
