/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PhysicalFirstReadout
import TNLean.PEPS.Approximation.EffectReplacementSources
import TNLean.PEPS.Approximation.EffectReplacementPolynomial

/-!
# Polynomial resources of the actual physical-first replacement

The original gate count and arity bound control the number of actual source
positions after effect elimination and the output exchange. Consequently the
sample count has a polynomial bound in the original resources. The same
replacement retains the previously proved polynomial branch-count bound.
All constants are independent of private dimensions and source Schmidt ranks.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229, 342–381 and 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.OriginalCircuit
open TNLean.PEPS.Approximation
variable {P : Type} {a : Layout P}

/-- Exchanging the output blocks preserves the source-position bound obtained
from the original gate count and per-gate participant bound. -/
theorem card_sourceLocations_physicalFirstReplacement_le
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r arity : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (hpart : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity) :
    Fintype.card (w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).sourceLocations ≤
        w.nonprivateCount * arity.choose 2 := by
  rw [EffectCircuit.physicalFirstReplacement,
    SourceCircuit.card_sourceLocations_physicalFirstOutput]
  exact w.card_sourceLocations_replacement_le hδ hb hpart

/-- The actual sample count for the constructed physical-first circuit has an
explicit polynomial bound derived from the original count and arity. The
coefficient is enlarged to at least one only to include the zero-source case. -/
theorem sourceSamplingCount_physicalFirstReplacement_lt_power
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r arity lifetime : ℕ} {B D δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r B)
    (hpart : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity)
    (L C_N C_B C_D : ℝ) (n s d p : ℕ)
    (hL : 1 ≤ L) (hCB : 0 ≤ C_B) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hN : (w.nonprivateCount : ℝ) ≤ C_N * L ^ n)
    (hBbound : B ≤ C_B * L ^ s) (hDbound : D ≤ C_D * L ^ d) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r B).mpr hb)
    let C_sources := max 1 (C_N * (arity.choose 2 : ℝ))
    (sourceSamplingCount (Fintype.card R.sourceLocations)
      (B ^ (4 * lifetime) * D ^ 4) (L ^ p)⁻¹ : ℝ) <
      (64 * C_sources ^ 2 * (C_B ^ (4 * lifetime) * C_D ^ 4) ^ 2 + 2) *
        L ^ (2 * (n + 4 * lifetime * s + 4 * d + p)) := by
  intro R C_sources
  apply sourceSamplingCount_lt_of_gate_power_bounds _ lifetime B D L C_sources C_B C_D
    n s d p hL (le_max_left _ _) hCB hB hD _ hBbound hDbound
  have hc : (Fintype.card R.sourceLocations : ℝ) ≤
      (w.nonprivateCount : ℝ) * (arity.choose 2 : ℝ) := by
    exact_mod_cast w.card_sourceLocations_physicalFirstReplacement_le
      physical priv hδ hb hpart
  calc
    _ ≤ (w.nonprivateCount : ℝ) * (arity.choose 2 : ℝ) := hc
    _ ≤ (C_N * L ^ n) * (arity.choose 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg _)
    _ = (C_N * (arity.choose 2 : ℝ)) * L ^ n := by ring
    _ ≤ C_sources * L ^ n :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans hL) _)

/-- Every gate of the actual physical-first replacement has polynomially many
branches, with its original monomial, coefficient and effect bounds. -/
theorem card_branchLabels_physicalFirstReplacement_le_power
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    (K r N : ℕ) (S L C_K C_N C_S : ℝ) (u n s p : ℕ)
    (hb : w.IsExpansionBounded r S) (hmonomial : w.IsMonomialBounded K)
    (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCN : 1 ≤ C_N) (hCS : 0 ≤ C_S) (hS : 0 ≤ S)
    (hK : (K : ℝ) ≤ C_K * L ^ u)
    (hN : (N : ℝ) ≤ C_N * L ^ n) (hSbound : S ≤ C_S * L ^ s)
    (hδ : 0 < sourceGateBudget (L ^ p)⁻¹ N)
    (g : (w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).gateLocations) :
    (Fintype.card ((w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).branchLabels g) : ℝ) ≤
        C_K * (64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) ^ r *
          L ^ (u + 2 * r * (n + s + p)) := by
  have he := (SourceCircuit.isExpansionBounded_physicalFirstOutput
    (w.produce.auxiliary (stackLength r S (sourceGateBudget (L ^ p)⁻¹ N)))
    physical priv _ (K * stackLength r S (sourceGateBudget (L ^ p)⁻¹ N) ^ r) S).mpr
      (isExpansionBounded_replacement hδ w hb hmonomial)
  have hc : (Fintype.card ((w.produce.physicalFirstReplacement hδ physical priv
      w.isAllowed_produce ((w.isExpansionBounded_produce_iff r S).mpr hb)).branchLabels g) : ℝ) ≤
      ((K * stackLength r S (sourceGateBudget (L ^ p)⁻¹ N) ^ r : ℕ) : ℝ) := by
    exact_mod_cast (he.at_gate g).1
  exact hc.trans (replacementMonomialBound_le_of_power_bounds K r N S L C_K C_N C_S
    u n s p hL hCK hCN hCS hS hK hN hSbound)

end TNLean.PEPS.PairEffect.OriginalCircuit
