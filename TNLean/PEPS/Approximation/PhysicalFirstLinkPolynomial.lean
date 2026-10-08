/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PhysicalFirstPolynomial
import TNLean.PEPS.Approximation.SourceAlphabetPolynomial

/-!
# Polynomial link dimensions from original gate resources

The actual physical-first source replacement has one polynomial bound for
both its branch-pair links and its sample links. The coefficient and exponent
are explicit expressions in the original uniform bounds and the requested
accuracy exponent. They do not depend on the particular construction, its
private dimensions, or its source Schmidt ranks.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229 and 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-original-sampling-physicalfirstlinkpolynomial-01
TNLean.PEPS.PairEffect.OriginalCircuit.card_physicalFirstNetworkAlphabet_le_power
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.OriginalCircuit
open TNLean.PEPS.Approximation
variable {P : Type} [DecidableEq P] {a : Layout P}

open Classical in
/-- The actual star and sample alphabets obey a single polynomial bound
whose constants depend only on the original resource bounds. This holds for
any retained collection of gate occurrences and any choice of its roots.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem card_physicalFirstNetworkAlphabet_le_power
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    (K r N arity lifetime : ℕ) (B D L C_K C_N C_B C_D : ℝ)
    (u n s d p : ℕ)
    (hb : w.IsExpansionBounded r B) (hmonomial : w.IsMonomialBounded K)
    (hpart : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity)
    (hcount : w.nonprivateCount ≤ N)
    (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCN : 1 ≤ C_N) (hCB : 0 ≤ C_B)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hK : (K : ℝ) ≤ C_K * L ^ u) (hN : (N : ℝ) ≤ C_N * L ^ n)
    (hBbound : B ≤ C_B * L ^ s) (hDbound : D ≤ C_D * L ^ d)
    (hδ : 0 < sourceGateBudget (L ^ p)⁻¹ N) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r B).mpr hb)
    let k := sourceSamplingCount (Fintype.card R.sourceLocations)
      (B ^ (4 * lifetime) * D ^ 4) (L ^ p)⁻¹
    let C_sources := max 1 (C_N * (arity.choose 2 : ℝ))
    let C_branch := C_K * (64 * C_N ^ 2 * ((r : ℝ) * C_B) ^ 2 + 2) ^ r
    let C_sample := 64 * C_sources ^ 2 * (C_B ^ (4 * lifetime) * C_D ^ 4) ^ 2 + 2
    ∀ (gates : Finset R.gateLocations) (root : R.gateLocations → P)
      (e : DistributedOperatorContraction.Link gates R.participants root),
      (Fintype.card (DistributedOperatorContraction.alphabet gates R.participants root
        (fun g ↦ R.branchLabels g × R.branchLabels g) k e) : ℝ) ≤
        (C_branch ^ 2 + C_sample) *
          L ^ (max (2 * (u + 2 * r * (n + s + p)))
            (2 * (n + 4 * lifetime * s + 4 * d + p))) := by
  intro R k C_sources C_branch C_sample gates root e
  apply R.card_sourceNetworkAlphabet_le_of_power_bounds gates root k L C_branch C_sample
    (u + 2 * r * (n + s + p)) (2 * (n + 4 * lifetime * s + 4 * d + p)) hL
  · dsimp [C_branch]
    positivity
  · dsimp [C_sample]
    positivity
  · intro g _
    exact w.card_branchLabels_physicalFirstReplacement_le_power physical priv
      K r N B L C_K C_N C_B u n s p hb hmonomial hL hCK hCN hCB hB
      hK hN hBbound hδ g
  · exact (w.sourceSamplingCount_physicalFirstReplacement_lt_power physical priv hδ hb
      hpart L C_N C_B C_D n s d p hL hCB hB hD
      ((Nat.cast_le.mpr hcount).trans hN) hBbound hDbound).le

end TNLean.PEPS.PairEffect.OriginalCircuit
