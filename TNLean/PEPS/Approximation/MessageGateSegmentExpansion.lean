/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.MessageGateExpansion

/-!
# Weighted gates as message-free segments

An existing finite weighted list of party monomials can be regarded as a
list of message monomials by placing each party monomial in a segment.
Expanding this list returns the original weighted list exactly. Its order,
repeated terms, zero coefficients, and empty-list case are preserved.
The underlying party monomials remain unchanged, so any later source-count
bound concerns the same monomials.

This identity is an auxiliary for the allowed expansions in polynomial-PEPS
Theorem 5.2. It does not assert the complete protocol resource bounds.
Source: September 24, 2026, polynomial-PEPS manuscript, `04-compression.tex`,
allowed monomials and message expansion, lines 32–43; `thm:compression`,
Theorem 5.2, lines 143–149.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.PairEffect.MessageGate

variable {P : Type} {a b : Layout P}

/-- Regarding every party monomial as a message-free segment and then
expanding gives the original weighted list, including order and multiplicity.
No allowedness or quantitative bound is required for this algebraic identity.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43
and 143–149. -/
@[simp]
theorem expand_map_segment (A : PartyGate a b) :
    expand (A.map fun q ↦ (q.1, MessageMonomial.segment q.2)) = A := by
  simp [expand, MessageMonomial.expand, List.flatMap_map]

end TNLean.PEPS.PairEffect.MessageGate
