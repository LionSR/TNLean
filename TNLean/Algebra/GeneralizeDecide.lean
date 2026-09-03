/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.Basic

/-!
# Deciding a goal after abstracting finitely many finite-type values

Identities between bit polynomials, such as the phase tables of the CZX
circuit tuple, depend on a fixed finite list of values in finite types (bits in
`ZMod 2`, exponents in `ZMod 4`) that occur inside larger expressions
(`x 0`, `(s j).1.1`, and so on). The tactic `generalize_decide` abstracts those
values into fresh variables and then decides the resulting closed statement by
exhaustive evaluation.
-/

/--
`generalize_decide t₁, …, tₙ` replaces each term `tᵢ` by a fresh variable and
closes the goal by `decide +revert`, which quantifies over the fresh variables
and evaluates the resulting closed proposition. The terms must take values in
finite types with decidable equality, and the goal must become a decidable
closed statement once they are abstracted.
-/
syntax "generalize_decide" (ppSpace colGt term),+ : tactic

macro_rules
  | `(tactic| generalize_decide $t:term) =>
    `(tactic| (generalize $t = x; decide +revert))
  | `(tactic| generalize_decide $t:term, $ts:term,*) =>
    `(tactic| (generalize $t = x; generalize_decide $ts,*))
