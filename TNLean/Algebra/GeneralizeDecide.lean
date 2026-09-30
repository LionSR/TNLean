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

A sibling tactic, `revert_decide_kernel`, covers the simpler case where the
only free datum is already a named local hypothesis in a small finite type
(a lookup-table index, say), and evaluating the reverted, closed proposition
needs the kernel evaluator rather than the elaborator's `decide`.
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

/--
`revert_decide_kernel x₁, …, xₙ` reverts each named local hypothesis `xᵢ` and
closes the resulting goal by `decide +kernel`, which evaluates the closed
proposition by kernel reduction rather than the elaborator's own evaluator.
Use it for a goal whose only free datum is already a bound index into a
small finite type (e.g. a lookup-table equality `f b = g b` for `b : Fin n`),
where plain `decide` is slow enough to need kernel-level reduction.
-/
syntax "revert_decide_kernel" (ppSpace colGt ident)+ : tactic

macro_rules
  | `(tactic| revert_decide_kernel $x:ident) =>
    `(tactic| (revert $x; decide +kernel))
  | `(tactic| revert_decide_kernel $x:ident $xs:ident*) =>
    `(tactic| (revert $x; revert_decide_kernel $xs*))
