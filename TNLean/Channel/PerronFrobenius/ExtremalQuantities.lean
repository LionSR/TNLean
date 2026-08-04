/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Extremal quantities r(X) and rTilde(X) for positive maps

For a positive map `T` on `M_D(ℂ)`, Wolf defines on the cone of positive
semidefinite operators the functionals `r(X) := sup {λ ∈ ℝ | (T - λ id)(X) ≥ 0}`
and `rTilde(X) := inf {λ ∈ ℝ | (T - λ id)(X) ≤ 0}` (Equations (6.29)--(6.30)),
and then the maxima `r := sup_{X ≥ 0} r(X)` and `rTilde := sup_{X ≥ 0} rTilde(X)`
in the text below those equations.

## Main definitions

* `PerronFrobeniusExtremal.rSet`: the set `{λ ∈ ℝ | (T - λ id)(X) ≥ 0}`.
* `PerronFrobeniusExtremal.r` and `PerronFrobeniusExtremal.rTilde`: the
  extremal functionals of Wolf Equations (6.29) and (6.30).
* `PerronFrobeniusExtremal.rMax` and `PerronFrobeniusExtremal.rTildeMax`: the
  maxima `r` and `rTilde` over nonzero positive semidefinite `X`.

## Implementation notes

Wolf's functionals are defined only on the cone of positive semidefinite
operators, and the defining sets carry no sign restriction on `λ`.  The Lean
definitions are total, so on the degenerate input `X = 0` they return junk
values: `rSet T 0 = Set.univ` (since `T 0 - λ • 0 = 0` is positive semidefinite
for every `λ`), and Mathlib's totalized `sSup`/`sInf` of an unbounded set are
`0`, hence `r T 0 = 0` and `rTilde T 0 = 0` rather than the extended-real
`+∞`/`−∞` of the source formulas.  Meaningful use requires `X.PosSemidef` and
`X ≠ 0`; for a positive map `T` the defining sets are then nonempty and
bounded, so `r T X` and `rTilde T X` agree with the source supremum/infimum.
The maxima `rMax`/`rTildeMax` range over nonzero PSD `X`, matching Wolf's
remark that the sets "are compact or can be made so, e.g., by imposing
`tr[X] = 1`".

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6,
  Equations (6.29)--(6.30) and the maxima defined in the text below them;
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
  lines 608--619 (definitions) and 635--637 (compactness remark).

## Tags

positive maps, Perron--Frobenius, spectral radius, extremal quantities
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {D : ℕ}

namespace PerronFrobeniusExtremal

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The set `{λ ∈ ℝ | (T - λ id)(X) ≥ 0}` whose supremum is Wolf's `r(X)`,
Equation (6.29).  Wolf's functional is defined on the cone of positive
semidefinite operators; the set itself carries no sign restriction on `λ`.
For `X = 0` the set is `Set.univ`, since `T 0 - λ • 0 = 0` is positive
semidefinite for every `λ`. -/
def rSet (T : Mat →ₗ[ℂ] Mat) (X : Mat) : Set ℝ :=
  {t : ℝ | (T X - (t : ℂ) • X).PosSemidef}

/-- `r(X) = sup {λ ∈ ℝ | (T - λ id)(X) ≥ 0}`, Wolf Equation (6.29).
The meaningful domain is nonzero positive semidefinite `X`: at `X = 0` the set
`rSet T 0` is `Set.univ`, so `r T 0` is the junk value `sSup Set.univ = 0` of
Mathlib's totalized `sSup`, not the extended-real `+∞` of the source formula. -/
noncomputable def r (T : Mat →ₗ[ℂ] Mat) (X : Mat) : ℝ :=
  sSup (rSet T X)

/-- `rTilde(X) = inf {λ ∈ ℝ | (T - λ id)(X) ≤ 0}`, Wolf Equation (6.30).
As for `r`, the meaningful domain is nonzero positive semidefinite `X`; at
`X = 0` the defining set is `Set.univ`, so `rTilde T 0` is the junk value
`sInf Set.univ = 0` of Mathlib's totalized `sInf`. -/
noncomputable def rTilde (T : Mat →ₗ[ℂ] Mat) (X : Mat) : ℝ :=
  sInf {t : ℝ | (T X - (t : ℂ) • X) ≤ 0}

/-- The maximum `r := sup_{X ≥ 0} r(X)` of Wolf's extremal functional, defined
in the text between Equations (6.29)--(6.30) and Theorem 6.3 (local source
lines 617--619).  The range is restricted to nonzero `X`, matching Wolf's
remark that the sets "can be made [compact], e.g., by imposing `tr[X] = 1`"
(local source lines 635--637), and avoiding the junk value of `r` at `X = 0`. -/
noncomputable def rMax (T : Mat →ₗ[ℂ] Mat) : ℝ :=
  sSup (r T '' {X | X.PosSemidef ∧ X ≠ 0})

/-- The maximum `rTilde := sup_{X ≥ 0} rTilde(X)` of Wolf's second extremal
functional, defined in the same source passage as `rMax` (Wolf Chapter 6, text
between Equations (6.29)--(6.30) and Theorem 6.3; local source lines 617--619).
As for `rMax`, the range excludes `X = 0`, where `rTilde` takes its junk
value. -/
noncomputable def rTildeMax (T : Mat →ₗ[ℂ] Mat) : ℝ :=
  sSup (rTilde T '' {X | X.PosSemidef ∧ X ≠ 0})

end PerronFrobeniusExtremal
