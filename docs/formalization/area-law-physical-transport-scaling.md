# Physical transport coefficients and radius smallness

The scalar conversion in `Scan/SubsystemDimensionScale.lean` connects the
physical subsystem bounds to the scanner's logarithmic coefficients. It uses
only the existing physical dimension and rounded-radius results; it introduces
no scanner certificate or additional assumption on auxiliary dimensions.

## Fixed parameters and witnesses

Fix a physical local dimension `q ≥ 1`, a radius coefficient `Cr ≥ 0`, and
arbitrary real transport constants `Cent`, `eent`, `Cen`, `een`. Let

- `A = 1 + (2 Cr + 3)² log q`
- `E = max (0, eent, een)`
- `Cl = 4 E`
- `C = 1 + (|Cent| + |Cen|) A^E`

Then `C ≥ 1`, `Cl ≥ 0`, and `exists_transport_coefficients_log_bound` gives
both coefficient inequalities for every `n` with `log n ≥ 1` and every
`1 ≤ ℓ ≤ transportLogDimBound q (roundedLogRadius Cr n)`. Thus `C` and `Cl`
are chosen before `n`, the domain, scanner, labels, auxiliary dimensions,
history, round family, or replica count. The `log n ≥ 1` threshold is likewise
independent of those choices.

The signed coefficient is bounded by its absolute value. The exponent is
increased to `E` while the base is at least one, then the base is increased
using `E ≥ 0`. Existing Mathlib real-power lemmas perform both steps and the
product-power identity. Increasing the base before normalizing a negative
exponent would reverse the required inequality.

## Radius-smallness conversion

For natural `r ≥ 1`, `transportLogDimBound_le_radius_sq` proves

`transportLogDimBound q r ≤ (1 + 9 log q) r²`.

`mul_transportLogDimBound_le_of_radius_small` therefore converts
`a ≥ 0` and `a r² ≤ c₀ / (1 + 9 log q)` into
`a * transportLogDimBound q r ≤ c₀`.
`exists_pos_radius_smallness_threshold` chooses the positive threshold before
`r` and `a` whenever `c₀ > 0`. For the rounded radius, the existing
`eventually_one_le_roundedLogRadius` supplies `r ≥ 1` when `Cr > 0`.
The coefficient result permits `Cr = 0`; this eventual positive-radius result
does not.

This is the conversion from the premise on `a r₀²` in `08-scanner.tex`, lines
358–359, to the premise on `a ℓ` in `06-transport.tex`, lines 331–350. Source:
[`openai/math@adc7f124`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).

## Use in the next transport estimates

Choose the fixed transport constants first, then the physical logarithmic
constants and smallness threshold. Only afterward fix the system size,
physical scanner, and finite dependent family of actual rounds. The existing
family result may choose its common nonnegative logarithmic error, remainder,
and logarithmic coefficient for that fixed family. None of the scalar constants may depend on the system size,
width, replica count, or selected round.

The actual-move and nonempty split-support bounds in `Scan/TransportDimension`
supply the physical cap. Arbitrary larger admissible transport parameters need
not satisfy it. Unsplit supports continue to carry no dimension bound.
For entropy, coefficient enlargement must be multiplied by a nonnegative error
factor before subtracting the error. For energy, derive nonnegativity of the
actual weighted error from its integrals before multiplying the coefficient
inequality. These scalar results do not change the common family remainder.

The prescribed `Cr` is fixed independently of the final scanner coefficient
`C`. If a later scanner statement requires `C ≥ Cr`, enlarge the final `C`
without changing the radius. A pre-existing arbitrary scanner constant is not
automatically large enough. Growing `D` and `W` remain explicit in downstream
terms such as `n D (log n)^12` and `D² W²`. The weaker premise `r ≤ D` cannot
replace the prescribed rounded logarithmic radius: polynomially growing radii
have polynomially growing physical dimension caps. No bound on `W` is inferred
from `W ≥ 1`, and physical energy-ground-state identification remains separate.

## Regressions and validation

The existing strictly registered `TNLeanTest/ActualSubsystemDimension.lean`
now checks the common quantifier order, dimension one, zero radius coefficient,
mixed-sign coefficients and exponents, radius-one equality, zero rate and
threshold, and the eventual rounded-radius composition. Counterexamples cover
negative-power base monotonicity, bases below one, `n = 1`, an oversized
admissible transport parameter, radius zero, and a negative rate. The four new
public theorems have stock-axiom guards in
`TNLeanTest/ActualSubsystemDimensionAxioms.lean`.

The candidate is source-reviewed only until hosted validation runs. No local
Lean, Lake, cache, dependency, installation, or overlay operation is required
or recorded as passing. The existing CI policy and workflow are unchanged:
strict serial elaboration has a 90-second limit per changed production or test
module, standard linters, and warnings as errors. Hosted validation must run
that production check, the shared-geometry fixture prerequisite and regression
module, both existing physical-dimension axiom audits, the ordinary aggregate
checks, and blueprint declaration/prose checks. Blueprint completion tags for
the new results must wait for that validation.
