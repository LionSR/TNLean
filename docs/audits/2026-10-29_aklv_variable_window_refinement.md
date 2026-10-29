# Physical AKLV refinement with a variable window

`AKLV/VariableWindowRefinement.lean` proves one actual physical refinement
step that retains the sharp polynomial rank estimate. It is applicable both
to the fixed-window changing-target entropy construction and to the separate
accuracy-dependent window choice for the sharper MPS approximation.
Neither complete argument is asserted by this bounded theorem.

## Physical statement and constructed objects

The original Hamiltonian is a sum of positive contractions supported on
adjacent pairs of a finite chain. Its supplied unit ground vector Ω has
energy μ and positive rank-one projector gap g, with μ+g in the actual
spectrum. The local dimension bound q≥2 and gap bound g≤1 are derived.
A unit input x satisfies \(\|x-\Omega\|^2\le1/16\); no rank bound on x,
filter, regional minima, clipped target, spectral ceiling or perturbation
bound is supplied.

For every fitting window s≥6 at position a, the theorem constructs genuine
minima eⱼ of the three reference regional sums and their common minimizing
vector. These are fixed before the truncation threshold. The centered ground
energy satisfies E₀+Σeⱼ=μ and 0≤E₀≤6.

For every \(t\ge T(g)=1024+16\log(1/g)\), the actual two-exterior clipped
Hamiltonian Bₜ is positive and has norm at most 2t+s. An actual unit ground
vector φₜ has energy Eₜ≥0, projector gap at least 9g/10 and

\[
\|\phi_t-\Omega\|^2\le e^{-t/16}/100.
\]

This target and its energy are chosen before the degree. The input obeys
\(\|x-\phi_t\|^2\le1/4\) and \(|\langle\phi_t,x\rangle|\ge1/2\).
For every natural degree ℓ, a real polynomial p has degree exactly ℓ and
p(Eₜ)=1. Its actual matrix K=p(Bₜ) fixes φₜ and has

\[
\operatorname{OSR}_{a+\lfloor s/2\rfloor}(K)\le
D_{s,\ell}:=\bigl(q(\ell+1)\bigr)^ {
32(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)}.
\]

Set

\[
\delta_{t,\ell}:=
\left(2\exp\left(-2\ell\sqrt{(9g/10)/(2t+s)}\right)\right)^2.
\]

The theorem constructs a unit scalar c with Kx≠0 such that the single actual
vector \(\psi=cKx/\|Kx\|\) is unit and satisfies

\[
\operatorname{SR}_{a+\lfloor s/2\rfloor}(\psi)
 \le D_{s,\ell}\operatorname{SR}_{a+\lfloor s/2\rfloor}(x),
\]
\[
\|\psi-\phi_t\|^2\le8\delta_{t,\ell}\|x-\phi_t\|^2,
\qquad
\|\psi-\Omega\|^2\le16\delta_{t,\ell}+e^{-t/16}/50.
\]

The stronger first inequality follows from contraction of orthogonal
projection: the component of x perpendicular to φₜ has norm at most
\(\|x-\phi_t\|\). It is suitable for the changing-target induction, in
which that input distance decreases with the step index. The rank estimate
is derived for the same actual normalized image, by applying the cut-coordinate
intertwining identity and the operator-to-vector Schmidt rank bound.

The adopted physical initialization theorem supplies a unit input x satisfying
the required original-ground error, with its actual rank bound. That theorem
is not assumed as an extra condition on the physical Hamiltonian.

## Source passages and the two parameter choices

The official source is AKLV, arXiv:1301.1162v1,
`/tmp/tnlean-aklv-official-source-20261029/source/1dfrustrated34.tex`, SHA-256
`65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.

* Lines 1003–1013 state Lemma 6.3 (`l:5`). Lines 1018–1022 choose
  tᵢ=t₀+ic. Lines 1025–1045 vary the clipped target and choose
  \(\ell_i=O(\sqrt{(t_i+s)/g})\) with constant shrinking. The loose estimate
  \(\log D_i=O(\ell_i\log q)\) is sufficient for that entropy sequence.
  Lines 1047–1052 accumulate logarithmic rank costs; the printed rank rather
  than logarithm of rank is a typographical error. Lines 1061–1075 use the
  resulting Schmidt tails in the entropy sum.
* Lines 1503–1517 give the separate sharper MPS estimate. For fixed local
  dimension, take t=O(log n), degree
  \(\ell=O(\log n\sqrt{(s+\log n)/g})\), and retain the sharp rank
  \(\widetilde O(\exp(\ell/s+s))\). The accuracy-dependent width
  \(s\asymp(\log n)^{3/4}g^{-1/4}\) then gives the printed subpolynomial
  bond dimension, with the stated logarithmic factors suppressed.

A fixed-width construction using only a crude exponential-in-degree rank
estimate would lose that sharper approximation rate. The new statement
therefore retains the full dependence on s, ℓ and √ℓ. It does not claim that
the scalar optimization, all-cut MPS assembly, finite small-window cases or
coherent changing-target sequence have been completed.

The restriction s≥6, the fitting-window condition, and the actual first
excited energy remain explicit. The regional support and count conventions
are those recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`.

## Verification

Checks use the fully verified read-only TNLean mathematical source
`908de62f163b9505312b914a2fad03dafa23948d`, allowing only its documentation
successor `e6785a190e5ffe603dd9ca238451696c70bdc7b5`, with unchanged QICLean
pin/package `01f237e808b03fb0612ceb617f9bca2c407da927`.
A fresh private namespace contains read-only artifact links; new compiler
outputs are private. The 295 imported TNLean/QICLean sources and objects,
manifest and toolchain are guarded before and after checking. No provider,
package, cache or Mathlib artifact is changed; the own worktree has no `.lake`.
No ordinary build is queued by this contribution.

The new module and the small initialization proof refactor pass actual
named-module strict checking, with default heartbeats, strict implicit
arguments, Mathlib standard linters and warnings as errors:

| Module | Source SHA-256 | Seconds |
|---|---|---:|
| `AKLV/VariableWindowRefinement.lean` | `4d182d31550fc3a51122bb312dd9903e6a0ba249daadf7edb45282f804900332` | 14.00 |
| `AKLV/Initialization.lean` | `a2b2ceed7b74d76c06cfb110e0ffb051d74f25d834dacdd18d59e5bee61d949d` | 14.44 |

Imported manual foundation inspection of both public theorems passes in
4.01 seconds, with only `propext`, `Classical.choice` and `Quot.sound`.
Both changed sources and private objects are hash-checked before and after
inspection; its source remains under `/tmp`, not in the repository.

The initialization statement is unchanged. Its squared-triangle proof now
uses Mathlib's `add_sq_le`, as do both new squared comparisons. This removes
the third repeated hand-written squared-difference argument; the existing
abstraction and the refactored occurrences are recorded in the tactic ledger.
The scoped tactic scan finds no repeated blocks at its default thresholds.

Place `ch35_aklv_variable_window_refinement.tex` after
`ch35_aklv_initialization.tex`. No generated aggregator, chapter registration
or dependency-pin change is included. Ordinary module and compiled-blueprint
verification remain with common integration.

## Completed common verification

The integrated mathematical revision
`f5e011c2e551b318e6df7f7d6e5e81725dedea7a`, with the module-docstring-only
successor `4bdda88ad1455106fd05ba6d874ecd1aca53aadb` and exact QICLean pin
`4175de302e6b580d1bbb4a022f57424ab9f05e73`, passed the full 15,112-job
build, strict checks, imported foundations and compiled blueprint checks.
Only the standard three axioms occur. Prose, integrity, paper-gap and
changed-module timing checks passed; Mathlib was not rebuilt. Detailed
scope and timing qualifications are recorded in
`docs/audits/2026-10-29_verified_soft_residual_refinement_range.md`.
