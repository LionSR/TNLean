# Issue #138 blocker audit — operator Jensen / Ando–Lieb

## Scope

This pass re-audited the remaining Wolf Chapter 5 operator-convexity gap in the
current `main`-based worktree, with the target declarations

- `IsPositiveMap.cor52_item1_rpow_of_subunital`
- `IsPositiveMap.cor52_item2_rpow_of_subunital`
- `IsPositiveMap.cor52_item3_log_of_subunital`

from `TNLean/Channel/Schwarz/OperatorMonotone.lean`, and the downstream
Ando–Lieb goal.

No honest proof edit to those declarations landed in this pass.

## Current available infrastructure

### Mathlib

Available on the current toolchain:

- operator monotonicity of $x \mapsto x^p$ for $p \in [0,1]$:
  `CFC.monotone_rpow`, `CFC.rpow_le_rpow`
- operator monotonicity of $\log$ on strictly positive operators:
  `CFC.log_monotoneOn`, `CFC.log_le_log`
- order-reversing inverse API on positive invertible operators:
  `CStarAlgebra.inv_le_inv`, `inv_le_inv_iff`
- the auxiliary operator-monotone function
  $x \mapsto 1 - (1 + x)^{-1}$:
  `CFC.monotoneOn_one_sub_one_add_inv_real`

Still explicitly missing upstream:

- operator concavity of $x^p$ on $[0,1]$
- operator convexity of $x^p$ on $[1,2]$
- operator concavity of $\log$
- a general operator Jensen theorem for positive unital/subunital maps

The current Mathlib source still says this out loud:

- `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean`
  lists TODOs for operator concavity/convexity of `rpow`
- `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`
  lists a TODO for operator concavity of `log`

### TNLean

Already proved in the repo:

- `Matrix.IsHermitian.trace_cfc_eq_sum` and `_re`
- `Matrix.diagonal_jensen_of_convexOn`
- `TNLean.trace_rpow_concave`, `TNLean.trace_rpow_convex`
- `PositiveOnAbelian.diagonal_family_schwarz_le`
- `map_conjTranspose_mul_map_le_of_normal_of_subunital`

These suffice for the trace-valued Chapter 5 consequences and for the quadratic
case $p = 2$, but not for the full operator-valued Jensen statements.

## Exact reduction of Corollary 5.2

Let $A \ge 0$ and write its spectral decomposition as
$$
A = \sum_i \lambda_i P_i,
$$
with orthogonal spectral projections $P_i$ and scalars $\lambda_i \ge 0$.
For a positive map $T$, set
$$
B_i := T(P_i).
$$
Then each $B_i \ge 0$, and
$$
\sum_i B_i = T(1) \le 1
$$
for the subunital cases, or $\sum_i B_i = 1$ in the unital log case. Also,
$$
T(A) = \sum_i \lambda_i B_i,
\qquad
T(A^p) = \sum_i \lambda_i^p B_i,
\qquad
T(\log A) = \sum_i (\log \lambda_i) B_i.
$$
So the three target theorems reduce to the following finite-POVM Jensen
inequalities for a positive family $\{B_i\}$:

1. for $r \in [0,1]$,
   $$
   \sum_i \lambda_i^r B_i \le \left(\sum_i \lambda_i B_i\right)^r;
   $$
2. for $r \in [1,2]$,
   $$
   \left(\sum_i \lambda_i B_i\right)^r \le \sum_i \lambda_i^r B_i;
   $$
3. for $\lambda_i > 0$,
   $$
   \sum_i (\log \lambda_i) B_i \le
   \log\left(\sum_i \lambda_i B_i\right).
   $$

This is exactly the Hansen–Pedersen / Choi–Davis–Jensen phenomenon.

## What the current repo can already do

The existing abelian-domain machinery proves the quadratic family inequality
$$
\left(\sum_i \overline{z_i} B_i\right)
\left(\sum_i z_i B_i\right)
\le
\sum_i |z_i|^2 B_i,
$$
namely `PositiveOnAbelian.diagonal_family_schwarz_le`.

Applied to $z_i = \lambda_i$, this gives the endpoint
$$
T(A)^2 \le T(A^2),
$$
which is the $p = 2$ instance of Corollary 5.2(2), and equivalently the
$p = 1/2$ endpoint of Corollary 5.2(1). The normal-input Schwarz theorem gives
the same endpoint.

However, this quadratic argument does **not** extend by itself to arbitrary real
exponents. The missing step is precisely a compression/Jensen theorem for
noncommuting positive families.

## Precise blocker

The smallest reusable missing theorem family is one of the following
mathematically equivalent packages.

### Option A: Hansen compression inequalities

For a contraction or isometry $V$ and a positive matrix $X$:

- if $r \in [0,1]$,
  $$
  V^\dagger X^r V \le (V^\dagger X V)^r;
  $$
- if $r \in [1,2]$,
  $$
  (V^\dagger X V)^r \le V^\dagger X^r V;
  $$
- for $X > 0$,
  $$
  V^\dagger (\log X) V \le \log(V^\dagger X V).
  $$

### Option B: finite-POVM Jensen inequalities

For PSD matrices $B_i$ with $\sum_i B_i \le 1$ (or $= 1$ in the log case),
prove the three displayed inequalities above directly.

### Option C: general operator Jensen theorems

A theorem of the form

- positive subunital map $T$ + operator-concave $f$ with $f(0) \ge 0$
  implies $T(f(A)) \le f(T(A))$
- positive subunital map $T$ + operator-convex $f$ implies
  $f(T(A)) \le T(f(A))$

specialized to $f(x) = x^r$ and $f(x) = \log x$.

At present, neither Mathlib nor TNLean provides any of A/B/C for the non-trace
operator-valued setting.

## Consequence for the three Cor. 5.2 declarations

All three remain honestly blocked on the current repository state.

- `cor52_item1_rpow_of_subunital`: blocked beyond the endpoint $p = 1/2$
- `cor52_item2_rpow_of_subunital`: blocked beyond the endpoint $p = 2$
- `cor52_item3_log_of_subunital`: blocked entirely; monotonicity of `log` is
  not enough without a Jensen/compression theorem

There is also a naming mismatch worth remembering: the third theorem is named
`..._of_subunital`, but its actual hypothesis is unitality
`hUnit : T 1 = 1`, and that stronger hypothesis is the correct one.

## Ando–Lieb

The Ando–Lieb / Lieb joint concavity theorem still needs additional
infrastructure beyond the Cor. 5.2 gap. The standard proof route uses the
integral representation
$$
A^s B^{1-s} = \frac{\sin(\pi s)}{\pi}
\int_0^\infty t^{s-1} A(A+tB)^{-1}B\,dt,
$$
together with resolvent monotonicity / convexity. No such operator-mean API or
matrix-valued integral representation is currently available in Mathlib.

## Recommended next step

A focused follow-up should target the smallest operator-valued Jensen API first,
preferably in one of the equivalent forms above. Once that lands, the three
Cor. 5.2 statements in `OperatorMonotone.lean` should collapse immediately, and
only then does it become realistic to revisit the Ando–Lieb theorem.