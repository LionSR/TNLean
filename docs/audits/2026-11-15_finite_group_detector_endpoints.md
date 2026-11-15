# Finite-group detector: an obstruction for every even cyclic order

This audit addresses item 2 of [#8060](https://github.com/LionSR/TNLean/issues/8060),
the finite-group detector `detectG` in arXiv:2405.00439. It gives a new
six-operator counterexample, rather than identifying that detector with the
four-operator commutator already examined in
[#8532](https://github.com/LionSR/TNLean/pull/8532).

**Outcome.** For one fixed depth-two circuit representing the on-site symmetry
\(X^{\otimes N}\), the six-operator detector has value \(-1\) on every normalized
state although the anomaly and the product of domain-wall phases are trivial.
The construction extends to every even cyclic order. It uses coherent
endpoint choices for all intervals. Merely
requiring a single circuit, unitarity, correct interior action, arbitrarily
separated cuts, and injective symmetry-broken ground states does not repair
the claim. A separate Lean module now proves the six-factor order-two matrix
identity for the printed cut order, checked by hosted Lean with strict linter
options. The circuit identification and general even-order calculation below
remain ordinary exact proofs with executable checks, without Lean proofs.

## Source and ordering conventions

The source is `Papers/2405.00439/MPU-DW.tex`, lines 2108–2117: the paragraph
beginning “For the general case of any finite group”, the definitions of
\(X,Y\), and `detectG`. The relevant existing discussion is
`docs/paper-gaps/gs24_truncation_detector_endpoint_dependence.tex`.

Write \(m=o(g)\) and \(T_{rs}=U_g^{[a_r,b_s]}\). At \(m=2\), applying
the truncations in the order described by the source's operational prose
means

\[
  X_{\rm chron}=T_{22}T_{11}T_{00},\qquad
  Y=T_{01}^{\dagger}T_{22}^{\dagger}T_{10}^{\dagger}.
\]

Every displayed operator here acts on kets from right to left. The product
symbol \(\prod_{r=0}^{m}\) in the source does not itself specify a
noncommutative ordering. If read instead as multiplication in increasing
written index, it gives \(X_{\rm inc}=T_{00}T_{11}T_{22}\). Both readings
are audited below.

There is a second, independent discrepancy: the prose says
\(a_0<a_1<b_0<b_1\), then \(a_1<a_2<b_0<b_2<b_1\), whereas the
display after \(X\) requires \(a_0<a_2<a_1<b_0<b_2<b_1\). Call these
the prose and printed geometries. The counterexamples work for **both**;
neither correction of the left-cut inequality resolves the obstruction.

## A single circuit producing a coherent left-endpoint dressing

Let \(X,Z\) denote the Pauli matrices, so \(X^2=Z^2=1\) and
\(XZ=-ZX\). On an even periodic chain, take a first layer of gates
\((ZX)_{2k}\otimes X_{2k+1}\), and a second layer
\(1_{2k-1}\otimes Z_{2k}\). The second layer multiplies the first one on
the left. Both layers consist of disjoint nearest-neighbour gates. Their
product is \(U=X^{\otimes N}\), because each even site has
\(Z(ZX)=X\) and each odd site has \(X\).

For any interval \([a,b]\) with \(a\) even and \(b\) odd, retain exactly
the gates whose two sites belong to the interval. Every even site except
\(a\) retains its second-layer \(Z\); the second-layer gate ending at
\(a\) crosses the left cut and is dropped. Thus, with
\(P_{ab}=\prod_{a\leq k\leq b}X_k\), the truncation is

\[
  T_{ab}=Z_a P_{ab}.
\]

This is one fixed circuit, with one rule for every interval, not an
independently rephased collection of interval operators. Each truncation is
unitary, acts as \(U\) away from its left endpoint inside the interval, and
acts trivially outside. Its adjoint in \(Y\) is its **actual adjoint**
\(P_{ab}Z_a\), not a new truncation of the inverse global symmetry.

Take the symmetry-broken states \(\psi_A=|0\cdots0\rangle\) and
\(\psi_B=|1\cdots1\rangle\). They are injective bond-dimension-one MPS,
exchanged by \(U\), and are the ground states of the gapped Ising interaction
\(\sum_k(1-Z_kZ_{k+1})/2\). Their correlation length is zero. The on-site
representation has trivial three-cocycle and trivial cyclic product of
domain-wall phases. The expected value in `detectG` is therefore \(+1\).

## Exact value of the chronological six-operator detector

First use the printed geometry \(a_0<a_2<a_1<b_0<b_2<b_1\). More
generally, let \(W_a\) be an arbitrary unitary at each left endpoint and set
\(T_{ab}=W_a P_{ab}\), with the same \(W_a\) whenever the left cut is
reused. For \(D=YX_{\rm chron}\), every local tensor factor except the
one at \(a_1\) is the identity. At \(a_1\), the six factors in written
order are

\[
  X\,X\,(W_{a_1}X)^{\dagger}\,X\,(W_{a_1}X)\,X
       =XW_{a_1}^{\dagger}XW_{a_1}.
\]

At \(a_0\) only the common-endpoint factors from \(T_{01}^{\dagger}\)
and \(T_{00}\) act, giving \((W_{a_0}X)^{\dagger}(W_{a_0}X)=1\).
At \(a_2\) the product is
\(X(W_{a_2}X)^{\dagger}(W_{a_2}X)X=1\). At all remaining sites,
there are only powers of \(X\); the forward and backward coverage
multiplicities agree because

\[
  \mathbf1_{[a_0,b_0]}+\mathbf1_{[a_1,b_1]}
   =\mathbf1_{[a_0,b_1]}+\mathbf1_{[a_1,b_0]}.
\]

The \(T_{22}\) interval occurs on both sides and does not change this
coverage equality. Consequently \(D\) is precisely the one-site operator
\(XW_{a_1}^{\dagger}XW_{a_1}\) at \(a_1\).

For the prose geometry \(a_0<a_1<a_2<b_0<b_2<b_1\), the same argument
gives instead the one-site operator \(W_{a_2}^{\dagger}XW_{a_2}X\) at
\(a_2\); every other factor is the identity. In particular, choosing
\(W_a=Z_a\) in either geometry yields

\[
  YX_{\rm chron}=-1,\qquad
  \langle\psi|YX_{\rm chron}|\psi\rangle=-1
\]

for every normalized \(\psi\). These identities refute the arbitrary
circuit-truncation reading of item 2 of #8060, including its order-two
specialization. They do not use the four-factor commutator theorem.

For arbitrary separation, in the printed geometry choose
\((a_0,a_2,a_1,b_0,b_2,b_1)=(0,2L,4L,6L+1,8L+1,10L+1)\), with
\(L\geq1\), on an even ring with \(N\geq12L+2\). For the prose geometry
swap \(a_1,a_2\). All left cuts are even, all right cuts are odd, and all
six positions become mutually far apart as \(L\) increases.

## The alternative reading of the product symbol

For \(X_{\rm inc}=T_{00}T_{11}T_{22}\), use the right-endpoint circuit
already described in #8532: its first layer is \(X_{2k}\otimes(ZX)_{2k+1}\)
and its second is \(Z_{2k+1}\otimes1_{2k+2}\). Retaining gates inside an
even-to-odd interval gives \(T_{ab}=Z_bP_{ab}\).

In either geometry, the only nonidentity local factor of
\(YX_{\rm inc}\) is at \(b_2\). The six factors there reduce to

\[
  X\,(ZX)^{\dagger}\,1\,1\,X\,(ZX)
   =Z X Z X=-1.
\]

Hence the alternative product convention also has a fixed-circuit
counterexample. For clarity, the complete sign calculation is:

| Forward written product | Left dressing \(Z_aP_{ab}\) | Right dressing \(Z_bP_{ab}\) |
| --- | ---: | ---: |
| \(T_{22}T_{11}T_{00}\) | \(-1\) | \(+1\) |
| \(T_{00}T_{11}T_{22}\) | \(+1\) | \(-1\) |

These are whole-chain operator values, for both geometries. In particular,
the old right-endpoint example alone would give **no obstruction** for the
chronological finite-group word. Counting reused endpoints without tracking
their positions within the operator word misses this distinction.

## The obstruction for all even cyclic groups

Let \(m\geq2\), \(\zeta=\exp(2\pi i/m)\), and work on an
\(m\)-dimensional physical site with the shift and clock matrices

\[
 u|q\rangle=|q+1\pmod m\rangle,\qquad
 W|q\rangle=\zeta^q|q\rangle,\qquad Wu=\zeta uW.
\]

The on-site symmetry \(u^{\otimes N}\) represents a generator of the
cyclic group of order \(m\), with trivial anomaly. Replace \((ZX)\otimes X\)
in the left-endpoint circuit by \((Wu)\otimes u\), and replace
\(1\otimes Z\) in the second layer by \(1\otimes W^{\dagger}\).
The full circuit is again the on-site symmetry, and retaining gates inside
an even-to-odd interval gives \(T_{ab}=W_a u^{[a,b]}\).

Use the chronological product \(X=T_{mm}\cdots T_{00}\) and the
source's written undo product
\(Y=T_{01}^{\dagger}T_{m2}^{\dagger}\cdots T_{2m}^{\dagger}T_{10}^{\dagger}\).
For the printed geometry
\(a_0<a_m<\cdots<a_1<b_0<b_m<\cdots<b_1\), every non-endpoint
factor cancels. At \(a_0\) the factor also cancels. At \(a_r\), for
\(1\leq r\leq m\), the local word is

\[
 u^{-(m-r+2)}W^{\dagger}u^{m-r}Wu^2=\zeta^r1.
\]

Indeed \(W^{\dagger}u^kW=\zeta^{-k}u^k\) and \(\zeta^m=1\).
The local scalar for \(r=m\) is one. In the prose geometry
\(a_0<a_1<\cdots<a_m<b_0<b_m<\cdots<b_1\), the local word at
\(a_r\) is instead

\[
 u^{-2}W^{\dagger}u^{-(r-1)}Wu^{r+1}=\zeta^{r-1}1.
\]

All other sites give the identity in both cases: away from a left endpoint
there are only powers of \(u\), and the forward and backward intervals
have the same multisets of left and right cuts. Thus both geometries give
the exact whole-chain operator

\[
 YX=\zeta^{m(m-1)/2}1
   =\begin{cases}-1,&m\text{ even},\\1,&m\text{ odd}.\end{cases}
\]

For every even \(m\), the detector therefore disagrees with the trivial
anomaly and cyclic domain-wall phase product. The \(m\) product states
\(|q\cdots q\rangle\) provide injective symmetry-broken ground states,
for example for the ferromagnetic Potts interaction which assigns energy
one to unequal neighbouring labels. The cuts can have arbitrary separation
and the circuit is homogeneous with period two. For odd \(m\), this
particular homogeneous clock dressing gives one; no claim about arbitrary
odd-order endpoint choices follows from that cancellation.

## Precise additional hypotheses and what they would prove

Within the left-dressed on-site model, there is an exact correction at order
two: \(YX_{\rm chron}=1\) if and only if the endpoint unitary at the larger
of \(a_1,a_2\) commutes with \(X\). This follows directly from the two
residual operators above, using unitarity. For a particular state it suffices
that this residual operator fixes the state. This is an established statement
about this model; no claim is made that it is necessary or sufficient for an
arbitrary anomalous MPU.

For any order \(m\), the on-site family \(T_{ab}=W_a u^{[a,b]}\) does
give \(YX_{\rm chron}=1\) if every \(W_a\) commutes with \(u\). At each
site the endpoint factor then cancels with its reused adjoint, and the
remaining powers of \(u\) cancel by equality of the coverage multiplicities.
This is a sufficient endpoint covariance condition for this explicitly
specified on-site family; it is not asserted for general MPU truncations.

For a general group element of order \(m\), one possible **conditional**
detection statement can be stated without concealing the missing comparison.
Fix the chronological convention and put
\(F_r=T_{rr}\). List the operators whose adjoints occur in the undo sequence
in chronological order as

\[
 D_0=T_{10},\qquad D_s=T_{s+1,m+1-s}\ (1\leq s\leq m-1),
 \qquad D_m=T_{01}.
\]

For a vector \(\psi\), require explicitly:

1. Reference excitation vectors \(v_0,\ldots,v_m\), with
   \(F_0\psi=v_0\).
2. For every \(1\leq r\leq m\), the actual truncation satisfies
   \(F_rv_{r-1}=B^g_{g^rx,g^{r-1}x}v_r\).
3. Reference undo vectors \(w_0,\ldots,w_{m+1}\), with
   \(w_0=v_m\), \(w_{m+1}=\psi\), and
   \(D_s^{\dagger}w_s=w_{s+1}\) for every \(0\leq s\leq m\).

Induction and linearity give
\(X_{\rm chron}\psi=(\prod_{r=1}^m B^g_{g^rx,g^{r-1}x})v_m\), and the
undo identities then give

\[
 YX_{\rm chron}\psi
   =\left(\prod_{r=1}^m B^g_{g^rx,g^{r-1}x}\right)\psi.
\]

Taking the inner product with \(\psi\) gives the corresponding detector
expectation, with a factor \(\|\psi\|^2\), or the source's normalized value
when \(\|\psi\|=1\). This elementary implication is a formulation of
sufficient **extra assumptions**, not a derivation of them from the paper.
The substantive open task is to construct the reference excitations and to
prove each comparison on every intermediate state, including the undo steps,
for a specified class of truncations. Knowing the action only on the initial
ground states is insufficient. Even a common circuit and coherently reused
endpoint factors do not imply the needed identities, as the counterexample
shows.

The source contraction results `truncatedSymmetry_isUnitaryBetween` and
`truncatedSymmetryOfEndpoints_cons_snoc` provide neither these intermediate
state comparisons nor identifications of all source endpoint spaces with one
common chain space. Their documented coordinate-space restriction remains in
`docs/paper-gaps/fbc25_truncated_symmetry_endpoint_unitarity_scope.tex`.
No result in this audit resolves that restriction or the active domain-wall
construction tasks.

## Reproduction and formalization status

Run:

```sh
python3 scripts/audit_finite_group_detector_endpoints.py
```

The script checks all 84 choices of six ordered positions among nine sites,
both geometries, both forward product conventions, both endpoint sides, and
three endpoint matrices \(1,X,Z\): 2,016 local tensor calculations. It
also applies the actual retained two-site circuit gates and their reversed
adjoints to every computational basis vector of a fourteen-site chain for
all eight geometry/order/side combinations: 131,072 detector evaluations.
It checks the full periodic circuit against \(X^{\otimes14}\), the exact
location of the residual sign for separation parameters 1, 2, 5, 20, and
100, and commuting endpoint choices as positive controls. It additionally
checks the two general cyclic local-word formulas at every site and every
local basis label for orders 2 through 20, using modular integer exponents
of \(\zeta\). All arithmetic uses integers, with no numerical tolerance
or floating-point evaluation of roots of unity.

The project retains Lean and Mathlib `v4.36.0-rc1`; this change does not edit
the toolchain or dependency manifest. This checkout has no Lean/Lake executable
or `.lake` cache, and the environment's disabled outbound network prevented
fetching them. Hosted validation is requested through draft
[PR #10641](https://github.com/LionSR/TNLean/pull/10641).

`TNLean/MPS/MPU/FiniteGroupDetectorEndpoint.lean` proves
unitarity for the dressed family, the six-factor matrix identity at order two
for arbitrary printed-order cuts, and its normalized expectation value. It
passed the direct strict Lean check on PR head `2c4976385aabafe8fdf44d0d20b5fe52a5b49973`
in [job 132915070941](https://github.com/LionSR/TNLean/actions/runs/43747633939/job/132915070941),
building in 6.4 seconds. That overall job failed separately because the first
revision of the general group module used a nonexistent tactic import. There
are no axioms or proof placeholders. The exact Python calculation remains
supporting evidence, not a substitute for kernel verification.

`TNLean/MPS/MPU/FiniteGroupDetectorPhase.lean` separately proves the exact group identities
\(u^aw^{-1}u^bwu^d=c^bu^{a+b+d}\) and
\(\prod_{r=0}^{m-1}u^{-r-2}w^{-1}u^rwu^2=c^{\binom m2}\), assuming
\(cu=uc\) and \(w^{-1}uw=cu\). These statements isolate the local
algebra at every order without assuming a whole-detector phase as a
hypothesis. It also derives that the product at order \(2k\) is \(c^k\)
whenever \(c^{2k}=1\). Constructing the clock/shift instance and identifying the full
spatial word with this ordered product remain separate tasks.
Hosted Lean built this module in 2.4 seconds on head `577e4ae`; the strict
check found an unused `simp` argument, which the next revision removes.

For the clock and shift matrices above, the conjugation phase is
\(c=\zeta^{-1}1\). The abstract local-word product then has phase
\(\zeta^{-\binom m2}\), which agrees with the spatial calculation's
\(\zeta^{\binom m2}\) because \(2\binom m2=m(m-1)\). At even order
\(m=2k\), its half-period value is \(\zeta^{-k}=-1\). These identifications
explain the relation between the two calculations; the matrix instance and
spatial identification are still not additional checked declarations.

The circuit-to-interval identification and the all-even-order clock/shift
extension are **not formalized** by that module. The finite-group detection
claim for a corrected class of truncations also remains open. Before presenting
item 2 as formalized, settle these comparisons and register a source-gap entry
for `detectG` with the ordering convention stated explicitly. No source-labelled
theorem should silently acquire the extra intermediate-state hypotheses.
