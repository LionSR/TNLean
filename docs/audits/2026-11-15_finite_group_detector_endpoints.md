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

An exact computation with integer matrices and signed permutations passed
2,016 local tensor cases, 131,072 complete-basis fourteen-site circuit
detector evaluations, and 24,206 cyclic local-basis cases at orders 2 through
20. It includes both printed/prose geometries, both product conventions,
left/right dressings, commuting controls, and separation parameters
1, 2, 5, 20, and 100. A separate exact check of the precise Lean cell geometry
and QIC shift convention passed 425,410 cases. These integer and modular-exponent
checks are supporting symbolic evidence, not Lean kernel verification.

Lean and Mathlib remain pinned to `v4.36.0-rc1`; no dependency pin is changed.
This checkout has no Lean/Lake executable or cache, and the HTTP proxy blocks
fetching the toolchain even with network permission. Hosted validation uses
[draft PR #10641](https://github.com/LionSR/TNLean/pull/10641).

On head `8d2c81ad0f13ea1baf8b9445b192fd277cfa0ecf`, all eight modules below
passed their direct strict Lean checks in
[job 132953985017](https://github.com/LionSR/TNLean/actions/runs/43760420642/job/132953985017):

- `FiniteGroupDetectorEndpoint`: arbitrary printed-order cuts, exact order-two
  matrix identity, dressed-family unitarity, and normalized expectation.
- `FiniteGroupDetectorPhase`: exact conjugation and triangular group phase,
  with the even-order reduction.
- `FiniteGroupDetectorSpatial`: the complete interval word at every spatial
  position, followed by the total spatial phase.
- `FiniteGroupDetectorCircuit`: two actual circuit layers, exact nominal-pair
  deletion, and their full and single-entry-region operators.
- `FiniteGroupDetectorClock`: the existing QICLean clock and shift matrices,
  their actual conjugation scalar and periods, and the all-even-order phase.
- `FiniteGroupDetectorTensor`: the whole-chain tensor operator, including all
  odd legs and right endpoints, equals minus the identity at positive even order.
- `FiniteGroupDetectorTransport`: the conditional state transport and normalized
  expectation described below.
- `FiniteGroupDetectorConstruction`: the actual retained-circuit-to-tensor
  composition, full even-order detector and normalized expectation, and an
  existence theorem choosing the complex-exponential primitive root.

The initial builds in that job took 2.8 seconds for the circuit module,
8.8 seconds for the full tensor module, 1.4 seconds for the conditional
transport module, and 1.6 seconds for the complete composition. The full Lean
project build, affected-file strict checks, compilation-time checks, text-style
linter, blueprint declaration checks, and paper-gap declaration checks also
passed on that head. There are no source proof placeholders or added axioms.
These proof-status claims refer to that exact code revision; the final
documentation revision may differ. The overall blueprint web/PDF status is
recorded by the PR's CI checks rather than inferred from successful Lean builds.

## Conditional general detection and the remaining physical comparisons

`FiniteGroupDetectorTransport.lean` states every forward and undo
intermediate-state comparison explicitly and derives the detector's action and
normalized expectation. The general version includes undo scalar factors as
well, so the output is the product of both forward and undo factors. The
unphased undo sequence is a separate specialization. No whole-detector phase
is an input hypothesis, and no reference excitation is defined to be an
unknown whole-detector output.

The actual B-product identity is already available in
`IsDomainWallFamily.prod_eq_inv_cyclicInvariant`, not just the pure-cochain
identity `ScalarThreeCochain.domainWallPhase_eq_inv_cyclicInvariant`.
It assumes a nonzero domain-wall family with the blocked local action,
a normal MPU representation, normal state tensors of positive bond dimension,
and covariance of their periodic vectors. For any `g ^ m = 1`, it identifies
the product of the actual coefficients
`B g (g ^ r • g • x) (g ^ r • x)` with the **inverse** cyclic invariant.
No arbitrary truncation action is an input or a consequence of that identity.

The new separate module `FiniteGroupDetectorDomainWall.lean` composes that
actual-family theorem with the intermediate-state transport theorem. Under
explicit forward B-coefficient comparisons, its phased version retains all
undo coefficients. A second version derives phase-free adjoint undo steps
from unitarity and the individual forward comparisons
`U r *ᵥ w (r + 1) = w r`. Its expectation version retains the initial
state's squared norm, so normalization is not silently assumed.

The same module derives the first crossed coefficient `B g (g • x) x` from
`groupWallString_cross_mulVec_mpv_apply`. The required additional comparisons
are that the first truncation agrees with the canonical string on the ground
state and that the second agrees on the first canonical excitation. The
canonical string contraction supplies the coefficient and the actual
four-wall vector; neither is an assumed full-detector output. The existing
canonical string creation theorem identifies that first excitation with its
two-wall periodic vector. Its nonzero-wall and separating-left-inverse
assumptions are retained.

`FiniteGroupDetectorLocalComparison.lean` additionally contracts a canonical
string crossing **any** wall `e y z`, with arbitrary rectangular exterior
chains. It produces the actual coefficient `B g y z` and the transformed
wall `e (g • y) (g • z)`, together with the two new endpoint walls. The
exterior functions can contain spectator walls, so this local comparison is
not limited to the first two-wall state. It applies in particular to
`y = g ^ r • g • x`, `z = g ^ r • x`. Its proof uses the native endpoint
identities and the family's blocked local action inside a trace. It still
does not prove truncation/string agreement on those multiwall states.

**Validation status of this continuation:** on exact head
`4dcea2f8565c3c0d43a1a4b3179c9b739aa0b5f9`, all ten modules passed their
direct strict Lean checks and the full project build in
[job 132989739236](https://github.com/LionSR/TNLean/actions/runs/43771965742/job/132989739236).
The affected-file strict, compilation-time, text-style, blueprint-declaration,
and paper-gap declaration checks also passed. The two new modules initially
built in 6.7 and 4.9 seconds. Both blueprint PDF volumes passed in
[job 132989739248](https://github.com/LionSR/TNLean/actions/runs/43771965742/job/132989739248).
The web job is tracked separately by the PR's current checks; these Lean and
PDF results do not imply that job succeeded.
Local import, forbidden-token, blueprint-role, reader-prose, whitespace, and
standalone LaTeX-fragment checks passed. Local source synchronization finds
all five new declarations; absent external QICLean sources prevent a complete
local synchronization check. No proof placeholders or new axioms are added.
The earlier eight-module fixed-circuit result was fully green on exact head
`d0b5cd14f118c5abb47d0eff6541e284dfafdc65` (run `43762978260`).

The remaining physical task is to derive all forward comparisons and the
phase-free undo comparisons for a specified class of actual circuit
truncations, on a common chain space and for the full sequence of canonical
multiwall excitations. The first crossed comparison is conditional on
truncation/string agreement, not a proof of that agreement. In particular,
ground-state agreement alone does not justify agreement on later excitations.
The published endpoint-dependence gap note applies:
https://sirui-lu.com/TNLean/paper-gaps/gs24_truncation_detector_endpoint_dependence.pdf.

The original finite-group detection claim is not presented as formalized.
No GroupCocycleMPO or active wall/boundary module has been changed, and no
extra intermediate-state hypothesis has been silently attached to a source
labelled theorem.
