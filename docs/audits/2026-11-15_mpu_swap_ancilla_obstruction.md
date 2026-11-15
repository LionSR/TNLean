# Interpreting stabilized swap symmetry

This continuation distinguishes source interpretation from mathematical
obstruction. It does not claim that CPSV17's swap lemma is false. The local Lean
candidate in `SwapAncillaCompatibility.lean` is uncompiled. It is an additive
continuation of #10640 after the first run at `3d82a4bd` diagnosed the transport
helper's source errors.

## Source reading and ownership

The source introduces the two-species swap in `SSymmetries`, lines 1301--1322,
and defines `threeMPU2` by one-sided output multiplication, lines 2053--2063.
In `def:equivalent-symmetry`, lines 1356--1366, the same symmetry acts after
identity ancillas and blocking, without an explicit abstract extension rule.
The later `prop:U1-U2-equiv-ancillatrick`, lines 2210--2234, adds a third spin
while retaining labels for the two original spins. This supports extending
the original labelled-spin swap by the identity on the third spin.

Thus the explicit action in #10640 is a natural concrete reading of the source
example. The source does not ask for equivalence for every mathematically
possible extension of an abstract action. Describing the extension as specified
data is necessary for the current abstract API, but is not itself evidence that
the intended concrete source comparison has an additional physical hypothesis.

Live checks on 2026-11-15 found no other open PR mentioning #6017, #7422 or
ancilla stabilization beyond #10640. #7422 is closed with acceptance explicitly
allowing documentation of underdetermination at the abstract level; its body
calls it a residual source/API gap rather than an active implementation leaf.
#6017 remains the owner of the general equivalence definitions and standard-form
path criterion. This continuation leaves those definitions unchanged.

## A swap component cannot belong to the current global family

There is an obstruction stronger than incompatibility between two separately
chosen swap components. A globally dimension-indexed family compatible with
**every** identity-ancilla embedding cannot have the ordinary swap-combined
action even at physical dimension four.

Indeed, its compatibility from dimension two with a two-dimensional ancilla
would require some map $f$ on two-dimensional matrices such that

$$f(X)\otimes I_2=S_2(X\otimes I_2)^\dagger S_2$$

for every $X$. With $P=|0\rangle\langle0|$ the right side is $I_2\otimes P$.
This cannot equal any $Y\otimes I_2$: the diagonal entries of $Y\otimes I_2$
at $(0,0)$ and $(0,1)$ are both $Y_{0,0}$, whereas those of $I_2\otimes P$
are respectively one and zero. No choice of $f$, even nonlinear or
discontinuous, can satisfy the equation. Since $P\otimes I_2$ is symmetric,
the identical argument applies to swap-combined transposition.

The candidate states the nonmembership in the embedding image and both
impossible `Function.Semiconj` statements for arbitrary $f$. After identifying
the single-site configuration space with its physical alphabet, this is the
necessary compatibility equation for any
`FiniteChainOperatorSymmetryFamily` with the proposed dimension-four component.
The explicit Lean bridge through that one-site equivalence remains to be
written; the matrix-level obstruction itself is fully stated in the candidate.
This explains why a family indexed by dimensions alone and compatible with all
factorizations is too restrictive for the distinguished-species swap.

## Canonical swaps at two square dimensions also fail compatibility

Write $S_m$ for the standard swap on $\mathbb C^m\otimes\mathbb C^m$,
flattened to dimension $m^2$. Suppose a dimension-only family uses
$X\mapsto S_mX^\dagger S_m$ at every square physical dimension $m^2$ and is
required to commute with the standard identity-ancilla embeddings.

Take the original physical space $\mathbb C^4$ as two qubits, add an ancilla
$\mathbb C^4$, and use the exact product coordinates of `physicalIdMatrix`.
Let $P=|0\rangle\langle0|$ on $\mathbb C^4$. The original swap $S_2$ fixes
coordinate zero, so the embedded action is

$$\iota_4(S_2PS_2)=P\otimes I_4.$$

The canonical swap at the enlarged dimension is instead $S_4$: it exchanges
the entire old four-dimensional space with the entire four-dimensional ancilla.
Consequently,

$$S_4\iota_4(P)S_4=S_4(P\otimes I_4)S_4=I_4\otimes P.$$

These matrices differ at the product coordinate $(0,1)$, flattened to index
one: their diagonal entries are respectively one and zero. Since both $P$ and
$P\otimes I_4$ are real symmetric, the same calculation disproves identity-
ancilla semiconjugacy for the transposition-combined action. This is a failure
of the required embedding equation, before considering any path or canonical
form. It proves that the obvious assignment of the canonical flattened swap to
every square dimension cannot supply the desired coherent dimension-only
family. It does not preclude coherent extensions that retain the original
factorization, and it says nothing against the ordinary dagger, transpose or
conjugation families.

The source-written Lean candidate also gives this exact matrix inequality and the two
failed `Function.Semiconj` statements. It does not yet state the corresponding
`FiniteChainOperatorSymmetryFamily` no-go theorem with the one-site
configuration equivalence; that final bridge remains a formalization step.

## Agreement on the embedding image cannot select the full action

The ambiguity persists even within local real symmetric involutive unitaries,
at nontrivial original physical dimension. On an ancillary qubit let

$$Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.$$

For the original two-species swap $S$, use the two real symmetric involutions
$Q_0=S\otimes I_2$ and $Q_1=S\otimes Z$ on the enlarged space. The full
actions $F_j(Y)=Q_jY^\dagger Q_j$ agree on the entire ancilla embedding image:
for every original operator $B$,

$$F_0(B\otimes I_2)=(SB^\dagger S)\otimes I_2=F_1(B\otimes I_2).$$

Both are continuous involutions preserving unitaries, and both have the
source's real symmetric unitary form. Nevertheless, for $Y=I\otimes X$,
$F_0(Y)=Y$ and $F_1(Y)=-Y\neq Y$. Replacing adjunction by transposition gives
the same difference and the same agreement on every embedded original operator.

This demonstrates nonuniqueness of the full fixed-operator condition from its
values on embedded operators. It does not, by itself, prove a difference between
the source's fully stabilized phase relations. A separate path argument would
be needed for that claim; none is inferred from this example.

## Coprimality is a separate exact obstruction

Let $d>0$ and suppose $p_ad=p_bd$ and $\gcd(p_a,p_b)=1$. Cancellation gives
$p_a=p_b=p$, and then $\gcd(p,p)=p=1$. Thus both ancillary sizes are one.
Positive common ancillas of size greater than one, including the one in
`prop:U1-U2-equiv-ancillatrick`, cannot be witnesses of the current
coprime-ancilla predicate for equal-dimensional endpoints.

This is about the present definition, not about a lack of a proof technique.
A source reading that permits arbitrary common ancillary factors needs either
arbitrary positive balanced sizes or a minimal coprime enlargement followed by
an additional common factor. The latter two conventions agree on the allowed
balanced sizes. Revising the general predicate belongs to #6017.

## Result and validation status

There is no demonstrated obstruction to the intended concrete labelled-spin
comparison: #10640 supplies a source-written candidate for that interpretation.
There is a demonstrated obstruction to realizing its dimension-four swap action
in the current global family API at all, and
to interpreting the current coprime predicate as permitting arbitrary common
ancillas. The generic source definition also lacks sufficient information to
choose an arbitrary full extension solely from its action on the embedding
image. These are three distinct statements.

The two-to-four image witness, the four-to-sixteen compatibility witness, and
the two full actions on four original levels with a qubit ancilla were checked
using exact arithmetic. The source/coordinates and the private permutation
sandwich formula were reviewed against pinned Mathlib's `PEquiv` matrix lemmas.
The additional Lean candidate has no placeholders, but no Lean elaboration or
axiom check has run. No new source completion or global phase counterexample is
claimed. The initial #10640 build failed after reaching the new transport helper;
its reported errors are repaired in the same continuation. No passing Lean check
is inferred from those repairs. The next hosted run must check all three modules
and their complete current signatures.
