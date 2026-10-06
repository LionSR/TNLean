# Effective continuous generators and physical string order

Source: Papers/0802.0447/StringOrder-v10.tex, lines 291–296 and 331–359.
Base TN revision: 227c905a7456efc4c0cf151bb178081d3a7a272d.

## Exact statement and source convention

Assume the source's canonical data: positive bond dimension, E_A(I)=I,
Λ>0, tr Λ=1, E_A†(Λ)=Λ, and the full simple-peripheral-eigenspace purity
condition. Let H be Hermitian and nonscalar. Define the source row-vectorized
matrix E=Σ_i A_i⊗conjugate(A_i) and L=H⊗I−I⊗conjugate(H).
If [L,E]=0, one Hermitian physical generator K gives continuous unitary paths
u(t)=exp(i t K), V(t)=exp(i t H), with

Σ_j u(t)_ij A_j = V(t) A_i V(t)†

for every real t. Throughout a sufficiently small punctured neighborhood of
zero, u(t) is nonscalar and the actual complex correlator with x=y=I converges:

S_N(I,I,u(t)) → |tr(ΛV(t))|² > 0.

This proves the forward implication from an effective Hermitian generator to
physical string order. It does not assert the full source classification, a
converse for arbitrary ambient physical stabilizers, or a uniform/exchanged
limit in t and N. The limit is taken in N for each fixed t. Identity endpoints
are already Hermitian. The paths are exactly unphased, so this particular
complex limit needs no peripheral-phase demodulation.

The scalar virtual line is explicitly excluded. For the coefficient matrix
F((a,b),i)=A_i(a,b), the supported right lift K0 kills ker F. The physical row
convention is K=K0ᵀ, which kills the conjugate subspace conjugate(ker F).
Identity action on that unused physical support is a convention for the
constructed witness; it is not a new source-counterexample claim. This batch
uses the existing projective-nontriviality convention of physical string
order, and leaves the prior scalar-phase correction and its evidence intact.

## Transfer versus Choi coordinates

The Choi Gram G=FF† and the source transfer matrix E are not identified.
Their entries are related by G((a,b),(c,e))=E((a,c),(b,e)). Hermiticity of H
then gives the actual commutator identity

[L,G]((a,b),(c,e))=[L,E]((a,c),(b,e)).

This proves the covariance adapter needed by the generic supported Hermitian
lift. The generic transferMatrix convention elsewhere is conjugate(A)⊗A;
the new source-facing rowTransferMatrix states the opposite pair order
explicitly. No silent replacement of one realignment by another occurs.

K0 lifts L through F, and the physical row generator is its ordinary
transpose, not its adjoint. A complex Pauli-Y regression verifies the correct
sign and proves inequality for the untransposed alternative. Another finite
regression checks a genuinely nonzero commutator realignment.

## Purity and endpoints

No physical Kraus independence, injectivity, or full physical support is
assumed. If K were scalar, [H,A_i]=c A_i would imply H−E_A(H)=cI.
Dual stationarity and tr Λ=1 give c=0, and canonical fixed-space simplicity
then makes H scalar, a contradiction. The generic derivative/slope theorem
supplies projective nontriviality at all sufficiently small nonzero times.

For identity endpoints, the existing phase-retaining asymptotic theorem is
used with peripheral phase 1. Dual stationarity gives
tr(ΛE_A(V))=tr(ΛV), and Hermiticity gives tr(ΛV†)=conjugate(tr(ΛV)).
No separate Λ-invariance premise is introduced. Continuity and V(0)=I ensure
that tr(ΛV(t)) is nonzero near zero. Irreducibility and peripheral primitivity
are derived from canonical purity using the existing owner, not added as
source-facing hypotheses.

## Ownership and simplification

The generic support lift, exponential-path analysis, and Kronecker exponential
identities are supplied by the accompanying QIC batch. The TN batch contains
only the four source-facing MPS modules and its coordinate/capstone regression.
It reuses existing trace-adjoint duality instead of a private finite-sum
reproof, and removes an unused draft-only exponential wrapper. The existing
unused-injectivity C2→C1 theorem is not consumed or changed. Held #8709 is not
a dependency. No parallel physical string-order or support predicate is added.
A focused tactic-pattern scan found no three-occurrence pattern in the new
sources. Broader unrelated cleanup was deliberately excluded.

## Validation and integration boundary

All four new TN modules and the regression passed actual direct elaboration
with exact package options, the standard Mathlib linter set, warnings-as-errors,
and one thread. The final modules took 2.6–4.9 seconds and the complete TN test
5.4 seconds. No heartbeat/recursion limit was raised. All nine TN bridge and
capstone dependency guards report only propext, Classical.choice, and Quot.sound.
Source/artifact hashes are in the accompanying validation JSON.

The complete imported closure was restored from exact pinned sources or
source-matched prebuilt artifacts. Unchanged packages used their actual
package options; the known BrouwerProduct deprecation remains an existing
warning. No unchanged dependency was edited to hide it. Every changed source
and test retained warnings-as-errors.

Generated imports have been regenerated and checked, and strict CI regression
registration is included. The downstream dependency now pins merged QIC PR #555 at
c61daa23f385237a4d992a602c94812ca9f909b8. All three new upstream source files
and their generated import owner match the validated Git blob hashes.
GitHub comparison confirms no changed files from the validated published
head 35a3dd087be95ea23b4d6a3b0700ad3aab9ec4f8. The staged capstone and
complete regression were rechecked strictly against this source-identical
upstream tree. Upstream aggregate, strict regression, blueprint, and timing
CI passed before its merge. Aggregate Lake
build, blueprint rendering/checkdecls, and remote CI remain integration gates;
the direct checks are not represented as their substitutes.

Local full blueprint Python validation was not run: automatic approval review
cancelled polling of the workspace-local tool setup. No retry or alternate
installation route was taken. Native tenkz rendering is checked separately;
normal PR blueprint CI remains mandatory before merge.

The changed blueprint excerpt and standalone covariance diagram passed native
XeLaTeX rendering with the repository print preamble/macros and tenkz pin
08a6493f3605dcf2ca5b512823ccb2698dfc027b. Visual inspection found no clipping,
overlap, missing glyphs or physical/virtual legs, and no overfull/underfull
boxes. The two native pictures have matching open-west, open-east, and
upward-physical boundary signatures, with no hard findings or advisories.
The existing presentational equation wrapper does not perform hard scoped
equation checks; none is claimed. Twelve references to omitted surrounding
sections are expected in the isolated excerpt. This success is separate from
the unrun full-volume Python blueprint checks.
