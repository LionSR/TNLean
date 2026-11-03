# Recursive viable spaces for a gapped nearest-neighbour chain

This contribution constructs a balanced tree of viable spaces for the full
ground space of a positive nearest-neighbour Hamiltonian. It proves an
existence theorem for a specified recursion, with explicit dimension and
generator-rank bounds. It does not identify this recursion with the full
adaptive algorithm of Arad, Landau, Vazirani and Vidick.

## Physical hypotheses and approximation

Let \(H=\sum_i h_i\) act on \(L\) sites of dimension \(q\), with
\(0\le h_i\le I\) supported on adjacent sites. Assume there are distinct
spectral values \(\mu<\nu\), that \(\mu\) is the ground energy, and that
every other spectral value is at least \(\mu+\gamma\), where
\(\gamma>0\). Write \(G\) for the full ground space and \(r=\dim G\).
The bounds use \(g=\min\{\gamma,1\}\). Scalar Hamiltonians are excluded
by the source's distinct-eigenvalue hypothesis.

Independent truncation parameters first give normalized approximants to
every ground vector. Put \(u=1+\log q+\log(1/g)\). For
\(0<\delta\le1\), set
\[
b=16+\log(1/g)+\log(16(L+1)/\delta).
\]
There is an integer \(B\ge1\), chosen before the ground vector, such that
\[
\log B\le K\bigl(u^3/g+g^{-1/4}b^{3/4}u\bigr)(1+\log b)
\]
for a universal constant \(K\). Every unit ground vector has a unit
open-boundary matrix product approximation with bond dimension at most
\(rB\), overlap at least \(1-\delta\), and squared norm error at most
\(\delta/2\). The capped-gap comparison with the printed bound for
\(\gamma>1\) is not asserted.

Approximants to an orthonormal basis give one reference space of dimension
\(r\), mutually close to \(G\). Every vector of that reference space has
a common matrix product bond bound. For a prescribed interval, the
Schmidt-rank comparison retains the whole exterior, including both sides
of the interval. Collective trimming therefore uses the squared reference
bond in its error estimate.

## The recursive construction

Universal constants are chosen before the chain. Put
\[
m=\max\{q,50\},\quad v=1+\log m+\log(1/g),\quad
\ell=\lceil Cv^2/g\rceil,\quad D=(m\ell^2)^{22\ell}.
\]
The scalar parameter theorem proves all needed filter and tail bounds;
they are not hypotheses of the final theorem. In particular \(\ell\ge21\)
and \(\log D\le22(C+1)(6+2\log(C+1))v^3/g\).

The Hamiltonian determines one family of at most \(D^2\) operators for
each interval longer than \(4\ell\), before any child spaces or sampling
size are chosen. For \(0<\beta<1\), put
\[
A=1+\log r+\log D+\log(1/\beta),\qquad
s=\lceil4096rA\rceil,\qquad M=D^6s^3.
\]
At short leaves the recursion uses the full local space. At a long
interval it tensors the two child spaces, selects an actual Haar-coordinate
sample, applies the ordered operator words, and performs one collective
trim. Fixed-input success events are nonempty, which supplies a parent
operation for every admissible pair of children.

At every interval the resulting space is \(3/200\)-viable for the same
original ground space and has dimension at most \(M\). It has at most
\(M\) recorded spanning vectors. With the common reference bound
\(D_{\mathrm{ref}}\), each recorded vector has internal-cut Schmidt rank
at most \(10^6D_{\mathrm{ref}}^2(L+1)M\). This last bound is a statement
about the recorded vectors, not an unchanged bound for their whole span.

The block leaves, final trim, and capped gap are explicit scope restrictions.
Adaptive joint probability, an energy-estimation invariant, final spectral
extraction, and a running-time estimate remain separate tasks.

## Source and extraction

The source is ALVV, arXiv:1602.08828v2,
`References/1602.08828/local_alg_arxiv_v2.tex`: independent hard truncation
(`c:goodagsphardtrunc`, lines 979–1005), the ground-state approximation
(Theorem 4.9, beginning at line 1080), collective trimming
(`lem:trimming`, 660–697), and the degenerate-ground-space algorithm
(`t:alg1`, 1777–1817). The parameter correction and recursion restrictions
are recorded in `docs/paper-gaps/alvv16_approximation_parameters.tex`.

Twenty-one missing modules are extracted from revision
`9ad6cdd3c23da0ce9b5e6cc36edfec99f0211ff7` onto main
`5fc343a57d70eefd2902780107851ab9b0753a82`. They contain 46 new public
declarations and the adjacent-interval union lemma relocated from the
Hastings namespace. The existing five-region residual theorem is also
generalized to an independent real threshold and made public. Its norm
bound is \(3t+4\ell\), and its residual bound permits every bandwidth
\(\eta\ge0\) with \(19+\eta\le t\), without a gap assumption.
The existing equal-scale construction specializes \(t=\ell\). The old declaration is removed, all uses resolve to the
general lemma, and its existing blueprint entry is updated. No compatibility
alias is retained for this elementary fact shared by both arguments.

The finite-dimensional prerequisites are in
[QICLean #1017](https://github.com/LionSR/QICLean/pull/1017), pinned at
`000d65159e3f737730a3f6c718584300456b3440` in both manifests. That revision
passes all hosted checks and a local axiom audit of its 56 new public
declarations.

## Verification

At mathematical revision `32c17b7554`, the local target build (9,695 jobs)
and full library build (15,545 jobs) pass. Strict checks pass for all 25
changed Lean files and seven discovered regression files. The compiled
whole-library blueprint declaration check also passes. All 48 added or
relocated public declarations depend only on the standard kernel axioms
`propext`, `Classical.choice` and `Quot.sound`. These checks include the
independent-threshold residual, both filter constructions and the final
recursive theorem. Hosted checks of this revision remain in progress.

The blueprint/source check passes against the exact submitted QICLean
revision and the pinned Mathlib sources. All 48 added or relocated public declarations have active mathematical
references, labels are unique, and the
new sections have no unresolved references. The theorem-role check has
identical output to frozen main's 41 pre-existing mismatches. Forbidden
proof-token and whitespace checks pass. The mathematical sections compile
as a PDF excerpt with no overfull boxes; the principal approximation and
recursion statements were inspected visually.

The tactic-pattern scan identified three repeated Hermiticity proofs.
They now use the shared QICLean lemma. Elementary gap, finite-set and
existential transports use existing lemmas, as recorded in the tactic
ledger. The two existing filter constructions are included in the changed
Lean modules that passed compilation and strict checks.

## Integration with main on 2026-11-03

The contribution incorporates TNLean main `729589b6e9`, preserving its
three-chapter organization of the viable-set development. New sections
remain in the chapter containing their mathematical construction.
Both area-law submissions use QICLean revision `128648d4b81e81eff6704be68afd45e1a81b6b9c`,
which combines the accepted pre-upgrade revisions of QICLean #1016 and
#1017. Their proofs are unchanged. QICLean main has moved to Mathlib 4.36;
this compatible revision retains TNLean's Mathlib 4.35 toolchain.
The integrated full build and declaration checks are in progress.

## Mathlib 4.36 integration

Main revision `bcbaffef857d28e783e71ae6a72ed4f82f720634` upgrades the project to Mathlib
4.36. This contribution follows that toolchain and pins QICLean to
`c457682404aa548b4acd16ac27be5d3835e68892`, which contains the accepted
soft-truncation and viable-subspace estimates on Mathlib 4.36. The proofs
added by this contribution are unchanged. The checks recorded above used
Mathlib 4.35; verification of the updated dependency combination is pending.
