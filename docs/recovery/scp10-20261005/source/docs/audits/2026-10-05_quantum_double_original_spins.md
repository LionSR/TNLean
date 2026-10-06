# Literal original-spin quantum-double terms

## Source, dependencies and scope

Read SCP10 `Papers/1001.3807/paper_v3.tex`, lines 2858–2937, and visually
checked `figs6/tc-lattice.pdf`. The source's original A product is arrow
ordered. Its B action uses L on outgoing and R on incoming arrows. The
clockwise A faces are chosen as tile interiors, as required by the footnote
to equation (7.10). The intervening A faces have the opposite geometric
orientation. Their ordered product is NW.b · SW.a · SE.d · NE.c.

This additive packet builds on integration commit
`bb237daff6155e1a8f347d21423a2a772ea837d3`, including the independently reviewed
physical regrouping, full K Hamiltonian/common kernel, and binary physical
face geometry. It reuses that geometry where its types and statements are
group-independent. No binary commutativity lemma proves a generic-group result.

The existing normalization correction is retained: the original B average
is `|G|⁻¹ ∑u M(u)`. The printed unnormalized sum does not become an orthogonal
projector by absorbing its scalar into a state. See the already reviewed
`docs/paper-gaps/scp10_quantum_double_local_hamiltonian.tex`.
The native comparison uses fine periods 2w,2h with w,h≥3, as recorded in
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

The old local gap note's statement that arrow-by-arrow agreement is not
asserted, and its first three remaining obligations concerning placement,
commutation/common kernel and PEPS parent comparison, are now superseded by
this packet together with the previously reviewed full-lattice packet. The
parent should reconcile that old status paragraph during integration. The
separate redundant-factor physical renormalization remains distinct from the
proved exact regrouping; it is not claimed here.

## Proved content

- The actual fine-spin A holonomies are defined as explicit ordered products,
  independently of the transported K constraints.
- B outgoing/incoming sets are defined on fine physical sites. Their disjoint
  union is the original four-site face, and all spectators are unchanged.
  The source's L/R rule is a genuine group action on the full configuration
  space. Horizontal, vertical and seam placements are included.
- Original A penalties, forward-ket B matrices, normalized B averages and
  B penalties are independently defined before any transport comparison.
  Coefficient equality is proved separately for A, every individual B action,
  the normalized B average, every penalty and the whole Hamiltonian.
- The actual original penalties are pairwise commuting orthogonal projectors;
  they and their sum are positive. The full kernel is their common kernel,
  not an assumed PEPS support or a single trivial-holonomy sector.
- Original A kernels are exactly ordered-flat supported coefficient functions.
  Original B kernels are exactly invariant coefficient functions.
- Physical regrouping maps the entire original kernel onto the full K kernel.
  The original kernel is the span of actual commuting closures and has dimension
  equal to the number of simultaneous-conjugacy classes of commuting pairs.
- The correctly normalized product of all complementary penalties is the
  orthogonal projector onto that complete kernel.
- The literal elementary T contraction is nonzero, with all-identity coefficient
  |G|. It equals exactly `|G|^(2wh) Q |1,…,1>`, or the same scalar times the
  sequential normalized B projection. The scalar counts all shared-bond color
  assignments, retaining stabilizer multiplicities. No false normalization is
  hidden inside a purported projector.

## Verification and integration

Five production modules and one focused Lean test module are additive. The test
instantiates S₃, checks both B directions, spectator identity, a seam-crossing
wrong-L/R counterexample, and actual inner/hole fine-spin configurations for
which reversing the nonabelian A product changes flatness. The hole test crosses
both periodic seams. Generic tests have no commutation, pullback-identification,
common-kernel or sector-span hypotheses.

Independent review additionally checks the source figure, finite nonabelian
orientations and a fresh strict Lean rebuild against pinned-source dependency
hashes. Verification records live outside committed source. The QICLean source
pin is `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. Shared Lake packages are read-only.
Focused checks do not constitute a whole-repository build or whole-book check.

The new blueprint fragment is
`blueprint/src/chapter/ch24_peps_quantum_double_original_spins.tex`.
The parent must register its chapter import, generated Lean imports, and test
entry, and the existing normalization note's bibliography entry if absent. A
ready-to-copy entry is in the external validation evidence. No router, shared package, remote branch, issue or pull request is changed
by this packet. No MPU-gauging module is imported or edited.

## Tactic-pattern note

The two direction-specific fine-to-block action comparisons have the same
outline but reduce different incidence equations. Their distinct source arrow
checks are retained. Subsequent operator consequences use the established
unitary transport and commuting-projection-product results. The generic
preparation reuses the earlier binary argument via those general abstractions;
no new tactic or duplicated group-averaging theory is introduced.
