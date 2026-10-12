# Normal-block adjoint boundary transport: source-scope audit

## Exact hypotheses and conclusion

The input is an actual finite unweighted MPO block sum. Each block has
positive virtual dimension and its flattened Kraus family is normal. The
label dual is involutive. For every block and every **positive** length, the
periodic operator of the dual block equals the physical conjugate transpose
of the original operator.

The conclusion constructs rectangular matrices V_a and W_a with both
V_a W_a = I and W_a V_a = I, derives the exact one-letter physical-adjoint
similarity, and transports every arbitrary block boundary X by
V_a conjugate(X) W_a. Here conjugate is entrywise complex conjugation, not
virtual conjugate transpose. The ambient output boundary is explicitly the
sum of the transported input diagonal blocks, inserted into their dual
summands. The same output boundary works for every length, including zero.

## Derivation and scope

Two applications of the existing normal-target reduction theorem give the
opposite dimension inequalities. Involution identifies the twice-dual block,
so the dimensions coincide. Mathlib's rectangular-index version of
`mul_eq_one_comm_of_equiv` turns the reduction's one-sided inverse into a
two-sided inverse. Existing word-similarity and physical-adjoint evaluation
lemmas then give arbitrary-boundary transport. Existing block word evaluation
and trace decomposition assemble the actual original `MPOTensor.blockSum`.

The periodic physical-adjoint equality is an additional, explicit physical
star-representation hypothesis. It is **not** deduced from the purely
algebraic boundary-product condition `algcond` of arXiv:2203.12563v3, from
fusion multiplicities, or from biorthogonal fusion tensors. No weak Hopf
algebra, antipode, positivity, or unitarity theorem is asserted. No
one-site injectivity, canonical normalization, pairwise block inequivalence,
or assumed arbitrary-boundary adjoint closure is added.

This is a sufficient bridge with the displayed hypotheses, not a claim that
GLM23 proves those hypotheses from algebraic multiplication. It must not be
marked as completion of a source-labelled weak-Hopf or star-representation
existence theorem.

## Canonical-parent consumer

`NormalBlockBoundaryParentHamiltonian.lean` applies the existing checked
`IsBoundaryCompatible.parentHamiltonianES_commute_mpo_block` theorem to the
actual block sum. Its entire-boundary-range adjoint-closure hypothesis is
discharged by the derived, length-independent boundary transport above.
The additional input is compatibility with the state tensor, together with
positive interaction length L and L ≤ N. The conclusion is commutation of
the periodic canonical parent Hamiltonian with each original periodic MPO
block at chain length N. No state-tensor normality or injectivity is assumed.

The matching strict regression spells out the raw periodic physical-adjoint
identities and compatibility. It has no supplied boundary adjoint-closure
witness. A fifth axiom guard covers the parent commutation conclusion.
This is a concrete canonical-parent consequence relevant to Section 5 and
Appendix B, not a construction of a weak Hopf algebra or its integral and not
an identification with the literal averaged interaction.

## Source and verification status

The integrated candidate is based on local commit
`a8c119cae8e7d18eff3925b42b8958097bb79f0c`, whose tree
`d1984fc8234dbbe14bc0cf17c35b2443ea5c2022` matches the published
#8693 head `0c2bf8a153198745d53ee3a74c0df2fdc9518cd9`.
Initial authoring used `43274c153f006d9f0acdb330a99db2427f3bd008`.
All existing boundary and parent dependencies are supplied by the integration
base; no copied dependency is part of this change.

The candidate contains four new production modules and three regressions.
At the first published head
`f46a818ab46c18c82b9f48776d337b1561b0eac3` (tree
`0f87cc390a1adbcdcecc861c54d4a28f5b2ff0cf`), the
[full Lean job](https://github.com/LionSR/TNLean/actions/runs/37389193983/job/112029984176)
passed on 2026-10-05. All four production modules compiled, and all three
separate regression modules passed the repository's strict option set and
all nine guards. Each guarded declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`. Compilation-time, text-style, blueprint
and paper-gap declaration checks also passed. The four new production modules
took 4.7, 3.9, 3.0, and 3.9 seconds, respectively, in that run.

The completion batch adds checked markers to the 29 explicitly scoped
blueprint declaration owners and their eleven corresponding proof environments.
It also replaces two `letI` tokens by the linter-recommended `let` inside
proposition proofs. No theorem statement, assumption, argument, dependency pin,
or regression changes. The recorded first-head evidence belongs to the exact
commit above; every later head requires its own complete CI result.

The positive regression signatures expose normality, positive dimensions,
periodic physical adjoint identities, involution, exact dual dimensions,
one-letter gauges, and a single boundary valid before quantifying over all
lengths. They also cover empty-chain transport and an empty label family.
The only allowed dependency axioms are `propext`, `Classical.choice`, and
`Quot.sound`. These tests do not weaken any theorem's hypothesis set.

## Concrete algebraic counterexample

`BoundaryAdjointCounterexample` gives the physical matrix
`P = [[1, 1], [0, 0]]` as a bond-one MPO and the bond-one state `|0>`.
Both tensors are injective and normal. Exact local fusion and action identities
supply length-independent arbitrary-boundary closedness and compatibility.
Every virtual boundary commutes with every letter, but the adjoint at length
one lies outside the entire boundary range. This is a derived counterexample
to inferring physical star closure from the algebraic hypotheses alone, not a
counterexample to the paper's physical star or weak-Hopf assumptions.

The regression computes the actual canonical one-site parent as `diag(0,1)`
from its projection properties and ground space, and proves that it does not
commute with `P`. The production counterexample passes strict standalone
elaboration against its declared imports. A combined exact-body check of the
production file and regression, with their union of declared imports, passes
all four standard-axiom guards. The subsequent published-head CI above also
checks the separately compiled regression import and full package build.

The new blueprint has 29 unique, explicitly scoped declaration owners. Its
two Tenkz boundary contractions retain the virtual order and use entrywise
boundary conjugation. Native and actual-wrapper audits, 21 exact coefficient
tests, focused strict web generation and the inspected twelve-page PDF pass.
The native/actual-wrapper checks were rerun successfully on the exact initial
publication tree. The initial publication's
[complete exact-head PR CI](https://github.com/LionSR/TNLean/actions/runs/37389193983)
finished successfully on 2026-10-06: full strict web generation, native/event
sweep, equation-layout browser checks, root/subpath search tests, generated-page
tests, declaration synchronization and changed-source coverage all passed.
Import completeness and the Tenkz demolition guard also passed. The tested
merge checkout `6fb240996765d8689d75bde07efdb59620cd4bd5` has exactly the
publication tree `0f87cc390a1adbcdcecc861c54d4a28f5b2ff0cf`.
Local socket restrictions still prevent a local browser rerun. This does not
claim a new full-volume PDF or live deployment; the PDF evidence remains the
inspected focused twelve-page preview.

The exact stack has three chapter-30 equation wrappers: the existing
multiplicity-L row and the two normal-adjoint rows. Independently stacked
#8711 contributes two further mixed-action rows. Combining those branches
requires reconciling the wrapper count and retaining its dedicated fail-closed
browser check. This package changes no PEPS or MPU source.
