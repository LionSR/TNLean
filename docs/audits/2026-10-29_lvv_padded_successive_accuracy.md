# Arbitrary accuracy from one padded LVV successive construction

## Mathematical result

For every local dimension $q\ge2$ and positive original projector-gap lower
bound $\Delta$, the theorem
`exists_uniform_positive_chain_successive_accuracy` chooses natural numbers
$P,d$, with $P\ge1$, before the original length $L$, the requested inverse
accuracy $R$, and the positive nearest-neighbour interaction.
For natural $L,R\ge1$, it forms the actual padded chain of length
$N=L+2R^2$ and runs the proved successive viable-set construction once on
that interaction, at the fixed lower gap $g=\min\{\Delta,1\}$.

The padded interaction embeds every original term in the first $L$ sites.
Each appended site carries the actual penalty $I-|0\rangle\langle0|$,
assigned to the new nearest-neighbour bond having that site as right
endpoint. Every term remains a supported positive contraction. The actual
Hamiltonian is $H\otimes I+I\otimes A$, where $A$ is the sum of these
penalties. Its prescribed product basis vector has energy zero and
projector gap at least one. Thus an original normalized ground vector
$\Gamma$ extends to a normalized ground vector
$\widehat\Gamma=\Gamma\otimes|0\rangle^{\otimes(N-L)}$ at the same energy,
with projector gap at least $g$. No equality of attained spectral gaps is
required.

The successive families $S_i$ are selected before the original ground
energy and vector. They are the families of that same padded run, beginning
with the scalar family $S_0=\{1\}$; they are not chosen independently at
each stage. Every retained family has cardinality and individual effective
bond bound at most $P(N+1)^d$. All stages are $c/N$-viable for the padded
target, where $c=(g/169)^2<1$.

At stage $L$, the all-zero right column of the actual viable witness lies
in the actual span of $S_L$ and has norm at most one. Its nonzero overlap
allows normalization, which improves the overlap. A phase rotation preserves
that retained span. In original-chain coordinates it gives a unit MPS
$\psi$ with
$\|\psi-\Gamma\|^2\le 2c/N\le R^{-2}$ and bond bound
$P(N+1)^d$.

The uniform polynomial of the previous successive theorem is squared:
$P=P_0^2$, $d=2d_0$. Consequently its degree is independent of $R$; the
final bound is polynomial jointly in $L$ and $R$. Reducing the gap as a
function of accuracy is not used.

## Source and scope

This product-ancilla argument is a consequence of the proved LVV successive
construction. It is not presented as a printed padding step in LVV13
(arXiv:1307.5143v1, `algo53.tex`, final induction, lines 652–678).
The mathematical construction uses the existing independent-column bond
trimming and Huang Gaussian error reduction. Their documented constant
corrections and conservative bounds remain in force:

- [Quadratic trimming radius](https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf).
- `docs/paper-gaps/lvv13_constant_bond.tex`.
- `docs/paper-gaps/lvv13_runtime_ground_energy.tex`.

The theorem concerns finite families, retained spans, and MPS ranks.
It makes no computational running-time claim or claim to every printed
quantitative estimate. Its hypotheses are the original supported positive
nearest-neighbour contractions, local dimension $q\ge2$, and the
rank-one projector-gap ground-state condition. No supplied ancillary gap,
cut decomposition, viable witness, MPS approximation, or attained excited
energy is assumed.

## Initial verification

The construction is extracted onto TNLean `6da5dd6c42`, with QICLean pinned
to public revision `648432e86018a50272372ecf2e80c8263e81b601`
([QICLean #1002](https://github.com/LionSR/QICLean/pull/1002)).
The extracted sources contain no `sorry`, `admit`, `native_decide`,
`unsafeCast` or new axiom declarations.

Generated import completeness and the production-file length check pass.
The proof-pattern scan was run; the functional-calculus pattern is recorded
in the ledger, and the uniform bond estimates reuse `IsOpenMPS.mono`.
All newly introduced blueprint labels and citations resolve. The role check
reports only the four existing mismatches in the base revision's
`ch35_aklv_energy_truncation.tex`. The ground-energy note compiles with its
bibliography without unresolved references or layout warnings.

The mathematical sources at commit `105ba5beb5` passed fresh verification
on 2026-10-29. The subsequent changes only clarify the chapter introduction
and record these results.

- The canonical locked full-library build passed (15,045 jobs), including
  the complete QICLean library at the pinned revision.
- All 36 changed mathematical modules passed separate Lean elaboration
  with warnings as errors, both automatic implicit options disabled,
  Mathlib standard linters and the package synthesis-depth limit.
- Axiom inspection of the complete successor, successive-family,
  uniform approximation and arbitrary-accuracy theorems reported only
  `propext`, `Classical.choice` and `Quot.sound`.
- Blueprint/source synchronization passed, and every new reference
  resolves in the active blueprint. After the full build,
  `leanblueprint checkdecls` checked all 30,601 blueprint declaration names.
- `python3 scripts/paper_gap_leanid_sync.py --check` passed for all 3,287
  declaration names cited in the paper-gap notes.

The manual axiom inspection used standard input and left no Lean fixture.
These checks are recorded in
[TNLean #10362](https://github.com/LionSR/TNLean/pull/10362).

## Reconciliation with the sampled construction on October 30

TNLean main at `b285e741bc` includes the sampled successive construction
from #10339. Its `ViableSet/CutDecomposition.lean` and `ViableSet/FinalMPS.lean`
are identical to the corresponding sources used here. They therefore no
longer occur in this pull request's mathematical changes.

The shared cut decomposition and final-span estimates each have one detailed
blueprint entry. The sampled and Gaussian constructions use those entries.
All sections are included from the gapped-chain chapter, with gluing, trimming,
error reduction and the endpoint lemmas preceding the constructions. The final
MPS extraction and product-state extension conclude the viable-set development.
Only the principal approximation results are designated as theorems.

The ground-energy discussion is consolidated in
`docs/paper-gaps/lvv13_runtime_ground_energy.tex`. It distinguishes the false
energy-independent estimate in the preprint from the published correction,
preserves both counterexamples, and describes the Gaussian existence result.
The former sampling-note path and bibliography entry have been removed.

QICLean is pinned to `a505cd42d30f9d1ae5629700a11b8d5b95981fbc`, the public
revision of #1002 after its merge of QICLean main. The pin cannot yet be
removed: `Matrix.PosSemidef.gap_mono` and
`Matrix.PosSemidef.tensorSum_gap`, used in `ChainPaddingGroundState.lean`,
are absent from TNLean main's QICLean revision `14ecc5b64b`.
The duplicate TNLean declaration
`Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose` is removed from
`MPS/Core/Blocking.lean`; the imported QICLean theorem now supplies it under
the same name.

Verification after reconciliation:

- The canonical locked full-library build passes (15,118 jobs), including
  the updated QICLean dependency. The initial build exposed the duplicate
  adjoint-injectivity declaration above; the full build was repeated after
  its removal.
- `MPS/Core/Blocking.lean` passes strict elaboration with warnings as errors,
  both automatic implicit options disabled, Mathlib standard linters and
  the package synthesis-depth limit.
- Imported axiom inspection of the four principal successive-construction
  theorems again reports only `propext`, `Classical.choice` and `Quot.sound`.
- Blueprint/source synchronization, generated imports and manifest agreement
  pass. The active blueprint has no duplicate labels, and every reference
  in the changed chapters resolves.
- The role check reports twenty discrepancies across seven files, each
  unchanged from the merged main revision `b285e741bc`. None concerns the
  revised viable-set or Gaussian sections.
- The changed chapter sources and consolidated note pass the pinned formatter
  and LaTeX lint checks. The six-page note compiles with its bibliography,
  without unresolved references or overfull boxes, and has been visually
  checked.
- After the full build, `leanblueprint checkdecls` passes for all 31,097
  blueprint declaration names, and the paper-gap declaration check passes
  for all 3,397 cited declaration heads. Both checks run under the repository
  build lock.
