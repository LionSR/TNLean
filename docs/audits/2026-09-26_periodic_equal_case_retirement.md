# Retirement of conditional scalar equal-case statements

Issue #7733 identifies two unused statements superseded by the
multiplicity-bearing Fundamental Theorem for periodic matrix product states.
The source is arXiv:1708.00029, Theorem 3.8 (`thm:bdequal`),
`Papers/1708.00029/main.tex`, lines 643–693.

The removed declarations are:

- `MPSTensor.fundamentalTheorem_periodic_equalCase_matching`;
- `MPSTensor.fundamentalTheorem_periodic_equalCase`.

The first assumed an overlap hypothesis instead of deriving it from equality
of the generated states. The second additionally assumed equality of powers
of the scalar weights and treated only one multiplicity copy per block.
Neither had a Lean consumer outside the second declaration's call to the
first. Their blueprint nodes `thm:periodic_equalcase_matching` and
`thm:periodic_equalcase_scalar_component` have been removed.

The replacement is
`MPSTensor.fundamentalTheorem_periodic_equalCase_derivedPeriods` in
`TNLean/MPS/Periodic/IrreducibleFormPeriods.lean`, linked to the source-labelled
blueprint theorem `thm:periodic_ft`. It takes literal sector decompositions,
irreducible spectral-radius-one blocks, pairwise non-repetition, and equality
of states at every positive length. It derives the periods, multiplicity
matching, finite-order diagonal gauge, and global bond similarity. No
compatibility aliases for the retired statements are retained.

The docstring of `MPSTensor.PeriodicEqualCaseFT` now distinguishes that
multiplicity-bearing theorem from its own still-explicit hypothesis on
arbitrary tensors admitting an MPV-level irreducible-form representation.
Deleting the conditional scalar statements does not prove that abstract
hypothesis and does not discharge Theorem 4.1's canonicalization assumptions.

An axiom check on September 26, 2026, of the compiled declarations
`fundamentalTheorem_periodic_equalCase_derivedPeriods`,
`fundamentalTheorem_periodic_proportional_irreducibleForm`, and
`periodicOverlapDichotomy` returned only `propext`, `Classical.choice`, and
`Quot.sound` for each. This checks proof dependencies of those declarations;
it does not establish the still-missing Section 4 results.

The subsequent blocking development proves
`IsPeriodic.exists_blockTensor_periodic_orbit_compression`: blocking a
period-`m` tensor by positive length `p` gives exactly `gcd(m,p)` nonzero
trace-preserving irreducible sectors, each of period `m / gcd(m,p)`, with
unit weights and equality of generated families. Its scoped locked build
passes. This completes the arbitrary-blocking source lemma; the
MPV-level gauge hypothesis and trace-preserving root construction remain
separate obligations in Theorem 4.1.

The canonicalization argument now begins with an arbitrary refinement root.
`exists_irreducibleForm_refinement_root_tensor` first normalizes its active
irreducible sectors, blocks them, and compares them with the literal target.
The derived-period equal-case theorem forces their total dimension to equal
the original bond dimension. Thus zero-sector removal does not lose
information at length zero. `pRefinementCanonicalization_literal_root`
combines this result with the isometric physical pullback supplied by
`IsPRefinable`. Neither theorem assumes a generic equal-case theorem or
canonical form of the original root. The trace-preserving root and bounded
Kraus-rank selection remain separate obligations.

The literal equal-case theorem now also yields the normalization needed in
the forward channel construction. In `EqualCaseWeightNorm.lean`, unit-modulus
target weights force unit-modulus source weights by taking norms in the
matched copy identity. The source direct sum is consequently trace
preserving. `EqualCaseUnitary.lean` chooses unitary basis gauges while
preserving exactly the scalar phases appearing in that identity. The subsequent global assembly is described below; the corrected forward
theorem remains unfinished.

The canonical refinement pullback and its dependencies pass a scoped locked
Lake build (9,466 jobs). Its reported local-instance style warning was
corrected. The new weight-normalization and unitary-matching declarations
pass strict elaboration and kernel axiom checks with only `propext`,
`Classical.choice`, and `Quot.sound`. The unitary-matching module passed
a scoped locked build (9,059 jobs).

`fundamentalTheorem_periodic_equalCase_unitary_global` now derives the
complete global unitary relation from the literal equal-case hypotheses.
It retains a phase for every multiplicity copy, with order dividing the
period of that copy, and proves the finite-order, commutation, conjugation,
and positive-length vector identities. No matching gauge is assumed by this
theorem. Its proof assembles the matched block unitaries and the copy
permutation; the previous global similarity theorem and the new unitary
version share `equalCase_flat_conj_of_blockwise` for their dependent copy
calculation. Strict elaboration passes for all three changed modules.
The kernel axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for the new assembly and global theorem, and for the refactored
similarity theorem. The scoped locked build of the extension is pending.

The remaining forward construction must retain the correspondence between
these multiplicity copies and the cyclic orbit sectors of the blocked root.
That correspondence supplies the phase family to
`exists_phaseTwistedTensor_blockTensor`. The resulting one-site root must
then be conjugated by the global unitary and shown to have the prescribed
transfer-map power. The global theorem alone does not establish this step.

The arbitrary-blocking theorem now also retains its literal matrices in
`IsPeriodic.exists_blockTensor_periodic_orbit_decomposition`: the cyclic
projections, orbit map, orbit projections, compression isometries, and
letterwise sum identity are returned together with the proved periods.
The previous vector-family statement is a direct consequence. This prevents
the choice of periodic orbit tensors from being separated from the cyclic
projections required by the phase construction. Strict elaboration passes.

`IsPeriodic.exists_phaseTwisted_orbit_decomposition` connects these literal
corners to the phase-distribution theorem. It chooses the periodic orbit
tensors and their compression isometries once; every subsequent family of
phases of order dividing the orbit period is realized by a trace-preserving
one-site tensor on the original spaces. The resulting blocked letters are
exactly the sum of the phased compressed corners. Strict elaboration passes.
The remaining connection is the grouping of repeated blocks: equal-case
matching phases must be transported back to these original orbit copies.

The kernel audits of both the retained orbit decomposition and its phase
construction also use only `propext`, `Classical.choice`, and `Quot.sound`.
Blueprint source synchronization and whitespace checks pass. The scoped
Lake builds remain queued behind another worktree's build; no full-repository
build or full `checkdecls` success is claimed.

The overlap argument previously used only to prove equality of dimensions
now also exposes the repeated-block relation for periodic tensors in a
common MPV phase class. Its unitary form supplies
`exists_unitary_phaseClass_grouping`. This theorem groups an arbitrary
nonzero weighted periodic family into non-repeated representatives while
retaining a bijection between copies and original blocks, equality of their
periods, and equality of weight moduli. For every assignment of scalars to
the grouped copies it proves a unitary conjugation with the original blocks
carrying the transported scalars. Thus the equal-case phases can be moved
through grouping without changing their permitted orders. Strict elaboration
passes; the one reported line-length warning was corrected. The remaining
assembly must combine this result with the isometric orbit decompositions
and the one-site phase twists across all root blocks.

Strict elaboration after the style correction is clean. Kernel audits of the
repeated-block consequence, its unitary form, and the grouping theorem report
only `propext`, `Classical.choice`, and `Quot.sound`. The new scoped grouping
build is queued under the shared lock. The live body of #619 was reread: its
remaining Section 4 requirement and agreement of Lean, blueprint, gap notes,
and GitHub issue status remain part of completion; no tracker was closed.

Isometric assembly is now proved for one block decomposition and for nested
ones. `exists_unitary_phaseTwisted_block_family` combines these results with
the actual orbit phase construction across an arbitrary weighted periodic
family. It returns one global unitary for the original blocked tensor and
all permitted orbit phase choices. When the outer weights have unit modulus,
the twisted one-site direct sum is trace preserving. All new modules pass
strict elaboration. The remaining forward argument must derive this weight
normalization from equal-case matching and compose the grouping and matching
unitaries with the constructed root.

Kernel audits of the isometric assembly, its nested form, the common-unitary
orbit twist, and the weighted-family twist report only `propext`,
`Classical.choice`, and `Quot.sound`. Blueprint source synchronization,
whitespace checks, and compilation of the updated forward gap note pass.
Their scoped Lake build is queued behind the live build in
`worktrees/mpu-anchored-residual-coordinates`.

For the remaining composition, write `F` for the flattened blocked root
family and `C` for the literal isometric target. Unitary grouping gives
`P = G F G*` and `Q = H C H*`. Equal-case matching gives `Z P = U Q U*`,
while scalar-preserving grouping gives `Z P = G_z F_z G_z*`. Therefore
`F_z = G_z* U H C H* U* G_z`. The weighted-family construction supplies
`A_twist^[p] = Y F_z Y*`. With `T = Y G_z* U H`, conjugating the one-site
root by `T*` gives the required blocked target. Before this application,
unit target weights force unit grouped source weights, hence unit modulus
of every original root weight by positivity of the blocking length. These
normalization and composition steps remain to be joined in the final
forward theorem; the displayed calculation is a proof plan, not a claim
that the forward theorem is already formalized.

The normalization and composition steps above are now proved.
`weight_norm_eq_one_of_periodic_block_families_sameMPV₂Pos` transfers
normalization through repeated-block grouping, and
`weight_norm_eq_one_of_blocked_periodic_sameMPV₂Pos` derives unit modulus
of the original root weights from their positive powers.
`exists_unitary_matching_of_periodic_block_families_sameMPV₂Pos` retains
a finite-order phase on each original block and an actual unitary conjugation.
Finally, `exists_leftCanonical_root_of_blocked_periodic_sameMPV₂Pos`
constructs a trace-preserving one-site tensor whose blocked matrices equal
the literal normalized target matrices. Repeated blocks are allowed in both
families. This proves the root construction for these explicit block-form
hypotheses; it does not yet prove the general corrected forward statement.
The remaining step connects an arbitrary refinement witness to this theorem
through canonical form and the physical isometry. The reverse root-rank
selection problem also remains separate and unresolved.

The general witness connection is also proved: active periodic reduction
removes the canonical-form assumption on the root, and
`isPDivisibleChannel_of_isPRefinable_periodic_block_family` proves the corrected
forward implication for a literal direct sum of periodic blocks with
unit-modulus weights. Physical mixing commutes with this direct sum and
preserves the period of each block. The theorem assumes neither a
trace-preserving root nor a reconstruction predicate. Strict elaboration
with the package's implicit-argument and linter settings passes. Retirement
of the old refuted reconstruction predicates and their conditional consumers
still remains; the reverse root-rank selection problem is unchanged.

Kernel audits of both normalization theorems, the repeated-family unitary
matching, both exact-root theorems, and the corrected forward implication
report only `propext`, `Classical.choice`, and `Quot.sound`. Blueprint source
synchronization and whitespace checks pass; the updated forward gap note
compiles to PDF. The earlier scoped builds of the all-family phase construction
and unitary phase-class grouping have completed successfully. The new root and
literal-forward Lake builds remain queued under the shared repository lock;
the strict elaboration results above do not claim a full repository build.

The obsolete reconstruction predicates and their conditional consequences
have now been removed from the forward and reverse modules. The old bundled
equivalence is replaced by
`isPRefinable_iff_isPDivisibleChannel_of_rootSelection`: its forward direction
uses the proved literal normalized-block theorem, and its reverse direction
assumes only selection of a channel root of Kraus rank at most the physical
dimension. The reverse module proves the Kraus-isometry step from a blocked
transfer identity and the consequence for a specified bounded-rank root;
neither requires an irreducible-form hypothesis. Strict elaboration passes
for all three revised modules. Genuine rescaling and non-unitary-gauge
obstructions remain in the gap note and blueprint. The root-selection problem
remains open, so the bundled theorem is explicitly conditional and is not
identified with the unrestricted source theorem.

The live body of #7762 was reread. Its mathematical requirements are now met
locally: the corrected forward theorem is proved without added reconstruction
hypotheses, the two named obsolete predicates are deleted, and the forward
paper-gap note is marked resolved. Its false-source classification is retained
because the printed unnormalized assertion remains false. The remote issue
is still open; these shared-worktree changes have not been published or merged.
Theorem 4.1's converse is explicitly outside #7762 and remains part of #619.

Removed declarations and replacements:

- `PeripheralEqualCaseZGaugeOfSameMPV`, `PeripheralEqualCaseRootFromZGauge`,
  `PeripheralEqualCasePeriodicFTOfSameMPV`, `PRefinementCanonicalization`,
  `PeripheralEqualCaseRootChannelOfZGauge`, and their reduction theorems
  `peripheralEqualCase_periodicFT_of_sameMPV`,
  `pRefinementCanonicalization_of_peripheralEqualCase_periodicFT_of_sameMPV`,
  `peripheralEqualCaseRootFromZGauge_of_rootChannel` are replaced by the proved
  literal block matching, orbit phase construction, and exact root theorems.
- `thm_4_1_p_refinement_forward` and
  `thm_4_1_p_refinement_forward_of_peripheralEqualCase_periodicFT_of_sameMPV`
  are replaced by `isPDivisibleChannel_of_isPRefinable_periodic_block_family`.
- `PRefinementInverseCanonicalization`, `PRefinementInverseRootKrausRankBound`,
  `pRefinementInverseCanonicalization_of_rootKrausRankBound`, and
  `thm_4_1_p_refinement_reverse` are replaced by the direct sufficient criteria
  `isPRefinable_of_transferMap_eq_blockTensor` and
  `isPRefinable_of_channel_root_hasKrausRankLE`.
- `thm_4_1_p_refinement` is replaced by
  `isPRefinable_iff_isPDivisibleChannel_of_rootSelection`.

The new root and literal-forward scoped Lake builds passed, followed by the
9201-job scoped build of the revised bundle and canonical refinement pullback.
Kernel audits of the new reverse criteria and conditional bundle report only
`propext`, `Classical.choice`, and `Quot.sound`. Blueprint source synchronization,
whitespace checks, and both updated paper-gap PDF compilations pass. No full
repository build or full blueprint `checkdecls` success is claimed.

The remaining Section 4 symmetry corollary still consumes `PeriodicEqualCaseFT`
in `Symmetry/Corollary41.lean`. Its current group-action statement explicitly
omits the source's diagonal unitary and exact displayed equation. The next
literal-block proof can apply repeated-family unitary matching to the
physically rotated blocks and the original blocks. The matching phases have
orders dividing the block periods; their inverses give a diagonal block-scalar
unitary commuting with the original direct sum. This should yield the source
formula and positive-length vector invariance without the abstract equal-case
hypothesis. This paragraph is a construction plan, not a proved result.

The literal symmetry construction is now proved.
`exists_diagonal_unitary_of_irreducibleForm_physical_symmetry` derives the
periods from the irreducible normalized blocks and produces the source's
diagonal unitary, a unitary bond conjugation, commutation with every tensor
matrix, all-length vector invariance, and the exact physical-symmetry equation.
The proof allows repeated blocks and nonzero complex weights, hence includes
the source's positive multiplicities. Its pointwise group-action consequence
is `exists_diagonal_unitary_of_irreducibleForm_onSiteSymmetry`; no projective
multiplication law is inferred from pointwise choices.

The following obsolete conditional declarations were removed:
`PeriodicEqualCaseFT`,
`IsIrreducibleForm.zGaugeEquiv_blockTensor_of_periodicEqualCaseFT`,
`zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical`,
`cor_4_1_physical_symmetry_zgauge`, and
`cor_4_1_physical_symmetry_zgauge_explicit`.
Their symmetry content is replaced by the literal source corollary above;
the blocked root construction is supplied by the proved exact refinement-root
theorem. The unused identity `twistedTensor_eq_rotatePhysical` was also removed.
The abstract hypothesis module and its conditional blocked specialization are
no longer imported. The separate projective-coherence assumption remains
explicit because the source does not assert it.

Strict elaboration and kernel audits pass for the block-scalar helper,
phase-vector invariance, literal symmetry equation, source corollary, and group
specialization. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
The scoped 9208-job Lake build of the entire periodic symmetry subdirectory
and the projective-representation module passes. Blueprint source synchronization
and whitespace checks pass. The updated route-alignment note compiles to PDF;
its pre-existing monospace rendering warnings for Unicode subscripts remain.
A broader build of the full periodic area is running separately.

An independent review confirms that the literal symmetry theorem has all
three source conclusions, the correct equation orientation, and no extra
source hypothesis. The review of root selection found the sufficient
invertible-Kraus-span criterion recorded in the root-rank note, but no general
selection proof or genuine counterexample. The live #622 and #664 descriptions
were reread: their reverse Kraus-rank requirement remains unsatisfied. The full
periodic-area Lake build now passes (9215 jobs).

A declaration check against the loaded Lean environment now finds all 226
active declarations referenced by the periodic blueprint chapters. The check
imports the freshly built periodic area and the separately built common-period
canonical-form module, which owns two of those references. This is an actual
Lean environment check, in addition to source-text synchronization; it is
scoped to Chapter 22 and does not claim a full-repository `checkdecls` run.
The only unresolved mathematical step identified in the reread Section 4
tracker is bounded-rank root selection for the converse. Publication and native
issue-status updates also remain outstanding.

## Bounded-rank characterization of refinement

The forward construction now exposes its left-canonical tensor root on the
original physical alphabet. The theorem
`isPRefinable_iff_exists_channel_root_hasKrausRankLE` consequently characterizes
refinement by existence of a CPTP root with Kraus rank at most the physical
dimension, with no root-selection premise. It replaces the unused conditional
`isPRefinable_iff_isPDivisibleChannel_of_rootSelection`; no compatibility alias
is retained. Unbounded divisibility remains distinct from this proved
characterization. The unresolved mathematical question is whether a root
satisfying the rank bound can always be selected.


The sufficient invertible-word-span condition is also proved. Choi rank is
identified with the dimension of the one-letter Kraus span; multiplication
by an invertible element in the length-(p−1) span embeds that space into the
length-p span. Therefore a supplied root, even on a larger physical alphabet,
has a Kraus representation of size at most the target's physical dimension
and yields a refinement. This does not establish existence of such a root
from channel divisibility alone.

The bounded-root characterization and dimension lemmas passed the scoped
locked Lake build (9,201 jobs). The sufficient refinement criterion and the
entire Periodic area then passed the locked build (9,227 jobs), with the
existing MPO physical-blocking module included as a target. Kernel audits of
the eight new root/rank declarations report only `propext`,
`Classical.choice`, and `Quot.sound`. The revised root-rank paper-gap note
compiles, and the blueprint synchronization scan passes.

The loaded Lean environment also verifies all 234 declarations cited by
Chapter 22 and the new MPO blocked-word node. This scoped check does not
replace the full repository `leanblueprint checkdecls` validation.


## Completion audit against issue #619

A new read-only comparison with the live issue and bundled paper confirms the
following status. The original scope is unchanged.

| Requirement | Current evidence | Status |
|---|---|---|
| Multiplicity-bearing proportional theorem, with equal matched periods | `fundamentalTheorem_periodic_proportional_irreducibleForm`; source `thm:bd`, lines 613–632; blueprint `thm:periodic_ft_proportional` | Proved with source block hypotheses and per-length nonzero proportionality |
| Multiplicity-bearing equal theorem | `fundamentalTheorem_periodic_equalCase_derivedPeriods`; source `thm:bdequal`, lines 643–690; blueprint `thm:periodic_ft` | Proved, including copy permutations, multiplicity phases, and global similarity |
| Literal symmetry corollary | `exists_diagonal_unitary_of_irreducibleForm_physical_symmetry`; source lines 834–845 | Proved with all three source conclusions |
| Trace-preserving root from refinement | `exists_leftCanonical_root_of_isPRefinable_periodic_block_family` and its divisibility consequence | Proved for the corrected normalized literal form; the unnormalized printed implication is false |
| Reverse implication from channel divisibility alone | The bounded-root characterization and invertible-word-span criterion do not select a bounded root in general | Incomplete |
| Declaration and build validation | Full repository build passes (10,872 jobs); all 9,940 blueprint declaration names resolve in the imported library | The `leanblueprint checkdecls` executable still terminates with exit 133 on this macOS installation; its declaration-membership check passes when run directly in Lean |
| GitHub tracking and publication | #82, #5343, #5344, #5387, and #829 are closed; #619, #622, and #664 remain open | Local changes are unpublished, and the Section 4 issue descriptions still name retired conditional declarations |

The kernel audit was rerun on both source-labelled Fundamental Theorems,
the literal symmetry corollary, and the corrected forward implication. Each
uses only `propext`, `Classical.choice`, and `Quot.sound`. The overlap
paper-gap note now records its former scope restrictions as resolved; the
separate root-rank note remains open. All 47 declaration citations in these
three periodic notes resolve in the loaded Lean environment.

The root-rank note also records two reviewed mathematical reductions, clearly
separated from its Lean results. Sparse couplings show why unequal reset
states and an aperiodic self-loop do not turn the existing rank-decrease
examples into counterexamples to selection. The differential of the power
map shows that any possible rank decrease requires a target channel whose
linear-map spectrum is not simple and nonzero. Neither observation resolves
the general converse.

The explicit scalar counterexample is now proved by
`MPSTensor.refinement_normalization_counterexample`: the one-site tensor
with coefficient four is a positive-weight multiple of a normalized
period-one block and is 2-refinable, whereas its transfer map cannot be the
square of a channel. Its kernel audit uses only `propext`,
`Classical.choice`, and `Quot.sound`. The full locked repository build
passes with 10,872 jobs.

The final repository verification passes the locked full build (10,879 jobs)
and the generated-import check (62 aggregators, 1,472 production modules).
Blueprint synchronization passes. A direct check in the imported `TNLean`
environment resolves all 9,982 entries in `blueprint/lean_decls`. This is
the declaration-membership test used by the upstream checker; the native
`leanblueprint checkdecls` executable remains unavailable because it exits
with status 133 on this installation. Changes remain local.

## Necessary conditions for a root of an irreducible target

`RefinementRootIrreducibility.lean` proves that every tensor whose blocked
transfer map equals an irreducible target's transfer map is itself
irreducible. The argument passes invariant subspaces from letters to words
and allows different physical dimensions for the two tensors.
`RefinementRootPeriod.lean` proves that if a period-m tensor remains
irreducible after p-site blocking, then m and p are coprime: every nonzero
commuting orbit projection must be the identity, leaving a single orbit.
These necessary conditions require no bound on the root's Kraus rank.
They formalize the corresponding reduction in the root-selection gap note;
they do not discharge the general bounded-root existence problem.

Both modules pass strict elaboration and locked builds. All three public
declarations have only `propext`, `Classical.choice`, and `Quot.sound` as
axioms. The full repository build passes (10,881 jobs); generated imports
cover 1,474 production modules. Blueprint synchronization passes, and the
loaded `TNLean` environment resolves all 9,985 declaration entries. No new
proof placeholders were introduced.

## A supplied root cannot always be compressed

`MPSTensor.supplied_root_rank_counterexample` now proves a precise
obstruction to the universal supplied-root reduction proposed in #664.
The cyclic-reset channel on sectors of dimensions (1, 2, 2, 1, 1) has
Choi rank 10. Its square has Choi rank 9 and is represented by a
trace-preserving nine-letter tensor with an irreducible periodic block.
The theorem supplies that target's one-block irreducible form and channel
divisibility, while proving that the specified root has no Kraus
representation with at most nine operators.

The construction is nondegenerate: both physical alphabets are minimal
for their respective channels, every sector has positive dimension, and
the target is irreducible. This does not refute existential root selection.
Indeed, replacing the middle reset by a unitary gives another root with
seven Kraus operators; that alternative-root calculation is recorded in
the mathematical note, not asserted as a Lean theorem.

The source-context theorem and its dependencies pass the locked build
(9,060 jobs). Kernel audits of the counterexample, composition identity,
irreducibility, and both rank computations report only `propext`,
`Classical.choice`, and `Quot.sound`. No proof placeholders remain in
the new modules. The updated paper-gap note compiles successfully.
The unrestricted normalized converse remains open: a proof must select
a suitable root, rather than compress an arbitrary supplied root.

Final verification of this counterexample passes the full locked repository
build (10,885 jobs), the generated-import check (1,478 production modules),
and blueprint synchronization. All 9,997 blueprint declaration entries
resolve in the imported `TNLean` environment. The final counterexample and
the root's irreducibility also pass fresh standard-axiom checks. As recorded
above, the native declaration-checker executable remains affected by the
macOS exit-133 failure; the successful declaration check uses its equivalent
Lean environment-membership test.

## Trace preservation in the root-deformation argument

The root-rank gap note now records two mathematical reductions for a single
irreducible CPTP target: every completely positive root is trace preserving,
and every direction in the kernel of the power-map differential preserves
trace to first order. Both follow from the one-dimensional adjoint fixed
space. These arguments have not been formalized in Lean. They correct the
earlier suggestion that trace preservation could obstruct the first-order
deformation in this irreducible setting.

The exact deformation remains unproved. For square roots the residual
quadratic term is H², which the differential equation does not eliminate.
Neither this observation nor the supplied-root counterexample settles
existence of a different root with the required Kraus-rank bound. The
multi-block converse also remains open.

## Invertible transfer maps

The root-selection problem now reduces to singular target transfer maps.
`Matrix.rank_le_rank_map_of_injective_positive` proves that an injective
positive linear map cannot lower the rank of a positive semidefinite matrix.
Its proof maps the span of the positive face supported by the input into
that supported by the output and compares their dimensions.

Applying this result to a completely positive map tensored with the identity
proves `Channel.choiRank_le_comp_of_injective`. Iteration gives
`Channel.choiRank_le_pow_of_injective`: an injective completely positive
map has Choi rank no greater than any positive power. These declarations
are in `TNLean/Algebra/InjectivePositiveMapRank.lean`. They impose no
irreducibility or trace-preservation assumption.

The theorem
`MPSTensor.isPRefinable_of_isPDivisibleChannel_of_injective` consequently
proves refinement from channel divisibility for any tensor whose transfer
map is invertible. A root of an invertible map is itself invertible, so
its Choi rank is at most the target's Choi rank and hence at most the
physical dimension. The existing Kraus-isometry construction then gives
the refinement. No canonical-form assumption is needed.

The blueprint states this invertible case separately from the unrestricted
source converse. The gap note replaces the earlier simple-spectrum argument
by the stronger rank argument, including repeated eigenvalues and
non-diagonalizable invertible maps. The singular case remains unresolved;
no conclusion about existential root selection follows from the earlier
supplied-root counterexample.

The new algebra module passes strict elaboration and its locked build
(3,162 jobs). The refinement theorem passes its scoped locked build
(9,064 jobs). All five public declarations have only `propext`,
`Classical.choice`, and `Quot.sound` as axioms; neither new module contains
proof placeholders. The full repository build passes (10,887 jobs), and
the generated imports cover 1,480 production modules. Blueprint
synchronization passes, and all 10,002 declaration entries resolve in the
rebuilt `TNLean` environment. The gap note compiles successfully. The
native declaration-checker executable has the previously recorded macOS
failure; the successful check uses the equivalent Lean environment test.

## Testing deletion of the zero-eigenspace action

The singular-target analysis rules out a proposed simplification: deleting
the root's action on the generalized zero eigenspace. The existing
seven-dimensional reset root already vanishes there, whereas the known
lower-rank alternative adds a nonzero square-zero action. Suppressing
that action is therefore not a rank-minimization principle.

The gap note also gives exact rational four-state matrices P and Q with
P strictly positive and stochastic, P² = Q², and Q obtained by removing
the nilpotent part of P, but Q has an entry −1/10. The associated
measure-and-prepare channel is primitive; its truncated square root is
not even positive. Independent exact calculations verified the column
sums, decomposition P = Q + N, identities N² = QN = NQ = 0, and the
square-free annihilating polynomial of Q. The note compiles and the
whitespace check passes.

These calculations are mathematical, not new Lean declarations. The
four-state root and target both have Choi rank 16, so this is a
counterexample to the deletion procedure only. It does not refute
existence of a bounded-rank channel root. The general singular-target
converse remains unresolved. No Lean files changed during this analysis.

## Faithful-state scaling does not supply the missing bound

For an irreducible CPTP root F with faithful stationary state ρ, the
conjugated map G(X) = ρ⁻¹ᐟ² F(ρ¹ᐟ² X ρ¹ᐟ²) ρ⁻¹ᐟ² is unital and
preserves Tr(ρX). This conjugation preserves powers and Choi ranks.
It preserves ordinary trace only if F*(ρ⁻¹) = ρ⁻¹; irreducibility then
forces ρ to be scalar. Consequently the usual rank monotonicity of
bistochastic maps does not apply to arbitrary faithful-state conjugates.
Two independent left and right scalings do not generally preserve powers.

The formal rank-ten root with rank-nine square also rules out any universal
transformation to bistochastic maps preserving both powers and Choi ranks.
Thus scaling cannot justify the missing bound for arbitrary supplied roots.
It does not decide existential selection of a different root. Reinspection
of the source converse, lines 812–818, and the current rank declarations
leaves that selection theorem unproved for singular targets. No additional
Lean theorem or source-completion claim results from this analysis.
