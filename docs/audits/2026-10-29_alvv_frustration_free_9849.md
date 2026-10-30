# ALVV regional replacement: issue 9849

## Disposition

The full requested Theorem 5.14 cannot be proved as printed. Its operator
Schmidt rank bound fails for an interior region of an eight-qubit chain with
orthogonal projection terms and a unique frustration-free ground state.
The actual replacement has rank seven across the middle cut, exceeding
`d² + 2 = 6`. The exact minor has determinant `-512/177147`.

The mathematical construction, uniqueness argument, exact matrix entries and
integer certificate are in `docs/paper-gaps/alvv16_ff_rank.tex`. The standard
library script `scripts/check_alvv_ff_rank_counterexample.py` independently
constructs the selected entries with rational arithmetic and checks both
projector identities and the displayed nonzero determinants. This is not a
full Lean counterexample theorem. No source-labelled completion of the full
Theorem 5.14 is asserted. Issue 9849 must remain open.

## Source and overlap review

Primary source: <https://arxiv.org/html/1602.08828v2#S5.SS4>, Definitions 5.10
and 5.11, Lemmas 5.12 and 5.13, Theorem 5.14. The paper's local LaTeX source
is not present in this checkout; the primary HTML version was read directly.
The issue and all six comments were read. All 36 open TNLean PRs returned by
the connected GitHub search were checked on 2026-10-29; none owns the regional
replacement. Other ALVV viable-set and physical-bootstrap PRs have distinct
scope. The earlier generic claim concerns QICLean's already merged module.

Baseline: TNLean `3af48c1843059427e4ab3eb84caf9539ac4efa91`.
Isolated local branch: `agent/9849-alvv-frustration-free`.
QICLean stays pinned at `acda92aa70e69b37507e422bceb5414036859fe6`.
Lean stays at `v4.35.0-rc3`; Mathlib stays at
`c55e6e786f49471c72fbddbec5415808896aec1e`.
No dependency file was changed and no generic detectability lemma was copied.

## Proved milestones and exact scope

`ALVV/FrustrationFree.lean` defines the real parity-layer construction using
masked terms and the existing QICLean complementary product. Its replacement
retains every exterior term. It proves projection and layer-kernel identities,
positivity, termwise frustration freeness, and equality of the **full** original
and replacement kernels. The ambient space may be any complete real or complex
inner-product space; selected regional layers are assumed internally commuting.
There is no supplied kernel equality, uniqueness premise, or gap premise in
these kernel results.

`ALVV/FrustrationFreeGap.lean` proves that each collapsed parity family consists
of commuting projections and that its complementary product equals the original
parity product. It then imports QICLean's constant-three converse for the actual
collapsed families. It proves orthogonal-complement preservation and combines
this with the original detectability inequality to obtain the quadratic-form
bound `γ / (3 * (γ + g²))` for every original-kernel-orthogonal unit vector.
The source normalization `g = 2`, `0 < γ ≤ 1` gives the numeric bound `γ/15`.

`ALVV/FrustrationFreeRank.lean` now proves the corrected rank statement for
actual finite lists of chain matrices, extended by zero, and proves that its
matrix construction maps exactly to the earlier continuous-map regional replacement. At every cut, the bound is
`q²+3` for an arbitrary interval; for a prefix (`a=0`) or suffix (`m≤b`),
it is `q²+2`. These statements require only local dimension `q≥1` and the
actual nearest-neighbor supports. They do not assume a rank decomposition,
commutation, positivity, projection structure, or the desired rank estimate.
The proofs obtain the local tensor decompositions from the supported-operator
matrix-unit theorem, multiply actual factors, and absorb regional products into
one-sided exterior sums when the cut is outside the region. The explicit
star-algebra bridge identifies this with the construction used for kernels.

The endpoint convention is recorded in the note: source qudits
`J={j₀,...,j₁}` have regional bonds `{j₀,...,j₁−1}`. The paper's later phrase
“parity subsets of J” must use this bond set to agree with its explicit sum.
In zero-based coordinates the site region is `[a,b+1)` and bonds are `[a,b)`.
No boundary bond is counted in both a regional product and the exterior sum.

The abstract gap theorem in `FrustrationFreeGap.lean` explicitly takes the two
original commuting parity families, their bounded commutation degree, and their
original quadratic-form gap. The new `FrustrationFreeChain.lean` discharges all
of this chain-specific assembly. It derives disjoint-bond commutation from the
actual supports; proves that each active parity-ordered factor has the unique
position associated with its original bond index; and injects its noncommuting
positions into the two positions associated with adjacent bonds. This gives
commutation degree two without a supplied certificate. It also identifies the
ordered original sum and its complete common kernel with the supplied actual
Hamiltonian, and identifies the collapsed parity sums with the actual regional
replacement, retaining every exterior bond.

The public `chainReplacement_gap` is therefore a concrete-chain theorem, with
only the original finite projector terms, their actual nearest-neighbor
supports, positive local dimension, and the original quadratic-form gap as
premises. It gives `γ/[3(γ+4)]` on every unit vector orthogonal to the full
original kernel. `chainReplacement_gap_linear` gives `γ/15` when `γ≤1`.
`ker_chainReplacement` derives full kernel equality from these same local
assumptions, and `chainReplacement_frustrationFree` derives each regional and
retained constraint from a supplied original zero-energy vector.

The capstone `frustrationFree_regionalReplacement_chain` assembles the actual
layer projection identities, positivity, full kernel equality, preservation of
the supplied unit ground vector, all termwise constraints, both proved OSR
bounds, and the explicit gap on the **replacement** kernel's orthogonal
complement. No parity commutation, degree certificate, replacement identity,
rank decomposition, or target gap is a premise. Uniqueness is not needed: the
result preserves the whole ground space, so it also preserves uniqueness in
the source's unique-ground-state setting. This completes the corrected chain
statement, while the original unrestricted `d²+2` rank assertion remains false.

The norm typo is fixed by using squared norms in both inequalities. QICLean's
converse holds for every unit vector, so no eigenvector premise is introduced.
For an interior region, both exterior sides can contribute independently to
operator Schmidt rank; this is the separate blocker in the source's rank proof.

## Verification

- The exact pinned Mathlib cache had already been downloaded in environment
  setup, and `Mathlib.olean` was checked before the first targeted build.
  Only targeted QICLean/ALVV dependencies were built; Mathlib was not rebuilt.
  The rank proof reuses supported-operator algebra from the existing Hastings
  module, which required additional pinned QICLean dependencies. Those unchanged
  dependencies replay existing linter warnings; the new rank module is clean.
- `lake build TNLean.MPS.AreaLaw.ALVV` passed with the package's configured
  Mathlib linters. The concrete chain module took 5.7s and the final pure
  aggregator took 2.7s. Earlier rank, kernel and gap modules took 7.0s, 2.9s and 5.0s.
- All four production proof files passed direct strict elaboration with
  `warningAsError=true`, `relaxedAutoImplicit=false`,
  `maxSynthPendingDepth=3`, and `linter.mathlibStandardSet=true`.
- All 52 public declarations were actually imported and checked using temporary
  `#print axioms` commands outside the repository. Every declaration depends
  only on `propext`, `Classical.choice`, and `Quot.sound`. No persistent Lean
  fixture was added.
- Generated imports, Blueprint source synchronization, all 52 new public
  Blueprint links, reader-facing prose, proof-hazard/line-width scans, the
  tactic-pattern scan, and whitespace checks passed.
- The note and the Blueprint excerpt compiled with pdfLaTeX without layout
  warnings. Their earlier two-page versions were visually inspected, and the
  expanded versions were checked again after adding rank results and endpoints.
  Pinned latexindent 3.24.7 was applied to the new mathematical prose.
- The exact rational counterexample script passed.

A full-library build and full-root `leanblueprint checkdecls` were not run;
`leanblueprint` is not installed, and importing the full unbuilt TNLean root
would exceed this bounded targeted verification. The 52 new declaration names
were checked through the built ALVV aggregator instead. The counterexample's
unique-ground-state and gap argument is mathematical prose, not a Lean theorem.

At the initial local handoff, no branch was pushed, PR published, or remote
issue edited. The later draft-publication authorization and review are recorded
below.

## Continuation after independent verification

The parent reported a different eight-qubit counterexample, with both boundary
terms `I−|00><00|` and rank-one interior terms `|v><v|/3`, and a minor determinant
`−128/59049`. Our original construction instead has rank-two bulk terms
`I−|00><00|−|v><v|/3`, only the left boundary term has rank three, and its
minor determinant is `−512/177147`. The two certificates must not be conflated.
The original note and exact script remain inspectable at commit `122c9b219`.
At that stage no publication was made; the parent explicitly deferred it while
the corrected bounds were proved.

## Final chain assembly

The parent explicitly authorized continuing through the concrete-chain capstone.
That continuation is complete for the corrected theorem; there is no remaining
mathematical assembly blocker. The only source discrepancy is the false printed
interior rank bound. The original hypothesis set is represented by finite
projector terms and their supports, a unit zero-energy vector, and the original
quadratic-form gap. The gap is stated on the full common-kernel complement; this
agrees with the source's ground-vector complement when that ground state is
unique. All further commutations, identities and degree bounds are proved.
No full efficient-algorithm or running-time conclusion is claimed.

## Independent review and draft preparation

A separate native subagent independently reviewed exact mathematical commit
`7464df74d`. It read the actual declarations against ALVV Section 5.4, checked
the finite source assumptions, endpoint convention, both rank bounds, full
kernel equality, active-factor degree two and squared-norm gap constants. It
found no unresolved mathematical blocker and independently recomputed the
original minor determinant `−512/177147` by rational Gaussian elimination.
The review submitted no GitHub approval or remote mutation. An audit-only QIC
pin typo in that reviewed commit was corrected to the exact existing manifest
revision; the dependency configuration and checkouts were always unchanged.

Current main `6aa526f1fbb94afbbd89c96ff231ba66563cbcae` was inspected and
merged locally without rewriting the original commits. Its two new commits add
viable-set results and split Blueprint chapters; no proof module in this change
or the ALVV Blueprint file changed during the integration. Both additions to
the paper-gap README were preserved when resolving the append conflict. The
latest open PR list and targeted search contain no overlapping issue-9849
implementation.

After integration, the targeted ALVV build passed again, all four proof modules
passed strict elaboration with warnings as errors, and all 52 public foundation
checks passed. The exact arithmetic certificate, generated imports, Blueprint
source synchronization, prose and whitespace checks also passed. Half-open
interval notation in the new mathematical exposition uses the existing
`\lbrack` convention to avoid ambiguous delimiter lint. No mathematical
statement or proof body was changed during publication preparation.

The parent authorized a separate **draft** PR after this review and regression
gate, with no merge or review approval by this worker. Full-library checks and
hosted CI remain the parent's merge gates; no benchmark or security setting was
changed.

## Privacy-preserving publication metadata

GitHub rejected the first branch push with GH007 because the original local
commits use a private author email. No remote branch was created. The email
privacy protection was left enabled and no setting or permission was changed.
The original reviewed commits and local branch are retained without rewriting.
Publication uses a separate snapshot commit based on current main and the same
verified final file tree, authored with the public noreply identity already
used by this repository's main commits. This avoids exposing the private email
while retaining the exact reviewed local history for the parent. No force push
is used.
