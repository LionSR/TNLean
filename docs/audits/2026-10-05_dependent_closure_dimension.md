# Dependent four-block closure independence and exact dimension

## Result and exact scope

The new capstone is
`TNLean.PEPS.DependentTorus.finrank_fourCutSpace` in
`TNLean/PEPS/DependentTorusClosureDimension.lean`:

    finrank ℂ (fourCutSpace D A) = Nat.card (CommutingPairConjugacyClass G).

This is the dimension of the four actual seam-cut boundary ranges intersected
inside the physical space of the same four tensors. It is not a theorem
identifying that space with the microscopic plaquette-parent kernel on a larger
torus. That geometric bridge remains a separate task. In particular, this packet
must not be cited as completion of the unrestricted source Theorem 5.9 on its own.

The other main result is
`DependentTorus.linearIndependent_closureClass_commuting`: the actual closure
states indexed by commuting simultaneous-conjugacy classes are linearly
independent. `DependentTorus.closureClass` is the well-defined quotient of the
actual contraction, not a newly defined surrogate state space.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Definition 5.8 and
Theorem 5.9, `Papers/1001.3807/paper_v3.tex:1560–1621`. Spanning is the already
proved dependent four-cut theorem corresponding to Theorem 5.5,
`paper_v3.tex:1424–1513`. Per-bond coefficient functionals come from Lemma 4.6,
`paper_v3.tex:1015–1029`. The all-pair independence theorem, including
noncommuting pairs, is an auxiliary algebraic extension of the source's
commuting closure assertion.

## Signature comparison

- A finite group `G`, with no commutativity restriction.
- Eight actual labelled bonds, each with its own finite alphabet `D e` and
  independently chosen matrix representation `U e`.
- Semi-regularity on each actual bond, not merely on an incident tensor product.
- The shared-bond representation is matched between endpoints, acting directly
  at the head and by inverse transpose at the tail, as in the existing dependent
  contraction convention.
- Four independent finite physical alphabets `Phys v` and independently chosen
  tensors `A v`.
- Actual local G-injectivity for each tensor's own incident representation.
- No regular representation, common alphabet, homogeneous tensor, G-isometry,
  supplied left inverse, assumed spanning, assumed independence, or parent-kernel
  identity appears as a premise.
- Unitarity is unnecessary for this algebraic inverse-transpose proof. The
  source's unitary convention is included, without an added assumption.
- The geometry is precisely the source's four-block, eight-labelled-bond model.
  Both oppositely directed parallel bonds remain separate. There is no
  period-at-least-three assumption inherited from a simple-graph torus.

## Proof chain and orbit scalar

1. Constant vertex conjugation changes both seam labels by the same conjugation.
   If a vertex gauge relates two standard closure label assignments, the
   identity labels on the nonseam bonds force neighboring vertex labels equal.
   Existing nonseam connectivity then makes all four vertex labels constant.
   Reading one vertical and one horizontal seam determines the simultaneous
   conjugation. No commuting-pair hypothesis is used in this step.
2. The canonical closure is expanded as the coherent sum over four independent
   vertex-group labels, with normalization `|G|^-4` from the four actual averages.
   The product of eight per-bond trace-dual pairings tests the actual complete
   closure label configuration; every edge retains its own representation.
3. The previous group calculation restricts the surviving vertex labels to the
   constant functions. For detected `(a,b)` and closure `(g,h)`, extraction is

       |G|^-4 * sum_x 1[a = x g x^-1 and b = x h x^-1].

   This is derived, not assumed. Off-class coefficients vanish. The diagonal is

       |G|^-4 * Nat.card (centralizer {g,h}),

   which is nonzero because a group and the common centralizer contain identity.
   The coefficient is not incorrectly normalized to one and orbit sizes are
   not silently omitted.
4. Canonical vertex-gauge invariance proves conjugacy invariance of the actual
   canonical closure. The original invariant local maps recover each actual
   tensor from its averaging projector, so the same equality holds for the
   original physical contractions. This needs invariance, not injectivity.
5. Quotienting those actual vectors defines the well-defined `closureClass`.
   Applying the extracted functional at one representative to a linear relation
   kills the other classes and leaves a nonzero diagonal coefficient, proving
   canonical independence.
6. Genuine G-injective local inverses exist by the already proved finite-group
   left-inverse equivalence. Their product sends every original closure to the
   corresponding canonical closure. Applying that same map to a relation gives
   independence for all four independent physical tensors. Restriction to the
   commuting classes gives the source's family.
7. The range of commuting pair representatives equals the range of commuting
   classes. Finite-dimensional linear algebra gives the dimension of their
   span. The existing source-faithful dependent four-cut spanning theorem then
   identifies that span with the actual four-cut intersection.

No equality of coherent sums is converted into termwise statements before
applying the trace-dual functionals. No local or global isometry is inferred
from G-injectivity.

## Files and integration

Three new production modules contain 17 public declarations:

- `TNLean/PEPS/DependentTorusClosureExtraction.lean` (seven declarations)
- `TNLean/PEPS/DependentTorusClosureIndependence.lean` (seven declarations)
- `TNLean/PEPS/DependentTorusClosureDimension.lean` (three declarations)

The new blueprint fragment is
`blueprint/src/chapter/ch24_peps_dependent_closure_dimension.tex`. Its scope is
explicitly the four-block closure-space assertion, and it covers each of the
17 declarations exactly once. Shared import routers, chapter aggregators,
source theorem labels, and existing audit files are unchanged.

## Verification

Validation uses the pinned Lean 4.35.0-rc3 toolchain and source-audited imports
from `four-cut-independent-review/lib`, whose imported QICLean source pin is
`2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. New modules are compiled to a separate
local output tree; imported artifacts are read-only symlinks. No Mathlib source
rebuild, cache mutation, package update, full clone, or full repository build is
performed.

The strict verification options are `autoImplicit=false`,
`relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`,
`linter.mathlibStandardSet=true`, and `warningAsError=true`.

All three new production modules and the regression pass the strict flags,
without warnings. The final author-run timings were 3.631s, 3.801s, 2.955s, and
5.367s respectively. Independent review recompiled the production modules into
its own output tree and matched all 153 reused TNLean/QICLean source/artifact
pairs, including all 21 imported QICLean sources against the exact pinned source.
All 17 public declarations pass explicit axiom guards: the three group-label
lemmas use only `propext` and `Quot.sound`; the remaining fourteen use only
`propext`, `Classical.choice`, and `Quot.sound`.

`TNLeanTest/PEPS/DependentTorusClosureDimension.lean` provides:

- fully dependent generic signatures for all-class and commuting independence
  and both closure-span and four-cut dimensions;
- the genuinely nonabelian group S3, with noncommutativity checked in Lean;
- actual permutation representations with two through nine regular copies,
  giving eight pairwise-distinct bond dimensions 12 through 54;
- per-bond semi-regularity proved by extracting a coefficient against an actual
  basis vector, rather than assumed for the fixture;
- proofs that no edge vector space is linearly equivalent to one regular copy;
- four pairwise-distinct canonical physical dimensions;
- canonical and independently chosen physical-tensor applications;
- identity diagonal coefficient 1/216 and noncentral transposition diagonal
  coefficient 1/648, an off-class zero, and explicit equality of closures
  labelled by the conjugate transpositions (01) and (12);
- standard-axiom guards for the extraction and four main capstones.

The reviewer additionally exhaustively checked all 46,656 S3 pair/vertex-gauge
cases against the eight literal labelled bonds, confirming the simultaneous
conjugacy counts, 11 all-pair orbits, and eight commuting orbits. This finite-model
calculation supplements the Lean proof; no computational bypass is used in it.

The blueprint fragment passes exact declaration coverage and label resolution:
all 17 declarations are covered once, and all dependency labels exist. Its native
inverse/extraction diagram is attached to the independence proof and records the
complete physical and incidence tuple indices in its adjacent comments. The
original source diagram `figs3/boundary-lin-indep.pdf` was rendered and inspected.
The new fragment was compiled twice with exact pinned tenkz commit
`08a6493f3605dcf2ca5b512823ccb2698dfc027b`, then both PDF pages were visually
inspected. The final standalone render has no overfull/underfull boxes or
unresolved references. This is a focused standalone render, not a full blueprint
router build.

The repository tactic-pattern scanner was run over the available sparse source
corpus. The quotient-class separation proof shares the existing two-occurrence
pattern in `PairConjugacyOperators`: evaluate a relation with a class-separating
functional, reduce to a single term, and use a nonzero diagonal. A future third
consumer should factor the abstract separation lemma; no new repeated tactic
macro is warranted here. Shared ledgers were left to integration.

Focused validation artifacts are under `.validation/`, with independent evidence
in `.validation/review/`. No full repository/Lake, CI, or whole-blueprint build is
claimed. No push or merge was performed.
