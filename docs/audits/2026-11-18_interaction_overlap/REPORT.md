# Read-only integration assessment: TNLean #10905 delta vs #10881

Fixed versions and counts are in metadata.json. No implementation branch was edited,
no checkout switched, no build or strict check run, and no external comment posted.
The git merge-tree operation writes only Git objects; its conflicted tree is not a
validated integration and was not checked out. Existing warm worktrees/caches remained intact.

## Complete mechanical inventory

Delta 8a040ee527c3a4861ab2a5c1369bf9a9c9d611fd ->
592a46e4e442f87205c407720acbb487db0d2fcf: 233 paths, +4255/-3452;
199 Lean (108 PEPS, 88 MPS, 3 Lattice), 34 non-Lean.
Three commits: 83d35e2a (strip-count proof refactor), f4214b6b (merge),
592a46e4 (Hamiltonian migration). No files are deleted: definitions are removed
inside retained module files. No scripts or fixture changes occur in this delta.

10881 head fa9a40e22fa6384ba4a723e8bf675bb2cd20c5e7 has 287 changed paths
against its 75fc2228 merge base; the intersection is 68. merge-tree finds
46 content-conflict files (44 Lean, 2 Blueprint). Their full paths are in
conflict-paths.txt; complete manifests and per-path inspection scope are beside it.
The two PRs share merge base 8a040ee and QIC pin 729428582b78ab7529b3796099193649f947354a.

Fetched main advanced to 87455a5addbea191daf9b2d0c3b2e36cc6235674 via #10902,
#10906 and #10907. Its 8 changed paths intersect neither the 233 delta paths nor
10881's 287 paths. This is a path-overlap observation, not an integration build.

Reproduction (after fetching these exact commits):

    git diff --name-status 8a040ee527c3a4861ab2a5c1369bf9a9c9d611fd 592a46e4e442f87205c407720acbb487db0d2fcf
    git diff --name-only 75fc22288234ef66239cb4c2fa0b22914cfa5c6b...fa9a40e22fa6384ba4a723e8bf675bb2cd20c5e7
    git merge-tree --write-tree fa9a40e22fa6384ba4a723e8bf675bb2cd20c5e7 592a46e4e442f87205c407720acbb487db0d2fcf

Set-intersect the first delta path list with the second list, sort UTF-8 paths,
and write one LF per line including the final line. Hashes:
- delta-paths.txt: a89ef7782466085294e7c17ce881f315bfe9885e7936ebe731611029c4080930
- 10881-paths.txt: 173083b2c139b2913af213672bf167ce04d92dce3e6d9d8c8e2bca29b2845e13
- overlap-paths.txt: 4f126b1db0335fd3f7b808008852bd7be0f8d843c74c3b39ce490cc1e5bb4e13

## API change examined

ChainHamiltonian, DomainHamiltonian and LocalHamiltonian bundled term/support,
Hermiticity and norm bounds. They become the existing QIC ChainInteraction,
DomainInteraction and PlaneInteraction abbreviations of Interaction; J is no
longer a type parameter, Hermiticity and norm bounds become theorem arguments,
supported becomes mem, and operator becomes hamiltonian. This is a single-object
migration, but is not merely textual renaming: argument order, zero constructors,
namespace ownership and conversions change.

DomainInteraction.toChain still inserts zero terms across domain gaps; its
norm theorem explicitly uses J>=0. The rectangular conversion now takes only
Phi; Hermiticity and norm are separate lemmas. The latter's unused-support
argument still derives the required nonnegative bound from an actual site and
retains arbitrary real J. Do not replace it by a blanket J>=0 premise.

## Integration blockers and concrete scope risks

1. RangeSquareGroundState.lean:52 on 10905 uses norm + IsGapped + singleton
   groundSpace. 10881 restored norm + projector PSD inequality + groundSpace
   membership for arbitrary Delta. Taking the migration-side signature would
   lose that restoration. The one-site q=2 zero Hamiltonian at Delta=0 has a
   two-dimensional ground space: the existing fixture deliberately supplies
   membership, not a singleton witness. This is an integration discrepancy
   between branches, not a claim that 10905 newly introduced it relative to
   its older base.
2. ThreeWaySplitting.lean:370 has the same mismatch. Preserve the PSD/member
   statement under ManyBody.ChainInteraction; do not restore hspan or positive
   Delta just to make the migrated proof typecheck. zero_gap_tn_wrappers tests
   every natural j,m, including cuts outside a one-site chain.
3. RectangularHamiltonian projector-gap transport must remain an arbitrary-gap
   PSD/member coordinate transport. Its changed conversion arity and removed
   operator field require migrating fixtures, not adding an old-owner wrapper.
   SquareZeroFloorOptimizer also has an explicit conflict between the two gap
   formulations. Preserve the sign-free weighted-fidelity result and required
   total-Hermitian premise. PinnedZeroFloorOptimizer auto-merges to the broader
   PSD/member signature in the merge-tree: not every overlapping path regresses;
   its call must still match the resolved SquareZeroFloor owner.
4. BoxEntropySupremum has both the gap mismatch and old prose about possible
   zero-size IntRect restored on the migration side. Retain 10881's distinction:
   the integer rectangle has size >=1, while its physical intersection can be
   empty. Check hbox at r=0/empty intersection through existing fixtures.
5. Four script files still directly reference removed owner APIs:
   box_supremum_zero_gap_regression, generic_gap_boundary_regression,
   ground_state_gap_scope_regression, zero_gap_tn_wrappers_regression.
   range_square_zero_gap_regression additionally tests the broad zero-gap
   conversion even without an old-owner name. All five need to survive the
   canonical migration. The complete old-name references are recorded in
   fixture-owner-references.txt. These references are a static incompatibility;
   no compiler failure is claimed to have been independently executed here.

Strip rider 83d35e2a changes only two proof bodies in StripGeometry. The inspected
statements and constants are unchanged, and the shared cover lemma states the
same cardinality bound from a site-cover witness. This is a separable, small
proof refactor; no new kernel verification was run.

## Recommended single-path order

1. Keep 10881's validated range restorations and fixtures as the integration
   baseline; account for current main's independent updates. Do not replace
   that baseline wholesale with the external migration head.
2. Review/apply the strip-count proof delta separately (once), since it does not
   depend on restoring the old Hamiltonian bundles.
3. Port the 592a46e4 owner migration onto that baseline: one canonical Interaction
   object, explicit Hermiticity/norm assumptions only where needed, unchanged
   arbitrary-gap PSD/member public scope. Retain genuinely positive-gap bridges
   only where the conclusions need division/uniqueness.
4. Resolve the 46 conflicts by mathematical signature, then inspect the 22 other
   overlapping paths for argument/owner mismatch. Migrate the five named fixtures
   in the same change and retain selector registration. Do not add compatibility
   definitions or a parallel ground-state predicate to make the merge compile.
5. Validate owners, conversions, fixtures and affected consumers on the final
   source/pin, then aggregate checks/CI. Existing 10881 compilation evidence does
   not transfer to this migration tree. Synchronize Blueprint signatures, uses,
   ownership and scope text with the resolved statements before claiming readiness.

## Review boundary

All 233 paths and all 68 overlaps are mechanically inventoried. Nine delta
files have selected signatures/proof hunks examined as recorded in coverage.tsv;
224 are manifest-only, not substantively reviewed. Additional fixture excerpts
and the QIC canonical model definitions were inspected. No claim of complete
proof equivalence, complete source-scope review, compiled integration or merge
readiness is made. No external/shared branch was modified.
