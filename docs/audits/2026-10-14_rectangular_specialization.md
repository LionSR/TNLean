# Native rectangular area-law specialization

## Scope and status

This change proves the conditional implication
`AreaLaw.UniformAreaLaw → AreaLaw.RectangularEntropyAreaLaw`.
The uniform finite-domain area law remains the sole substantive analytic
hypothesis. Neither Theorem 1.1 nor unconditional Corollary 1.2 is claimed as
completed. Issues [#8759](https://github.com/LionSR/TNLean/issues/8759) and
[#9339](https://github.com/LionSR/TNLean/issues/9339) remain open.

The physical hypotheses are exactly native site and undirected-edge support
membership, Euclidean operator norms at most J, Hermiticity of the total sum,
and the unit eigenvector/full-system projector-gap condition. Individual
terms need not be Hermitian. The constant is chosen before width, height,
interaction matrices, ground energy, vector and cut, for every q ≥ 1 and
J, Δ > 0. It is the same constant in all three bounds, with coefficients
C, 4C and 2C. All natural side lengths, including zero, are admitted.

The construction takes Hermitian parts, proves no norm loss and exact recovery
of the original total, injects native singleton/pair supports into the actual
range-one support family, and uses zero for unused supports. It proves the
reindexed operator identity and transports the unit vector, gap, entropy and
all three boundary cardinalities. No input field assumes a transport result,
entropy estimate or desired conclusion.

The existing square theorem and its signature remain unchanged. A separately
named consequence of the rectangular theorem consumes that statement. The
new specialization imports the accepted generic entropy relabeling theorem
from the square file; the square file does not import the rectangular result.

## Frozen source and dependency inventory

Parent: `LionSR/TNLean@2d9f97d38804888a85e269e5ffe7df145c2bb75d`.
Parent tree: `f57ad8059366af1b85399e731f820d996bb86b3b`.
No dependency revision or package option changes are included.

- Lean: `v4.35.0-rc3`.
- QICLean: `5f76b263e3a1c418645102d90f7bef6b92f04cf3`.
- Mathlib: `c55e6e786f49471c72fbddbec5415808896aec1e`.
- Full dependency inventory is the unchanged parent `lake-manifest.json`.
- Paper revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Area-law introduction blob: `7358b19bfe22251ce7156c86b46ea7e8adde373a`.
- Area-law preliminaries blob: `bd1f48f1bee76536bd104593f3111d2644f7369f`.
- Polynomial-PEPS introduction blob: `0f6f4dcdd46d9e764b4f1e52718bf330cdc4313a`.

Accepted providers at the frozen TNLean parent:

| Provider | Reused mathematical content |
|---|---|
| `AreaLaw/RectangularDomain` | Arbitrary-side graph, site and configuration equivalences; range-one pairs |
| `AreaLaw/LocalHamiltonian` | Actual support-indexed finite-domain Hamiltonian and ground-state predicate |
| `Approximation/SquareHamiltonianHermitianTerms` | Existing lossless Hermitian-part proof pattern, generalized to undirected rectangle edges |
| `Approximation/SquareAreaLawHamiltonian` | Existing actual placement, sum and gap-transport proof pattern |
| `Approximation/SquareAreaLawSpecialization` | Generic `finiteProductEntropy_relabel` and unchanged square theorem statement |
| `AreaLaw/EdgeBoundaryCalculus` | Crossing-edge membership characterization |
| `AreaLaw/BoundaryConventions` | Actual endpoint/inner boundaries and degree-four counting |
| `AreaLaw/VertexBoundaryCorollaries` | Same-constant 4C/2C inequalities |
| `AreaLaw/TwoFamilies` | Equality between domain and generic finite-product regional entropy |
| `AreaLaw/ZeroBoundary` | Norm-only q=1/empty-cut facts and physical zero-crossing-boundary theorem, used by consumers |
| `QICLean/Algebra/HermitianPartSum` | Hermitian-part sum equals a Hermitian total |
| `QICLean/Algebra/L2OpNormReindex` | Exact Euclidean operator-norm invariance under coordinate permutation |

No unaccepted provider from another branch is used. The unresolved analytic
premise is explicitly quantified, not treated as an accepted theorem.

## Consumer and guard inventory

- `TNLeanTest/RectangularSpecialization.lean` consumes the uniform theorem and
  its unchanged square conclusion; checks the constant before arbitrary
  width and height; derives q=1 entropy directly from normalization; exercises
  both zero-side cases, empty/full cuts, arbitrary zero native boundary,
  one-site entropy, one-row and one-column crossing counts; and constructs
  cancelling +iI and −iI site terms whose total is Hermitian while one term
  is explicitly proved non-Hermitian.
- `TNLeanTest/RectangularSpecializationAxioms.lean` names all 42 public
  declarations, including seven model fields, checks declaration presence,
  and rejects every kernel dependency outside `propext`, `Classical.choice`,
  and `Quot.sound`. Fourteen principal transport/consequence declarations
  additionally have exact `#guard_msgs` / `#print axioms` checks.
- All 42 public declarations have unique blueprint ownership tags.
- The source-labelled `cor:rectangles` node has no completion or Lean ownership
  tag. The conditional implication has its own distinct label.

## Validation boundary

Only the pinned repository's pure Python source parsers were run, with all
subprocess entry points blocked. Candidate module sizes, source declaration
ownership, blueprint tags, paper-gap declaration references, the exact new
sorted aggregator imports, numbered-name predicates and reader-facing prose
were checked. This is source-level checking, not kernel verification or a
whole-repository checkdecls run. No Lean, Lake, compiler, build, dependency
fetch, cache action, installation, formatter or renderer was executed locally.

Required hosted validation: all three changed production modules; both
TNLeanTest modules; the existing square specialization consumer; affected
aggregators and normal repository blueprint/gap/size/import checks. The exact
axiom expectations are candidate assertions until that hosted run succeeds.
No added blueprint entry is marked complete before hosted validation.

## Attribution and exclusions

Prepared under the bounded claim in
[issue #9339](https://github.com/LionSR/TNLean/issues/9339#issuecomment-6178755815).
The source-faithfulness attribution follows
[#8737](https://github.com/LionSR/TNLean/issues/8737): independently formalized
from the immutable manuscripts, generalizing accepted TNLean proofs and
reusing its QICLean/Mathlib dependencies; no external OpenAI Lean proof text
was copied. The task does not claim the region construction, amplification,
analytic area-law proof or final polynomial-PEPS theorem, and does not duplicate
#9340, #9341, #9342, #9343, #8754 or #9334.
