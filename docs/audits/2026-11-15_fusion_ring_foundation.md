# Fusion-ring foundation: prerequisite and interface audit

Issue: #8322. Inspected revision: `cbf482955f46f36c71c95ab1547b3cc86b6d58c2`.

This is an implementation handoff, not a completed formalization.
`IntegerFusion.lean` passed the hosted strict source check, including warnings
as errors, at head `582d7c3a642cd48b07a0b17c6331afecfe787afb` in
[CI run 21230](https://github.com/LionSR/TNLean/actions/runs/43751459767),
build job `132926426879`. Its source blob is
`31000da9f089187646f7a8fcdf83bd1d48c18d1f` and is unchanged in the next candidate.
The bridge and Ring construction still await validation.

## Candidate implementation

Branch: `feat/8322-integer-fusion-foundation`.
Draft PR: [#10636](https://github.com/LionSR/TNLean/pull/10636).

- `IntegerFusion.lean`: integer convolution, its coefficient formula,
  additivity and zero laws, singleton multiplication, additive evaluation,
  and its multiplicativity for families satisfying the fusion identities.
- `IntegerNIMRep.lean`: transposed integer matrices, multiplication and explicit
  unit compatibility, additive matrix evaluation, and restriction of a RingHom
  with prescribed basis products and images to the legacy multiplication and
  unit conditions.
- `BasedRing.lean`: a faithful regular action, candidate associativity and unit
  proofs, the data-dependent integer Ring carrier, and lifts of arbitrary
  compatible ring-valued families, NIM-reps and ring-valued characters.

The convolution and evaluation lemmas in `IntegerFusion.lean` are checked.
The remaining files are candidate scripts without placeholders. Lean validation
of the Ring instance and forward extensions remains pending. The first attempt
to check the bridge hit the new module system's prohibition on importing the
legacy `Defs.lean` from a new-style module. The two adapter files now retain
legacy import format; the standalone integer foundation remains a public module.
Uniqueness of extension, a duality anti-involution on the integer ring, the
group-algebra identification, and consumer migration remain open.
Exact-integer checks of 100 signed coefficient triples each for S3 and Fibonacci
passed associativity, both unit laws, matrix multiplicativity and recovery from
the regular action's unit column. These checks do not establish Lean validity.

## Prerequisites and coordination

The GitHub PR metadata and local ancestry agree:

| PR | Merged (UTC) | Merge commit, present in HEAD |
| --- | --- | --- |
| [#8267](https://github.com/LionSR/TNLean/pull/8267) | 2026-09-27 15:33:40 | `b45d4a4d1a2d17f6220b28d1eae30b6baf7d5547` |
| [#8270](https://github.com/LionSR/TNLean/pull/8270) | 2026-09-27 05:50:02 | `2d9832a9a67f4424c43021fc687bce1b9cfd5a13` |
| [#8298](https://github.com/LionSR/TNLean/pull/8298) | 2026-09-27 05:09:23 | `bf342373654055542340fbd5523ea2e7023a26a9` |

Issue #8322 is open and has no GitHub assignee. A search for open PRs mentioning
8322 returned none; this is not evidence that no other worker owns the task.
The parent delegation assigns this foundation here and reserves concurrent
#8321 and tnlean-35 work. Do not migrate `Defs.lean` or `Dimension.lean` in this
slice. Keep foundation and representation results in new modules.

## The representation orientation is essential

`MPOTensor.IsNIMRep` in `Defs.lean` says

\[
  \sum_c N_{ab}^c M_{c,x}^y
    = \sum_z M_{b,x}^z M_{a,z}^y.
\]

If the matrix has row `x` and column `y`, this is
`sum_c N a b c * M c = M b * M a`, with the order reversed.
Consequently the proposed ring homomorphism into ordinary integer matrices
must send a basis label `a` to the matrix with entry
`rho(a)[y,x] = (M a x y : Int)`. Transposition gives

\[
  \rho(a)\rho(b) = \sum_c N_{ab}^c\rho(c).
\]

Using `rho(a)[x,y] = M a x y` instead would describe a homomorphism from the
opposite ring. Commutative examples can hide this error. A Python exact-integer
check of the left regular action of the six-element noncommutative group S3
checked all 36 legacy multiplication identities and all 36 transposed
homomorphism identities. It also found a pair for which the untransposed
homomorphism identity fails. This is an algebraic sanity check, not Lean
validation.

## Unitality changes the hypothesis set

The old `IsNIMRep` predicate has no unit condition. The all-zero action satisfies
it for every choice of structure constants. For a nonempty matrix index type,
this cannot extend to a unital ring homomorphism: the zero matrix differs from
the identity matrix.

Thus an equivalence with unital RingHom representations must explicitly assume
`M e x y = if x = y then 1 else 0`. Do not claim equivalence to `IsNIMRep`
alone. Conversely a ring homomorphism with nonnegative basis entries gives
both the old multiplication predicate (after transposing back) and this unit
condition. Nonnegativity belongs on the images of basis labels, not on every
integer combination: negatives of basis elements are also in the source ring.

The old `IsFusionCharacter` already includes `chi e = 1`. Extending characters
from integer combinations requires a ring target. The old predicate allows
arbitrary semiring targets, so a universal replacement by a RingHom with that
same target is not available; natural-valued characters can instead be cast
to integer-valued characters. This restriction must be explicit in a bridge.

## Proposed implementation and proof obligations

The existing `IsFusionRing` in `FusionRing.lean` records natural-valued
structure constants, associativity, a two-sided unit, an involutive duality,
the coefficient of the unit, and reversal of products under duality.
The candidate `FusionRing` data structure retains these conditions unchanged.

On integer finitely supported combinations define

\[
 (uv)_c = \sum_{a,b}u_a v_b N_{ab}^c,
 \qquad 1 = [e].
\]

The basic coefficient theorem, multiplication of two singleton terms,
distributivity, associativity, and both unit laws must be proved before
installing the Ring instance. The associativity calculation reduces to the
existing `IsFusionRing.assoc` after casting natural sums to integers.
The carrier must distinguish the chosen fusion data so that different
multiplications on the same label type do not compete as global instances.

Next prove the universal extension property: a family `f a : R` in a ring R
with `f e = 1` and `f a * f b = sum_c (N a b c : R) * f c` extends uniquely by
`u |-> sum_a (u a : R) * f a`. Integer casts are central, so this works for
noncommutative ring targets, including integer matrix rings.
Apply this to the transposed NIM-rep matrices, with the explicit unit law,
and separately to characters. State and prove the restriction/extension
identities in both directions.

For group fusion use Mathlib `MonoidAlgebra Int G` directly. The general
construction should have an explicit ring equivalence to that existing type;
do not replace Mathlib's group-algebra instance with a new global instance.
Pinned Mathlib scouting confirmed `Finsupp.equivFunOnFinite`, `onFinset`,
singleton and finite-sum APIs are available. The issue's existing scouting
comment also identifies `MonoidAlgebra.single_mul_single` and the lift API.

## Validation blocker

The checkout pins Lean/Mathlib `v4.36.0-rc1`, has no `.lake` directory, and no
`lean`, `lake`, or `elan` executable was found. Requests for the elan installer,
the pinned Lean release, and a Git remote each failed with HTTP 403.
Cloud environment status reported current observations and network policy
`mode: disabled`, `state: enforced`. No environment-change tool is available
in this task. This is an environment policy block, not an automatic approval
review rejection.

Resume in an environment with the pinned toolchain and permitted dependency
access. Follow the Linux cache-first instructions in `AGENTS.md`: fetch the
prebuilt Mathlib cache, verify `Mathlib.olean`, then build only the new modules
with package lint options. Validate blueprint declarations after successful
Lean builds. Hosted PR CI is checking the remaining candidate. Only the
checked integer-convolution and evaluation entries carry `leanok` markers;
the bridge and Ring entries remain unmarked until their source checks pass.
