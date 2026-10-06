# GLM23 joint endpoint boundary columns and dependent spectators

Source: `Papers/2203.12563/REsubmission.tex`, Section 5, lines 1695–1777.
This package continues the mixed family with one shared physical alphabet for
each endpoint. It does not establish the full block-injective phase theorem.

## Boundary matrices

For each block let `Cₓ` be the actual unweighted mixed tensor and let `Vₓ`
include its first virtual summand. The new boundary matrices have entries

- `L[i; x,a,b] = (Cₓⁱ Vₓ)[a,b]`, with enlarged exterior row `a`;
- `R[j; x,c,e] = (Vₓ† Cₓʲ)[c,e]`, with enlarged exterior column `e`.

Both maps use the same physical alphabet as the actual mixed family.
Their injectivity follows by restricting the columns of the full jointly
spanning mixed physical map. The latter is identified with the existing
one-site joint boundary map. The endpoint simultaneous span hypotheses stay
explicit; no physical orthogonality or independent block Gram matrix is used.

The first Gram matrix restricted to first-sector exterior rows is exactly
`Σᵢ conj(Aₓ⁰ⁱ[a,b]) Aᵧ⁰ⁱ[c,e]`, including `x ≠ y`. The regression uses two
scalar blocks with physical columns `(1,0)` and `(1,1)`, so this cross-label
entry is one. The joint polar factors have orthonormal columns and strictly
positive joint weights. Their positive factors may mix block labels.

Factoring every zero-endpoint insertion as `Vₓ Vₓ†` gives the exact
coefficient `Σᵦ,𝚌 L[i;x,a,b] Aₓ⁰(w)[b,c] R[j;x,c,e]`. The entire interior
word remains the original endpoint word. This step makes no change of
physical basis at an interior site.

## Dependent spectator spaces

The transport theorem applies to an arbitrary finite label type `Q`, arbitrary
finite active spaces `I(q)`, and a family of operators `G(q)`. It proves kernel
and orthogonal-kernel fiber decompositions and the squared-norm identity.
Every common nonnegative norm gap is preserved on the finite dependent
spectator extension. The reverse implication requires each spectator fiber
to be nonempty. The label type itself may be empty. Neither positivity nor
self-adjointness of `G(q)` is needed.

The endpoint specialization retains every ordered pair `q = (x,y)` and uses
`I(q) = Fin(Dₓ⁰) × Cfg(d₀,N) × Fin(Dᵧ⁰)`. Assuming the first dimensions are
positive, it replaces the exterior multiplicity `Dₓ⁰ Dᵧ⁰` by
`(Dₓ⁰ + Dₓ¹)(Dᵧ⁰ + Dᵧ¹)` while preserving the exact same gap constant.
The second dimensions may be zero. No diagonal restriction `x = y` is made.

## Remaining endpoint comparison

The next step must identify actual boundary-normalized kernels and operators,
using joint first and last physical maps while leaving the joint canonical
interior parent intact. For a nonunitary coordinate change, orthogonal
constraints must be formed from transported kernels with
`deformedConstraintProjection`; similarity conjugation of an orthogonal
projector is not itself the orthogonal projector in the original inner product.

At chain length two, the first and last boundary edges coincide. A later
Hamiltonian sum must handle that edge once, or impose an explicit threshold
that makes the two boundary edges distinct. The word factorization here allows
an empty interior and introduces no edge sum. The unbounded canonical gap
subsequence permits choosing a sufficiently long strict endpoint window.

The operator identification needed to apply the dependent spectator theorem
is not assumed or claimed in this package. Once that identification is proved,
the source gap must come from the common canonical joint-parent theorem
`exists_openParentHamiltonianES_toTensorFromBlocks_gap_subsequence_of_wordTupleSpanTop`,
which supplies one constant on unbounded lengths. A minimum of separate
block gaps does not supply that joint-parent theorem.

## Validation status

The integrated source checkpoint includes three production leaves, two focused
regression files, both generated-import additions, the existing regression-loop
extension, and the two chapter inputs. Static proof-token, whitespace, generated
import, and non-comment line-length checks pass.

Documentation checks passed with the pinned latexindent 3.24.7. All 44 new public
declarations have exactly one blueprint owner; global source synchronization,
scoped reverse coverage, and scoped reader-facing prose checks pass. The global
checker read the manifest-identical canonical QICLean sources without creating
or mutating a build cache. The focused native PDF has ten pages, with all five
pages containing the new leaves visually inspected and no overflow, undefined
reference, or missing-character warnings. The HTML has all 24 new anchors and
no missing internal links, duplicate IDs, or rendering sentinels. The inherited
Tenkz picture rendered to a valid six-path SVG without errors or advisories.

The production code and both regression files are checked at author source
`9aa0bb88595f6d4627213f2afa888eaff0051e49`, tree
`9feb0b7b2b920022d105d848a02caae08988f6ad`. The canonical validation checkout
had the identical tree at `25ba3d8942f2cabe6b2b7917049dde19524dab76`.
Lean 4.35.0-rc3 was run with two threads and the existing package options.
The three focused production targets completed successfully, with no warning
in a changed module. Inherited Gametheory/QICLean deprecations were replayed.
Local module elapsed times were 21, 110, and 179 seconds for the boundary
columns, dependent transport, and ordered-pair specialization respectively;
these local diagnostics are separate from the remote CI timing gate.

Both regression files passed with `autoImplicit=false`,
`relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`,
`linter.mathlibStandardSet=true`, and `warningAsError=true`. Their logs are
empty. All five strict axiom guards retain exactly `propext`,
`Classical.choice`, and `Quot.sound`. The examples retain the overlapping
cross-label Gram entry, empty labels, the two-site single-edge factorization,
unequal finite fibers, imaginary-unit action, empty spectators for forward
transport, changed nonempty multiplicities, and every ordered pair when the
second dimensions may vanish.

A focused native declaration check imported the new leaves and checked all
44 documented names, with zero errors or warnings. This is scoped declaration
validation, not a whole-repository aggregate build. Evidence and source SHA-256
hashes are in
`/workspace/shared/glm23-recovery/joint-boundary-native-validation.json`;
its referenced build, strict-regression, and declaration logs record the exact
commands and outcomes. No placeholder proof, new axiom, resource-cap increase,
or additional mathematical hypothesis was introduced by the repairs.
