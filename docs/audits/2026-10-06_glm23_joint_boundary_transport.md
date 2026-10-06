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

Lean elaboration, package linter checks, strict axiom-print checks, and native
blueprint declaration validation still await the repository's single build
slot. No placeholder proof, new axiom, or resource-cap increase is used. The
blueprint entries remain without checked proof markers until that validation
succeeds.
