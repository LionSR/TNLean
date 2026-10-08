# Finite-domain area law and polynomial PEPS approximation

This document records the physical models and theorem statements for the
September 24, 2026 manuscripts *A two-dimensional area law from a global
spectral gap* and *Polynomial PEPS approximation of gapped square-grid ground
states*. The source revision is
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The mathematical statements have different scopes. The area law allows every
finite induced square-lattice domain and every finite interaction range. The
PEPS approximation concerns the original open square with site and
nearest-neighbor edge interactions. It asserts a global vector approximation,
which requires more than an entropy bound on each cut.

The definitions in this change are independently formalized from the manuscripts.
No upstream Lean proof text is copied or adapted. Code provenance and the
coverage of mathematical statements are distinct; the provenance policy remains
tracked in [#8737](https://github.com/LionSR/TNLean/issues/8737).

## Area-law hypotheses and quantifiers

Source: [Theorem 1.1 and Corollary 1.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/00-introduction.tex#L11-L85).

| Printed datum | Formal expression | Scope and interpretation |
|---|---|---|
| Fixed integer `q ≥ 1` | The first quantified parameter of `UniformAreaLaw` | Includes `q = 1`. |
| Fixed integer `R ≥ 0` | `R : ℕ`, quantified before `C` | Includes range zero. |
| Fixed `J, Δ > 0` | Explicit positivity hypotheses before `∃ C` | No dependence on the physical instance. |
| A finite `Λ ⊆ ℤ²` | `Λ : Finset (ℤ × ℤ)` | No connectedness, shape, or nonemptiness hypothesis. |
| The induced nearest-neighbor graph | `domainGraph Λ` | Paths remain within the domain. Holes and disconnected components are allowed. |
| Site space `ℂ^q` | `StateSpace Λ q = EuclideanSpace ℂ (Site Λ → Fin q)` | Exactly `q ^ Λ.card` configuration coordinates. |
| One term per nonempty support of graph diameter at most `R` | `AdmissibleSupport Λ R` and `LocalHamiltonian.term` | The index is a subtype of finite supports, not a family with unrestricted multiplicity. Zero terms are allowed. |
| Support on `X` | `QuantumCircuit.supportedOperators q X` | The existing site-operator algebra; `localLift` uses the existing placement `embedOp`. |
| `h_X = h_X*` and `‖h_X‖ ≤ J` | The `hermitian` and `norm_le` fields | The norm is the Euclidean induced operator norm. |
| `H = ∑_X h_X` | `LocalHamiltonian.operator` | The sum is Hermitian by `operator_isHermitian`. |
| A unit ground vector at real energy `E₀` | Unit-norm and eigenvector clauses of `IsGappedGroundState` | The positive projector-gap clause forces this eigenvalue to be minimal when `Δ > 0`. The checked equivalence is part of #8739. |
| Unique ground vector up to phase and `H − E₀I ≥ Δ(I − |Ω⟩⟨Ω|)` | The positive-semidefinite clause of `IsGappedGroundState` | With the unit and eigenvector clauses and `Δ > 0`, this implies a one-dimensional ground eigenspace. The corresponding QICLean theorem is tracked in #8739. No gap for a restriction is assumed. |
| Any `A ⊆ Λ` | `A : Finset (Site Λ)` after all physical data | Includes empty, full, and disconnected cuts. |
| `∂Λ A` consists of unordered crossing edges | `edgeBoundary Λ A : Finset (Sym2 (Site Λ))` | Each edge occurs once; empty and full cuts have empty boundary. |
| `ρ_A = Tr_(Λ∖A) |Ω⟩⟨Ω|` | `reducedState` | Uses `Matrix.partialTraceRight` after Mathlib's configuration splitting. |
| Natural logarithms and `0 log 0 = 0` | QICLean's `vonNeumannEntropy` | No independent entropy definition is introduced. Singular marginals are permitted. |
| `∃ C`, uniformly over `Λ,H,E₀,Ω,A` | `UniformAreaLaw` | The constant precedes all physical data. Requiring `C ≥ 0` merely chooses a nonnegative bound. |

`exists_walk_length_le_iff_edist_le` identifies the support convention with
Mathlib's extended graph metric. Disconnected pairs have distance infinity;
no natural-valued distance that identifies infinity with zero is used.
`isAdmissibleSupport_zero_iff` proves that the range-zero supports have exactly
one site. Adjacent pairs have range-one support by
`isAdmissibleSupport_pair_of_adj`; its rectangular specialization transports
native nearest-neighbor supports into the induced integer domain. The zero
interaction family is defined even on an empty domain.

Ambient dilation is a separate operation on finite subsets of `ℤ²`. It is not
used to decide admissibility of a Hamiltonian support. The rectangle graph
isomorphism and `rectangleConfigurationEquiv` identify the native rectangular
coordinates with the induced integer domain; their coordinate origin is zero,
a translation of the manuscript's origin at one.

## PEPS hypotheses and quantifiers

Source: [Theorem 1.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/00-introduction.tex#L20-L57).

| Printed datum | Formal expression | Scope and interpretation |
|---|---|---|
| Fixed `q ≥ 2`, `J, Δ > 0` | Parameters before `∃ C c` in `PolynomialPEPSApproximation` | Constants depend only on these parameters. |
| Every open `L × L` grid, `L ≥ 2` | `squareLatticeGraph L L` | No periodic edges or extra routing vertices. |
| One supported term per site and edge, norm at most `J` | `SquareHamiltonian.siteTerm`, `edgeTerm`, support and norm fields | Individual summands are not required to be Hermitian. |
| Hermitian total `H` | `SquareHamiltonian.hermitian` | Refers to the sum of the site terms plus the sum of the edge terms. |
| Unique unit ground vector and full-system projector gap | `SquareHamiltonian.IsGappedGroundState` | Same coordinates and operator inequality as above; equivalences belong to #8739. |
| PEPS on the same grid | `A : Tensor (squareLatticeGraph L L) q` | Uses TNLean's existing edge-dependent tensor family. |
| Positive bond dimensions and `Dmax ≤ C L^c` | Both universal edge clauses of `HasPEPSApproximation` | Each original edge is bounded; dimensions need not be equal. |
| Nonzero contraction `Φ` | `pepsVector A ≠ 0` | Nonvanishing is required before normalization. |
| Normalized global vector error at most `L⁻¹`, up to phase | The existential real-phase clause of `HasPEPSApproximation` | Uses the Euclidean norm on the entire configuration space. The phase-minimizer equivalence with the printed minimum is tracked in #8739. |
| `C,c > 0` chosen before `L,H,E₀,Ω` | `PolynomialPEPSApproximation` | No constant may depend on these physical data. |

The reduction to the area-law interaction model must first replace each site
or edge term by its Hermitian part. It must preserve the total Hamiltonian,
support, and norm bound. This reduction is not presumed by either target and
remains a theorem obligation of #8739. It must not be replaced by an extra
Hermiticity assumption on the PEPS summands.

## Shared geometry and exponents

`Geometry.Template` expresses Definition 9.3. It records the sampled closed
rectangles or triangles, their four allowed side slopes, the exact sampled
lattice sets, the nonempty union, both diameter bounds, and
`Ctpl N₀(s₀+1) ≤ n`. In the manuscript, `Ctpl` is a sufficiently large positive
numerical constant fixed before the templates. The structure is defined for
every real parameter; geometric estimates must explicitly require a uniform
lower bound on that parameter, chosen independently of the template.
The ordinary nondegenerate polygon convention is used:
triangles have noncollinear vertices and rectangles have nonzero orthogonal
adjacent sides. Samples may be empty; the complete template is nonempty.
Clearance from the cut, the core, and the ambient dilated collar are separate
definitions. No entropy estimate or existence theorem is included.

`OrderedTwoFamilyPartition` is a finite set partition with a residual set,
a family map to `Fin 2`, and a common order on labels. Its induced order on each
family supplies the earlier-region union. No Hamiltonian, gap, size bound,
or mutual-information bound is a field. A common order imposes no restriction
on the source's two separate orders: any interleaving preserves both.

`Exponents` stores the final numerical data as exact rationals. The proof of
`geometry_gaps` establishes all the strict inequalities of
`geometry:exponent-gaps`. The explicit choice `p = 1000000` meets the source's
requirement `p/(p+1) > 1 − 10⁻⁶`. Parameter-dependent initial box exponents are
not identified with the final choices.

`Geometry.DistanceLayers` proves the endpoint-distance and nonadjacent-layer
estimates for the actual closed dyadic layers. The product metric on `ℝ × ℝ`
is the sup metric. For every origin, nonnegative scale `k`, finite endpoint
set `Z`, and nonnegative integer radius `C`, each point in a layer closure
has distance at least `C * 2^k` from every endpoint and distance at most
`2 * (C + 1) * 2^k` from some endpoint. Existence of that endpoint follows
from layer membership, so no nonemptiness hypothesis is added to the
distance theorem. This gives the corresponding two bounds for the infimum
distance to `Z`.

The separation estimate is pointwise for every pair of points in the two
layer closures. When `h ≥ k + 2`, their distance is at least
`(C - 1) / 2 * 2^h`. This is positive for the source radius `C ≥ 2`; the
proved inequality also includes smaller radii, when its lower bound may
be nonpositive. Empty layers are allowed. These results establish the
source's `geometry:layer-distance` and `geometry:nonadjacent` estimates;
contacts, simultaneous repairs, and the two-family construction remain
separate proof obligations.

`Geometry.fineLayerIndices` subdivides each actual half-open layer cell
into cells at a finer dyadic scale. For fine exponent `ℓ ≤ k`, its set of
indices is exactly the set of fine cells meeting the layer, with cardinality
`4^(k−ℓ)` times the coarse-cell count. The fixed fine and pitch exponents
are `floor(ζk)` and `floor((1+δ₀)k)`. Both arguments are nonnegative, so
these are ordinary integer floors. The fine-cell side divides the layer
side, which divides the pitch, at every nonnegative scale.

Coordinate-residue averaging acts on this predetermined fine-cell set.
The modulus is the exact pitch-to-cell ratio. The endpoint count and
averaging give coefficient `16*(2*C₀+1)^2`; the two floor losses cost a
factor of four. Thus `exists_sparse_dyadic_belt_shift` proves the source's
`geometry:belt-count` estimate with the explicit bound
`64*(2*C₀+1)^2*b*2^(-δ₀*k/2)`. The coefficient is fixed after the radius
and before the domain, cut, origin, and scale. Empty endpoint sets and
layers are included. Primary-tile geometry, contacts, repairs, birth separation, and
the two-family construction remain open.

The three dyadic sides are uniformly separated at large scales. For every
fixed real factor `M`, one threshold chosen independently of the domain and
cut gives `M t_k ≤ r_k` and `M r_k ≤ s_k` for every later scale. An explicit
threshold for the factor `2^d` is `10^7 d`. This proves the scale-separation
passage in Section 11, lines 200–207. The later geometric constructions remain
separate obligations.

For every real exponent `p`, the polynomially weighted decay
`(k+1)^p*2^(-δ₀*k/2)` is eventually bounded by `2^(-δ₀*k/4)` and is summable.
One positive constant bounds the sum over every finite set of scales. These
numerical estimates are independent of the domain, cut, origin, and initial
scale. They supply the series estimate used in Section 11, lines 668–692;
the descendant count and the construction and count of actual repairs remain
unproved. In particular, these auxiliary results do not prove the full
`geometry:total-repairs` statement.

## Mathematical coverage

| Source label | Present status | Remaining mathematical work |
|---|---|---|
| Area-law `eq:hamiltonian` | Model defined | Local counting and analytic consequences. |
| Area-law `thm:area` | Target proposition defined | Faithful full proof, #8759 and its prerequisites. |
| Area-law `cor:rectangles` | Graph and configuration identification proved | Hamiltonian and entropy transport and the boundary estimates. |
| Area-law `scanner:template` | Template area bound, depth-layer bound, and mixed dyadic-square counts proved for the actual polygon model | Entropy bounds, #8758. |
| Area-law `geometry:cancellation` | Proved for a pure state on any finite tensor product, with its finite-domain lattice specialization | None. |
| Area-law `geometry:exponent-gaps` | Exact arithmetic proved | Applications at uniform thresholds. |
| Area-law `geometry:belt-count` | Actual fine-cell layer refinement and count, dyadic scale divisibility, residue selection, sparse-belt decay, and polynomial-factor absorption proved | Primary-tile geometry, contacts, repairs, and birth separation. |
| Area-law `geometry:total-repairs` | Polynomial absorption, summability, and a uniform numerical bound on finite scale sums proved as auxiliary results | Descendant bounds, the repair construction, and comparison of actual repairs with this series. |
| Area-law `geometry:layer-distance` | Lower and upper endpoint-distance bounds for actual layer closures proved | Use in the later region construction. |
| Area-law `geometry:nonadjacent` | Pointwise separation of actual layer closures proved | Use in contact and repair estimates. |
| Area-law `prop:two-families` | Translated dyadic cells, nested neighborhoods, exact layer unions, closure formulas, uniform cell counts, exhaustion, endpoint-distance bounds, nonadjacent-layer separation, primary regions, belts, cell contacts, side matching, cell fans, and initial regions proved | Simultaneous repairs, birth separation, and the full partition. |
| PEPS `thm:main` | Target proposition defined | Faithful tensor construction and error bounds, #8773 and its prerequisites. |

Defining a target proposition does not prove the corresponding theorem. The
source-labelled area-law and PEPS approximation headline theorems have no
`\leanok` marks in the blueprint.
Neither statement assumes an area law, a PEPS approximation, a subregion gap,
frustration freedom, commutativity, or translation invariance.

## Ownership and verification

The physical lattice definitions belong to TNLean. Generic entropy, gap,
fidelity, and phase results belong to QICLean. The physical models use the
existing QICLean entropy and partial trace and will consume reviewed companion
revisions for the results tracked in #8739 and #8761–#8763.

Implementation is tracked in [#8738](https://github.com/LionSR/TNLean/issues/8738).
The interface checks and source comparison are complete; the issue remains
open for maintainer review. Build and declaration-audit evidence accompanies
the pull request.
Agent assistance: OpenAI Codex (GPT-6) produced the new definitions, elementary
proofs, and accompanying documentation. Maintainer review of the mathematical
choices remains pending under the contribution policy.
