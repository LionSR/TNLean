# Edge-dependent canonical cut support and coherent coefficients

## Source and scope

SCP10, arXiv:1001.3807, Lemma 4.6 and Theorem 5.5, especially the coherent
boundary comparison at source lines 1488–1513. This patch supplies a
graph-independent algebraic step for the closure argument. It does not by
itself assert the native torus closure theorem or identify flat labels.

The hypotheses are a finite directed labelled multigraph, a finite group,
a finite coordinate type `D e` on each labelled edge, and a representation
`U e` on that coordinate type. The virtual dimensions and representations
are genuinely dependent on the edge. Parallel edges and both incidences of
self edges remain distinct. No unitarity, common dimension, simple-graph
assumption, or boundary factorization occurs.

For any cut family `C : ι → Finset Edge`, the only geometric premise is
`∀ e, ∃ i, e ∉ C i`: every edge is uncut in at least one member of the family.
The index type need not be finite or inhabited. The empty-edge case works
with an empty cut family.

## Results

`DependentBondCoefficients.lean` defines the physical site-to-bond coordinate
equivalence and its coefficient-space linear equivalence. These are composed
from the existing endpoint equivalences, with head rows and tail columns.
An arbitrary product of edge matrix functionals acts on these actual physical
vectors, and its value on a product of edge matrices factors over the edges.

The trace-dual coefficient map uses Lemma 4.6 separately on each edge.
`bondCoefficientExtraction_bondProduct` is the full-configuration Kronecker
delta, and `bondCoefficientExtraction_sum` extracts the coefficient of an
arbitrary coherent sum. These results require semi-regularity of every edge
representation. They do not infer termwise equality from equality of sums.

`DependentCutBondSupport.lean` proves:

1. Every physical slice at an uncut edge of an actual canonical cut vector
   belongs to the span of that edge's representation matrices. The proof
   first handles actual matrix-unit cut columns and extends to the entire
   joint-boundary range.
2. Complementary uncut edges force membership in the dependent product range.
   This uses the already established `mem_range_dependentPhysicalProductFamilyMap_iff`.
3. `exists_bondCoefficients_of_mem_cutSpaces` gives an actual coherent
   expansion of the simultaneous cut vector, without semi-regularity.
4. `eq_sum_extracted_bondProducts_of_mem_cutSpaces` reconstructs the vector
   from its trace-dual coefficients when all edge representations are
   semi-regular.
5. `bondCoefficientExtraction_network_averagingSite` exposes the extracted
   canonical network with arbitrary edge insertions as its normalized
   coherent sum over vertex group labels. It retains the factor
   `|G|^(-|Vertex|)` and the oriented products
   `U_e(q(head e)) B_e U_e(q(tail e)^(-1))`.

`DependentCutCoefficientSupport.lean` further proves that a nonzero extracted
coefficient of any actual canonical cut vector admits one simultaneous vertex
labeling on every uncut edge. Its negative form eliminates any label for which
no such realization exists. This conclusion is proved from arbitrary matrix
insertions first, then extended over the full joint-boundary cut range.
Native torus flatness is therefore left as a geometric consequence of the
selected uncut edges, without duplicating the coherent coefficient argument.

## Validation

The three source modules and `TNLeanTest/PEPS/DependentCutBondSupport.lean`
pass direct Lean checks with the pinned prebuilt imports and:

```
-j1 -DautoImplicit=false -DrelaxedAutoImplicit=false
-Dlinter.mathlibStandardSet=true -DmaxSynthPendingDepth=3
-DwarningAsError=true
```

The regression module has two parallel edges of dimensions two and three,
complementary singleton cuts, arbitrary independent edge representations,
coherent coefficient extraction and reconstruction, and the arbitrary-insertion
network identity. It also tests an empty edge set with an empty cut family.
The regression additionally rules out unequal labels on two uncut parallel
edges and checks the positive simultaneous vertex-label witness.
Axiom guards on the six central theorems report only `propext`,
`Classical.choice`, and `Quot.sound`.

No Mathlib source rebuild was performed. No router, blueprint source, or
existing theorem was modified. Parent integration owns the native geometry,
source-faithful closure capstone, import routes, and final blueprint update.

## Pattern review

The dependent one-coordinate slice factorization is named
`dependentProduct_coordinateSlice_eq_smul` and reused in the support proof.
Product-functional factorization and coherent network expansion likewise have
named lemmas rather than repeated tactic blocks. A focused tactic scanner was
run on the three new modules; it found no repeated tactic windows meeting its
default promotion threshold. Existing torus-specific proofs remain untouched
in this isolated child patch.
