# Native nonuniform microscopic parent classification

## Scope and result

This packet proves the native-simple-torus form of SCP10, arXiv:1001.3807,
Theorems 5.7 and 5.9. Both torus periods are at least three. Every ordered
edge retains its own finite virtual alphabet and semi-regular representation;
every vertex retains its own G-injective tensor and finite physical alphabet.
There is no common representation, tensor, bond dimension, isometry, or
physical dimension assumption.

The source statements are `Papers/1001.3807/paper_v3.tex:1515--1621`.
The representation is explicitly a property of each bond in the source's
closure definition. The present proof uses the existing microscopic graph
parent and its original local open-region ranges. It replaces the source's
four-block proof route by a derived native flat-connection expansion, without
changing the parent or assuming the conclusion of the four-block theorem.
The period restriction is stated in every relevant module and in the new
blueprint fragment; unrestricted smaller labelled tori are not claimed here.

## Existing Hamiltonian, exact equalities

`ker_torusPlaquetteParentHamiltonian_eq_nativeCommutingClosureSpan` starts
with an existing `Tensor`, independent represented edges, G-injectivity of
its original site maps, and `IsRegionParentInteraction` for each microscopic
plaquette. The existing positive sum `regionParentHamiltonian` has full
ambient kernel equal to the span of actual native commuting closures.
Its dimension is `Nat.card (CommutingPairConjugacyClass G)` by
`finrank_ker_torusPlaquetteParentHamiltonian`.

Independent physical alphabets use the already verified graph padding tensor,
not a parallel parent definition. The capstone
`ker_nonuniformTorusPlaquetteParent_eq_map_nativeCommutingClosureSpan` says
that the **entire ambient kernel** of that existing padded graph parent is
exactly the product zero-extension image of the original commuting-closure
span. `nonuniformNativeParentEquiv` explicitly identifies these two spaces:
its forward map is product zero extension and its inverse is product coordinate
restriction. Their formulas, uniqueness of the original representative, and
the exact dimension are separate checked declarations.

Consequently unused padding coordinates introduce no extra ground vectors.
There is no supplied local-image assumption and no restriction of the theorem
to selected ambient vectors. The original-space statement is an explicit
linear equivalence, not a claimed alternative Hamiltonian definition.

## Proof route and orientation

1. Every actual parent vector has a reconstructing canonical coordinate vector
   and a coherent trace-dual expansion. These come from the independently
   reviewed parent-to-cut packet in the base commit.
2. The derived regional support makes every nonzero term a vertex coboundary
   on every microscopic plaquette. Its oriented plaquette holonomy is therefore
   trivial; no flatness assumption is added to the parent theorem.
3. The arbitrary-period tree gauge reduces every such flat term to two
   commuting native seam holonomies. Applying the **actual** local averaging
   projectors identifies that term with its literal commuting closure.
   Original physical site maps recover every initial parent vector.
4. Conversely, local invariance alone moves a commuting closure off any chosen
   plaquette. On every internal edge the inserted matrix becomes identity.
   A new fully dependent regional contraction proof splits internal and
   noninternal endpoint coordinates and supplies the genuine open-region
   boundary witness. It assumes neither positive bond dimensions nor
   injectivity or semi-regularity.
5. Trace-dual extraction forces a gauge between standard closures to be
   constant on all native vertices. The diagonal coefficient is exactly
   `|G|^(-card V) * |C_G(g,h)|`, not a guessed normalization or a four-site
   normalization transported without proof. Constant conjugation separates
   the actual pair classes. Genuine physical inverses transfer independence.
6. Positivity identifies the existing Hamiltonian kernel with the regional
   slice intersection. Both inclusions and the independent class family
   give the exact classification and dimension.

The ordered-edge bond matrix uses head as row and tail as column. Vertex
labels act by `q(head) * p * q(tail)^(-1)`. The ordered horizontal wrapping
edge carries the inverse horizontal label, while the ordered vertical edge
carries the vertical label. Native directed transports therefore carry the
horizontal label and the inverse vertical label. The nonabelian tests retain
these distinctions; no abelianization is used.

## Reuse and Mathlib scouting

The packet reuses the existing dependent contraction, canonical averaging,
trace-dual pairings, common local inverses, graph parent kernels, native torus
flat-connection classification, and pair-conjugacy quotient. Mathlib's
`Submodule.equivMapOfInjective`, `LinearEquiv.ofEq`, and
`finrank_span_eq_card` provide the original-space equivalence and dimension
argument. No new equivalence, span, quotient, or parent infrastructure is
invented. The tactic-pattern scanner found no repeated patterns at its default
threshold in the new production and regression sources; no ledger change
was needed.

## Validation and regressions

All eight production modules and both regression files are checked with Lean
4.35.0-rc3, automatic and relaxed implicits disabled, package synthesis depth
three, standard Mathlib linters, warnings as errors, and one compiler worker.
All 41 public declarations are audited for axioms; only `propext`,
`Classical.choice`, and `Quot.sound` occur.

The concrete regression combines all of the following in one actual model:

- native 3-by-3 torus;
- nonabelian group S3;
- independently sized 12- and 18-dimensional bonds, each containing multiple
  regular copies, reindexed to the exact finite bond dimensions;
- independent physical alphabets of dimensions 31,105 and 20,737;
- factor-two, nonsurjective physical embeddings with an unused `none`
  coordinate; G-injectivity and failure of surjectivity are proved;
- full ambient canonical parent-kernel equality and class-count dimension;
- the explicit forward equivalence, restriction inverse, reconstruction,
  and unique original closure-span representative;
- genuinely noncommuting labels and inverse-sensitive seam orientations.

A separate generic regression retains arbitrary periods and independently
typed bonds/sites. The three-page blueprint fragment has all 41 public
anchors, verified cross-references, and a clean standalone XeLaTeX render;
every page was visually inspected. Existing external labels are stubbed only
for standalone layout testing after their presence is checked in the source.
No full repository build or fully integrated blueprint generation is claimed.
The recursive provenance audit checks 216 TNLean/QIC modules, including 23
QIC modules, against exact source/artifact receipt pairs.

### Timing caveat

The frozen strict run records 77.4 seconds for the padded classification
module and 124.5 seconds for its concrete regression, exceeding the repository's
50-second timing threshold in this executor. A separate profiler attributes
86.9 seconds to imports, versus 376 milliseconds of elaboration, 89 milliseconds
of tactics, and 98 milliseconds of type checking for the padded module. The
independent reviewer observed an approximately 99-second first import of the
normally 3.8-second base closure module, but the subsequent independent
padded-module and regression checks took only 4.17 and 8.57 seconds. These
repeated clean runs meet the per-module timing threshold and identify the
outliers as import/runtime loading variability rather than expensive proof
elaboration. Both strict correctness and linter checks passed throughout.

## Reproducible local evidence

The private `.validation` directory contains the exact source hashes,
per-module strict logs, artifact hashes, public declaration list, axiom
output, recursive import provenance, and rendered pages. Reproduction:

```sh
source .validation-env.sh
python3 .validation/final_check.py
python3 .validation/audit_provenance.py
```

The dependency overlay is read-only symlinks to source-audited artifacts;
only the ten new module outputs are regular private artifacts. Every reused
TNLean/QIC import must match both source hash and artifact hash in an existing
reviewed receipt. QIC sources are taken from the exact pinned `2ba242` source
checkout. Mathlib is never rebuilt and no package cache is cloned.

Shared root imports, sub-aggregators, blueprint routers, integrated declaration
checking, remote CI, and publication remain integration work. This packet
changes only new source, test, blueprint, and audit files. It excludes MPU
gauging and paused work on issue 8572.
