# Arbitrary complements in the asymmetric fundamental theorem

PR #10259 originally linked the arbitrary-complement statement of
`thm:asym_uniq_common_basis` to constructions using only `matchedCompl`,
a family fixed by `Classical.choose`. This repair is based on the exact
head `f94a7cb25f206b4f808f475ef21ed50832be95c5`.

## Mathematical statement

For matched positions of two reductions, write
`U_k = M_{k+1} ∩ M′_{π(k)+1}` and `K_k = M_k ∩ M′_{π(k)+1}`,
with positions counted from zero. A supplied complex-linear subspace `L_k`
needs only `K_k ∩ L_k = 0` and `K_k + L_k = U_k`.

`MatchedComplements` bundles exactly this family and these two properties.
The reading map on each `L_k` is bijective by the existing
`bijective_leftRow_domRestrict`. The flag identities give spanning; the
existing slot-coordinate construction then derives coordinate invertibility
and independence using the dimension equality of the reduction. No
independence, dimension, adapted-coordinate, or factorization premise is
added to the supplied family.

The existing `commonCoord`, `commonGauge`, `unipotentFactor` constructions
and their primed versions now take an explicit optional family `L`.
Their decomposition, dimension, triangularity, identity-diagonal, and
factorization theorems are proved for that same arbitrary `L`. The
matching and its intertwining permutation matrix remain independent of `L`.
The default family retains the original chosen complements.

`matchedComplements_conjTriangular` retains `L.space` literally after
triangular gauge changes. Its complement properties follow from equality
of the matched kernels and intersections. Both the unipotent change and
its converse now apply to this transported supplied family. There is no
restriction of the blueprint statement to a chosen complement.

## Example statements

The new `ch25_asymmetric_ft_examples.tex` gives mathematical statements and
links for the periodic, no-gauge, diagonal, multiplicity, one-block,
sharpness, and four-dimensional worked examples, including their explicit
flags and adapted factorizations. Coordinate-reading definitions have
separate entries. Existing sharpness links remain in the uniqueness chapter.

The lecture note *The asymmetric fundamental theorem of matrix product
states* is not present in `Papers/` or `Notes/`. Example numbering follows
the module citations. The new statements were compared with the actual Lean
signatures and checked independently in the displayed finite-dimensional
examples; an independent comparison with the absent note is not claimed.

## Validation

Passed local validation:

- `lake build TNLean.MPS.FundamentalTheorem.Reduction.UniquenessAllReductions
  TNLean.MPS.Examples.MultiBlock`.
- All three changed Lean files elaborate with the exact strict flags from
  `scripts/ci_lean_checks.py`, including warnings as errors. Their standalone
  times were 11.5 s, 29.2 s, and 7.5 s respectively.
- A temporary universally quantified raw complement family, with only
  disjointness and the sum identity, proves spanning, independence, the flag
  decomposition, and the factorization by the generalized declarations.
  The unipotent converse accepts that same raw family. Both acceptance
  theorems and the two main unipotent theorems have only `propext`,
  `Classical.choice`, and `Quot.sound` as axioms.
- All 112 declaration references in the new example entries and the two
  amended uniqueness entries resolve against the compiled targeted imports.
  This includes every one of the new chapter's 93 references.
- Blueprint source synchronization, its scanner tests, pinned LaTeX
  formatting of all three affected chapters, added-line prose checks,
  line-width and whitespace checks pass.
- Independent semantic reviews checked the arbitrary-family proof and all
  new example statements. Independent exact arithmetic checked the displayed
  four-dimensional conjugations, factorizations, intersection dimensions,
  and complement subspaces.

Mathlib prebuilt artifacts were fetched and verified before targeted builds;
no Mathlib module was rebuilt from source. Temporary acceptance files are
outside the repository. The complete root-import `checkdecls` command and
full repository CI remain for the publication step; the local declaration
check imports the two relevant compiled targets.

The two pre-existing review threads are left unresolved for author/reviewer
assessment. This local repair does not publish to the author's branch or
merge the PR.
