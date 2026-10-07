# Primary birth regions and rectangular fragments

Seventeen original declarations in `PrimaryRegions.lean`,
`PrimaryFragments.lean` and `AdjacentScales.lean` describe actual primary birth
regions of a translated dyadic layer. A birth region is the closure of the
intersection of the layer with one open pitch interior. It is exactly the
finite union of its nonempty closed cell fragments. Each such fragment is a
closed rectangle of sup diameter at most the coarse-cell side; the whole
birth region has sup diameter at most the pitch. Points belonging to different
primary identifiers in one layer are separated by at least the belt width.

For coarse index k at most pitch index p, the number of nonempty fragments
in one primary is at most `(2^(p-k) + 2)^2`. This scale ordering is intrinsic
to the manuscript scales and is explicit in the general-scale statement.
The exact rectangle formula requires a nonempty intersection. The containment
and diameter bounds include empty primary regions and empty fragments.

Three arithmetic results show that the rounded fine index is monotone,
increases by zero or one at a consecutive scale, and yields fine-cell sides
whose consecutive ratio is one or two. They carry no additional hypothesis.
They do not establish the affine mesh, midpoint subdivision or contact geometry.

## Source and mathematical scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The primary construction is in lines 212–218; the rectangular fragments,
diameters and same-layer separation are in `geometry:primary-pieces`, lines
237–249. The adjacent-scale arithmetic supports the initial-contact and
isolated-star discussion in lines 299–306 and 352–356, under
`geometry:initial-stars`. The proof text is independently written; no upstream
Lean source or proof text is reused.

This contribution counts the fragments of one primary. The number of primary
identifiers across a whole layer is the separate continuation
`PrimaryCounting.lean`. The affine mesh and contacts, isolated stars, repairs
and descendants, birth separation from earlier actual regions, the complete
two-family partition and both manuscript headline theorems remain open.
Independent geometry review approved the scope and mathematical statements of
these seventeen declarations without claiming the full partition.

## Exact source and canonical local verification

The exact verified mathematical source is
`d469be1a0a7799f4613e64e8139893b0fa2ee11d`, published in
[TNLean #8851](https://github.com/LionSR/TNLean/pull/8851).
The later formatting-only revision
`8f060ee701641816520b394d8de198d3271dbe44` preserves the bytes of all three
Lean modules and the imported-declaration audit. The log headers record the
actual source revision captured when the verification driver began, before
that formatting change.

The commands ran consecutively through the own-worktree
`scripts/lake_build_locked.sh --` under the shared repository lock, reusing
the warmed cache and pinned prebuilt Mathlib artifacts. Waiting consumed no
CPU. No local full-library build or Mathlib source rebuild was repeated.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Targeted Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | 0 | 11.746 |
| Imported-declaration audit | `lake env lean docs/provenance/evidence/8758-primary-regions-axioms.lean` | 0 | 4.266 |
| Whole-library compiled blueprint declarations | `leanblueprint checkdecls`, from `blueprint/` | 255 | 16.950 |

The new leaf modules compiled without warnings: `AdjacentScales` in 2.6
seconds, `PrimaryRegions` in 2.9 seconds and `PrimaryFragments` in 2.5 seconds.
The imported audit prints all seventeen exact public names. Every reported
dependency is one of `propext`, `Classical.choice` and `Quot.sound`; no
`sorryAx`, extra axiom or prohibited proof mechanism is reported.

The whole-library compiled declaration check failed because the local cache
lacks the pre-existing object file for `TNLean.MPS.Examples.Fibonacci`.
Its diagnostic identifies the missing `Fibonacci.olean`; the subsequent
`lake exe checkdecls blueprint/lean_decls` invocation returned nonzero.
This missing artifact belongs to the MPS examples, outside the new Geometry
modules. The failed command is not recorded as passed or used as proof
verification. The full-library CI build supplies the separate compiled
blueprint check; its outcome remains pending in this record.

## Evidence logs and provenance

Committed log paths and SHA256 hashes:

- `8758-primary-regions-build.log`: `9c657b6bdd477315f688e3fbdf482010792772fe057824cd875cc1cfa1f9f81e`.
- `8758-primary-regions-axioms.log`: `0fe6f7ebd56e701386c55ef31e8beffdfa70659ab1040a7a910b91a584d76045`.
- `8758-primary-regions-blueprint.log`: `4ce2494fe9ba99e69aff625fe06d7c6658dd39ef619df70333f5e09f904a65b2`.

The logs record the actual command, exact revision, elapsed time and exit
code. Captured output has trailing whitespace removed; diagnostic and axiom
output is retained, including the failed compiled-blueprint result.

The source, build evidence and exact axiom output pass the complete
205-entry current-policy provenance validation, including the pinned
manuscript, license and notices. The provenance update promotes precisely the
seventeen new rows; all previous 188 entries and their evidence remain
byte-identical. Their recorded verification contains the passing targeted
build and imported-declaration audit. It does not claim that the separate
whole-library blueprint command passed.

## Integration checks and remaining verification

Strict non-mutating Lean elaboration with the package options and independent
mathematical review passed before canonical integration. Complete blueprint
source synchronization, including reverse coverage and duplicate reporting,
passed with 20,159 distinct references and 20,153 theorem-like entries.
Generated-import checks cover 75 aggregators and 2,832 production modules.
Source synchronization is distinguished from compiled declaration checking.

Full-library CI, compiled blueprint declarations and rendering are tracked in
[TNLean #8851](https://github.com/LionSR/TNLean/pull/8851). They were pending
when this evidence was prepared; no successful full-library or compiled
blueprint result is claimed here. Their eventual outcome is reported
separately on the pull request.
