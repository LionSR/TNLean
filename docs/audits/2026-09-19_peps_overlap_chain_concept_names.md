# Concept names for the PEPS overlapping-union chain and the two unconditional capstones

First slice of the unshipped rename-and-merge of the numbered PEPS chains
recorded as section 10 of the numbered-sequel debt item. Two adjacent stages of
the `PEPS/RegionBlock` overlapping-union chain are merged into concept-named
modules, and the two `2`-suffixed unconditional Fundamental Theorem modules are
renamed by their content. No declaration is renamed, added, or removed, so every
blueprint `\lean{...}` tag keeps its target.

## Merged modules

| Absorbed modules | Surviving module |
|---|---|
| `TNLean/PEPS/RegionBlock/UnionInjectivityOverlap.lean`, `TNLean/PEPS/RegionBlock/UnionInjectivityOverlap2.lean` | `TNLean/PEPS/RegionBlock/UnionInjectivityOverlapSetup.lean` |
| `TNLean/PEPS/RegionBlock/UnionInjectivityOverlap3b.lean`, `TNLean/PEPS/RegionBlock/UnionInjectivityOverlap6.lean` | `TNLean/PEPS/RegionBlock/UnionInjectivityOverlapBridge.lean` |

Both pairs are phase-honest rather than arithmetic. The first pair holds the
setup of the source's two-step inverse application: the two host three-block
geometries `overlapLeftGeometry` and `overlapRightGeometry`, the first inverse
application `overlap_firstStrip`, the right geometry's blue-side host-weight
rebuild, and the `P₁`--`P₀` crossing edges. The second pair holds the bridge row
and the closure: the first strip reduced through the crossing collapse, the
bridge host-coefficient identity in the right geometry's native types, the
`P₀`-outer fiber restriction, and the capstone
`regionBlockedTensorInjective_union_overlap`. The docstring of
`UnionInjectivityOverlap3b.lean` stated that its split was made for the
file-length convention alone, so nothing mathematical is being joined across a
phase boundary.

The four modules share one `open scoped`, `namespace`, and `variable` preamble
verbatim, so the merge needs no `section` wrapper and no signature acquires or
loses an instance argument. Each merged module keeps one copyright header, one
import block, one module docstring, and one References block; the two absorbed
References blocks are dropped as duplicates.

## Renamed modules

| Old path | New path |
|---|---|
| `TNLean/PEPS/TorusFundamentalTheorem2.lean` | `TNLean/PEPS/TorusUnconditionalFundamentalTheorem.lean` |
| `TNLean/PEPS/NormalSquareFundamentalTheorem2.lean` | `TNLean/PEPS/NormalSquareUnconditionalFundamentalTheorem.lean` |

Neither module is a continuation. `TorusFundamentalTheorem.lean` proves the
scalar condition on the discrete torus and is a separate mathematical layer, not
the first half of a split; the `2` module assembles the unconditional torus
theorem `fundamentalTheorem_normalTorusPEPS_unconditional` on top of it. The
open-square module has no predecessor file at all: it assembles
`fundamentalTheorem_normalSquarePEPS_unconditional`. Both new names state the
mathematical responsibility the modules already carry in their docstring titles.

## Allowlist

`NUMBERED_DEBT_ALLOWLIST` in `scripts/check_numbered_lean_files.py` is a ratchet
that only shrinks. Five entries are retired in the same change:
`UnionInjectivityOverlap2.lean`, `UnionInjectivityOverlap3b.lean`,
`UnionInjectivityOverlap6.lean`, `TorusFundamentalTheorem2.lean`, and
`NormalSquareFundamentalTheorem2.lean`, leaving 29 of the previous 34.

## What was checked

The import ladder is linear. Outside the generated aggregators, the only
importers of the absorbed modules were the next chain stage
(`UnionInjectivityOverlap3.lean`) and `NormalSquareInjectivity.lean`; both are
retargeted, and neither gains a module in its import cone, because the merged
module is exactly the union of the two it replaces. The two renamed modules had
no importer but the `TNLean/PEPS.lean` aggregator, which is regenerated.

Blueprint exposure of this material is by declaration, never by path: no
blueprint source cites any of the six paths, and the declaration inventory is
unchanged, so the blueprint and Lean declaration sets remain in sync. The
`TNLean.PEPS` aggregator, which imports every module of the development, builds
clean with the package linter options.

## Retained and deferred

The remaining stage `UnionInjectivityOverlap3.lean` stays numbered and
allowlisted: it is an 816-line module, so merging it into either neighbour
exceeds the file-length cap. Its docstring cross-reference to the absorbed
modules is updated to the surviving name.

The other numbered chains in the same area are untouched here. The
`Recovery` pairs `{5, 6}` and `{10, 11}` and the `CoarseThreeSite` pair `{2, 3}`
are the remaining phase-honest merges; the `Recovery` pairs `{4, 5}`, `{6, 7}`,
`{8, 9}` and the `CoarseThreeSite` pairs `{5, 6}` and `{8, 9}` are refused,
because each cuts across the mathematical phase its two docstrings name, and
`CoarseThreeSite5.lean` and `CoarseThreeSite6.lean` additionally carry different
`variable` preambles, so joining them would change tagged signatures. The
`CoherentFrameInstance2.lean` and `GaugeInjectivity2.lean` renames are deferred
to a later slice.

Dated audit notes that cite the old paths are left as written: they record the
state of the development on their own date and are not living references. The
living citations in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
`docs/tactic_patterns.md`, and the open entry of `docs/proof_debt_ledger.md` are
updated to the new paths.
