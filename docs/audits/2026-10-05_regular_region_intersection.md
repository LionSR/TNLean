# Regular regional intersection with exterior legs retained

## Result and source scope

This batch proves the actual regular-coordinate intersection identity for
finite-simple-graph regions `R` and `S` satisfying:

- `R ∩ S = {b}`;
- no edge joins `R \ S` to `S \ R`.

`regularGlobalRegionRange_inf_eq_union` identifies the intersection of their
actual lifted regional ranges with the actual range of their union. It uses
`mem_regularGlobalRegionRange_iff_invariant_flat`, via individual vertex and
edge fixedness, rather than a closed-state inclusion or an assumed range
identity. No abelian or connectedness hypothesis is added. Half-edges crossing
either regional boundary remain present.

The flatness proof aligns local potentials by replacing
`kS(v)` with `kS(v) * kS(b)⁻¹ * kR(b)`. Their values then agree at the unique
shared vertex. The inverse of the constant right multiplier acts on the left
of each endpoint equation, preserving it for nonabelian groups. The no-cross
hypothesis ensures that every internal union edge lies in one of the two
regions. Restriction proves the converse and range antitonicity.

### Removing exterior physical factors

The ambient theorem alone retains physical coordinates at exterior vertices.
The batch additionally proves the localization, rather than assuming that
those factors may be dropped:

- `regularSubregionSlice R T` fixes the half-edge configurations of `T \ R`.
- `regularRegionRangeWithin T R` requires every such slice to lie in the
  range of the actual open-region matrix of `R`.
- `regularRegionConstantExtension T` sends a vector `x` on `T` to the vector
  whose value at an ambient configuration `α` is `x (α|T)`.
- `regularRegionRangeWithin_eq_comap` proves the exact pullback identity.
  Every within-core complementary assignment extends to the whole graph by
  setting exterior labels to the group identity.
- `regularRegionRangeWithin_self` identifies the self-condition with the
  actual open-region matrix range.
- `regularRegionRangeWithin_inf_eq_range` therefore proves the intersection
  on the physical factors of `R ∪ S` alone. Its conclusion has no exterior
  physical factor and retains every open virtual boundary label.

### Literal source geometry

`threeBlockFourLegGraph` has the core path `0–1–2` and eight distinct exterior
leaves: `3,4,5` at `0`, `6,7` at `1`, and `8,9,10` at `2`. Each core vertex has
four incident legs and the core region has eight boundary edges; these counts
are proved in Lean. The regression also verifies that every exterior vertex
has degree one.

`threeBlock_regularGlobalRegionRange_intersection` is the ambient equality on
all eleven physical factors. `threeBlock_regularRegionRange_intersection`
is the localized equality on exactly the three core physical factors, with
the genuine three-block open-region matrix on the right. Its boundary input
is an arbitrary tensor on all eight virtual boundary labels, so correlations
among those labels are not restricted.

This matches the regular-coordinate three-block geometry of SCP10,
arXiv:1001.3807, Theorem 5.4. The source drawings `figs3/grow-intersect.pdf` and
`figs3/grow-N.pdf` were rendered and inspected: the three core tensors retain
their top/bottom legs and the endpoint side legs. A one-dimensional strip with
those legs discarded is not used.

This is **not completion of source Theorem 5.4**. Arbitrary G-injective physical
site maps, arbitrary semi-regular virtual representations, heterogeneous
representations and broader blocking/geometry remain separate. The new
blueprint entry is explicitly regular-only and does not replace the source
claim with stronger-hypothesis completion tags. The localization itself is
proved and is not a remaining gap.

## Validation

Base: `3b3da4eff`.

- Lean 4.35.0-rc3, compiler commit
  `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Three production modules and `TNLeanTest/RegularRegionIntersection.lean`
  pass fresh targeted elaboration with `autoImplicit=false`,
  `relaxedAutoImplicit=false`, `pp.unicode.fun=true`, `maxSynthPendingDepth=3`,
  `linter.mathlibStandardSet=true`, and `warningAsError=true`.
- Final elapsed times: generic intersection 2.924 s; localization 3.195 s;
  literal source geometry 2.594 s; regression 2.581 s. These are local
  diagnostics, not cross-machine benchmarks.
- Regressions include generic equality, nesting, flatness gluing, the
  nonabelian group `Equiv.Perm (Fin 3)` for both ambient and core-only source
  identities, all core/exterior degrees, and the boundary count. A triangle
  also exercises the fact that the no-cross-edge condition is substantive.
- Five guarded theorem-axiom checks report only `propext`, `Classical.choice`,
  and `Quot.sound`. No proof holes, new axioms, or kernel-bypass tactics occur
  in the new Lean files.
- Exact source and artifact provenance was checked for 137 transitive
  TNLean/QICLean dependencies from the existing completion validation cache.
  Artifacts from the physical-commutation worktree additionally matched its
  source/artifact SHA-256 provenance. The Lean toolchain, Lake manifest and
  package options match the donor. No Mathlib rebuild or shared cache write
  was performed.
- All 20 public declaration tags in the new blueprint fragment resolve.
  Repository-wide source scanning still reports existing missing external
  declarations in this standalone worktree; it is not a full-blueprint pass.
- Pinned latexindent formatting passes. The fragment was compiled standalone
  and both rendered pages inspected; there are no unresolved local references,
  citation warnings, or overfull/underfull boxes in the final render.
- The repository tactic-pattern scan was run; this batch introduces no
  three-times repeated proof pattern requiring promotion.

The private `.validation/` directory records dependency hashes, compiler
commands, fresh logs, final artifact hashes, blueprint checks and rendered
pages. No full repository/root build, generated-import update, or full
`leanblueprint checkdecls` pass is claimed. Shared import routers and blueprint
routers are deliberately left to the integrating task.
