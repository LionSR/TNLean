# The RMP cosmetic-gap bar

The RMP benchmark seeks mathematical parity in tenkz's own graceful house
style. It does not seek pixel identity with the author source. A difference in
colour, line weight, glyph outline, slant, or equivalent planar routing is
therefore faithful when it preserves the mathematical object, topology,
boundary, labels, orientation, and declared crossing order.

This distinction controls the verdict:

- **K1 — recorded property:** the model records the property but the renderer
  does not yet ink it. Fix the shared renderer or theme, then re-review every
  affected case. Do not patch individual cases.
- **K2 — house style or stale note:** the note records an intentional house
  form, an equivalent presentation, or a correction that has already removed
  the stated defect. Re-review the hash-pinned render and promote it to
  `faithful`; do not redraw it to imitate source pixels.
- **K3 — gracefulness:** the meaning is intact, but the default rendering is
  loose, crowded, oversized, or ambiguous. Prefer a shared metric, route, skin,
  or family-level fix. Use a case-local adjustment only when the geometry is
  genuinely exceptional.
- **K4 — small omission:** a finite source item such as a label, arrow, tensor,
  leg, or projection mark is absent or extra. Fix and re-review the individual
  case.
- **X — not cosmetic:** the ledger itself contradicts the cosmetic status by
  recording a topological, boundary, contraction, ordering, or crossing
  defect. Move the case to the appropriate ordinary RMP verdict before any
  cosmetic sweep.

`cosmetic-gap` is reserved for K1, K3, and K4 while their stated residue is
visible. K2 is not a permanent gap class: after a visual check confirms that
the mathematical contract is intact, its verdict and note should become
`faithful`. X is an audit escalation, not a fifth cosmetic kind.

## Current classification

This table classifies the 98 `cosmetic-gap` verdicts at merge
`c3b4667c10faa7cadaf4a18fdbab3bc72b85fa18`. The reason column records the
disposition of the current verdict note; it is not a substitute for the
hash-pinned visual check required before changing a verdict.

| Target | Kind | Reason / next action |
|---|---:|---|
| `rmp-ii-peps-projection` | — | Promoted to `faithful` 2026-08-04: projector layer, named A site, named bond, and boundary all present; tint and leg colour are house style. |
| `rmp-ii-mps-marginal` | K3 | Replace the heavy trace closure through the shared minimal closure idiom. |
| `rmp-ii-peps-marginal` | K3 | Reduce excessive trace-loop height through the closure metric. |
| `rmp-ii-mpu-brickwork` | — | Promoted to `faithful` 2026-08-04: twelve legs, alternating layers, and labels match; labelled boxes for dotted gate pairs are the inherent circuit presentation. |
| `rmp-ii-mpu-two-shift` | K1 | Resolved 2026-08-04: the case now carries the workbench-twin skin-pairings model with the published palette; the row channels keep house ink where the panel colours the movers. |
| `rmp-ii-mpu-normal-form` | K3 | The solid S-route is heavier and less compact than the graceful default should be. |
| `rmp-ii-spectrum-transfer` | K3 | Supply the shared designed tail idiom for the two fixed-point tails. |
| `rmp-ii-spectrum-fixed-points` | — | Promoted to `faithful` 2026-08-04: fold side, factor order, and open ends match; capsule glyphs are equivalent house routing. |
| `rmp-ii-blocking` | — | Promoted to `faithful` 2026-08-04: re-review and oracle pass confirmed the one-site isometry matches the source panel; the wider house pill is intentional styling. |
| `rmp-ii-staircase` | K3 | Resolved 2026-08-04: the re-audit confirmed the vertical mirror; the case now ascends as in the source. Residue: house box for the rounded V glyph (#5363). |
| `rmp-ii-circuit` | — | Already `faithful` (2026-08-02 two-viewer review); the doubling tree carries the complete eight-output identity. |
| `rmp-ii-ortho-left` | — | Promoted to `faithful` 2026-08-04: cup topology, glyph orientation, and labels match; thin house wires are intentional styling. |
| `rmp-ii-boundary-lasso` | K1 | Resolved 2026-08-04: the palette is model-recorded as declared species; the physical policy legs stay house-ink because the policy stub does not read the host species. |
| `rmp-ii-boundary-region` | K2 | The boundary is recorded as repaired; no residue is named. |
| `rmp-ii-boundary-state` | K2 | A brace versus a box is an equivalent house mark for the same region. |
| `rmp-ii-zcl-mpdo` | K3 | Make the shared trace closure more compact than the current racetrack. |
| `rmp-ii-channels-ts` | — | Promoted to `faithful` 2026-08-04: legs and channel directions match; the straight double arrow is equivalent house routing. |
| `rmp-ii-mpdo-ol` | K4 | Reconcile the ledger's finite `extra-element` defect with the note saying the contrast panel is gone, then re-review the hook spacing. |
| `rmp-ii-peps-rg` | X | The current hooks cross where the source keeps them separated; restore the source crossing topology. |
| `rmp-ii-inverse-renormalization` | K3 | Remove the residual family-level spacing looseness. |
| `rmp-iii-a-f-symbol` | — | Promoted to `faithful` 2026-08-04: crossing order, directions, sectors, and all six labels verified against the author figure. |
| `rmp-iii-a-pulling-through` | K3 | Normalize curve weight and panel spacing. |
| `rmp-iii-a-commuting-hamiltonian` | — | Promoted to `faithful` 2026-08-04: gate span and contractions match; the labelled white pill is house typography. |
| `rmp-iii-a-proof-one` | — | Promoted to `faithful` 2026-08-04: alpha-dot contraction and reduced tensor match; the rounded pill is a house glyph form. |
| `rmp-iii-a-proof-two` | — | Promoted to `faithful` 2026-08-04: stacked fusion matches wire for wire; bond hue and box size are theme choices. |
| `rmp-iii-a-proof-three` | — | Promoted to `faithful` 2026-08-04: the full fusion stack and the up stub above beta match; red operator rails are the house semantic hue. |
| `rmp-iii-a-ghz-state` | K1 | Resolved: the case now records the full six-by-eight staggered model on the kernel (all junctions, bonds, and legs verified present 2026-07-30); only the shared kernel spacing and stroke profile differ. |
| `rmp-iii-a-ghz-tensor` | — | Promoted to `faithful` 2026-08-04: four open indices and equation match; labelled box and orthogonal legs are house forms. |
| `rmp-iii-a-hadamard` | X | Promoted to `structural-gap`: its pairing is `wrong-source`; repair and verify the source mapping before judging the explicit label. |
| `rmp-iii-a-spt-mpo` | — | Promoted to `faithful` 2026-08-04: string pull, both crossings, action boxes, and the U_g insertion verified under the boundary audit. |
| `rmp-iii-a-spt-intertwiner` | X | The open fusion map has no trace cyclicity; restore the source factor order before reviewing glyph scale. |
| `rmp-iii-a-g-injective-projector` | X | Its ledger pairing is `wrong-source`; repair the projector source mapping before any verdict promotion. |
| `rmp-iii-a-mpo-action` | K3 | Restore a graceful diagonal physical-leg route. |
| `rmp-iii-a-mpo-injective` | K2 | Ring topology is preserved; unrecorded hatching and hue require house-style re-review, not a renderer promise. |
| `rmp-iii-a-torus-one` | — | Promoted to `faithful` 2026-08-04: both wound cycles, the inner bends, and the crossing at i verified; outlined box and weight are house style. |
| `rmp-iii-a-torus-two` | — | Promoted to `faithful` 2026-08-04: periodic word, marked fourth tensor, and ten open legs match; public theme replaces vivid source ink. |
| `rmp-iii-a-torus-three` | K2 | Outline versus solid fill on the enlarged crossing is house style. |
| `rmp-iii-b-dyon` | K2 | The marked region and open string are present after route migration. |
| `rmp-iii-b-self-braiding` | K2 | Tensor counts, winding classes, tail crossing, and boundary are complete. |
| `rmp-iii-b-braid-one` | K2 | Stations and noncrossing winding strings match the source. |
| `rmp-iii-b-braid-two` | K2 | The nested noncrossing strands match the flattened source. |
| `rmp-iii-b-braid-three` | K2 | Lattice slant differs without changing the winding contraction. |
| `rmp-iii-b-condensation` | K4 | Add the finite projection mark named by the verdict note. |
| `rmp-iv-ground-space-1d` | K3 | Improve the small X glyph and overly tight placement. |
| `rmp-iv-ground-space-2d` | X | `physical=up` creates ports but records no wire direction; model the source arrowed legs before theme review. |
| `rmp-iv-intersection-lhs-one` | — | Promoted to `faithful` 2026-08-04: both virtual ends close into L with matching physical legs; sideways cups are equivalent routing. |
| `rmp-iv-intersection-rhs-one` | — | Promoted to `faithful` 2026-08-04: uncovered wire and B--C close into R; sideways cups are equivalent routing. |
| `rmp-iv-intersection-lhs-two` | — | Promoted to `faithful` 2026-08-04: west cup closure and both openings match; sideways routing preserves the boundary. |
| `rmp-iv-intersection-rhs-two` | — | Promoted to `faithful` 2026-08-04: east cup closure, no crossing, sideways ends equivalent. |
| `rmp-iv-intersection-lhs-three` | — | Promoted to `faithful` 2026-08-04: two virtual and three physical openings match; sideways ends equivalent. |
| `rmp-iv-intersection-rhs-three` | — | Promoted to `faithful` 2026-08-04: both closures and openings match; routing is a house choice. |
| `rmp-iv-intersection-lhs-four` | — | Promoted to `faithful` 2026-08-04: five openings match; the horizontal identity wire is equivalent to the U-route. |
| `rmp-iv-intersection-rhs-four` | — | Promoted to `faithful` 2026-08-04: five open ends match Rtensor4; no spurious crossing. |
| `rmp-iv-intersection-lhs-five` | — | Promoted to `faithful` 2026-08-04: the restored three-index boundary matches; sideways stubs preserve it. |
| `rmp-iv-intersection-rhs-five` | X | Re-audit the mirrored open C--X contraction before accepting it as equivalent routing. |
| `rmp-iv-intersection-lhs-six` | X | Promoted to `blocked`: the missing `nested-regions` capability leaves an invented lattice and the wrong contraction. |
| `rmp-iv-intersection-rhs-six` | X | Promoted to `blocked`: the missing `nested-regions` capability leaves an invented lattice and the wrong contraction. |
| `rmp-app-czx-state` | — | Promoted to `faithful` 2026-08-04: source grouping and lattice wiring verified; lighter enclosure fill is a public-theme choice. |
| `rmp-workbench-ii-newfig7` | K2 | Crossing-gadget styling is a house-form difference. |
| `rmp-workbench-ii-projector-on-pta` | X | Promoted to `structural-gap`: omitting two of four source triangles changes the multiplicity of the sandwich sum. |
| `rmp-workbench-ii-peps-rg-workbench` | X | Its ledger pairing is `wrong-source`; repair and verify the source mapping before judging the U-application idiom. |
| `rmp-workbench-ii-positive-mpo-old` | K2 | The ledger already records equal X sizes; re-review the hash-pinned render as faithful. |
| `rmp-workbench-ii-peps-gauge-old` | K3 | Preserve diagonal leg flow and smooth the marked detour tangents. |
| `rmp-workbench-ii-peps-gauge-without-a` | K3 | Apply the same shared gauge-family geometry correction. |
| `rmp-workbench-ii-mpu-wrap-second` | K2 | Both source-directed pairing rows are now in the correct order. |
| `rmp-workbench-ii-boundary-a-old` | K4 | Restore the finite arrow and R-bar label details, then re-review the region. |
| `rmp-workbench-ii-boundary-b-old` | X | The case does not record `species=`; migrate the semantic colour coding into the model first. |
| `rmp-workbench-ii-peps-fine-graining` | K2 | The structured-grid redraw already contains the required panel. |
| `rmp-workbench-ii-historical-composite` | K2 | A flat tilted grid is the house equivalent of the source 3D cube. |
| `rmp-workbench-iii-eq50` | K2 | All four source legs are present; no residue is named. |
| `rmp-workbench-iii-eq51` | K2 | Plain semantic ink versus source red is a public-theme choice. |
| `rmp-workbench-iii-eq52` | K2 | Plain semantic ink versus source red is a public-theme choice. |
| `rmp-workbench-iii-diagram-one` | K2 | Both rings close; boundary-size change is the identity itself. |
| `rmp-workbench-iii-diagram-two` | K2 | Y, A, and physical loop orientation match the source. |
| `rmp-workbench-iii-diagram-three` | K1 | Per-edge direction ink is a shared ports/arrow rendering property. |
| `rmp-workbench-iii-historical-composite` | K3 | All mathematical parts are present; only placement nuance remains. |
| `rmp-workbench-iii-diagram-four` | K2 | Stadium versus circle is a house glyph difference. |
| `rmp-workbench-iii-eq50-reduced` | K4 | Re-review and remove any labels not present in the source contract. |
| `rmp-workbench-iii-dual-reduced` | X | Challenge the current cyclic-equivalence note: the manifest declares an open intertwiner, so repair the source factor order. |
| `rmp-workbench-iii-mpo-representation` | K2 | The complete MPO word and labels are present; plain virtual-index ink requires house-style re-review. |
| `rmp-workbench-iii-f-tensor` | K2 | An explicit F box faithfully replaces the source's boxless crossing. |
| `rmp-workbench-iii-eq59-now` | K2 | Ring colour and stadium-versus-circle glyphs are house style. |
| `rmp-workbench-iii-ghz-state-workbench` | K1 | The manifest records `staggered-sites`; route the fix through the cell basis, not the published GHZ lattice mechanism. |
| `rmp-workbench-iii-ghz-up` | K3 | Improve glyph proportions and leg geometry as a family. |
| `rmp-workbench-iii-g-injective-pull` | X | Re-audit the source pairing: the current diagonal `U_g` belongs to the SPT panel. |
| `rmp-workbench-iii-intertwining-mpo` | K2 | Line weight alone is house style. |
| `rmp-workbench-iii-mpo-injective-white` | K2 | Direct strings faithfully replace the source's substituted boxes. |
| `rmp-workbench-iii-mpo-on-peps-definition` | K3 | Treat unrecorded hatching and hue as house style; fix only the family-level centring residue. |
| `rmp-workbench-iii-eq60-now` | K2 | Daggered insertions and genuinely diagonal legs are present. |
| `rmp-workbench-iii-enlarged-mpo-black` | K2 | The closed five-box ring and marked site are complete. |
| `rmp-workbench-iii-eq59` | K2 | Both windings, complete station counts, and joined resolution rails are present. |
| `rmp-workbench-iii-g-injective-mpo` | K3 | Resolved 2026-08-04: the eight sector labels sit on genuine open boundary half-edges, each with its own open wire; the four plaquette bonds stay internal and unlabelled. Residue: house box for the source circle glyph. |
| `rmp-workbench-iii-peps-renormalization-one` | X | The manifest requires four edge-centred PEPS atoms that the case omits; reconcile the contract before hatch review. |
| `rmp-workbench-iii-peps-renormalization-two` | K2 | Effective tensor, corner blocks, and fused legs are complete. |

## Sweep order

1. Correct every X ledger contradiction and handle it under the ordinary RMP
   structural verdict and repair process.
2. Re-review K2 against the current hash-pinned renders and change only the
   verdict metadata where the contract is intact.
3. Group K1 by the owning renderer/theme capability. Land one shared fix,
   rerender every consumer, and retire all residues it actually removes.
4. Group K3 by closure, tail, hook, pitch, glyph, gauge-route, and spacing
   families. Each family change must improve the default rather than merely
   move one case closer to legacy pixels.
5. Fix K4 in small source-family batches with side-by-side visual review.

Every batch still runs the focused RMP check, the full RMP audit, the shrink
ratchet, and the standalone tenkz corpus before its verdict hashes change.
