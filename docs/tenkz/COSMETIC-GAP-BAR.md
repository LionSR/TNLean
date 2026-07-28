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
| `rmp-ii-peps-projection` | K2 | Projector layer and named bond are already present; re-review as faithful. |
| `rmp-ii-mps-marginal` | K3 | Replace the heavy trace closure through the shared minimal closure idiom. |
| `rmp-ii-peps-marginal` | K3 | Reduce excessive trace-loop height through the closure metric. |
| `rmp-ii-mpu-brickwork` | K2 | Operator-word versus circuit presentation is inherent to the identity. |
| `rmp-ii-mpu-two-shift` | K1 | Pairing geometry is a renderer skin property; re-review after the shared skin work. |
| `rmp-ii-mpu-normal-form` | K3 | The solid S-route is heavier and less compact than the graceful default should be. |
| `rmp-ii-spectrum-transfer` | K3 | Supply the shared designed tail idiom for the two fixed-point tails. |
| `rmp-ii-spectrum-fixed-points` | K2 | The relation is recorded as corrected; re-review as faithful. |
| `rmp-ii-blocking` | K2 | Case, manifest, and fixture metadata now agree; no residue is named. |
| `rmp-ii-staircase` | K3 | Improve mirrored layout and the V-glyph aspect at the family level. |
| `rmp-ii-circuit` | K2 | The compact doubling tree carries the complete eight-output identity. |
| `rmp-ii-ortho-left` | K2 | Thin house wires versus bold source wires are intentional styling. |
| `rmp-ii-boundary-lasso` | K1 | Species hue is a shared theme property, not a case-local colour patch. |
| `rmp-ii-boundary-region` | K2 | The boundary is recorded as repaired; no residue is named. |
| `rmp-ii-boundary-state` | K2 | A brace versus a box is an equivalent house mark for the same region. |
| `rmp-ii-zcl-mpdo` | K3 | Make the shared trace closure more compact than the current racetrack. |
| `rmp-ii-channels-ts` | K2 | Straight double arrows versus curved source arcs are equivalent house routing. |
| `rmp-ii-mpdo-ol` | K4 | Reconcile the ledger's finite `extra-element` defect with the note saying the contrast panel is gone, then re-review the hook spacing. |
| `rmp-ii-peps-rg` | K2 | Rounded crossing hooks versus separated square hooks are house geometry. |
| `rmp-ii-inverse-renormalization` | K3 | Remove the residual family-level spacing looseness. |
| `rmp-iii-a-f-symbol` | K2 | Crossing order, directions, sectors, and all six labels are present. |
| `rmp-iii-a-pulling-through` | K3 | Normalize curve weight and panel spacing. |
| `rmp-iii-a-commuting-hamiltonian` | K2 | The h-glyph difference is house typography. |
| `rmp-iii-a-proof-one` | K2 | The invented boxes are gone and the copy dot is restored. |
| `rmp-iii-a-proof-two` | K2 | Bond hue and box size are public-theme choices. |
| `rmp-iii-a-proof-three` | K2 | The full fusion stack is present; red operator rails are the house semantic hue. |
| `rmp-iii-a-ghz-state` | K1 | Masonry truncation belongs to the shared lattice-genre work tracked by #4931. |
| `rmp-iii-a-ghz-tensor` | K2 | Copy dot versus labelled box and diagonal angle are equivalent house forms. |
| `rmp-iii-a-hadamard` | X | Its ledger pairing is `wrong-source`; repair and verify the source mapping before judging the explicit label. |
| `rmp-iii-a-spt-mpo` | K2 | The string, action boxes, and measured-leg crossings are complete. |
| `rmp-iii-a-spt-intertwiner` | K2 | Mirrored equivalent ordering and glyph scale are house presentation. |
| `rmp-iii-a-g-injective-projector` | X | Its ledger pairing is `wrong-source`; repair the projector source mapping before any verdict promotion. |
| `rmp-iii-a-mpo-action` | K3 | Restore a graceful diagonal physical-leg route. |
| `rmp-iii-a-mpo-injective` | K1 | Hatching and semantic hue are shared renderer/theme properties. |
| `rmp-iii-a-torus-one` | K2 | Wound cycles and inner bends are explicit; line weight is house style. |
| `rmp-iii-a-torus-two` | K2 | Public-theme colour replaces vivid source ink without changing meaning. |
| `rmp-iii-a-torus-three` | K2 | Outline versus solid fill on the enlarged crossing is house style. |
| `rmp-iii-b-idempotent` | K2 | The contraction is recorded as corrected; no residue is named. |
| `rmp-iii-b-dyon` | K2 | The marked region and open string are present after route migration. |
| `rmp-iii-b-self-braiding` | K2 | Tensor counts, winding classes, tail crossing, and boundary are complete. |
| `rmp-iii-b-r-tensor-left` | K3 | Normalize pitch while preserving the three-station winding route. |
| `rmp-iii-b-r-tensor-right` | K2 | Upright house box versus a slanted source parallelogram is equivalent. |
| `rmp-iii-b-braid-one` | K2 | Stations and noncrossing winding strings match the source. |
| `rmp-iii-b-braid-two` | K2 | The nested noncrossing strands match the flattened source. |
| `rmp-iii-b-braid-three` | K2 | Lattice slant differs without changing the winding contraction. |
| `rmp-iii-b-braid-four` | K2 | Upright boxes replace source parallelograms without changing the identity. |
| `rmp-iii-b-condensation` | K4 | Add the finite projection mark named by the verdict note. |
| `rmp-iv-ground-space-1d` | K3 | Improve the small X glyph and overly tight placement. |
| `rmp-iv-ground-space-2d` | K1 | Border hue and leg arrowheads are shared theme/string properties. |
| `rmp-iv-intersection-lhs-one` | K2 | Sideways virtual ends preserve the same boundary and contraction. |
| `rmp-iv-intersection-rhs-one` | K2 | Sideways virtual ends preserve the same boundary and contraction. |
| `rmp-iv-intersection-lhs-two` | K2 | Sideways virtual openings preserve the source boundary. |
| `rmp-iv-intersection-rhs-two` | K2 | The crossing is removed; sideways virtual ends are equivalent routing. |
| `rmp-iv-intersection-lhs-three` | K2 | The crossing is removed; sideways virtual ends are equivalent routing. |
| `rmp-iv-intersection-rhs-three` | K2 | Boundary and contraction match; routing is a house choice. |
| `rmp-iv-intersection-lhs-four` | K2 | A horizontal free identity wire is equivalent to the source U-route. |
| `rmp-iv-intersection-rhs-four` | K2 | The five open ends match and the spurious crossing is absent. |
| `rmp-iv-intersection-lhs-five` | K2 | Sideways stubs preserve the restored three-leg boundary. |
| `rmp-iv-intersection-rhs-five` | K2 | Mirroring preserves the equivalent C--X contraction. |
| `rmp-iv-intersection-lhs-six` | X | The ledger records `wrong-contraction`; move it out of `cosmetic-gap` before fixing the invented lattice. |
| `rmp-iv-intersection-rhs-six` | X | The ledger records `wrong-contraction`; move it out of `cosmetic-gap` before fixing the invented lattice. |
| `rmp-app-czx-state` | K2 | Lighter enclosure fill is a public-theme choice. |
| `rmp-workbench-ii-newfig7` | K2 | Crossing-gadget styling is a house-form difference. |
| `rmp-workbench-ii-projector-on-pta` | K4 | Restore the two missing source triangles. |
| `rmp-workbench-ii-peps-rg-workbench` | X | Its ledger pairing is `wrong-source`; repair and verify the source mapping before judging the U-application idiom. |
| `rmp-workbench-ii-positive-mpo-old` | K3 | Recover the intended relative X sizes through the family skin. |
| `rmp-workbench-ii-peps-gauge-old` | K3 | Preserve diagonal leg flow and smooth the marked detour tangents. |
| `rmp-workbench-ii-peps-gauge-without-a` | K3 | Apply the same shared gauge-family geometry correction. |
| `rmp-workbench-ii-mpu-wrap-second` | K2 | Both source-directed pairing rows are now in the correct order. |
| `rmp-workbench-ii-boundary-a-old` | K4 | Restore the finite arrow and R-bar label details, then re-review the region. |
| `rmp-workbench-ii-boundary-b-old` | K1 | Semantic colour coding belongs to the shared theme. |
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
| `rmp-workbench-iii-mpo-representation` | K1 | Virtual-index hue is a shared semantic-theme property. |
| `rmp-workbench-iii-f-tensor` | K2 | An explicit F box faithfully replaces the source's boxless crossing. |
| `rmp-workbench-iii-eq59-now` | K2 | Ring colour and stadium-versus-circle glyphs are house style. |
| `rmp-workbench-iii-ghz-state-workbench` | K1 | This shares the lattice-genre limitation and fix with the GHZ twin. |
| `rmp-workbench-iii-ghz-up` | K3 | Improve glyph proportions and leg geometry as a family. |
| `rmp-workbench-iii-g-injective-pull` | X | Re-audit the source pairing: the current diagonal `U_g` belongs to the SPT panel. |
| `rmp-workbench-iii-intertwining-mpo` | K2 | Line weight alone is house style. |
| `rmp-workbench-iii-mpo-injective-white` | K2 | Direct strings faithfully replace the source's substituted boxes. |
| `rmp-workbench-iii-mpo-on-peps-definition` | K1 | Hatching and hue are shared properties; recheck centring after they land. |
| `rmp-workbench-iii-eq60-now` | K2 | Daggered insertions and genuinely diagonal legs are present. |
| `rmp-workbench-iii-enlarged-mpo-black` | K2 | The closed five-box ring and marked site are complete. |
| `rmp-workbench-iii-eq59` | K2 | Both windings, complete station counts, and joined resolution rails are present. |
| `rmp-workbench-iii-g-injective-mpo` | X | The dropped eight half-edges are the complete declared boundary, not a cosmetic omission. |
| `rmp-workbench-iii-peps-renormalization-one` | K1 | Hatch ticks belong to the shared fused-side/lattice-genre work in #4931. |
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
