# The RMP cosmetic-gap bar

The RMP benchmark seeks mathematical parity in tenkz's own graceful house
style. It does not seek pixel identity with the author source. A difference in
colour, line weight, glyph outline, slant, or equivalent planar routing is
therefore faithful when it preserves the mathematical object, topology,
boundary, labels, orientation, and declared crossing order.

A render settles less than it appears to. A contracted index carries its type
in the model and not in its ink, so physical and virtual contractions stroke
alike and no comparison of pictures catches a mistyped one. The record stream
catches it, and the boundary signature catches it only when the mistyping moves
an open end. Every verdict below was reached at the render, so typing is the
one property a re-review must read out of the record rather than off the page.
`scripts/tenkz_contracted_types.py --all` reads it out: it compiles each target
and reports how many of its contracted indices are physical and how many
virtual, in both picture languages. Run it after any migration wave.

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
| `rmp-ii-peps-projection` | — | Promoted to `faithful` 2026-08-04, reconfirmed on the kernel 2026-08-05 (wave 5, Fable-verified): the plane respell preserves the drawn model; A takes the east station and |phi) becomes a port label, both clearer than the 0.7 placements. |
| `rmp-ii-mps-marginal` | — | Promoted to `faithful` 2026-08-05: the kernel migration replaced the heavy racetrack with minimal straight trace closures, and the state row regained its upward legs and open chain stubs; verified against the author panel at 200/400dpi. |
| `rmp-ii-peps-marginal` | K2 | Migrated to the kernel 2026-08-05 (#5507, Fable-verified): the bilayer basis now spells open transverse ket-bra legs, so the kept sites keep their legs and the traced column closes site by site; the recorded trace-loop overshoot is gone. Residue: the contract bilayer offset overlaps the two sheets where the source separates them vertically. |
| `rmp-ii-mpu-brickwork` | — | Promoted to `faithful` 2026-08-04: twelve legs, alternating layers, and labels match; labelled boxes for dotted gate pairs are the inherent circuit presentation. |
| `rmp-ii-mpu-blocking` | K1 | New 2026-08-05 with the kernel migration: the model records hull-routed side closures for the a/b beads, but the renderer does not yet ink a hull route on an endpoint index wire, so each closure draws along its column axis over the U-Ubar bond. Ink the contracted face-departure arc (LANGUAGE-1.0 s5) in the shared renderer, then re-review; the grid-tier predecessor's side-cup policy inked this correctly. |
| `rmp-ii-mpu-two-shift` | K1 | Resolved 2026-08-04: the case now carries the workbench-twin skin-pairings model with the published palette; the row channels keep house ink where the panel colours the movers. |
| `rmp-ii-mpu-normal-form` | K3 | The solid S-route is heavier and less compact than the graceful default should be. |
| `rmp-ii-spectrum-transfer` | — | Promoted to `faithful` 2026-08-05: the tail idiom, the house enclosure for the cut, and the measured rung/rail weights were settled in wave 1B, and the bracket mark form now draws (#5482), so the `n` annotation is the brace under the marked columns the source asks for rather than a bare south label. |
| `rmp-ii-spectrum-fixed-points` | K1 | Regressed from the 2026-08-04 `faithful` promotion by the kernel migration (wave 1B): the wires=2 self-loop fold draws flush with the glyph boundary, so the closure the grid render inked as a protruding cup arc is invisible (index wires draw straight-only; `via`/`route=arc` recorded but not inked). Restore the fold ink in the shared renderer, then re-review. |
| `rmp-ii-blocking` | — | Promoted to `faithful` 2026-08-04, reconfirmed on the kernel 2026-08-05 (wave 1B, Fable-verified): the stock pill silhouette (#5480) now gives the source's rounded glyph form; the wider house pill remains intentional styling. |
| `rmp-ii-staircase` | K3 | Resolved 2026-08-04: the re-audit confirmed the vertical mirror; the case now ascends as in the source. The rounded-V residue closed 2026-08-07: the four isometries stand on the stock pill silhouette (#5363). Remaining residue: the ket-zero label sits south rather than east of its dot. |
| `rmp-ii-circuit` | — | Already `faithful` (2026-08-02 two-viewer review); the doubling tree carries the complete eight-output identity. |
| `rmp-ii-canonical-right` | — | K1 resolved and promoted to `faithful` 2026-08-05: the mirrored triangle skin (#5485) draws the west apex the source draws for A_R, so the sole recorded residue is gone; alpha, beta, s, and their openness match at 200 and 400 dpi. |
| `rmp-ii-ortho-right` | — | K1 resolved and promoted to `faithful` 2026-08-05: with the mirrored triangle skin (#5485) both glyphs face west in the house definition-compass frame, and the panel is the exact mirror of the faithful `rmp-ii-ortho-left`; cup, contraction, and conjugate already matched. |
| `rmp-ii-ortho-left` | — | Promoted to `faithful` 2026-08-04, reconfirmed on the kernel 2026-08-05 (wave 1C, Fable-countersigned): mirrored into the house definition-compass frame the source glyphs face east, exactly the kernel triangle's east apex; cup topology and labels match. |
| `rmp-ii-boundary-lasso` | K1 | Resolved 2026-08-04: the palette is model-recorded as declared species; the physical policy legs stay house-ink because the policy stub does not read the host species. |
| `rmp-ii-boundary-region` | K1 | Re-reviewed 2026-08-05 with the kernel migration (wave 6, Fable-verified): sheet, species region with R, recovered Rbar label, and the red-then-black rail at partial R all match the published panel. Residue: the kernel enclosure draws contour-only (the source's translucent region fill is unrecorded ink) and physical port stubs stay house-black; fix in the shared renderer, then re-review. |
| `rmp-ii-boundary-state` | — | Promoted to `faithful` 2026-08-05 (wave 1C): the range-addressed enclosure mark draws the source's sigma_partial R box directly, retiring the brace-for-box note and the migration's interim floating label; solid-grey contour and glyph labels are house style. |
| `rmp-ii-zcl-mpdo` | K3 | K1 resolved 2026-08-09: the shared trace stroke now carries the calibrated crossing break, so the return reads over the virtual bond beside its site instead of contracting with it. Residue unchanged: make the closure more compact than the current racetrack. |
| `rmp-ii-channels-ts` | — | Promoted to `faithful` 2026-08-04, reconfirmed on the kernel 2026-08-05 (wave 1C, Fable-countersigned): legs and channel directions match; the straight double arrow is equivalent house routing. |
| `rmp-ii-mpdo-ol` | K1 | K4 reconciled 2026-08-05 (wave 1C): the `extra-element` defect was stale -- the author block draws one panel and the contrast panel left the case in a98b1e282. Residue: the single-row west/east trace wrap is recorded but draws flush with the chain, so the end identification is not legible; ink the wrap route in the shared renderer, then re-review (the left-right respelling of the source's top-down word is house layout, kernel having no rotation key). |
| `rmp-ii-peps-rg` | X | The current hooks cross where the source keeps them separated; restore the source crossing topology. |
| `rmp-ii-peps-rg` | — | X resolved and promoted to `faithful` 2026-08-05 (wave 5, Fable-verified): the kernel respell draws the final bead's virtual ring as an uncrossed closed return through invisible junctions, the house form for the source's identified upward hooks; panel (c) regains its east leg and the trace bead drops the invented physical leg. |
| `rmp-iii-a-f-symbol` | — | Promoted to `faithful` 2026-08-04: crossing order, directions, sectors, and all six labels verified against the author figure. |
| `rmp-iii-a-pulling-through` | — | Promoted to `faithful` 2026-08-05 (wave 7): the kernel respell carries the full ring, lambda insertion, action pair, joining string, free string ends, and all six direction marks; the diamond ring, straight action chord, and stadium lambda are house forms, retiring the curve-weight residue. |
| `rmp-iii-a-commuting-hamiltonian` | — | Kernel respell 2026-08-05 keeps the promoted model and drops the 0.7 render's single spurious gate output leg: the author draws the gate closed, so neither panel legs the pill; the labelled white pill remains house typography. |
| `rmp-iii-a-proof-one` | — | Reconfirmed `faithful` on the kernel 2026-08-05 (wave 3, Fable-verified): V_alpha is now the source's tall spanning rectangle instead of the pill, all-black; fused-output row slot for the source's face-centered exit is grid quantization. |
| `rmp-iii-a-proof-two` | — | Reconfirmed `faithful` on the kernel 2026-08-05 (wave 3, Fable-verified): the red house rails are dropped for the source's all-black ink; fused-output row slot for the source's face-centered exit is grid quantization. |
| `rmp-iii-a-proof-three` | — | Reconfirmed `faithful` on the kernel 2026-08-05 (wave 3, Fable-verified): the full stack matches level for level in the source's all-black ink, with equal audited signatures around the lambda coefficient. |
| `rmp-iii-a-ghz-state` | K1 | Resolved: the case now records the full six-by-eight staggered model on the kernel (all junctions, bonds, and legs verified present 2026-07-30); only the shared kernel spacing and stroke profile differ. |
| `rmp-iii-a-ghz-tensor` | — | Kernel redraw 2026-08-05 retires the labelled box with orthogonal legs in favour of the author's own glyphless junction with the 45-degree physical tick; four open indices and the equation are unchanged. |
| `rmp-iii-a-hadamard` | — | Resolved 2026-08-05: the paired panel (lines 359-360) IS the author's Hadamard glyph — paper line 1449 equates that extraction with the matrix, and the cluster state draws H as the filled dot on every internal bond; the case is redrawn as the dot-on-bond and promoted to `faithful`. |
| `rmp-iii-a-spt-mpo` | — | Promoted to `faithful` 2026-08-04: string pull, both crossings, action boxes, and the U_g insertion verified under the boundary audit. |
| `rmp-iii-a-spt-intertwiner` | — | X resolved 2026-08-05 (wave 7): the source factor order gh X (g/h)(g/h) = gh gh X (g/h) is restored on the kernel and the mirrored spelling is retired; promoted to `faithful` with the gh row quantization noted as house placement. |
| `rmp-iii-a-g-injective-projector` | X | Its ledger pairing is `wrong-source`; repair the projector source mapping before any verdict promotion. |
| `rmp-iii-a-mpo-action` | — | Resolved 2026-08-05: the kernel redraw restores the source's diagonal virtual pair on both panels; promoted to `faithful`. |
| `rmp-iii-a-mpo-injective` | K2 | Ring topology is preserved; unrecorded hatching and hue require house-style re-review, not a renderer promise. |
| `rmp-iii-a-torus-one` | — | Promoted to `faithful` 2026-08-04; wave-7 kernel migration reconfirmed 2026-08-05: the contract's own traced-lattice spelling carries both homotopy classes as wound strings crossing once at the outlined i, the canonical projection of the source's embedded donut. |
| `rmp-iii-a-torus-two` | — | Kernel respell 2026-08-05: the periodic word is one closed operator string returning below the row; square return corners and the outlined marked box are house forms for the source's rounded loop and filled blue tensor. |
| `rmp-iii-a-torus-three` | K2 | Outline versus solid fill on the enlarged crossing is house style. |
| `rmp-iii-b-dyon` | K2 | The marked region and open string are present after route migration. |
| `rmp-iii-b-self-braiding` | K2 | Tensor counts, winding classes, tail crossing, and boundary are complete. |
| `rmp-iii-b-braid-one` | K2 | Re-modelled on the plane frame 2026-08-06 (#5581): the author paints all four lattice lines inside one plane and hangs an out-of-plane stub on each site, so the two verticals the flat frame typed as contracted physical indices are now virtual bonds and the four site legs open into air. Stations and noncrossing winding strings still match, and b's bead moved from j's site leg to the lattice line running north out of j. Residue: the source runs its lattice legs past the stub reach and paints the anyons larger than the beads. |
| `rmp-iii-b-braid-two` | K2 | The nested noncrossing strands match the flattened source. |
| `rmp-iii-b-braid-three` | K2 | Re-modelled on the plane frame 2026-08-06 (#5581): the slant now matches the source, the two verticals the flat frame typed as contracted physical indices are virtual bonds, and the four site legs open into air. All six bead stations survive, with a's fourth bead moved from i's site leg to the lattice line running north out of i. Residue: the resolver contour is an upright box east of the source's sheared parallelogram, which the source uses to hide the a-b meeting. |
| `rmp-iii-b-condensation` | K4 | Add the finite projection mark named by the verdict note. |
| `rmp-iv-ground-space-1d` | K1 | Kernel migration 2026-08-05 (wave 4, Fable-verified) resolved the K3: X is the stock box at the standard size on the junction-spelled trace return. Residue: the recorded corner arcs of the return ink as straight diagonals (shared renderer, the boundary-algebra family limitation); re-review when arc inking lands. |
| `rmp-iv-ground-space-2d` | K3 | Reclassified from X 2026-08-05 (wave 6, Fable-verified): the X row's premise is false — both GS2D.pdf and the paper's fig4 twin draw plain undirected legs at 900dpi, so `physical=up` records the source faithfully and #5360 is not implicated. Actual residue: physical legs pierce both region windows at the hull's full page-up reach, crowding the sheet where the source draws short ticks; prefer a family-level leg-reach metric fix, then re-review. |
| `rmp-app-toric-dual` | — | Resolved and promoted to `faithful` 2026-08-05: the wire grammar gained a declared stroke (#5509, Extension-gate #5543), and the interior diagonals take the dashed rail. The earlier note called the source's diagonals dotted; at 900dpi the published figure dashes them. The contour-only enclosure is house ink for a context drawing, as on the primal twin. |
| `rmp-iv-intersection-lhs-one` | — | Promoted to `faithful` 2026-08-04, reconfirmed on the kernel 2026-08-05 (wave 4, Fable-verified): both virtual ends close through the pill's side cups with the lobe leg at the third station; the flat-top lobe stub is the house form for the raised lobe. |
| `rmp-iv-intersection-rhs-one` | — | Promoted to `faithful` 2026-08-04, reconfirmed on the kernel 2026-08-05 (wave 4, Fable-verified): the uncovered stretch and B--C close through the pill's side cups with the lobe leg at the first station. |
| `rmp-iv-intersection-lhs-two` | — | Promoted to `faithful` 2026-08-04; the wave-4 kernel respell retires the sideways-openings residue: both cut virtual ends now turn upward as the source draws them. |
| `rmp-iv-intersection-rhs-two` | — | Promoted to `faithful` 2026-08-04; the wave-4 kernel respell retires the sideways-ends residue: both cut virtual ends now turn upward as the source draws them. |
| `rmp-iv-intersection-lhs-three` | — | Promoted to `faithful` 2026-08-04; the wave-4 kernel respell turns both cut interior ends upward before the lobe leg, matching the source's order. |
| `rmp-iv-intersection-rhs-three` | — | Promoted to `faithful` 2026-08-04; the wave-4 kernel respell turns both cut interior ends upward between B and C, retiring the facing-break spelling. |
| `rmp-iv-intersection-lhs-four` | — | Promoted to `faithful` 2026-08-04; the wave-4 kernel respell draws the free identity wire as the source's open U, retiring the horizontal-wire equivalence. |
| `rmp-iv-intersection-rhs-four` | — | Promoted to `faithful` 2026-08-04, reconfirmed on the kernel 2026-08-05 (wave 4, Fable-verified): R is now the signed wide box atom rather than the 0.7 pill; S's outputs sit at its top-face stations (house form for the source's corner rises). |
| `rmp-iv-intersection-lhs-five` | — | Promoted to `faithful` 2026-08-04, reconfirmed on the kernel 2026-08-05 (wave 4, Fable-verified): the three-index boundary stands at the source's stations; the near-lobe stub points upward for the source's horizontal lobe stub (equivalent open-leg presentation). |
| `rmp-iv-intersection-rhs-five` | — | Re-audited 2026-08-05 (wave 4, Fable-verified): the 0.7 mirror was topologically equivalent, and the kernel respell restores the source embedding -- X's leg at the far west, C closing east through the cup, C's cut end sideways west; promoted to `faithful`. |
| `rmp-iv-intersection-lhs-six` | K2 | Resolved to `cosmetic-gap` 2026-08-05: kernel nested regions replace the invented lattice; the A--B patch window nests inside the L window and the cut bonds end on it. Residue: face stubs for the source's through-lines and the corner label station. Promote to `faithful` on a second-viewer countersign. |
| `rmp-iv-intersection-rhs-six` | K2 | Resolved to `cosmetic-gap` 2026-08-05: kernel nested regions replace the invented lattice; the B--C patch window nests inside the R window and the cut bonds end on it. Residue: face stubs for the source's through-lines and the corner label station. Promote to `faithful` on a second-viewer countersign. |
| `rmp-app-czx-state` | — | Promoted to `faithful` 2026-08-04: source grouping and lattice wiring verified; lighter enclosure fill is a public-theme choice. |
| `rmp-workbench-ii-newfig7` | K2 | Crossing-gadget styling is a house-form difference. |
| `rmp-workbench-ii-projector-on-pta` | — | Repaired and promoted to `faithful` 2026-08-05 (wave 3, Fable-verified): both sandwich sums now draw the archival widths (four plus identity against five plus four columns), restoring the sum's site multiplicity; cup arcs, black identity, and straight stubs are house ink for the source's brackets, blue strand, and hooks. |
| `rmp-workbench-ii-peps-rg-workbench` | — | X resolved and promoted to `faithful` 2026-08-05 (wave 5, Fable-verified): the pairing is repaired to FigPEPSRG panel (a) (author lines 744-753) with the unitary the figure caption applies to the four physical indices; the math-mode U application is the accepted coproduct idiom. |
| `rmp-workbench-ii-positive-mpo-old` | K2 | The ledger already records equal X sizes; re-review the hash-pinned render as faithful. |
| `rmp-workbench-ii-peps-gauge-old` | K3 | Preserve diagonal leg flow and smooth the marked detour tangents. |
| `rmp-workbench-ii-peps-gauge-without-a` | K3 | Apply the same shared gauge-family geometry correction. |
| `rmp-workbench-ii-mpu-wrap-second` | K2 | Both source-directed pairing rows are now in the correct order. |
| `rmp-workbench-ii-boundary-a-old` | K1 | Re-reviewed 2026-08-05 with the kernel migration (wave 6, Fable-verified): the K4 row's 'arrow and R-bar' items are misreadings of the published twin — the archival (a)old PDF has neither, and the case now carries its distinguishing R/R^c names and all-red rail. Residue as on `rmp-ii-boundary-region`: contour-only enclosure for the source's filled ellipse and house-black port stubs; fix in the shared renderer, then re-review. |
| `rmp-workbench-ii-boundary-b-old` | K1 | Resolved 2026-08-05: the source palette (red A row, gray B row, explicit in the author code at lines 618-649) is model-recorded as declared charge/flux species, matching `rmp-ii-boundary-lasso`; as there, the physical policy legs stay house-ink because the policy stub does not read the host species. |
| `rmp-workbench-ii-peps-fine-graining` | — | Promoted to `faithful` 2026-08-05 with the kernel migration (wave 8, Fable-verified): the one-site plane sheet keeps all five source legs and the 2x2 patch matches figrenorm2D panel (b) leg for leg; the flat tilted plane frame is the K2 equivalent of the source projection, and the fine-graining arrow stays plain math outside the audited kernel scope. |
| `rmp-workbench-ii-historical-composite` | — | Promoted to `faithful` 2026-08-05 with the kernel migration (wave 8, Fable-verified): the stacked (a)/(b) pair matches the archival sheet — open chain ends, upward physical legs, and the 2x2 boundary signature all verified; the flat tilted grid remains the K2 equivalent of the source 3D cube, and the archival arrows and panel letters stay plain math outside the audited kernel scope. |
| `rmp-workbench-iii-eq50` | — | Kernel migration 2026-08-05: all four legs verified against Eq50.pdf. The wide-glyph note is retired 2026-08-09: a box now takes the size-class reference on both axes, so the site is the square the source draws. |
| `rmp-workbench-iii-eq51` | K1 | The kernel side trace renders as identified extended ends; ink the recorded closure's long return at the renderer, then re-review the traced-chain family. |
| `rmp-workbench-iii-eq52` | K1 | Same closure-ink gap as eq51: the traced sides draw as identified ends, not the source's trace rectangle. |
| `rmp-workbench-iii-diagram-one` | — | Promoted to `faithful` 2026-08-05 (wave 3, Fable-verified): the kernel respell draws the closed racetrack through explicit junctions with the archival paired physical stubs; the stadium for the circle (#4931) and sharp corners are house forms. |
| `rmp-workbench-iii-diagram-two` | K1 | Y over A and both open indices match; the north/south trace draws as identified ends, not the source's return loop (eq51 family). |
| `rmp-workbench-iii-diagram-three` | — | Resolved 2026-08-05 (wave 7): the body now equals the pulling-through respell of the same author lines, restoring the action pair the old body omitted; per-edge direction ink draws from dir= on each leg, retiring the K1. Promoted to `faithful`. |
| `rmp-workbench-iii-historical-composite` | K3 | Re-reviewed 2026-08-05 with the kernel migration (wave 6, Fable-verified): both panels keep the closed operator loop, lambda corner, directed pendants, and sweeping arcs. Residue: the closed-string spline waves where the source rules a rounded rectangle (K3); the inward station ticks are undrawable because a port stub crossing a string is a hard error with no declarable order, and the dir mark on an east-bearing open stub does not ink (both K1, shared renderer). |
| `rmp-workbench-iii-diagram-four` | — | Promoted to `faithful` 2026-08-05 (wave 7): kernel ring with every outward arm and inward pierce and the junction-spelled periodic local map; the stadium lambda and square return corners remain house glyph forms. |
| `rmp-workbench-iii-eq50-reduced` | — | Promoted to `faithful` 2026-08-05: the invented L/a/R/b labels are removed; unlabelled stacked pair, tall reduction boxes, and one reduced index per side match the author lines. |
| `rmp-workbench-iii-dual-reduced` | — | Repaired and promoted to `faithful` 2026-08-05 (wave 3, Fable-verified): the kernel respell restores the source factor order (box west of the a,b word; c west of the box) with source-red virtual legs and equal audited signatures. |
| `rmp-workbench-iii-mpo-representation` | — | Promoted to `faithful` 2026-08-05: the per-bond labels are removed, the rail carries the declared source-red species, and the single red a sits at the open east index. |
| `rmp-workbench-iii-f-tensor` | — | Promoted to `faithful` 2026-08-05 (wave 7): the kernel redraw restores the source's boxless directed crossing with c declared over a, four one-strand quarter-turn hooks, and all six sector labels, retiring the F-box substitution. |
| `rmp-workbench-iii-eq59-now` | — | Promoted to `faithful` 2026-08-05 (wave 7): the projector ring carries the declared source red and the marked corner dot; the archival pairing is corrected to Eq59.pdf (Eq59now.pdf holds the SPT g-pull sketch); stadium L_g glyphs stay house style. |
| `rmp-workbench-iii-ghz-state-workbench` | K1 | The manifest records `staggered-sites`; route the fix through the cell basis, not the published GHZ lattice mechanism. |
| `rmp-workbench-iii-ghz-up` | — | Promoted to `faithful` 2026-08-05 (wave 2B): the kernel box atom carries four typed ports with clean stub geometry, matching the faithful G_down sibling's house form; the K3 leg-geometry residue is gone. |
| `rmp-workbench-iii-g-injective-pull` | X | Re-audit the source pairing: the current diagonal `U_g` belongs to the SPT panel. |
| `rmp-workbench-iii-intertwining-mpo` | — | Promoted to `faithful` 2026-08-05 (wave 2B): kernel respell verified against the author panel; the archival pairing is corrected to `sptintertwin gh.pdf` (interMPO.pdf is the a/b/c fusion intertwiner). |
| `rmp-workbench-iii-mpo-injective-white` | K2 | Direct strings faithfully replace the source's substituted boxes. |
| `rmp-workbench-iii-mpo-on-peps-definition` | K3 | Treat unrecorded hatching and hue as house style; fix only the family-level centring residue. |
| `rmp-workbench-iii-eq60-now` | — | Promoted to `faithful` 2026-08-05 (wave 2B): kernel star with all five insertions on their legs; the archival pairing is corrected to `Eq60.pdf` (the file named Eq60now.pdf holds the eq59-family lattice identity). |
| `rmp-workbench-iii-enlarged-mpo-black` | — | Promoted to `faithful` 2026-08-05 (wave 2B): kernel word with the marked fourth box unlabeled as in the source; the single-row trace return is drawn through corner junctions until the closure policy inks it (K1, family-level). |
| `rmp-workbench-iii-eq59` | K2 | Both windings, complete station counts, and joined resolution rails are present. |
| `rmp-workbench-iii-g-injective-mpo` | K3 | Resolved 2026-08-04: the eight sector labels sit on genuine open boundary half-edges, each with its own open wire; the four plaquette bonds stay internal and unlabelled. Residue: house box for the source circle glyph. |
| `rmp-workbench-iii-peps-renormalization-one` | K3 | X resolved 2026-08-05 (wave 7): the four edge-centred sites stand as glyphless junctions with their 50-degree physical legs. Residue: declared crossings gap the under bonds where the source butts plain lattice ink, and the external half-edges run a full pitch for the source's quarter. |
| `rmp-workbench-iii-peps-renormalization-two` | K4 | Re-graded 2026-08-05 (wave 7): topology and angle-port legs are complete; the source's four hatch ticks per box are drawn as one 60-degree physical leg because bundle multiplicity owes no ink under the kernel contract (LANGUAGE-1.0 s5, #4931). |

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
