# Shrink critique of the remaining-demand amendments

The verdict that governs the companion note: where a proposal is struck here,
it stays struck; where a unification is found here, the note presents the
unified element and not the two originals.

## Critique: where the five designs named the same object

Read against the contract, the corridor amendment, the shrink ledger, the 130-row verdict ledger, and the geometry and kernel sources. Everything below is checked against those, not against the designs' own claims.

---

## 1. The coincidences

### C1. The offset hull — six designs, one curve

This is the finding. Six independent proposals describe the same construction: *take a set of records, take their measured silhouettes in the frame's own axes, take the support hull of that set, push it outward by one clearance, round the turns.*

| who | what they called it | which records it clears |
|---|---|---|
| corridor amendment | the corridor lane | the whole picture |
| Cluster 2 | the lane, `route={<side> of <target>}` | a named set, one side of it |
| Cluster 4 | the measured contour, `form=enclosure` / `bracket` | a mark's members |
| Cluster 5 prop 3 | measured clearance, "as deep as the ink it must clear" | the records between two endpoints |
| Cluster 1 prop 3 | the measured enclosure, "the rounded hull plus daylight" | a mark's members |
| Cluster 1 prop 1 | the ring the four tensors stand on | four tensors |

They differ in **one parameter**: which records the curve must clear. Nothing else. Not the geometry, not the clearance, not the rounding, not the ordering rule.

The authors' own source settles it. Diagram 3 (Section III, lines 176–179): four tensors at `(\d:0.7)` and a red `rounded corners` rectangle at half-width `0.7`. That rectangle **is** the rounded hull of the four tensors plus clearance. The authors drew the corridor lane and the enclosure contour with one `\draw`, because they are one curve. Then they put atoms on it. So the same curve is, in three figures: stroked as a mark, travelled as a wire, and stood on as a place.

The service already exists and is already general: `\__tenkz_geom_support:nnnnnn` (silhouette of a skin at angle θ), `\__tenkz_geom_support_max:nnN` (fold over a record set with per-record θ), `\__tenkz_geom_corridor_along/trans/point/include/escape`. The corridor functions take *an obstacle set*, not the picture. Nothing about them is picture-scoped. The parameterisation the six designs are all groping for is already in the signature.

**Unification.** One kernel primitive: *the offset hull of a record set*. It is consumed by MARK (stroke it), by WIRE (travel on it), by ATOM (be placed and oriented by it), by the leg-reach rule (measure against it), and by label placement (stand outside it). Five consumers, and it costs no key, because every one of those five already has a key to carry the selector.

Direct consequence: **`route=around` must not be a route value.** It is `route={<selector>}` with the selector standing for the whole picture. Cluster 2 asks this in its open questions; the answer is yes, and it is the corridor amendment's own doctrine turned on itself — four spellings for one idea is exactly what that amendment exists to stop, and `around` plus `{n of X}` plus `form=enclosure` plus the cap depth is four again.

### C2. The record set — five designs, one value type

Cluster 2's `<target>`, Cluster 4's `..` range and braced list, Cluster 1's basis slot `(r,c,k)`, Cluster 3's `panel <k>`, and the existing `cell-set` type on `trace=` and `open=` are all one thing: an expression naming a set of records. The contract already has three spellings for a mark target alone ("a cell set, a wire place, or an address set", §2.1/§6) and one of them is parsed by hand out of a regular expression against `(r,c)-(r,c)` in the kernel.

**Unification.** One selector type, one production (`..`), consumed by mark targets, wire route targets, and the cell-set keys. This retires `cell-set` as a separate value type (a standing lonely-type flag), retires the mark's private target parser, and retires the mark-target grammar's three kinds. Cluster 4 gets this right; Cluster 2 independently needed the same object and reused the mark's; they should be one row, not two.

### C3. Local axes — three halves of one rule

- Cluster 1: an address on a carrier takes the carrier's axes; the atom reads its faces in them.
- Shelf probe 2: a face is an angle **in the record's own frame**, not a compass word on the page.
- Shelf probe 1: ink the frame measures lies in the frame; ink the frame only places stays upright.

These are not three proposals. They are the statement, the alphabet, and the ink half of one rule. Probe 2's angles are useless without Cluster 1's answer to *whose* axes; Cluster 1's carrier axes are unstatable while a face is one of eight fixed words; and probe 1's rule is what makes either visible.

Composed, they are strictly stronger than the sum: probe 2 deletes the eight-word face alphabet and the `n`-means-two-things overload; Cluster 1 supplies the axes; probe 1 gives the parallelogram skin and the parallelogram contour for free. Three blocked targets (`rmp-iii-a-ghz-state`, `rmp-ii-inverse-renormalization`, `rmp-workbench-iii-ghz-state-workbench`) and four cosmetic ones (`rmp-iii-a-mpo-action`, `rmp-iii-a-ghz-tensor`, `rmp-workbench-ii-peps-gauge-old`, `rmp-workbench-iii-peps-renormalization-one`) fall to the composition and to no one member of it.

### C4. Concentric ordering — four statements of one sentence

Corridor lanes step outward in declaration order. Cluster 2's two lanes on one side step outward in declaration order. Cluster 4's nested contours step inward by containment, ties by declaration order. Cluster 5's nested contours step inward "exactly as corridor lanes step outward". One sentence, written four times, in four documents. It is doctrine attached to C1, not an element, and `inset=` dies once — not twice, as the batch currently counts it.

### C5. Reach inversion — and it is already implemented

Cluster 2 proposes that a leg crossed by a lane is measured from the lane, not from a constant. Cluster 4 proposes that a contour grows on the label's side to admit the label. Cluster 5 proposes that a label station search moves ink to make room. The kernel already does two of these, in its own words at `tenkz-kernel.code.tex:2533`: *"The leg's reach: physleg, or past its highest declared crossing"* — and thirty lines later it also lengthens a leg past an enclosure it pierces.

**Unification.** One rule: *a reach is the maximum over everything declared to meet it.* Already written, currently keyed off the cell-range regular expression that C1 and C2 both want deleted. Deleting that branch without generalising this rule breaks a working mechanism.

### C6. A site that carries sub-sites — four spellings

Cluster 1's cell basis, the `cluster={RxC}` sugar, the `planes` sugar, and the `sheets=`/`sheet sep=`/`pairing=` family are one mechanism. The registry's own escape row already calls itself a "projected sheet basis". This is a genuine and large unification, and it is crystallographically exact: a bilayer is a Bravais lattice with a basis of two, and the pairing legs are intra-cell bonds. It also **destroys probe 1's binding constraint**: the two-sheet sugar is only a nesting trap while it is built from nested frames; as a basis it is one frame and cannot collapse.

### C7. Extent from declared counts, not from content

Cluster 5's reference glyph (extent = class reference × slot counts) is the same principle as `wide=`/`wires=`, and it directly contradicts §7's first equation rule (widest measured label box wins). The authors settle it: identical `0.55 × 1.2` rectangles for `X` and `X^{-1}`, and `circle (0.22)/(0.23)/(0.24)` hand-fudged so three same-class glyphs read as one size. Cluster 5 is right and §7's clause is wrong, in every scope and not only in equations.

### C8. Two proposals are literally the same proposal

Cluster 4 prop 5 and Cluster 5 prop 2 are one design: a label is placed against measured ink, `auto` acquires a definition, `nudge=` dies. Same three headline consumers (`rmp-ii-triangle-network`, `rmp-ii-mpo-sheet`, `rmp-ii-mpu-splitting`). Cluster 4 prop 4 and Cluster 5 prop 3's third clause are one design. The batch's arithmetic counts `nudge=` three times and `inset=` twice.

---

## 2. False friends

**F1. Basis membership is not selection.** Cluster 1 creates records at declared sub-cell offsets; Cluster 4 selects records. They look alike because both mention `(r,c,k)`-shaped things. They must *compose* — the basis slot has to be inside the address grammar the selector ranges over — but they are not one element and neither subsumes the other.

**F2. `bind=` does not pay for `check=`.** Cluster 3 buys the binder by retiring the audit key. But the binder verifies nothing: the contract holds that positional label arguments are opaque mathematics, Cluster 3 explicitly declines to look for occurrences of the bound name inside labels, and it concedes a vacuous binder is drawable. A key with no computable effect is a comment. Meanwhile `\tfrac{1}{|G|}` is admitted as an ordinary term with empty signature — and so is `\sum_{g\in G}`. The summation prefix draws with zero elements.

**F3. `slide=` and the joiner classes occupy the same room.** Cluster 2 adds a word inside `check=`; Cluster 3 deletes `check=`. Both cannot land. Neither noticed the other.

**F4. `rotate=` versus `matrix={..}` — both designs are backwards.** Cluster 1 kills `rotate=` and keeps `matrix=` as the escape; probe 1 kills `matrix=` (composition makes it reachable) and keeps `rotate=`. The evidence kills both. The contract's §4 names four rotation consumers; reading the ledger, `rmp-ii-pulling-through` is a carrier orientation, `rmp-iii-a-spt-mpo` and `rmp-ii-peps-rg` are projections, and `rmp-ii-circuit`'s note reads *"rotated 90 degrees and shallower than the source tree"* — the rotation there is our **defect**, not the source's demand. Zero of four. And probe 1's "composition makes any frame sayable" is only true while there is something to compose; if `rotate=` also dies, the composable stock is `flat`, `plane`, `circle`, and the argument for deleting `matrix=` becomes an argument for deleting the only escape. Resolution: kill `rotate=`, `matrix=`, `vertical`, and the plane subkeys; the frame alphabet closes to three words with no parameters, which also collapses `frame-spec` from a value type to a small enum.

**F5. `out`/`in` are angles, not words.** Cluster 5 adds two face words for the frame-relative outward direction. Under C3 that direction is the row's own axes' normal — an angle in the record's frame, which probe 2's grammar already carries. The two words are redundant the moment the composition lands, and the contract's `up=`/`down=` gloss ("page-relative: the outward physical face of the row, in whichever direction the frame sends it") is itself an overload that should have raised M6.

**F6. The pitch invariant is not "every frame".** Cluster 5 states that adjacent cells are one pitch apart in every frame. That is false for the projected plane by construction — the receding row is foreshortened, which is what the slant and rise ratios *are*. The clause is right where it has consumers (the circle frame, whose radius is currently unfixed) and wrong where it is generalised. Restrict it. Incidentally the formula checks against the source: for four stations it gives radius `pitch/√2 ≈ 0.707`, and the authors wrote `(\d:0.7)`.

---

## 3. Strike list

1. **Cluster 4 prop 5 (mark label placement)** — duplicate of Cluster 5 prop 2. Keep Cluster 5's, which defines the ring order and the deterministic search; `nudge=` is retired once.
2. **Cluster 4 prop 4 (nesting derived)** — as a standalone it has one real consumer. Of its four, `rmp-iv-intersection-lhs-six` and `-rhs-six` are routed to a wide box atom by the contract's own sign-off decision 2 (Cluster 4 concedes this), and `rmp-app-toric-dual` is **faithful** ("context-only; clean"). The rule survives as one sentence of C4 doctrine; the proposal does not.
3. **Cluster 3's `bind=`** — F2. One genuine blocked consumer (`rmp-workbench-iii-eq59-now`), since `rmp-iii-a-g-injective-projector` is recorded wrong-source and `rmp-ii-tangent-projector` is faithful.
4. **Cluster 3's `panel <k>` production** — a picture is a record class. Generated pictures take canonical names exactly as generated wires already do (`wrap-1`, `cup-1-2`). The existing named-record production serves it.
5. **Cluster 2's `slide=`** — F3, and it draws nothing. Its mathematical content (flip the side, the crossing set and its beads follow) is a consequence of the lane, not an element.
6. **Cluster 5 prop 4's `out`/`in` alphabet words** — F5. The pitch invariant survives, restricted to the circle frame.
7. **Cluster 1 prop 1 "Local axes" as its own amendment** — nothing survives as its own element: the face half is probe 2's, the carrier half is C1, the ink half is probe 1's. Its retirement of frame `rotate=` survives and is extended.
8. **`route=around` as a distinct value** — folds into the selector form (C1).
9. **Cluster 1's credit for `sheets=`, `sheet sep=`, `pairing=`, `sheet vector=`** — these are not in the 1.0 kernel tables; they are 0.7 rows already sentenced in the shrink ledger ("folds into declared skin pairings", "folds into `frame=` subkeys"). The basis is still the right mechanism; the savings are already booked and must not be booked twice.
10. **Cluster 4's `regionmargin`/`regionnest` credit** — those ratios live in the legacy lattice tier, not the metric registry. Real credit is `enclosepad`, `enclosetight`, `regioncorner`.
11. **Probe 2's consumer table for retiring `weight=`** — four of its six named consumers are faithful (`rmp-ii-ortho-right`, `rmp-ii-canonical-left`, `rmp-ii-canonical-right`, `rmp-ii-tangent-projector`, two of them annotated "better than the authors"). The retirement stands — a deletion needs no consumers — but the argument must be restated honestly as *zero authored consumers in the corpus*, not as six demanding targets. The same audit hits Cluster 4's `..` (one faithful of five) and Cluster 3's term grammar (one faithful, two wrong-source of ten).

One ledger correction the batch implies and nobody wrote down: probe 2 retires the capability name `multi-strand-braid`, but the note on `rmp-iii-a-spt-mpo` says *"45-degree double strand as axis-aligned stubs"* in the maintainer's own words. The name cannot be retired without correcting that note in the same change.

---

## 4. Net element count for what survives

Against the 1.0 contract's own tables, counting each retirement once, and excluding what the corridor amendment and the shrink ledger have already booked.

| ledger | before | after | net |
|---|---|---|---|
| kernel key rows | 52 | 43 | **−9** |
| commands | 7 | 6 | **−1** |
| record classes, environments | 4, 2 | 4, 2 | 0 |
| alphabet rows | 6 | 4 | **−2** |
| alphabet values | — | — | **−21** (−24 out: 8 faces, 5 tints, 3 weights, 4 mark forms, 3 frame values, 1 route; +3 joiner classes) |
| address productions | 9 | 8 | **−1** |
| sugar rows | 27 | 25 | **−2** |
| value types | 24 | ~20 | **−4** (check-spec, frame-spec, cell-set, number — the last pending census) |
| parser paths | — | — | strongly negative (~−7: two enclosure branches, two frame branches, the sheet mechanism, the rectilinear tracer, the compass table; +1 joiner row) |
| overload count | — | — | **−3** (`n` as face and page word; `<compass> outside` against `open <dir>`; the sheets union type) |

Keys retired: `slot=`, `inset=`, `nudge=` (atom), `nudge=` (mark), `via=`, `bend=`, `weight=`, `up=`, `down=`, `check=`. Keys added: one — `species=` at mark scope, which the scope-census counts as a row.

**Where it is not negative, plainly stated: the metric registry.** Cluster 5 says "keys added: none" and then names five ratios that do not exist (`glyph`, `slotpitch`, `padding`, `labelgap`, `labelstep`); Cluster 1's basis wants a member-clearance ratio. Against `enclosepad`, `enclosetight`, `regioncorner` and, optimistically, the three closure-reach rows, that is a wash at best. A ratio is an element; the batch is hiding growth in the one ledger it does not count.

To make it negative: fold `glyph`, `slotpitch` and `padding` into the size-class table, which already exists as a value type and already holds per-class quantities, so the reference extent is a column of a table rather than three new rows; use the existing `labelclear` where Cluster 5 writes `labelgap`; and derive `labelstep` from `daylight` rather than minting it. That is three ratios instead of six, and the registry ends smaller.

Two other honesty adjustments the batch should absorb before anything is signed. The gross claim across the five designs is roughly twenty kernel rows; net of rows already sentenced in the shrink ledger (`sheets`, `sheet sep`, `pairing`, `sheet vector`, the plane subkeys, `trace style`, `\tncut`, the annotation folds) and net of the double-counted `nudge=` and `inset=`, the genuinely new saving is the nine above. And the tombstone migrating `fused` to `weight=double` becomes a dangling pointer the moment `weight=` dies; it must be rewritten in the same change, since a tombstone that names a deleted spelling is worse than no tombstone.
