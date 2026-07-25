# Amendment to LANGUAGE-1.0: the remaining demand

Seven further amendments to the signed kernel contract, companion to the
corridor and crossing-order note. Each is argued from the benchmark's own
demand, each removes more of the language than it adds, and none needs a
dependency the package does not already load. Together they end with one
new key, one new address production, one new value family and three new
alphabet words, against ten keys, one command, two whole alphabets and
twenty-four alphabet words retired.

## The demand

The verdict ledger records, for each of the thirty-eight blocked targets,
what it needs before it can be drawn at all. Over the hundred and thirty:

| need | blocked targets |
|---|---|
| enclosure marks | 10 |
| crossing order | 9 |
| strings | 7 |
| rotated action | 5 |
| torus cycles | 4 |
| pulling through | 3 |
| braid resolution | 3 |
| ring closure, multi-strand braids, group averages, equation composition | 2 each |
| string slide, staggered sites, open strings, marked regions, cluster groups | 1 each |

The corridor and crossing order answer six of those sixteen names. Twenty
blocked targets carry only names from that note; fourteen carry only names
from this one; four carry one from each. The remaining hundred and
thirty-eight statuses are forty-one cosmetic gaps, twenty-seven structural
gaps, twenty faithful panels, three unreviewed, one unfaithful. The
dominant recorded defect over the whole corpus is a missing element,
twenty-nine times, ahead of the wrong contraction's twenty-three; the first
note was aimed at the second number, and this one is aimed at the first.

Four of the sixteen names are misnomers, and reading the authors' own
sources rather than the tags is what makes the amendments small.

**Multi-strand braids are not multi-strand.** The three targets carrying the
name draw several separate strings, each with its own bead, braiding across a
projected lattice. Occurrences of a doubled line in the four author sources,
2385 lines: zero. The name should be retired from the demand table and those
targets rewritten to crossing order, which serves them. One note contradicts
the retirement — *45-degree double strand as axis-aligned stubs* — and
describes a projection defect; it must be corrected in the same change.

**Cluster groups and staggered sites are one demand.** The CZX target carries
the first name and its note reads *totally wrong; composite sites + doubled
bonds*; the cluster-state workbench carries the second and its note reads
*staggering and arrow legs flattened*. Both want a cell that carries more than
one site. The tags must merge before either amendment lands, or the blocked
table double-counts.

**The string slide is not an element.** Flipping which side of a set a string
passes on, with its crossings and their beads following, is a consequence of
saying where the string runs. Nothing needs to be added to say it.

**The n-valent primitive named in the triangle note is not a glyph.** The
authors draw three plain dots with bonds at 0, 60 and −60 degrees and legs at
90, −120 and −60. The triangle is the network. No polygon appears anywhere in
the figure.

The forty-one cosmetic gaps sort into six causes, and targets carry more than
one: ten are glyphs sized by their labels, seven are labels with no station,
seven are closures deeper than the ink they clear, six are faces that cannot
point off the compass or frames with no fixed pitch, six are properties of
wires no author wrote, and fourteen are theme bindings or panels that drew
something the source does not. Nine defects are recorded as a weight
mismatch; reading them, one is line thickness, two are glyph scale and six are
closure shape. None is strand count. The status word should be split: about
twenty-seven of the forty-one wait on the kernel and the rest wait on a
palette or a redrawing.

## One curve under six names

Six mechanisms in the contract and in the five designs describe the same
construction — take a set of records, take their measured silhouettes in the
frame's own axes, take the support hull, push it out by one clearance, round
the turns.

| what it is called | which records it clears |
|---|---|
| the corridor lane | the whole picture |
| the enclosure contour | a mark's members |
| the detour past named records | the named records |
| the depth of a trace or a cup | the records between the two ends |
| the ring four tensors stand on | those four tensors |
| the reach of a leg a string crosses | everything declared to meet it |

They differ in one parameter: which records the curve must clear. Not the
geometry, not the clearance, not the rounding, not the ordering rule.

The authors settle it. Diagram 3 of Section III places four copies of one
tensor at `(\d:0.7)` and draws around them a `rounded corners` rectangle of
half-width `0.7`. That rectangle is the rounded hull of the four tensors plus
clearance, and in that one figure it is stroked as a mark, travelled as a
wire, and stood on as a place. The authors drew all three with one `\draw`.

The service already exists and is already general: the corridor functions take
an obstacle set, not a picture, and the maximum-support fold already runs over
a record set with a per-record angle. The parameter the six mechanisms are
groping for is already in the signature, and nothing passes it.

Amendments three and four are that finding. The rest follow it.

## Amendment three: the selector

### What is wrong

The language has three ways to name a set of records, and none of them is a
value type. A mark target is a cell set, a wire place, or an address set —
three kinds in one argument, told apart by hand. The cell-set type is claimed
by two picture keys and stands flagged as a lonely type. A wire that must
clear a set names it with an address list; a wire that must cross a leg names
the leg through a production added for that single purpose. Four spellings
again, this time for a noun.

The cell-range spelling is not merely redundant, it is false. The enclosure
reads four integers out of a range and uses them as page positions, taking the
column for the horizontal and the negated row for the vertical. It never asks
the frame. A range therefore draws in the right place only while the frame is
the identity — which is why the frame offset is pinned to zero, in the
maintainer's own words at the mark: shifting the frame alone would slide the
atoms out from under their own enclosures. It breaks today under a circle
frame and under a projected one, with the damage held invisible by a pinned
zero.

### The proposal

One selector, everywhere a set of records is named.

```
<selector> ::= <address>
             | { <address>, <address>, ... }
             | <address> .. <address>
```

The range joins the address grammar as one production, available wherever an
address is. Range, not hyphen: a cluster member is named `a-2-2`, and a hyphen
range cannot be told from a name the language itself generates.

```tex
\tnmark[form=enclosure, label pos=w]{(1,1) .. (1,4)}{$A^{[L]}$}
\tnmark[form=enclosure, species=marked]{{a-2-2, b-2-1, c-1-2, d-1-1}}{$X$}
\tnwire[kind=string, route={n of (1,1) .. (1,3)}]{open}{open}
```

`x .. y` denotes the records between x and y in the frame's own order: two
cells corner a block, two places on one wire bound a closed sub-arc, two
stations of a circle frame bound an arc. A named group denotes its members.
The model records the resolved membership — the normalized set of records —
and never the expression that produced it, so containment between two
selections is a fact the model holds rather than a number an author types.

### What it costs and what it buys

Three mark-target kinds become one. The mark's own reading of its target dies,
and with it the integer-as-position branch and the pinned frame offset. The
cell-set value type retires: it was kept at Session 0 on the promise that the
boundary algebra would gain consumers, and it gains them by becoming the
selector rather than by remaining a type of its own. The two picture keys that
carried it take the selector unchanged.

Consumers of the range form: the CZX state and the GHZ state, both blocked;
the boundary region and the two-dimensional ground space, both cosmetic gaps
whose notes name the contour. A fifth, the blocking figure, is recorded
wrong-source and must be redrawn against the author's one-site isometry panel
before it counts for anything.

The wire-place range has one consumer, the charge tile along the string of
`rmp-iii-b-dyon`, which is below tenure. What would settle it: a second and
third figure marking an interval of a string, or a decision to restrict the
production to cells and stations and let the dyon's tile be a mark on a bead.
The unity of the production argues for admitting all three readings; the count
does not yet.

### What it reuses

The `fit` mechanism is the shelf's answer for turning a set into a shape and
is what the older grid tier already calls. Usable for the bookkeeping, not for
the geometry: its box is page-axis-aligned by construction and cannot follow a
rotated, sheared or projected frame, which is exactly the recorded defect on
the boundary region — a page parallelogram where the author drew an ellipse in
the sheet. `spath3`, already loaded, splits a path by arclength and makes an
interval of a string a real interval rather than two ends.

## Amendment four: the offset hull

### What is wrong

Six spellings for the curve of the previous section, and a seventh — the
section-IV wrap — with no spelling at all until the corridor. The corridor
named one of the six and stopped at the picture's own silhouette. Every string
in the pulling-through family runs inside: between a tensor and the far end of
that tensor's own leg, at the silhouette of one site, a fifth of the way to
the margin. The corridor's measure is right and its scope is wrong for them.

The cost of the missing statement is on record. In the kernel fixture for
pulling through, one crossing was declared because only one existed — two of
the three legs stopped short of the string, so the crossing police had nothing
to refuse, and the figure came out asserting a relation the source does not.
A policy about order is silent where there is no crossing, and silence is how
the picture went wrong. The missing word is not *over* but *past*.

### The proposal

Name the curve once. **The offset hull of a selection** is the support hull of
the selected records' silhouettes, measured in the frame's own axes, expanded
by `daylight`, turned with radius `corner`. Five records consume it, each
through a key it already carries:

| consumer | spelling | what the hull is |
|---|---|---|
| a mark | `form=enclosure` | the stroked contour |
| a mark | `form=bracket` | the arc of that contour on the label's side |
| a wire | `route={<side> of <selector>}` | the curve it travels |
| an atom | `at=on <wire> t` | the place it stands and the axes it reads |
| a leg | — | the reach a crossing forces |

The route key gains one value family, in which the side is a compass word or
`all`:

```tex
\tnwire[kind=string, species=g, crossing=over, route={n of (1,1) .. (1,3)}]{open}{open}
\tnwire[kind=string, species=g, closed, name=ring, route={all of (1,1) .. (1,4)}]
\tnwire[route={all of picture}]{R.e}{R.w}
```

A wire routed this way travels at one standing offset from the hull of the
selection, on the named side, entering and leaving where that side's arc ends.
It crosses exactly those wires that leave the selection through a face on that
side, each once, in hull order. The author's claim is that this string passes
on this side of these tensors; the crossing set is the answer to that claim,
computed and never chosen. An empty crossing set is legal and meaningful, as
when a string runs south of a chain whose legs all point north. A derived
crossing enters the model with every field a declared one carries, so an audit
cannot tell the two apart, and its order comes from the string's habit or from
a declared exception.

`route=around` does not survive as a separate word. It is this route with the
selector standing for the whole picture, and the amendment that exists to stop
four spellings of one idea cannot leave two.

The direction of an open end becomes optional and takes its place from the
route:

```tex
\tnwire[kind=string, species=h, route={ne of flux}]{on leg e of A 0.4}{open}
```

With no direction the end lies on the route, one clearance past the outermost
wire it crosses — which is where the authors stop their own strings, at
`(0.05,3.8)` and `(0.5,3.05)`, one clearance past the two crossed legs. With a
direction it lies on the picture margin, as now. An open end is an index cut
by the picture's frame and is boundary data the equation audit matches panel to
panel. The corpus contains no place where a string mathematically ends: the
dyon's anchored end is a junction with a lattice leg inside the flux disc, the
torus string's lower end is a port of a box, and the corner strings continue
beyond the patch. So the language lacked a place for an open end, not a second
kind of end — and the spurious box recorded against the dyon is what the
missing place forced.

Two rules travel with the hull and are doctrine, not elements.

1. **Concentric order.** Curves over the same selection are separated by one
   clearance: outward in declaration order for routes, inward by containment
   for contours, ties broken by declaration order. This sentence was written
   four times across the five designs and is one sentence.
2. **Reach.** A reach is the maximum over everything declared to meet it. A
   leg crossed by a route is as long as the outermost route crossing it plus
   one clearance, so a crossing the author claimed always exists and the
   crossing police can no longer fall silent. A contour grows on the label's
   side to admit the label. The kernel already writes this for crossings and
   for pierced enclosures — and keys it off the integer branch amendment three
   deletes, so it must be restated against selections in the same change or a
   working mechanism breaks.

### What it costs and what it buys

Retired: the waypoint key, whose every use in the contract's own sketches is a
hull — the braid's waypoint is a constructed crossing, the torus and
section-IV waypoints belong to the corridor, the pulling-through waypoint is a
side of a selection. The curvature key, because an arc leaves and enters along
its ends' faces, which is how every curve in the corpus is written: the
authors write `to [out=180,in=180]` and `to [out=-90,in=0]` and never choose a
bend. The nesting key. The address production for a policy-generated leg,
added by sign-off decision three so a string could name a leg to cross; with
the side form the crossing set is derived and no one names a leg. The
production for a point on the picture margin, which is the open-end spelling
said twice — the contract's own sketches use both for the same thing.

Three mark forms go: the shaded band, which never differed from an enclosure
except in the shape of its selection; the lower brace, which merges with the
upper into one bracket, because the side a bracket speaks from is the side its
label sits on and every mark carries a label placement already; and the cut,
which has no consumer in the benchmark or the blueprint and fails tenure
outright, taking its sugar row with it. Three named ratios fold into
`daylight` and `corner`. Two drawing paths die: the rectilinear boundary
tracer of the older lattice tier, with its loop chaining and notches, which no
benchmark case consumes because no case selects a non-convex set; and the
page-axis contour.

Bought, besides the pulling-through family: the closure depth the corridor
left open. A trace closing a whole row must clear the whole row and comes back
as the long return the authors draw. A cup joining two vertically adjacent
ports at one column must clear one column and comes back as the shallow cap
they draw — `(2.1,0.06)--(2.1,0.25)--(2.4,0.25)--(2.4,-0.45)--(2.1,-0.45)--(2.1,-0.26)`,
three tenths deep in a five-column figure. Nobody chooses which; the two ends
already say. That finally states the cap idiom, against which the shrink
ledger has already sentenced the trace-style key without anyone writing down
what the idiom is.

Consumers. Route form: the pulling-through pair, the g-injective pull, the
white MPO-injective panel, the SPT string, Diagram 3, the dyon, the MPO
injectivity ring. Contour: the dyon, the CZX state, the two-dimensional ground
space, the boundary state, the old boundary workbench, the boundary region.
Closure depth: both marginals, the MPDO trace, the transfer-matrix tails, the
left orthogonality identity, the channel arrows, the MPU normal form.

### What it reuses

The hull is three lines over the maximum-support fold the geometry stage
already ships, and the corridor's own silhouette measure evaluated over a
subset. `hobby` closes the hull smoothly, which is how a one-member selection
becomes the author's disc rather than a rounded square, and gives an arc its
prescribed end tangents. `spath3` splits the closed hull so a bracket and an
enclosure share one geometry, and locates what rides at a crossing.
`decorations.markings` places a mark with the path tangent as its axis and is
the right ink for an atom carried on the hull — adopted as drawing and refused
as language, since it turns everything it places, label text included, and
knows nothing of a typed port. `tcolorbox` and `mdframed` frame typeset text,
not measured picture ink, and follow no frame. Nothing on the shelf places a
path so that a required crossing exists; that part is ours and is already
written as the corridor.

## Amendment five: local axes

### What is wrong

Five blocked targets are tagged with a rotated action, and rotating the page
draws none of them. Diagram 3 places its four tensors with `rotate=\d+90` at
station `\d`: the turn is exactly the ring's tangent there. Each tensor's
operator face runs along the ring and its physical face points radially out of
it, so the tensors contract in two directions at once — virtual along the
curve, physical with the lattice. Turning the page turns both together and
expresses neither. The two outer tensors obey the same rule against a
different carrier: one unturned on the vertical outer leg, one at a quarter
turn on the horizontal one, each set so its physical face runs along the leg it
sits on.

The same rule through a projection: the SPT string and the inverse
renormalization draw their lattice inside a canvas-in-plane scope, so the
site's four virtual legs follow the projected axes while the physical leg runs
straight up the page. Two port families, two answers.

The alphabet cannot say it. Atom faces are four compass words, and a compass
word means two things at once: the north face of a tensor, and northward on
the page. Under a half turn the face called north points south. The contract
holds that a word carries its operation across scopes and never a second
sense; this word carries two, and the overload meter that may never rise has
never counted it.

### The proposal

Three statements, one rule.

A frame assigns each address a point and a pair of axes. For an affine frame
the axes are its linear part, the same everywhere; for a circle frame they are
the tangent and the outward radius and they vary by station. An address on a
carrier — a wire, a leg, a hull — takes the carrier's axes.

A face is an angle in the record's own axes, not a word on the page.
Production three of the address grammar reads

```
a.θ@k          the port at angle θ on a, slot k
```

and a port declaration takes the same value:

```tex
\tndeclare{atom}{\tnprojector}{skin=box, ports={180:virtual, 0:virtual, 90:physical}}
\tn[at=on ring 0.25]{$\lambda$}
```

Ink the frame measures lies in the frame; ink the frame only places stays
upright. Skins, contours and wires are measured; label text is placed and
never turns.

Diagram 3's ring then carries no angles at all:

```tex
\[\begin{tenkz}[ring=4]      % sugar: cols=4, frame=circle, west=trace, east=trace
  \tn{} \tn{} \tn{} \tn{}
\end{tenkz}\]
```

Orientation is a consequence of where a record sits and is never an authored
quantity. A port's page direction is its angle plus its record's accumulated
turn, so the type check and the boundary signature are computed in the axes
the ports actually point along. Contraction is unaffected: turning an atom
changes no bond, only which way its faces look. Under a flat frame the local
axes are the global axes, so the flat corpus resolves unchanged.

### What it costs and what it buys

The eight-word face alphabet is deleted. An angle is the number the compass
table was already computing, and three private triangle-corner anchors in the
implementation collapse into the boundary anchor every stock shape carries.

The frame alphabet closes to three words with no parameters — `flat`, `plane`,
`circle`. The numeric page angle goes for want of consumers: the contract names
four, and reading them, one is a carrier orientation, two are projections, and
the fourth's note reads *rotated 90 degrees and shallower than the source
tree*, so the turn there is our defect and not the source's demand. Zero of
four. A degree is the angular millimetre, and a published figure contains no
millimetres. The transpose spelling has two consumers, below tenure, and the
authors spell it themselves as a choice of which lattice axis to call a row —
22 uses of one plane spelling against 16 of its transpose in one document. The
general matrix goes on its own count, not on the argument that composition
makes it reachable: with the page angle retired there is nothing left to
compose, and it has no consumers either. The three plane parameters have zero
consumers across all 130 cases, although the projected frame is named 26 times
and is the most-used frame after the default; they are named rows of the
metric registry with stated reasons and stay there.

The two page-relative atom keys go with them. They were one idea in two words,
distinguished only by which side of a sandwich the row sat on, which the frame
already knows; the outward physical face is the row's own normal, which is an
angle. They come back as one sugar row.

One clause travels with the circle frame and only with it: adjacent stations
are one pitch apart. That fixes a radius the contract leaves unstated and is
why a three-station ring comes out twice as loose as the source. For four
stations it gives `pitch` over root two, about seven tenths; the authors wrote
`(\d:0.7)`. The clause must not be generalized — in the projected plane the
receding row is foreshortened by construction, and that foreshortening is what
the plane's ratios are.

Consumers. Carrier axes: Diagram 3, the pulling-through pair, the dagger
insertions of the second equation-60 panel, the MPO action, the GHZ tensor,
the old PEPS gauge workbench. Angle faces: the triangle network, with legs at
90, −120 and −60 on plain dots; the first PEPS renormalization workbench, with
four physical stubs at 50 degrees on a square plaquette that no frame
produces; the second at 60; the dyon. Ink in the frame: the GHZ state, the
inverse renormalization, the cluster-state workbench, the boundary region.
Circle pitch: the triangle network, the MPO injectivity ring, the
one-dimensional ground space, the idempotent, the equation-51 workbench.

### What it reuses

Every stock shape already carries a boundary anchor for an arbitrary
direction: a leg at 17, 37, 50 or −120 degrees attaches exactly on the boundary
of a disc, a box, a rounded box and a triangle with nothing declared. The
angle of a station comes from the geometry stage, which already returns a
station's point together with its tangent; a direction is transported through
a frame's linear part by a function that already exists; and the silhouette
fold already takes an angle. The oblique canvas keys are the authors' own
idiom — 42 uses across the four sources, in exactly two spellings — and carry
measured ink into the frame's plane; taken in their general three-point form
only, since the named presets collapse a nested sheet to a line and report
nothing, measured, zero errors. The camera library is refused and its earlier
acceptance reversed: every projection it can produce satisfies one identity
that the projection all 130 figures use does not satisfy, and the two families
meet only where the shear is zero. It cannot draw a single target. Declaring a
new shape is unnecessary — the capability it would add exists on every stock
shape. The polygon key, tombstoned pending three consumers, should be made
permanently dead: the consumers arrived and they want angles, not corners.

## Amendment six: the cell basis

### What is wrong

The cluster-state block of Section III is two interpenetrating copies of one
cell set, the second offset by half a cell in each direction, each cell
carrying an up-facing and a down-facing site, with a bead at every bond
midpoint. That is a lattice whose cell carries a basis of two sites — the
standard decomposition, and the registry's own escape row already uses the
word, calling itself a projected sheet basis. The affine frame is the Bravais
half. The basis half has no spelling at all, which is why the case draws a flat
grid and the verdict reads *staggering and arrow legs flattened*.

Four mechanisms circle it and none states it: a group of dot atoms on a
quarter-pitch sub-frame with private member naming, two nested sheets on a
plane preset, a sheet count with a separation and a pairing rule, and an
expert sheet vector.

### The proposal

A subkey of the frame specification, the same door the plane parameters use:

```
frame={flat, basis={<row kind> at (<q>,<q>), ...}}
```

The members are a row list drawn from the row alphabet that already exists, so
a member's outward physical face comes from vocabulary the language already
has; offsets are quarter-pitch pairs. A frame with no basis has a basis of one
at the origin, so every existing picture is unchanged.

```tex
\[\begin{tenkz}[lattice={3x4}, frame={flat, basis={ket at (0,0), bra at (2,2)}}]\end{tenkz}\]

frame={flat, basis={wire at (0,0), wire at (2,0), wire at (0,2), wire at (2,2)}}
```

Twenty-three lines of nested loops in the authors' hand, and the composite site
the ledger records in the maintainer's own words as *composite sites + doubled
bonds*.

Production one of the address grammar gains a slot rather than a production:
`(r,c,k)` names member k of cell (r,c), and `(r,c)` alone names the whole cell,
which is what a cell already means to a selection. Frame population creates one
atom per cell per member; the model records each atom's cell and member index,
so the boundary signature sees basis members as the distinct entries they are.
Adjacency is declared by the offsets, so contraction stays a fact and not a
measurement.

### What it costs and what it buys

The sheet mechanism dies. The cluster row and the two-sheet row keep their
spellings and their tenure and lose their group expansions, so the
group-per-cell mechanism, the sheet-as-group mechanism and the cluster's
private member naming all die while the registry count holds and cluster
members become ordinary addresses. The atom displacement key loses its
remaining reason: an off-cell site is a basis member.

The savings on the sheet keys themselves are already booked and must not be
booked twice: those rows are not in the 1.0 kernel tables, and the shrink
ledger has already sentenced them — the separation and the sheet vector fold
into frame subkeys, the pairing folds into declared skin pairings. What the
basis executes is the one keep-because verdict standing over them, kept at
Session 0 on the promise that the condensation and CZX redraws would consume
it. They consume it as a basis, and the verdict expires.

It also destroys a trap. The two-sheet sugar is defined as nested sub-frames on
a plane preset, and nesting that preset inside itself annihilates one axis and
reports nothing — measured, a sheet drawn as a line, and an audit that
compares networks rather than silhouettes would pass it. As a basis it is one
frame and cannot collapse.

Consumers: the cluster-state workbench, the CZX state, the GHZ state, the
condensation lattice, the PEPS renormalization.

One ledger correction is required before this lands: the CZX target's tag must
merge with the staggering tag, or the blocked table double-counts.

What would settle the remaining question — which members bond. The
cluster-state figure bonds member to member inside a cell and across cells, and
nearest-neighbour-by-offset produces both; but that is a measurement, and the
doctrine is that adjacency is declared. The alternative is that a member
declares which neighbours it meets, which is grammar the figures may not need.
The condensation lattice decides it: its basis runs along the depth axis and
its intra-cell bond is the pairing leg.

### What it reuses

Nothing to buy. The frame record is a linear part plus an offset, and the
composition of two frames already exists — measured exactly, to four figures,
in either order and at either scope — so a basis is a list of offsets folded
against a frame that already accepts one. Matrix placement on the shelf sets
nodes on an integer grid and cannot express a sub-cell offset, which is what
the language already does.

## Amendment seven: extent from counts, labels from ink

### What is wrong

Two rules, each load-bearing for the other.

The glyph is sized by its label and the authors' is not. They never measure a
label. The positive-MPO figure writes two identical rectangles, 0.55 by 1.2,
one holding a matrix and one holding its inverse: the extent was decided before
the label existed. Where a label will not fit they move the label out rather
than grow the box — the intertwiner draws the same rectangle and sets its
subscripted name beside it. Where they do vary a radius they vary it by two
hundredths, drawing three same-class rings at 0.22, 0.23 and 0.24 so that they
read as one size. The shift operator draws a square, because one slot enters
each face.

Against that the contract sizes a glyph by the widest measured label in its
class, and only inside an equation. The two capsules of the local-purification
panel sit in one picture and are not covered — its note reads *X and X^-1
blocks must be the same size* — and a tensor changes size between two figures
because someone wrote a longer name in one of them.

A label has no station, only a compass point. Every label in the sources is
anchored away from the ink it names, and the four-site plaquette places eight
tiny sector labels by hand, two at each junction, each shifted by seven
hundredths so it touches neither the circle nor the rails. The authors do by
hand, eight times in one figure, what a station rule does once. Three targets
record a label lying on ink, two more record an illegible placement.

### The proposal

A glyph's extent is a function of two declared quantities and nothing else:
its size class, and the number of port slots on each pair of opposite faces.
The horizontal extent is the class reference times the greater of one and the
slots on the vertical faces; the vertical extent likewise. A round skin takes
the reference as its diameter, a box as its side, a triangle as its
circumscribing square, so an operator and its inverse match across skins.

```tex
\begin{tenkz}[rows={op,op}]
  \tn[skin=box, wires=2]{X^{-1}} & \tn[skin=box]{A} & \tn[skin=box, wires=2]{X}
\end{tenkz}
```

The first and third match because they share a class and slot counts, and for
no other reason. The middle is square because one slot enters each face.

A label that does not fit is not accommodated by growing the glyph. It goes to
the station rule, which is the second half. Every label belongs to a host — a
glyph, a wire, a place on a wire, a selection — and inherits from it a ranked
ring of stations: the compass points at one clearance, then the diagonals,
then the same ring one step out. The first station whose box meets no ink
already placed and no label already placed wins. Ink means the measured
silhouettes the geometry stage computes anyway, legs and stubs included, which
is precisely why labels touch legs today: a leg is drawn from a policy and
appears in nothing the label consults. A named placement is honoured, and
honouring it grows the host's contour on that side rather than putting the
label on ink; a pinned label that still collides is refused, as an undeclared
crossing is refused, and for the same reason — a figure that silently overlaps
two symbols asserts nothing, and the renderer never guesses which one the
reader should believe. `auto` acquires a definition: the face whose outward
support leaves the widest clear band.

The model records whether a label was set inside its glyph or beside it. That
bit is worth reading: it says the figure contains a name that outgrew its
class.

### What it costs and what it buys

The equation clause sizing a glyph by the widest label in its class is
deleted, replaced in every scope by the reference extent, which is a column of
the size-class table and not a key. Both displacement keys retire, one on
atoms and one on marks. Displacement existed for two reasons and both are
gone: shoving a label off ink, which the station rule does, and moving a record
off its cell, which is a basis member or an ordinary address. It is the largest
surviving term of the escape meter, so that meter falls rather than holding.

Consumers. Extent: local purification, the old positive-MPO workbench, the
one-dimensional ground space, the SPT intertwiner, the MPU wrap, the second
proof panel, the GHZ-up workbench, the g-injective MPO workbench, the
staircase. Stations: the triangle network, the MPO sheet, the MPU splitting,
the F-tensor workbench, the transfer-matrix spectrum, the old boundary
workbench, the two-dimensional ground space.

Amendments five and seven should land together: angle-valued faces make label
collisions worse before better, because a leg at 50 degrees puts its label
where no compass quadrant expected it.

### What it reuses

Node geometry already gives a minimum extent a label cannot shrink below, and
a fixed aspect that holds a shape's proportion independent of its content;
what is chosen here is not a mechanism but the policy that the floor is also
the ceiling, plus a column of reference extents. For the stations there is
nothing to buy: the shelf's label placement sets text at an angle and never
tests what is there, and the one library that genuinely resolves label overlap
runs only in the scripting engine and is refused. This is the sanctioned
build-ours item, and it is small because validation finishes before any ink is
emitted, so occupancy is known at the moment a station is chosen, and the
support fold that answers how far a set reaches along a direction is the
corridor's own.

## Amendment eight: the term

### What is wrong

Not one of the 130 cases uses the equation environment. Every one escapes to
plain display mathematics and glues its panels by hand: forty-odd relations set
as bare equals signs, four arrows, six tensor products, a subtraction of two
summations, coefficients and summation signs written as text beside the
picture, and — to get more than one row — an aligned block, a gathered block,
bare line breaks, and in one case a display closed and reopened, which ends the
single metric context the equation surface exists to guarantee.

Three things the language cannot state.

A term need not be a picture. A projector written as a symbol, a channel
applied to an argument, an elision: terms with no depicted boundary. The
contract has one narrow spelling for this and every case evades it by writing
the symbol outside the environment, where nothing can see it.

A joiner has a class, and the class fixes the audit. Equality, arrow and
map-to compare two terms. Addition and subtraction compare and continue. The
tensor product does not compare at all — it concatenates. The audit as signed
compares the boundary signatures of adjacent panels, so on the tangent-space
projector it would require a half-infinite block, a single identity wire and a
second half-infinite block to carry the same boundary, which is false and is
the point of the figure. That is a defect in the contract, not a gap in it.

A row of panels is mathematics. The fine-graining figure is two sub-figures
tagged (a) and (b), each a picture, an arrow and a picture; the
renormalization figure is four sub-figures laid two by two with a tensor
product inside three of them.

### The proposal

Inside the equation environment the body is rows separated by line breaks, and
each row is an alternating sequence of terms and joiners. A term is a picture
or mathematics. A joiner is the mathematics between two terms and carries one
of three classes: **relation**, **sum**, **product**. Only the product list is
the language's own datum — juxtaposition and the product signs; relation and
sum are read from the class the mathematics already has.

Every term has a boundary signature; mathematics has none, and its signature is
unknown. A relation requires equal signatures and ends the term. A sum requires
equal signatures and continues it. A product requires disjoint signatures and
concatenates them. Any joiner with an unknown operand yields an unknown result,
and the comparison is recorded as unperformed rather than as passed — which is
exactly what an elision between two panels asserts, and needs no spelling of
its own. A relation with an undepicted side is legal in a draft and refused
under strict, which the benchmark sets.

```tex
\begin{tenkzeq}
  \begin{tenkz}[physical=up]\tn{}\end{tenkz}
  \longrightarrow
  \begin{tenkz}[physical=up]\tn{} & \tn{}\end{tenkz}
  \\
  \begin{tenkz}[lattice={1x1}, physical=up]\tn{}\end{tenkz}
  \longrightarrow
  \begin{tenkz}[lattice={2x2}, physical=up]\end{tenkz}
\end{tenkzeq}
```

The group average needs no key. A scalar coefficient is a term of empty
signature; juxtaposition is a product; concatenating an empty signature leaves
the panel's boundary as it was. The summation sign is likewise mathematics, set
west of the panel on the shared axis, its limits smashed against a panel that
is always the taller. That is the rule falling out rather than being installed.

### What it costs and what it buys

The audit key retires and its value type with it — a standing lonely-type flag
that was to collapse only if its key died. The audit rule is derived from the
joiner's class and is not the author's to configure. The prose mark form
retires, taking that alphabet to three words, and its sugar row with it:
mathematics in place of a diagram is a term, refused under strict wherever it
stands and not only where an author remembered to mark it. The inline-picture
command is demoted to a sugar row over the picture environment, taking the
kernel from seven commands to six: with math-style sensing and a term grammar,
an inline picture and a displayed one are one concept in two spellings, which
the seventh grammar rule forbids. Four escapes into raw display machinery
close.

Consumers: the tangent-space projector, the fine-graining workbench, the
historical composite, the projector on the tangent space, the boundary lasso,
the equation-59 workbench, the PEPS renormalization, the second PEPS
renormalization workbench. Two further blocked targets carry the
equation-composition name and both are recorded wrong-source — the
renormalization workbench draws a unitary on a plaquette where the authors drew
four factorization sub-figures, and the projector target declares a four-leg
projector where the authors drew the g-string equality. Language work is
necessary for both and sufficient for neither; both must be redrawn against the
source before their verdicts can move.

What would settle the one rule the corpus cannot: whether disjointness under a
product is compared by position or by the names of the open legs. The
tangent-space projector tensors three blocks each with open physical and
virtual legs; if signatures are named, the three blocks' legs must be
distinguishable, and if positional, disjointness is vacuous and the product
check does nothing.

### What it reuses

The multi-row layout of the standard mathematics packages is the row engine
and is already loaded by every document that would use this. It is refused as
the surface, and the corpus is the reason: two figures escape into it today,
and inside those bodies the panels are opaque — no shared metric, no joiner the
audit can see, no boundary check performed. The vertically-centred-box axis of
the quantum-circuit package is taken verbatim and supplies the axis of a
symmetric panel and of every joiner glyph, with the wire-axis key overriding it
when a panel is lopsided, as an upward-physical picture always is. Large
operators with limits are the glyph, and the smash-operator idiom is exactly
the tall-operator-before-a-taller-box problem and is taken; its sibling for
stacked limits has no consumer among the 130 and is refused. Sub-figure
packages are refused: float-and-counter machinery that cannot appear inside a
display and sets its tags in caption type — the authors did not use them
either, they wrote the tag as a node. Commutative-diagram packages are already
refused by the standing survey, and the annotated-arrow look is available from
the standard mathematics packages without importing a diagram engine.

## Amendment nine: ink follows the type

### What is wrong

Two ink axes are authored where the model already holds the answer.

A mark chooses among five house tints while a wire chooses among declared
species, so one semantic identity has two unrelated spellings and neither can
reproduce a cited paper's palette. The dyon figure draws its region and the
string that ends in it in one red, and the tint key cannot say so. One of the
five tint words was never a tint at all: it named a reach and was implemented
as a fifth colour, which is the overload the one-token-one-meaning rule exists
to prevent.

A wire chooses its stroke weight, and no author ever does. The canonical-form
glyph draws its two virtual legs bold and its physical leg light. The
orthogonality identity draws the arc closing the virtual index bold and the arc
closing the physical index light, in one figure, side by side. Section III
makes the same distinction in colour: a black physical leg and a red virtual
leg on one box. The weight follows from what the index is, and the language
already types every port and already refuses a virtual port meeting a physical
one. The stroke axis is the same fact, unread — which is why the left
orthogonality panel is recorded *thin wires vs bold source*: it drew one weight
because weight was a choice nobody made.

The bundle value is worse than unused. It is defined as one heavy leg standing
for an index set, and its three declared consumers draw no such thing: two draw
plain single legs, and the third — the one figure whose whole subject is a
region's aggregate boundary index — draws an ordinary single line with a label.
The blueprint agrees, annotating its own west wire as bundling every edge's
virtual index while carrying a signature of one and one for arbitrary degree.
Bundling is a claim about the boundary signature, the audit already carries
that claim, and no ink is owed.

### The proposal

Marks expose the species key that atoms and wires already carry, with the same
type and the same meaning, and lose the tint key and its five words. The weight
key and its three words are deleted; the stroke width becomes two named ratios
in the theme, selected by the type the port already carries. A theme may set
them equal and get today's picture back.

```tex
\tndeclare{species}{charge}{hue=source:blue}
\tnmark[form=enclosure, species=charge]{v}{$\alpha$}
\tnwire[kind=string, species=charge]{...}{...}
```

### What it costs and what it buys

One key added at mark scope, two retired, eight alphabet words gone. The
bundling clause of the audit stays, reworded from a leg equalling its
constituents to a leg standing for them. Hatched species render through the
pattern library rather than through a key, so three targets complaining of lost
hatching cost no grammar at all.

The exact form of the argument for retiring the weight key: it has no consumers
to name, because no author ever wrote it. The six targets whose stroke is
recorded as wrong include four recorded faithful, two of them annotated *better
than the authors*. A deletion needs no consumers; what it needs is that nothing
is lost, and nothing is.

Consumers of species on marks: the dyon, the boundary lasso, the old boundary
workbench, the MPO injectivity ring, the two-dimensional ground space.

Two ledger corrections ride with this. The tombstone migrating the old fused
spelling to the doubled weight becomes a dangling reference the moment the
weight key dies and must be rewritten in the same change to say that the index
type decides the stroke. And the multi-strand capability name is retired from
the demand table, with the one contradicting note corrected in the same change.

### What it reuses

Colour-series machinery supplies the house cycle and the language already
consumes it; it is not usable as the binding, because the demand is per-paper
reproduction of a source colour and the species declaration already spells
that. The pattern library, already taken, delivers hatching as a species
rendering. The multi-strand package was measured and works — two- and
three-strand offsets render correctly on straight and curved paths alike, with
no cusp at an S-bend, and trimming gives a square simultaneous gap across all
strands — and is refused anyway for want of a single consumer. The measurement
stays on file; if a figure ever needs a doubled strand the adoption is one
line. One negative result is worth recording against that day: the white-halo
occlusion shortcut, which the authors use 18 times on single strokes, leaves a
mottled artefact on a multi-strand stroke and must never be used there.

## What is not proposed

| proposed and struck | why |
|---|---|
| a key binding a summation index | it verifies nothing — label arguments are opaque mathematics by the contract's own rule, so a vacuous binder is drawable — and the prefix draws as an ordinary term of empty signature |
| an address production for the k-th panel | a picture is a record class and takes a generated name, as generated wires already do |
| a slide declaration on an equation | it draws nothing, and flipping a route's side is a consequence of the route; it also occupies the key the term grammar retires |
| two face words for the outward and inward directions | the outward direction is an angle in the record's own axes and the grammar already carries it |
| the pitch invariant stated for every frame | false for the projected plane by construction; kept for the circle frame, which has five consumers |
| a separate nesting amendment | two of its four consumers are routed to a wide atom by sign-off decision two and one is recorded faithful; it survives as one sentence of the hull's doctrine |
| a separate label-placement amendment on marks | the same design as the atom's, and counted once |
| the multi-strand dependency | no consumer; refused with the measurement on file |

Two savings claimed twice across the designs are claimed once here: the
displacement keys and the nesting key.

## What this addresses

Of the thirty-eight blocked targets, the corridor and crossing order take
twenty outright and share four. These amendments take fourteen outright —
the inverse renormalization, the F-symbol, the pulling-through pair, the GHZ
state, the SPT string, the g-injective projector, the dyon, the CZX state, the
renormalization and fine-graining workbenches, the second MPU wrap, the
cluster-state workbench, the g-injective pull and the white MPO-injective panel
— and share four with the corridor: the third torus panel, Diagram 3, and both
equation-59 panels, where the corridor supplies a closed ring or a wound string
and the local axes orient the tensors standing on it. Whichever note lands
second inherits the joint acceptance figures.

Of the forty-one cosmetic gaps, about twenty-seven are addressed and fourteen
wait on a palette or a redrawing. Ten fall to the reference extent, seven to
the label station, seven to the measured closure depth, six to angle faces and
the circle pitch. Among the twenty-seven structural gaps, the condensation
lattice, both intersection panels, both PEPS renormalization workbenches, the
equation-51 trace ring and the idempotent are reached by the hull, the basis
and the local axes. Seven targets across all statuses carry a wrong-source
pairing and must be redrawn against the authors' own panels whatever the
language does.

One cause of forty-one is not turned into an amendment, and it is the largest
remaining question. Six targets want a property of a wire nobody wrote: a leg
made by the physical-face policy, a rail made by a side policy, a pairing made
by a skin, each recorded as thin where the source is bold, or missing an
arrowhead, or missing a stub. Two answers are available and they differ in
kind. Either every generated wire takes a species from the port type that made
it, so weight, hue and direction are theme bindings on two built-in species and
no kernel row changes; or a policy passes wire keys to the wires it makes,
which changes no key table but changes what a policy value is. The first is
cheaper and covers hue and weight. The second is needed if a direction mark on
a generated leg is mathematical content rather than decoration, which for the
fusion indices of the F-symbol figure it plainly is. This wants the
maintainer's decision before anyone drafts it.

## The net element count

Counted against the contract's own tables, each retirement counted once, and
net of what the corridor amendment and the shrink ledger have already booked.

| ledger | before | after | net |
|---|---|---|---|
| kernel key rows | 52 | 43 | **−9** |
| commands | 7 | 6 | **−1** |
| record classes, environments | 4, 2 | 4, 2 | 0 |
| alphabet rows | 6 | 4 | **−2** |
| alphabet values | — | — | **−21** |
| address productions | 9 | 8 | **−1** |
| sugar rows | 27 | 25 | **−2** |
| value types | 24 | about 20 | **−4** |
| parser paths | — | — | about **−7** |
| metric ratios | — | — | **−2** |
| overload count | — | — | **−3** |

Keys retired, ten: the mark tint, the mark nesting, the atom displacement, the
mark displacement, the wire waypoints, the wire curvature, the wire weight, the
two page-relative atom keys, the equation audit. Keys added, one: species at
mark scope, which the scope census counts as a row.

Alphabet values: twenty-four out — eight faces, five tints, three weights, four
mark forms, three frame values, and the corridor's route word folding into the
selector form — against three in, the joiner classes. Two whole alphabet rows
retire, the atom faces and the weights.

Address productions: the range joins, the policy-leg production and the
picture-margin production leave. Sign-off decision three is reversed, which was
the decision that raised the grammar to nine.

Sugar: the prose row, the cut row and the region row retire, the
inline-picture row arrives. Two rows keep their spellings, their tenure and
their consumers while losing their group expansions, so the count holds while
three mechanisms die under it.

Value types: the audit specification, the frame specification (which becomes a
three-word enum with no parameters), the cell set, and the plain number —
the last pending the census, since the two keys retiring it are, on a reading
of the key tables, its only two consumers.

Overloads: the compass word meaning both a tensor's face and a page direction;
the picture-margin address against the open-endpoint spelling; the sheet
count's union type. The meter that may never rise falls three times.

**The metric registry is where growth hides, and it is counted here.** The
designs between them named six ratios that do not exist. Three must not be
minted: the reference extent and the slot pitch are columns of the size-class
table, which already exists and already holds per-class quantities, and the
label clearance is the ratio of that name that already exists. The ring step
derives from `daylight` and the basis member clearance is `daylight`. Against
three retired — the two enclosure pads and the region corner — and one added,
the wire-width row splitting into a virtual and a physical ratio, the registry
ends at minus two. That count holds only if the three unminted ratios stay
unminted; a ratio is an element.

Seven amendments, one new key, one new address production, one new value
family, three new alphabet words. Everything else is a deletion or a rule. The
language ends smaller in every ledger it keeps, including the one it was not
keeping.
