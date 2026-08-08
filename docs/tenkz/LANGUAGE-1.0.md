# The tenkz language, version 1.0

The tenkz 1.0 kernel — record classes, environments, commands, keys,
alphabets, and ledgers — is fixed by this contract. The S4 surface swap has
executed: the package binds the kernel surface at load, the executable
registry (`tex/tenkz/tenkz-language-registry.tex`) carries this contract's
inventory, and the 0.7 front end is deleted. `\tenkzkernel` remains
callable, rebinds the same meanings, and is therefore inert; the 1.0
freeze's corpus rewrite deletes the spelling. A spelling absent from the
registry does not exist, and every table below is checked against the
registry by the census.

<!-- Status: signed off (#4687); this is the binding contract. Supersedes
     LANGUAGE.md (0.7). Kernel follows the Session-0 compression review; where
     the earlier D1-D8 draft and the compression review differ, the
     compression review wins. The §14 decisions were confirmed at acceptance
     (§14.3 was later reversed, as recorded there); execution state to the S4
     surface swap is tracked on issue #4709. -->

<!-- Amended 2026-07-25 by the nine signed amendments
     (AMENDMENT-corridor-and-crossing-order.md, AMENDMENT-remaining-demand.md,
     and the critique that governs them). Effectivity: the tables below are
     the inventory the executable registry is regenerated to at the S4 surface
     swap. Until that swap the registry still carries the parser rows this
     amendment retires, and each one holds a dated verdict in
     docs/tenkz/SHRINK.md naming the landing that executes it — the same way
     every earlier retirement in this project has been booked. -->

## 1. The sentence model

> A picture draws one typed tensor network in one frame. Frames — flat,
> projected, circular, each with a basis, at picture, group, or atom position
> — give every address a place and local axes. A projected sheet also owns its
> page-transverse physical axis. Thus an author writes addresses and never
> measures, and orientation is a consequence of where a record sits. The body
> declares atoms, wires, and marks. Every index ends
> in exactly one of a bond, a closure, or a declared open leg. Equations
> compose whole pictures under one shared metric and must expose equal
> boundaries. The language grows by declaration, never by drawing.

## 2. The kernel

Four record classes, two environments, six commands.

| Record class | Declared by | Holds |
|---|---|---|
| PICTURE | `tenkz`, `tenkzeq`, `\tngroup` | frame, side policy, selections, metric context |
| ATOM | `\tn`, frame population | skin, ports, labels, species, place |
| WIRE | `\tnwire`, side policy, skin pairings | endpoints, route, crossings, winding, closure origin |
| MARK | `\tnmark` | form, target, label |

Declarations (`\tndeclare`) and setup (`\tnset`) create no records; they
extend the vocabulary the records draw from.

### 2.1 Commands

| Command | Grammar | Creates |
|---|---|---|
| `\tn[keys]{label}` | atom at the next chain cell or `at=` | ATOM |
| `\tnwire[keys]{end}{end}` | a `closed` wire takes no positional ends; every other wire takes exactly two | WIRE |
| `\tnmark[keys]{target}{label}` | target is one selector (§3) | MARK |
| `\tngroup[keys]{body}` | scoped sub-frame; names inside stay addressable outside | PICTURE |
| `\tnset{keys}` | document or group policy | — |
| `\tndeclare{atom\|skin\|species}{name}{keys}` | the one extension door | — |

A wire end is an address, or `open` with an optional direction (§5). A
command is warranted only when
it declares a record class of its own; a key modifies the record being
declared. The generated reference prints this test beside every row.

### 2.2 Picture and equation keys (12)

| Key | Type | Values | Default | Scope | Diagnostic family |
|---|---|---|---|---|---|
| `rows=` | row-list | — | `{wire}` | picture | `TKZ-PIC-*` |
| `cols=` | integer | — | 3 | picture | `TKZ-PIC-*` |
| `frame=` | frame-spec | `flat` `plane` `circle`; a picture-level `flat` or `plane` may carry `basis=` | `flat` | picture, group, atom | `TKZ-FRAME-*` |
| `west=` `east=` `north=` `south=` | small-enum | `open` `none` `trace` `cup` | `none` | picture | `TKZ-SIDE-*` |
| `trace=` | trace-spec | selector or `physical` | empty | picture | `TKZ-SELECT-*` |
| `open=` | selector | — | empty | picture | `TKZ-SELECT-*` |
| `bonds=` | small-enum | `grid` `none` | `grid` | picture | `TKZ-PIC-*` |
| `align=` | row | row number or `midline` | `midline` | picture | `TKZ-PIC-*` |
| `size=` | small-enum | `s` `m` `l` | from math style | picture, equation | `TKZ-SIZE-*` |

With the default single-member basis, every frame contracts adjacent
compatible cells by default: `bonds=grid` holds in chain and lattice frames
alike, and `bonds=none` suppresses those frame-generated bonds. A
multi-member basis does not make connectivity follow coordinate coincidence;
it uses `bonds=none` and explicit wires.

A generated grid endpoint begins with the virtual default. Matching authored
port declarations may refine both ends to physical; declaring only one end
physical still conflicts with its implicit virtual peer.

The frame populates and the body overrides, for bonds as for atoms (§4). An
authored index wire joining two adjacent cells *is* that pair's bond, so the
frame mints no second wire under it and the pair's ports have one consumer.
The wire's species, stroke, and route are the bond's, which is how a figure
distinguishes the one edge it is about. The topology is unmoved: the same
contraction, the same boundary signature, whether the restatement carries ink
of its own or none. A travelling string states an operator index rather than
that contraction and retires nothing.

### 2.3 Atom keys (12)

| Key | Type | Values | Default | Diagnostic family |
|---|---|---|---|---|
| `skin=` | identifier | a declared skin; defaults §2.8 | theme default (`dot`; `none` on a void site) | `TKZ-SKIN-*` |
| `wide=` | positive-integer | — | 1 | `TKZ-ATOM-*` |
| `wires=` | positive-integer | — | 1 | `TKZ-ATOM-*` |
| `at=` | address | — | next chain cell | `TKZ-ADDR-*` |
| `name=` | identifier | — | generated | `TKZ-NAME-*` |
| `ports=` | typed-port-list | — | from skin | `TKZ-PORT-*` |
| `frame=` | small-enum | `flat` `plane` `circle` | `flat` | `TKZ-FRAME-*` |
| `species=` | identifier | — | empty | `TKZ-SPECIES-*` |
| `pairing cross=` | indexed-crossing-list | `<pairing-number>: <crossing-declaration>, ...` | empty | `TKZ-SKIN-PAIRING-*` |
| `size=` | small-enum | `s` `m` `l` | `m` | `TKZ-SIZE-*` |
| `label pos=` | angle | a bearing in the record's own axes, or `auto` | `auto` | `TKZ-LABEL-*` |
| `void=` | small-enum | `open` `sealed` | unset | `TKZ-ATOM-*` |

A face is an angle in the record's own axes (§3, §4), so the outward physical
face of a row is that row's own normal and needs no page-relative word. A
label's placement is the same kind of quantity and takes the same type: a
bearing from the host, read in the host's axes, so a label on a turned atom
turns with it and a label on a station of a circle frame stands radially out
of it. One rule, one alphabet, and the four compass words are one sugar
spelling of the four right angles serving faces and placements alike.

A typed-port list is a braced comma-separated list of ports, each written

```
<angle>[@<slot>] : <type> [ : <label> ]
```

where the type is `virtual` or `physical` and the label is the mathematics
set at that port's tip — `ports={90:physical:$i$, 0:virtual, 180:virtual}`.
The label component is where the retired page-relative keys went: an index
name belongs to the port it names, and a port already knows which way it
points. A cluster carrier is a glyphless group and owns no authored `ports=`;
attach wires to its addressable member atoms instead. `void=open` is a hole
that preserves indices; `void=sealed` removes the site and its bonds. A void
site's skin defaults to `none` rather than `dot`: a hole draws nothing —
no glyph and, by the `skin=none` rule it inherits, no label — unless the
author declares a skin, while every record — the bonds bridging an open
hole, its boundary entries — stands unchanged.

### 2.4 Wire keys (10)

| Key | Type | Values | Default | Diagnostic family |
|---|---|---|---|---|
| `kind=` | small-enum | `index` `string` | `index` | `TKZ-WIRE-*` |
| `route=` | route-spec | `straight` `orth` `arc` `{<side> of <selector>}` | `straight` | `TKZ-ROUTE-*` |
| `species=` | identifier | — | empty | `TKZ-SPECIES-*` |
| `closed` | flag | — | false | `TKZ-WIRE-*` |
| `wind=` | pair | cycle `{p,q}` | zero | `TKZ-WIND-*` |
| `around=` | address-list | — | empty | `TKZ-WIRE-*` |
| `cross=` | crossing-list | — | empty | `TKZ-CROSS-*` |
| `dir=` | small-enum | `to` `from` `none` | `none` | `TKZ-WIRE-*` |
| `stroke=` | small-enum | `solid` `dashed` `dotted` | `solid` | `TKZ-WIRE-*` |
| `name=` | identifier | — | generated | `TKZ-NAME-*` |

`dir=` draws the direction mark of a directed index, virtual or physical; it
changes no topology. On a resolved physical index the typed record, the port
consumption and mismatch checking, and the physical-leg stroke all stand; the
orientation of a directed physical open end enters the exposed boundary
signature, while an internal directed contraction leaves no boundary entry.
The mark stands at the named station along the leg's daylight — the stretch
of the leg outside the silhouette of the glyph it springs from — so the same
placement rule inks on every bearing, and a wide silhouette can no longer
swallow the mark of an east leg that a tall one lets a south leg keep.

`stroke=` names the pattern of the rail and nothing else: the weight, the
colour and the topology are untouched. A dashed rail carries an index the
picture draws but does not contract; a dotted rail carries a lattice lying
under the sheet being drawn. The dash lengths are house metrics, so a client
never spells a length of its own.

A wire carries no waypoint list, no bend factor and no stroke weight: a route names the records it must
clear, an arc leaves and enters along its ends' faces, and the stroke follows
the resolved endpoint type (§5).

### 2.5 Mark keys (5)

| Key | Type | Values | Default |
|---|---|---|---|
| `form=` | small-enum | `bracket` `enclosure` `label` | `label` |
| `species=` | identifier | — | empty |
| `tint` | flag | — | false |
| `label pos=` | angle | a bearing in the host's own axes, or `auto` | `auto` |
| `name=` | identifier | — | generated |

A mark takes the `species=` that atoms and wires already carry, with the same
type and the same meaning, so one semantic identity has one spelling and a
cited paper's palette reaches a contour and the string that ends in it alike.

### 2.6 Setup keys (4)

| Key | Type | Default |
|---|---|---|
| `pitch=` | length | em-relative; the exact ratio is a named row of the metric registry |
| `sizes=` | size-table | bundled table |
| `strict` | flag | false; benchmark and CI set it |
| `theme=` | identifier | `house` |

### 2.7 Value types (24)

flag · integer · length · pair · angle · identifier · small-enum · row-list ·
row · selector · route-spec · address · address-list · typed-port-list ·
crossing-list · port-pair-list · trace-spec · size-table · hue-source ·
bond-policy · size-class · void-policy · frame-spec · basis-spec.

These are semantic types, not aliases for TeX argument shapes. A `frame-spec`
pairs one of the three carrier words with its frame-owned subkeys.
`basis-spec` is separate because it is an ordered table of row kinds and
signed two-axis offsets, not a row list, selector, or untyped number.

The angle is minted rather than borrowed, and the reason is worth stating
because it is the only new type here that could have been avoided on paper.
A bearing is not a plain number: a number is a bend factor or an inset
count, page quantities with no frame, whereas an angle is read in a record's
own axes and transforms with them. Typing a face and a label placement as
`number` would have kept the count lower by reviving a type these amendments
retired and by flattening the distinction the local-axes rule exists to make.
The census gains one and says so.

The census covers key values; positional label arguments are mathematics and
carry no key type. Being mathematics, they take one rule about the math
shift: the kernel opens it and peels the author's outer `$...$` when a value
brings its own, so `\tn{$\bar A$}` and `\tn{\bar A}` are the same figure and
leave the same record. The rule governs atom bodies, all three mark forms,
port labels, and the matrix a labelled cup stands on. A prose panel
(`form=prose`) stands outside it, because it sets a sentence rather than a
matrix. Every registry row names exactly one value type; a shared key name
has one type and one meaning at every scope that exposes it. The overload
census (§11, meter M6) never rises.

### 2.8 Closed alphabets

| Alphabet | Words |
|---|---|
| side policy | `open` `none` `trace` `cup` |
| routes | `straight` `orth` `arc` |
| default skins | `dot` `box` `ring` `tri` `triwest` `roundrect` `dots` `none` |
| mark forms | `bracket` `enclosure` `label` |

Two whole rows retired. The atom faces retired because a face is an angle in
the record's own axes and not a word on the page, which also ends the compass
word's second sense. The weights retired because the stroke follows the type
the port already carries.

This table holds the words that cross scopes, which is what the rule below
governs; a `small-enum` whose words serve one key alone is listed with that
key and needs no row here. What the table may never hold is a value set that
is not closed. Two are open, and neither is here: `label pos=` takes an
angle, which is the same quantity a face is and carries the same type (§2.3),
and the side of a hull route belongs to the route family's own grammar (§5),
as a port's angle belongs to a typed port's. The four compass words are not
an alphabet row either. They are one sugar spelling of the four right angles,
serving faces and label placements by the same rule, and they arrive with the
change that implements angle-valued faces.

An alphabet word names one operation, applied at any scope. `open` opens an
index: as a side word it opens a boundary, as the selector key `open=` it
opens the selected cells, as `void=open` it opens a hole. `trace` closes to
the same object: as a side word it closes a row to itself, as the selector
key `trace=` it closes the selected cells. `none` suppresses or seals:
a sealed side, `bonds=none`, and the skin `none`. `cup` closes adjacent rows
to each other. This is the one-token-one-meaning discipline: a word carries
its operation across scopes and never a second sense. `periodic` and `tail`
are sugar (§9); they are not alphabet words. The skin `none` is the
invisible junction: a nameable point where wires meet without ink.

## 3. Addresses

Positions are addresses, never coordinates. One grammar serves atoms, wire
endpoints, routes, and mark targets — eight productions:

```
(r,c) or (r,c,k)       cell of the current frame; member k of its basis
a                      named record
a.θ@k                  the port at angle θ on a, slot k
n <dir> of a           n pitch steps from a          % 2 e of X
midway a and b         midpoint
on w t                 fraction t along wire w       % beads live here
crossing of a and b    the declared intersection of two wires
a .. b                 the records between a and b in the frame's own order
```

Operands compose: in productions four through eight an operand is itself an
address, so `crossing of g and on r 0.4` is well formed. `crossing` operands
must resolve to wires. The slot suffix `@k` is optional when the angle
carries one slot: `B.270` means `B.270@1`. A face's slot count is the
atom's own measured extent (`wide=` across a vertical face, `wires=`
across a horizontal one), and it answers wherever the atom stands — a
spanning atom at a midway or on-wire address keeps every slot a
frame-anchored one would. A cell named without a member
index denotes the whole cell, which is what a cell means to a selection.

Every record class is addressable by name, generated names included, and the
picture is a record (§2). It answers to `picture`, which is how a route or a
mark names the whole diagram without a second grammar for doing so.

A **selector** names a set of records — one address, a braced comma-separated
list, a range, or one selector less another:

```
<selector> ::= <term> | <selector> - <term>
<term>     ::= <address> | { <address>, <address>, ... } | <address> .. <address>
```

`x .. y` denotes the records between x and y in the frame's own order: two
cells corner a block, two places on one wire bound a closed sub-arc, two
stations of a circle frame bound an arc. The range is written with two dots
and never with a hyphen, because a cluster member is named `a-2-2` and a
hyphen range cannot be told from a name the language itself generates. The
`A - B` names what A names and B does not, and subtraction chains from the
left, so a staircase and a complement are ordinary selections rather than
shapes the grammar cannot state. The operator carries a space on each side:
addresses hold hyphens of their own, and this is the one place a hyphen
separates operands. Membership is a set of records, so the difference is the
set difference on those records and nothing else — the
model records the resolved membership and never the expression that produced
it, so containment between two selections is a fact the model holds rather
than a number an author types.

Records carry no displacement key. An off-cell site is a basis member of the
frame or an ordinary address, and a label that will not sit where it is takes
a station against measured ink (§6). Raw lengths exist solely as `debug at=`,
which the linter flags and the benchmark rejects; a published figure contains
no millimetres.

Address resolution is a dependency graph evaluated in one pass; a cycle is
the coded error `[TKZ-ADDR-CYCLE]`, printed with the cycle.

Open legs are policy, not objects. An unbonded typed port renders as a stub
in the direction of its face; a wire endpoint may be `open`, with a direction
when the end is to sit on the picture margin and without one when it takes
its place from the route (§5). Circle frames accept only the station-based
cardinal directions `n`, `e`, `s`, and `w`; diagonal circle opens are rejected
with `[TKZ-CIRCLE-OPEN-DIRECTION]` until a station-local or geodesic diagonal
construction is part of the language. There are no placeholder atoms.
<!-- Consumers of the open-end policy: every former tenkzfree body; e.g.
     rmp-ii-triangle-network, rmp-ii-mpo-sheet, rmp-iii-b-braid-one. -->

A side that exposes indices says so. The four side words default to `none`,
so a picture that states no policy draws no side leg and carries the empty
boundary signature on those sides; `west=open`, or `boundary=open` for the
pair, is what mints the legs and puts them in the signature. This follows
from open ink being declared content (§13): the frame's grid is a coordinate
system that places atoms, not a claim that every rim cell owns a dangling
index, and a circuit or a single-atom picture would collect nonsense legs
under any other reading. `none` is the explicit spelling of the default and
changes nothing; the 0.7 grid dialect, whose pictures drew their west and
east stubs unbidden and sealed them with this word, is deleted, and its
reading died with it.

## 4. Frames

A frame assigns each address a point and a pair of axes. The alphabet closes
to three words with no parameters — `flat`, `plane`, `circle`. For `flat` and
`plane` the axes are the frame's linear part and are the same everywhere; for
`circle` they are the tangent and the outward radius and they vary by
station. An address on a carrier — a wire, a leg, a hull — takes the
carrier's axes.

A plane has one further direction. Its two local axes lie in the projected
sheet; its physical axis points vertically on the page and belongs to the
frame itself. Thus `physical=up` leaves a site along that third axis, whereas
`ports={90:physical}` still means the in-plane north face. The two statements
are deliberately different. A plane tensor with four virtual faces and one
physical face is therefore written with four numeric ports and the physical
policy; no fifth angle compensates for the projection.

The numeric page angle and the general matrix retire together, and the
transposed projection with them. Of the four rotation consumers the contract
named, one is a carrier orientation, two are projections, and the fourth's
own note records the turn as this package's defect rather than the source's
demand. A degree is the angular millimetre, and a published figure contains
no millimetres.

Ink the frame measures lies in the frame; ink the frame only places stays
upright. Skins, contours and wires are measured; label text is placed and
never turns. Orientation is a consequence of where a record sits and is never
an authored quantity: a port's page direction is its local direction
transported through its carrier's basis. Labels use that direction for
placement while their text remains upright, so the type check and the
boundary signature are computed in the axes the ports actually point along.
Contraction is unaffected —
turning an atom changes no bond, only which way its faces look. Under a flat
frame the local axes are the global axes, so the flat corpus resolves
unchanged.

**The basis.** A frame takes a subkey naming what each cell carries:

```
frame={flat, basis={<row kind> at (<east q>,<north q>), ...}}
```

Members are drawn from the row alphabet. Each integer pair is an eastward,
then northward offset in quarter pitches; negative values point west or
south. Member indices are one-based in declaration order. Thus `(r,c)`
selects every member of a cell, while `(r,c,k)` selects member `k`. Equal
offsets remain distinct members: coordinate coincidence neither identifies
records nor creates an edge.

The frame evaluates basis spacing in page space. Over the declared cell
window, it compares every unordered pair of distinct declared member families
under each live cell translation, using their centres and default-bead
silhouettes after the complete frame map. A translation is live only when two
distinct member records survive population at that displacement: a whole-cell
authored atom suppresses that cell's member sites, while a member-addressed
replacement remains a member record. A spanning member replacement contributes
its canonical anchor once, not an alias at every claimed cell. Each silhouette
is the transformed nominal bead body plus its audited page-space half-stroke.
For each candidate, the required
centre separation is the support of both silhouettes on the centre bearing
plus `daylight`; an exact coincidence uses the maximum affine body support,
the two half-strokes, and `daylight`. The candidate with the smallest
separation-minus-requirement margin is reported. Candidates are visited in
ascending `(member-a, member-b, dr, dc)` order, and equal margins retain the
first candidate. A negative margin emits `basis-spacing`. This support test is
conservative under shear: a quiet result
guarantees the named daylight on the centre bearing. In the event, `dist` is
the centre separation and `floor` is its support requirement (directional
except at exact coincidence), each displayed to six decimals. `margin` is the
raw separation minus requirement, displayed independently to nine decimals.
All three are in pitch units; `dr` and `dc` are member B's cell minus member
A's cell. The diagnostic does not move a member, identify two records, or
create an edge. Thus interleaving is one complete-basis check, not a
plane-specific parameter.

A frame with no explicit basis retains the existing single site at the
origin, so existing pictures are unchanged. Frame population creates one
atom per cell per declared member, and the model records both the cell and
member index. Offsets declare placement only. They never infer an edge:
multi-member bases use `bonds=none`, and their intra-cell and inter-cell
connections are ordinary declared wires. Cell-level `trace=`, `open=`,
physical, and side policies are rejected for such a basis because they do
not identify a member. A bilayer is consequently one frame with two basis
members and explicit intra-cell pairing wires; nesting cannot collapse it
into two unrelated frames.

An intra-cell pairing wire carries a type neither of its ends can state. A
member address names a lattice place, and a place is not a port. The type
belongs to the pairing, and the frame already knows which direction is
physical: on a plane, a wire joining two different members of one cell, both
of them declared `ket`, `op`, or `bra`, is that site's physical index — the
ket-bra pairing that a partial trace or a double-layer expectation value sums
over. It is recorded physical and strokes as the bond it already was. A `wire`
member carries a virtual index beside the bond and pairs with nothing, and the
same closure on a flat frame stays virtual, because only a plane declares the
transverse physical axis such a pairing follows. The rule reads a closed
pairing off the frame and the two row kinds exactly as `open up|down` reads an
open transverse leg off its direction word.

An authored atom at `(r,c,k)` replaces that member. An authored atom at
`(r,c)` replaces the whole populated cell, so every member address in that
cell resolves to the authored record rather than creating coincident
population underneath it. Member indices are strictly one-based.

In the current kernel stage an explicit `basis=` belongs to a picture-level
`flat` or `plane` frame. Group-local, atom-local, and circular bases are
rejected with `TKZ-FRAME-*` diagnostics until those carriers have a declared
composition or tangent-offset contract.

**One clause travels with the circle frame and only with it:** adjacent
stations are one pitch apart. That fixes a radius the contract otherwise
leaves unstated — for four stations it gives `pitch` over root two, about
seven tenths, which is what the authors wrote. It must not be generalized: in
the projected plane the receding row is foreshortened by construction, and
that foreshortening is what the plane's ratios are.

The full `frame=` contract acts at picture, group, and atom scope. The current
kernel stage exposes carrier words at picture and group scope; atom-local
frames remain tracked work. `\tngroup` transforms a sub-diagram as one
object: its records keep their names, its boundary signature transforms with
it, and the transform has its own model record — the audit compares networks,
never silhouettes.

Consumers, carrier axes: `rmp-iii-a-pulling-through`, `rmp-iii-a-mpo-action`,
`rmp-iii-a-ghz-tensor`, `rmp-workbench-ii-peps-gauge-old`.
Consumers, circle pitch: `rmp-ii-triangle-network`, `rmp-iii-a-ground-space-1d`,
`rmp-ii-idempotent`, `rmp-workbench-iii-eq51`.
Consumers, basis: `rmp-workbench-iii-cluster-state`, `rmp-app-czx-state`,
`rmp-iii-a-ghz-state`, `rmp-iii-b-condensation`.
Consumers, transverse pairing: `rmp-ii-peps-marginal`,
`rmp-iii-b-condensation`.

## 5. Wires

A wire is one typed index line. `kind=index` is a bond: two typed-port
endpoints, a straight route, and the type check `[TKZ-PORT-TYPE]` — a virtual
port never meets a physical one. A bare cell or grid endpoint is therefore an
implicit virtual endpoint, not an untyped escape hatch. Matching declarations
may refine a grid bond to physical. Endpoints generated by a policy that fixes
a type retain that requirement and cannot be refined. Two physical endpoints
produce the physical-leg stroke, while two virtual endpoints produce the bond
stroke. Those two strokes are one ink once both ends are consumed: a contracted
index carries its type in the record and not in its line, so no render tells a
physical contraction from a virtual one. Type reaches the page only on an open
leg, whose stub answers to it, and reaches a reviewer only through the record
stream and the boundary signature. Two ends that state no type still leave one
contraction typed: the pairing between two layers of one stacked site, which
Section 4 types from the frame and the two row kinds rather than from its ends.
`kind=pairing` is a declared skin's curved own-port route: it belongs to one
host, remains addressable by arclength, and its declared list order controls
the over-glyph ink and supplies the crossing order between pairings of that
same skin. `kind=string` travels: it carries routes, crossings, winding, and
beads, and its endpoints may be any address, cells included. The distinction
is a field of the record; all three are one record class.

**The offset hull.** The offset hull of a selection is the support hull of
the selected records' silhouettes, measured in the frame's own axes, expanded
by `daylight`, turned with radius `corner`. It is one construction with five
consumers, each reaching it through a key it already carries: a mark strokes
it as an `enclosure`, a mark strokes the arc of it on the label's side as a
`bracket`, a wire travels it as `route={<side> of <selector>}`, an atom
addressed `on <wire> t` stands on it and reads its axes, and a leg measures
its reach against it.

**Routes.** `route={<side> of <selector>}` sends a wire at one standing
offset from the hull of that selection, on the named side, entering and
leaving where that side's arc ends; the side is a compass word or `all`. It
crosses exactly those wires that leave the selection through a face on that
side, each once, in hull order. The author's claim is that this string passes
on this side of these records; the crossing set is the answer to that claim,
computed and never chosen. An empty crossing set is legal and meaningful. A
derived crossing enters the model with every field a declared one carries, so
an audit cannot tell the two apart.

An addressed all-side route joins its ends to a rounded hull polyline. Hull
faces remain straight and only the turns consume the shared `corner` metric,
so a boundary wire leaving through a traversed face meets the route exactly
once; changing an endpoint does not bow the face away from that crossing.

When an all-side route has addressed ends, the run begins and ends at the
turns of the measured hull nearest those ends. Address dependencies are
resolved first: an end such as `on carrier 0.25` therefore uses the carrier's
actual saved path. The same resolved turns determine both the drawn run and
its ordered crossing set. Coordinates cross into the route engine at TeX's
native scaled-point precision; policy classifies that same representable
point, with no separate decimal rounding. Smaller offsets are coincident.
An arbitrary addressed end must lie outside the selected hull: otherwise its
connector and the hull run can meet one boundary wire twice, contradicting
the route's single-crossing contract. A typed port belonging to the selection
is the exception, since it is the route's own endpoint rather than a boundary
wire to cross. The daylight clearance between the selected silhouettes and
the offset route remains outside the hull and is a valid place for an end.
An inside arbitrary end is `TKZ-ROUTE-END-INSIDE`.

Two rules travel with the hull, and they are doctrine rather than elements.
**Concentric order:** curves over the same selection are separated by one
clearance, outward in declaration order for routes, inward by containment for
contours, ties broken by declaration order. **Reach:** a reach is the maximum
over everything declared to meet it, so a leg crossed by a route is as long
as the outermost route crossing it plus one clearance, and a crossing the
author claimed always exists.

The direction of an open end is optional and takes its place from the route.
With no direction the end lies on the route, one clearance past the outermost
wire it crosses; with a direction it lies on the picture margin. An open end
is an index cut by the picture's frame and is boundary data the equation
audit matches panel to panel.

**Crossings are declared, never emergent.** `cross={over at <address>}` or
`under at <address>` names the crossing and its order; rendering gaps the
under strand by the `crossgap` metric ratio. A crossing may name any wire of
the picture, including the wire being declared; references resolve at
validation, not at reading order. A declared crossing whose paths do not
intersect is `[TKZ-CROSS-NOT-FOUND]`. An undeclared geometric intersection
of two wires is `[TKZ-CROSS-UNDECLARED]`. Both are hard errors: over/under
order is mathematical content and the renderer never guesses it. Pairings in
one skin inherit the order of their declared list. Crossings outside the skin
belong to an atom instance, not to the reusable skin declaration:
`pairing cross={1: under at crossing of self and pairing 1 of B}`.
The leading integer selects this atom's generated pairing. Here `B` is an
author-named atom; `pairing 1 of B` names its first generated pairing without
exposing the renderer's internal record id. Repeat the indexed item, separated
by commas, when one pairing has several declared crossings.
<!-- Consumers: rmp-iii-b-braid-one/-two/-three/-four,
     rmp-iii-b-self-braiding, rmp-iii-a-spt-mpo,
     rmp-iii-b-r-tensor-left/-right. -->

**Winding.** `wind={p,q}` records the homotopy class of a closed string on a
frame with traced sides; the rendered path realizes that class or errors.
The contractible `{0,0}` class is rejected in favor of an ordinary `closed`
string. `via=` belongs to waypoint-routed closed strings and is mutually
exclusive with `wind=`.
<!-- Consumers: rmp-iii-a-torus-one, rmp-workbench-iii-eq59. -->

**Detours.** `around=<address list>` routes the wire past the named records
against their measured silhouettes plus daylight — the pulling-through
idiom, and the hull route with the side left to the engine.
<!-- Consumers: rmp-iii-a-pulling-through, rmp-iii-a-g-injective-projector,
     rmp-workbench-iii-g-injective-pull, rmp-workbench-iii-mpo-injective-white. -->

**Closures.** Side policy words and selector keys normalize to wires whose
`origin` field records the policy that generated them (`origin=trace`,
`origin=cup`, ...). Closure is not a separate record class. A generated
closure wire carries a canonical name — `wrap-1` for row 1's trace return,
`cup-1-2` for the cup joining rows 1 and 2. When both opposite sides carry
cups, names are side-qualified (`cup-west-1-2`, `cup-east-1-2`) so every
derived wire remains addressable as one named record. Generated legs take
canonical names on the same rule and are named records like any other, which
is why no address production is needed to reach one. That holds of the legs
the `physical=` picture policy grows as well: each is a wire record named
`leg-<face>-<row>-<col>`, the name the crossing grammar already spells, so a
row whose legs are stated once by the policy loses nothing a per-atom port
list would give. Beads and labels attach to
closures by the ordinary address grammar. A leg has one model end and one
free tip, so `on <leg> t` is read along the leg the picture draws, from the
end the wire is written from to the end it is written to. A closed chain that renders open
is impossible by construction: the closure IS a wire record, and every wire
is drawn or errors.

A closure clears the selection it closes, so its depth is a consequence of
its two ends: a trace closing a whole row clears the whole row and comes back
as the long return the authors draw, and a cup joining two vertically
adjacent ports at one column clears one column and comes back as the shallow
cap they draw. Nobody chooses which.

**Beads.** A small tensor on a string is an atom whose address is
`on <wire> t`. There is no bead vocabulary.

**Stroke.** The stroke follows the type the port already carries: two named
ratios in the theme, one virtual and one physical, selected by the index and
never by the author. A theme may set them equal. Bundling is a claim about
the boundary signature, which the audit already carries (§7), and it owes no
ink of its own.
<!-- Zero authored consumers in the corpus: no author ever wrote a stroke
     weight, and of the six targets recorded with a wrong stroke, four are
     recorded faithful, two of them annotated better than the authors. A
     deletion needs no consumers; what it needs is that nothing is lost. -->

## 6. Marks

A mark is a non-topological record on a target: an `enclosure` stroking the
offset hull of a selection, a `bracket` stroking the arc of that hull on the
label's side, or a free `label`. A bracket that names no side speaks from the
south, where the authors draw a brace under a span. A mark target is one
selector (§3), and both hull forms read it through the same grammar every
other key does, so a cell range corners a bracket as it corners a contour.
Marks never own topology; deleting every mark changes no contraction.

Three forms retired. The shaded band never differed from an enclosure except
in the shape of its selection. The lower brace merged with the upper into one
bracket, because the side a bracket speaks from is the side its label sits on
and every mark carries a label placement already. The cut has no consumer in
the benchmark or the blueprint and fails tenure outright, taking its sugar
row with it.

`species=` binds the mark's ink to a declared semantic identity; `tint`
lays that ink over the paper the contour encloses. Nesting needs no key: containment between
two selections is a fact the model holds, and concentric order (§5) steps the
inner contour in by one clearance.

**Label stations.** Every label belongs to a host — a glyph, a wire, a place
on a wire, a selection — and inherits from it a ranked ring of stations: the
compass points at one clearance, then the diagonals, then the same ring one
step out. The first station whose box meets no ink already placed and no
label already placed wins, where ink means the measured silhouettes the
geometry stage computes anyway, legs and stubs included. A named placement is
honoured, and honouring it grows the host's contour on that side rather than
putting the label on ink; a pinned label that still collides is refused, as
an undeclared crossing is refused, and for the same reason. `auto` is the
face whose outward support leaves the widest clear band. The model records
whether a label was set inside its glyph or beside it, and that bit says the
figure contains a name that outgrew its class.
<!-- Consumers, enclosure: rmp-ii-blocking, rmp-app-czx-state,
     rmp-iii-a-ghz-state, rmp-iii-b-dyon, rmp-iv-ground-space-2d,
     rmp-ii-boundary-region. Stations: rmp-ii-triangle-network,
     rmp-ii-mpo-sheet, rmp-ii-mpu-splitting. Species on marks: rmp-iii-b-dyon,
     rmp-ii-boundary-lasso, rmp-ii-mpo-injectivity-ring. -->

## 7. Equations: `tenkzeq`

`tenkzeq` composes whole pictures around the mathematics between them and is
the audit scope. Its body is rows separated by line breaks, and each row is
an alternating sequence of terms and joiners. A term is a picture or
mathematics. A joiner is the mathematics between two terms and carries one of
three classes: **relation**, **sum**, **product**. Only the product list is
the language's own datum — juxtaposition and the product signs; relation and
sum are read from the class the mathematics already has.

1. **One metric context.** All panels share the pitch and the size-class
   table. A glyph's extent is a function of two declared quantities and
   nothing else: its size class, and the number of port slots on each pair of
   opposite faces. The horizontal extent is the class reference times the
   greater of one and the slots on the vertical faces; the vertical extent
   likewise. A round skin takes the reference as its diameter, a box as its
   side, a triangle as its circumscribing square, so an operator and its
   inverse match across skins. This holds in every scope and not only inside
   an equation, and a label that does not fit is not accommodated by growing
   the glyph — it goes to the station rule (§6).
2. **Math-style sensing.** Display, text, and script contexts choose the
   density profile; there is no manual compact or inline flag. An inline
   picture inherits the sensing.
3. **Axis alignment.** Panels align on the declared wire axis (`align=`).
4. **The audit follows the joiner.** Every term has a boundary signature;
   mathematics has none, and its signature is unknown. A relation requires
   equal signatures and ends the term. A sum requires equal signatures and
   continues it. A product contracts the facing cut: every index cut on the
   left factor's east frame continues as an index cut on the right factor's
   west frame — the same type and weight, an outgoing index continuing as an
   incoming one — and each such pair is one index, internal to the composite
   term, which exposes nothing; the remaining entries of both factors
   concatenate. The facing cuts must cancel completely, and an empty facing
   cut is the plain juxtaposition of a scalar or a tensor factor, whose
   signatures concatenate whole. A product group of panels is therefore one
   composite side of the relations around it, its signature the factors'
   outer signature with the contracted interfaces cancelled.
   Any joiner with an unknown operand yields an unknown result, and the
   comparison is recorded as unperformed rather than as passed — which is
   what an elision between two panels asserts, and needs no spelling of its
   own. A mismatch is `[TKZ-EQ-SIGNATURE]`, printing both signatures. A
   relation with an undepicted side is legal in a draft and refused under
   strict, which the benchmark sets. The audit rule is derived from the
   joiner's class and is not the author's to configure; there is no audit
   key, and so no undocumented off switch either.
5. **Coefficients and summations need no key.** A scalar coefficient is a
   term of empty signature; juxtaposition is a product; concatenating an
   empty signature leaves the panel's boundary as it was. A summation sign is
   likewise mathematics, set west of the panel on the shared axis, its limits
   smashed against a panel that is always the taller.
<!-- Consumers: rmp-ii-mpu-brickwork, rmp-iii-a-coproduct,
     rmp-workbench-iii-eq59-now, rmp-ii-mpu-unitarity,
     rmp-ii-tangent-projector, rmp-workbench-ii-fine-graining.
     Product joiner: rmp-ii-mpu-blocking. -->

## 8. Declarations and the extension gate

`\tndeclare{atom}{\tnprojector}{skin=box, ports={180:virtual, 0:virtual, 90:physical}}`
creates a one-label atom command. Ports live at any angle in the atom's own
axes, slotted, labelled, any mix of `virtual` and `physical` (§2.3 gives the
port grammar); every stock shape already
carries a boundary anchor for an arbitrary direction, so a leg at 50 or −120
degrees attaches exactly on the boundary of a disc, a box, a rounded box or a
triangle with nothing declared. A declared skin
(`\tndeclare{skin}{window}{base=box, pairings={...}}`) is ports plus
pairings; a pairing is a WIRE whose endpoints are the skin's own ports.
Skins contain no free ink: an element that is not a port or a pairing of
ports is not declarable. A declared species
(`\tndeclare{species}{flux}{hue=source:red}`) binds semantic ink;
`hue=source:*` values reproduce a cited paper's palette instead of the house
cycle.

### Declaration keys (3)

| Key | Type | Values | Used by |
|---|---|---|---|
| `hue=` | hue-source | house cycle name or `source:<color>` | species |
| `base=` | identifier | a declared or default skin | skin |
| `pairings=` | port-pair-list | `{n@1 > e@1 : R, ...}` own-port pairs | skin |

The standard prelude declares — as declarations, not kernel rows — the skins
`pill`, `mpo`, `window`, `boundary`, the fuse atom, and the species
`operator`, `marked`, `extra`, `passive`.

The extension gate is unchanged from 0.6: a new key needs three manifested
benchmark consumers named by target id; a new command needs a new record
class; every accepted capability provides a registry row, a teaching example
under fifteen lines, a coded diagnostic, a negative test, and a
cross-review. New in 1.0: the kernel ledger is budgeted (§11) — an accepted
kernel row displaces one or cites the gate exception in the same change.

## 9. The sugar ledger

Sugar is a registry row whose `sugar(<expansion>)` status states its kernel
expansion. The linter rewrites any source to pure kernel; a test class
proves sugar and expansion emit identical events; `\tnset{strict}` rejects
sugar entirely. The model and the event stream contain only kernel records.
Teaching text uses sugar freely. Twenty-five rows:

Write a physical label on its typed port, once:

```tex
\begin{tenkz}[rows={wire}, cols=1, bonds=none, physical=up]
  \tn[name=A, ports={90:physical:$i$}]{A}
\end{tenkz}
```

Here, in the flat frame, the descriptor creates the standard `port-open` leg
and suppresses the otherwise generated policy leg. If an authored wire
consumes `A.90`, the same descriptor labels that wire in the final port-label
pass. With no descriptor, the policy still refines a consumed `A.90` endpoint
to physical, but carries no label of its own. In a plane frame the policy leg
is the independent transverse axis described in Section 4; no numeric
`ports=` face aliases or consumes it.

Here *eligible* has a precise meaning. The atom must occupy a frame cell
`(r,c)` or a basis member `(r,c,k)`, and it must be neither a sealed void nor
a child of a cluster. A relative point, a midpoint, a point on a wire, and a
crossing are geometric constructions rather than further cells, so the
picture policy gives them no physical index. Such an atom may still declare
an independent physical port with `ports=` when the mathematics requires one.

The policy pays on a uniform row, where two or more sites share the leg: one
declaration replaces a port on every eligible atom, and a rare exception
refuses it with `physical=none`. It costs on a sparse row, where a single
site among many carries the index: every other site must then refuse the
policy, and the refusals outrun the port list they replaced. Write the
policy for the shared leg; write the ports for the lone one.

| Sugar | Expands to |
|---|---|
| `sandwich` | `rows={ket,op,bra}` |
| `physical=up\|down\|updown\|none` | expander: declares each frame-cell atom's outward face physical, one port per face slot — a `wide=k` atom answers with `k` legs, one per spanned cell, exactly as the authored `90@1..@k` port list; geometric overlay atoms are excluded; in a plane this is the independent page-transverse axis, not a numeric in-plane face |
| `boundary=open\|none` | `west=<w>, east=<w>` |
| `boundary=periodic`, `periodic` | `west=trace, east=trace` |
| `west={cup=$m$}` (any side) | side `cup` + `\tn[skin=ring, at=on <cup wire> 0.5]{m}` |
| `west={tail=$m$}` (any side) | side `open` + boundary-skin atom on the stub wire |
| `west label=$m$` etc., `bond label=` | `\tnmark[form=label]{<generated wire>}{m}` |
| `lattice={RxC}` | R wire rows (`rows={wire,...,wire}`), `cols=C` |
| `ring=N` | one wire row, `cols=N, frame=circle, west=trace, east=trace` |
| `surface=torus` | `west=trace, east=trace, north=trace, south=trace` |
| `planes` | `frame={plane, basis={ket at (0,0), bra at (2,2)}}` |
| `cluster={RxC}` | `frame={flat, basis={<R×C members at quarter pitch>}}`; members are ordinary addresses `(r,c,k)` |
| `\tnpic[k]{body}` | `\tn`-scope picture term: `\begin{tenkz}[k] body \end{tenkz}` under math-style sensing |
| `\tnX{m}` | `\tn[skin=ring]{m}` |
| `\tn*[k]{m}` | `\tn[conjugate, k]{m}` |
| `\tnbond[k]{a}{b}` | `\tnwire[kind=index, k]{a}{b}` |
| `\tnstring[k]{verbs}` | `\tnwire[kind=string, ...]` — verb table below |
| `\tnfuse[k]{m}` | `\tn[skin=tri, wires=2, k]{m}` — the prelude fuse atom, its split side bonded by the frame; authored keys follow the preset, so `skin=`, `wires=`, `ports=` in `k` override it; tenure: 0 benchmark consumers, held by 5 blueprint figures |
| `\tnspan[form]{k}{m}` | `\tnmark[form=...]{(r,c) .. (r,c+k-1)}{m}` |
| `\tndots` | `\tn[skin=dots]{}` (elision bit read by the audit) |
| `\tnskip` | `\tn[void=open]{}` |
| `\tntree[k]{word}` | expander: fuse atoms + wires from the word |
| `up at= down at= west at= east at=`, `combined=`, `span=` | `ports=` angle/slot grammar; `span=` folds into `wires=` |
| `role=` | `species=` (the four prelude species) |
| `\tndeclareatom` | `\tndeclare{atom}` |

Two rows are expanders: their expansion is a rule over the picture, not a
token substitution — `physical=` adds a port per wire-row atom, `\tntree`
builds atoms and wires from the word. Expander output is still pure kernel
records, and the same test class verifies it.
An expanded physical port contributes a boundary leg only while it is
unconsumed. If a wire contracts that face, the wire owns the port and its
label; neither a second leg nor a boundary-signature entry remains.

String verb table: `through a` → `route={all of a}` entering and leaving
tangent ports · `loop a` → `closed, route={all of a}` · `over w at p` /
`under w at p` → `cross=` · `wind {p,q}` → `wind=` · `bead{m}` → an atom
`on <wire> t` · `join s at p` → an endpoint `on s p`.

Sugar tenure: a sugar row needs three distinct consumers among the benchmark
cases and blueprint figures; a row below tenure is a mandatory agenda item
at the next shrink session (§11).

## 10. Tombstones

Deleted spellings stay in the registry as tombstones; the linter rejects
them forever with the migration hint. No deleted spelling is ever reused.

The frozen source corpus still passes through the compatibility renderers
while its figures migrate. Their executable `object` ledger may therefore
repair a source-facing deficiency without enlarging the canonical kernel:
`\tnsite` and `\tnput` accept a local `size=s|m|l`, with `m` as the
compatibility default, and `\tnput[circle]` supplies a plain inscribed circle.
These paths do not inherit the canonical picture size. Their inscribed labels
retain the compatibility renderer's historical content-sized outline; this
is not the fixed two-axis atom contract of §7.

| Dead spelling | Migration |
|---|---|
| `tenkzfree`, `tenkzcd`, `tenkzlattice`, `tenkzplanes` | `tenkz` with `lattice=`/`planes` sugar; fusion trees are `\tntree`; commutative diagrams belong to tikz-cd, outside this language |
| `\tnput` | `\tn[at=<address>]` |
| `\tnjoin`, `\tnedge`, `\tnarrow` | `\tnwire`; a directed index is `\tnwire[dir=to]` |
| `\tnsite` | `\tn[at=(r,c)]` |
| `\tnghost{m}` | addresses reference empty cells directly |
| boundary-skin placeholder atoms | open-end policy (§3) |
| `out=`, `in=` | `route=arc`, which leaves and enters along its ends' faces |
| `route=hv`, `route=vh`, `route=curve` | `route=orth`, `route=arc` |
| `drop`, `hug` routes | `route=orth` and `route={<side> of <selector>}` |
| `label shift=` | `label pos=`, a station on the host's ring (§6) |
| `col vector= row vector= sheet vector=` | `frame=plane`; a sheet is a basis member of one frame (§4) |
| `maps`, `polygon=`, `radius=` | died with `tenkzcd` |
| `tensor style=` | `skin=` |
| `fused` | nothing: the port type decides the stroke (§5) |
| connection `none` flag | omit the record; `void=sealed` removes a site |
| `wiring=` micro-DSL | skin pairings are wires (§8) |
| `cluster` as a skin | `cluster={RxC}` basis sugar — sub-spins must be addressable |
| `enclosure` as a skin | `\tnmark[form=enclosure]`; a boundary operator is a wide atom (§12.7) |
| `poly=k` | permanently dead: the consumers arrived and they want angles, not corners |
| `weight=string` | `kind=string` |
| `trace style=racetrack` | closure depth follows the selection the closure clears (§5) |
| `inline`, `compact` | math-style sensing + `size=` |
| `via=` | `route={<side> of <selector>}`: every waypoint in this contract's own sketches was a side of a selection |
| `bend=` | nothing: an arc leaves and enters along its ends' faces |
| `weight=` | nothing: the port type decides the stroke, and bundling is a claim the audit already carries |
| `nudge=` (atom and mark) | a basis member `(r,c,k)`, an ordinary address, or the label station rule (§6) |
| `inset=` | nothing: concentric order is doctrine on the hull (§5) |
| `slot=` | `species=`, which atoms and wires already carry |
| `up=`, `down=` | `ports=`: the outward physical face is the row's own normal |
| `check=` | nothing: the audit follows the joiner class (§7) |
| `conjugate` flag | nothing: duality is the wire's `dir=` (§2.4), and a conjugate overline is label mathematics |
| `form=cut`, `form=band`, `form=brace-below`, `form=prose`, `\tncut`, `\tnregion`, `\tnprose` | `form=enclosure`, `form=bracket`, or a term of unknown signature (§6, §7) |
| `frame=vertical`, `frame=rotate=<deg>`, frame matrices | `flat`, `plane`, `circle`; orientation is a consequence of where a record sits (§4) |
| `leg <face> of <cell>`, `<compass> outside` | a generated leg is a named record; an open end takes its place from the route (§5) |
| `(r,c)-(r,c)` cell ranges | `(r,c) .. (r,c)` — a hyphen cannot be told from a generated name |
| `\tnpic` as a command | the sugar row `\tnpic` over the picture environment (§9) |
| aliases `chain axis`, `legs at`, `rows`→span, `boundary legs`, `label at` | kernel spellings above |

## 11. The shrink gate

The language may not grow monotonically. Six meters are recorded in
`tests/tenkz/census-baseline.json`, created at Session 0 together with this
contract; from then on CI compares actuals per PR, and every change to a
meter touches the baseline file in the same diff.

| Meter | Measures | Ratchet |
|---|---|---|
| M1 | registry census split kernel / sugar / alias | kernel non-increasing except gate exception; total non-increasing between sessions |
| M2 | parser-path count | increase requires `Extension-gate: #NNNN` |
| M3 | escape usage (`debug at=` and the raw-geometry rows) in the corpus | non-increasing; each occurrence names a grammar gap |
| M4 | mean lines per benchmark figure, frozen denominator | non-increasing — the fidelity meter |
| M5 | alias count + sunsets | near zero at the 1.0 freeze |
| M6 | overload count | never rises |

Two ledgers via the registry status field: `kernel` rows are budgeted
one-in-one-out, the extension gate being the only exception path;
`sugar(<expansion>)` rows pass the expansion-closure check (every expansion
token is kernel) and hold tenure at three consumers; `alias` rows carry
sunsets; `escape` rows are counted by M3. Tombstones close the loop.

The shrink session runs jointly with the simplification gate (#4158) at
every milestone close, from inputs generated by `scripts/tenkz_shrink.py`:
census diff, consumer counts, always-co-occurring key pairs,
single-consumer value types, sugar-shaped commands, escape usage. Three
questions: which two elements are one; whose consumers could another
element serve; which sugar or alias lapsed. Output: a dated append-only
section of `docs/tenkz/SHRINK.md` with one verdict per flag. The session
passes only if the census strictly decreased or every flag carries a written
verdict; a keep-because verdict that expires twice dies or becomes doctrine.

**The metric registry is a ledger too**, and it is the one the meters do not
count. A ratio is an element: it is named, it is spelled, it is inherited by
every theme, and it is as expensive to remove after a release as a key. It
carries no meter of its own — the tooling stays as it is — and instead every
shrink session states its net movement in prose, with the same standard of
evidence as the key ledgers. The standing rule that follows from the nine
amendments: a quantity that is already a column of the size-class table, or
already a named ratio, is not minted a second time under a new name.

## 12. Spelling sketches

The seven figures the 0.7 language failed worst, **in kernel form**: every
token below is admitted by the tables above, and a sketch that names a
spelling those tables do not carry is a defect in the sketch. No millimetres
appear; `% sugar:` marks each sugar spelling with its expansion.

Kernel form is what settles the one question these sketches could otherwise
answer two ways. A face is an angle and so is a label placement (§2.3, §3),
so both are written below as angles and never as letters — `label pos=45`,
`label pos=180`, `B.270`, `R.90@1`. The only compass words left are the side
of a hull a route travels (`route={s of ...}`), which belongs to the route
family's own grammar, and the four boundary key names (`west=`, `east=`,
`north=`, `south=`), which are key names and not values at all. That is the
one-token-one-meaning rule doing its work rather than being suspended for the
examples.

An author need not write the angle. The four compass words survive as a sugar
spelling of the four right angles — `n` for 90, `e` for 0, `s` for 270, `w`
for 180 — covering faces and label placements alike, so every fixture in the
corpus keeps its spelling. That row arrives with the change that implements
angle-valued faces, and the sugar ledger moves from twenty-five to
twenty-six there rather than here, so the one arrival is counted once.

### 12.1 Braid (`rmp-iii-b-braid-one`)

```tex
\[\begin{tenkz}[rows={wire,wire}, cols=4, bonds=none]
  \tnwire[kind=string, species=left,  name=a, route={s of (2,2)}]{(1,1)}{(2,3)}
  \tnwire[kind=string, species=right, name=b, route={n of (2,3)},
          cross={under at crossing of a and b}]{(1,4)}{(2,2)}
  \tnmark[form=label, label pos=45]{crossing of a and b}{$R$}
\end{tenkz}\]
```

### 12.2 Torus with wound string (`rmp-iii-a-torus-one`)

```tex
\[\begin{tenkz}[lattice={3x3},          % sugar: rows={wire,wire,wire}, cols=3
              west=trace, east=trace, north=trace, south=trace]
  \tnwire[kind=string, species=flux, closed, wind={1,0},
          route={s of picture}]         % the homotopy class is recorded
\end{tenkz}\]
```

### 12.3 Pulling-through (`rmp-iii-a-pulling-through`)

```tex
\begin{tenkzeq}[size=m]
  \begin{tenkz}[rows={ket}, cols=3, physical=up]   % sugar: physical= adds the up ports
    \tnwire[kind=string, species=g,
            route={s of (1,1) .. (1,3)}]{open}{open}
  \end{tenkz}
  =
  \begin{tenkz}[rows={ket}, cols=3, physical=up]   % sugar: physical= adds the up ports
    \tnwire[kind=string, species=g, name=g,
            route={n of (1,1) .. (1,3)}]{open}{open}
  \end{tenkz}
\end{tenkzeq}
```

The second panel declares no crossing and needs none: the route crosses
exactly those legs that leave the selection northward, each once, in hull
order, and each derived crossing enters the model with every field a declared
one carries. The reach rule lengthens all three legs past the string, so the
crossings the author claimed all exist — which is the defect this sketch used
to carry, where two of the three legs stopped short and the crossing police
had nothing to refuse.

### 12.4 Two-shift MPU (`rmp-ii-mpu-two-shift`)

```tex
\[\begin{tenkz}[rows={wire,wire}, cols=4, bonds=none, west=trace, east=trace]
  \tnwire[kind=string, species=right, name=r1]{(1,1)}{(2,2)}
  \tnwire[kind=string, species=right, name=r2]{(1,3)}{(2,4)}
  \tnwire[kind=string, species=left, name=l1,
          cross={under at crossing of l1 and r1}]{(1,2)}{(2,1)}
  \tnwire[kind=string, species=left, name=l2,
          cross={under at crossing of l2 and r2}]{(1,4)}{(2,3)}
\end{tenkz}\]
```

### 12.5 CZX state (`rmp-app-czx-state`)

```tex
\[\begin{tenkz}[lattice={2x2}, bonds=none,   % sugar: rows={wire,wire}, cols=2
              frame={flat, basis={wire at (-1,1), wire at (1,1),
                                  wire at (-1,-1), wire at (1,-1)}}]
  % four members per cell; a member is the ordinary address (r,c,k)
  \tnmark[form=enclosure, species=marked]{{(1,1,4), (1,2,3), (2,1,2), (2,2,1)}}{$X$}
\end{tenkz}\]
```

### 12.6 Blocking (`rmp-ii-blocking` family)

```tex
\[\begin{tenkz}[rows={ket}, cols=4, physical=up]   % sugar: physical= adds the up ports
  \tn[ports={90:physical:$i_1$}]{A} & \tn[ports={90:physical:$i_2$}]{A}
  & \tn[skin=dots]{} & \tn[ports={90:physical:$i_L$}]{A}
  \tnmark[form=enclosure, label pos=180]{(1,1) .. (1,4)}{$A^{[L]}$}
\end{tenkz}\]
```

### 12.7 Enclosing operator with wrap (`rmp-iv-intersection-lhs-one`)

```tex
\[\begin{tenkz}[rows={wire,wire}, cols=4, bonds=none]
  \tn[at=(1,2), name=B]{B}   \tn[at=(1,3), name=C]{C}
  \tn[at=(2,2), skin=box, wide=2, wires=2, name=R]{R}  % the wide operator row
  \tnwire{B.270}{R.90@1}     \tnwire{C.270}{R.90@2}
  % B and C keep their upward ports unbonded: typed ports render their own stubs.
  \tnwire[kind=string, route={all of picture}]{R.0}{R.180}  % the wrap
\end{tenkz}\]
```

The wrap is one line for the first time, and it is the same construction the
enclosure strokes and the closure clears: an offset hull of a selection, here
the whole picture.

## 13. Grammar rules

1. One picture, one frame chain. Nesting is `\tngroup`.
2. Picture options declare topology and policy; they create no hidden atoms.
3. Body order may establish references; it never changes an earlier record.
   Crossing references resolve at validation (§5).
4. Topology measurement resolves hull routes and their address dependencies;
   validation then freezes the completed model before ink. The renderer never
   repairs, guesses, or silently drops requested ink. Unsupported ink is a
   coded hard error.
5. Open ink is declared content: the boundary signature is computed from
   port and wire records and written to the event stream.
6. Raw TikZ is not public syntax. Themes rebind ink and typography; they add
   no topology.
7. One concept, one canonical spelling; sugar is declared, expanded, and
   tested; tombstones never return.

## 14. Sign-off decisions

Decisions taken after the compression review, for explicit maintainer
confirmation at L1 acceptance:

1. **`dir=` wire key.** The compression review left directed virtual indices
   without a kernel spelling; `dir=to|from|none` fills the `\tnarrow`
   tombstone. `end=` is deleted in favor of positional `open <dir>`
   endpoints.
2. **Boundary operators are wide atoms.** The section-IV R operator is a
   `wide=` box ATOM (§12.7), not an enclosure mark — marks own no topology.
   This diverges from the plan's phrasing "enclosure mark + orth/around
   wires"; the enclosure mark keeps the blocking and region consumers (§6).
3. **`leg <face> of <cell>` address production — reversed 2026-07-25.** It
   was added so a string could name a leg to cross. With the hull route the
   crossing set is derived and no one names a leg, and a generated leg is a
   named record like any other closure wire, so the production leaves and the
   grammar returns to eight.
4. **Effectivity.** The 0.7 registry describes the current package until the
   kernel lands; the registry regeneration and the three Session-0 artifacts
   land with this contract's acceptance, and the census then enforces every
   count stated here. The retirements of 2026-07-25 are booked here and in
   `docs/tenkz/SHRINK.md`; the registry rows they retire move ledger when the
   parser rows move, in the change that implements each amendment.
5. **The tint-for-species exchange is deferred as a pair.** Retiring the
   mark's `slot=` and giving a mark the `species=` every other record carries
   is one exchange of net zero, and it is spelled in §2.5 above. It costs no
   key either way, so the registry books it in the change that adds the
   parser row rather than in two halves.
6. **The kernel side default is `none` — corrected 2026-08-06.** The key
   table above and the four `kernel-picture` registry rows read `open`,
   which was the 0.7 default copied into the kernel tier by hand: a grid
   picture does draw its west and east stubs unbidden and seals them with
   `boundary=none`, and neither is true under `\tenkzkernel`. Honouring the
   printed `open` was measured across the 130 benchmark targets and rejected:
   thirty stop compiling on a doubly consumed boundary port, forty-three grow
   legs, and forty move their boundary signature. The reading the contract
   supports is the one the kernel already implements — open ink is declared
   content (§13), so a side that exposes indices says so. The registry rows,
   the key table, and §3 now say that, and `none` is the explicit spelling of
   the kernel default rather than a seal.
7. **A void site draws no glyph — corrected 2026-08-07.** The skin default
   read `dot` for every atom, so `\tn[void=open]{}` drew a site
   indistinguishable from a real one and a sealed void drew a free-floating
   dot with no bonds. A hole means an absent site: both void words now
   default the skin to `none`, and the record half of the contract — the
   bonds bridging an open hole, its surviving physical index, the boundary
   signature — is untouched. A declared `skin=` still draws, and the
   `\tnskip` ledger row stays one key long and is glyph-faithful as printed.
   The default inherits the whole `skin=none` reading: a void's authored
   label is suppressed with its glyph, so a labelled anchor that must stay
   visible declares a skin.
