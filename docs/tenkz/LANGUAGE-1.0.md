# The tenkz language, version 1.0

The tenkz 1.0 kernel — record classes, environments, commands, keys,
alphabets, and ledgers — is fixed by this contract. The executable registry
(`tex/tenkz/tenkz-language-registry.tex`) is regenerated to the inventory
below in the change that lands the kernel; until then the 0.7 registry and
`LANGUAGE.md` describe the current package. The Session-0 artifacts —
`tests/tenkz/census-baseline.json`, `scripts/tenkz_shrink.py`,
`docs/tenkz/SHRINK.md` — land with this contract's acceptance. Once the
kernel lands, a spelling absent from the registry does not exist, and every
table below is checked against the registry by the census.

<!-- Status: L1 draft for maintainer sign-off. Supersedes LANGUAGE.md (0.7).
     Kernel follows the Session-0 compression review; where the earlier D1-D8
     draft and the compression review differ, the compression review wins.
     Open sign-off decisions are collected in §14. -->

## 1. The sentence model

> A picture draws one typed tensor network in one frame. Frames — chain,
> lattice, circle; flat, rotated, sheared, projected; at picture, group, or
> atom position — turn names into places, so an author writes addresses and
> never measures. The body declares atoms, wires, and marks. Every index ends
> in exactly one of a bond, a closure, or a declared open leg. Equations
> compose whole pictures under one shared metric and must expose equal
> boundaries. The language grows by declaration, never by drawing.

## 2. The kernel

Four record classes, two environments, seven commands.

| Record class | Declared by | Holds |
|---|---|---|
| PICTURE | `tenkz`, `tenkzeq`, `\tngroup`, `\tnpic` | frame, side policy, cell sets, metric context |
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
| `\tnmark[keys]{target}{label}` | target is a cell set, an address set, or a wire place (§6) | MARK |
| `\tngroup[keys]{body}` | scoped sub-frame; names inside stay addressable outside | PICTURE |
| `\tnpic[keys]{body}` | one inline picture as a mathematical atom | PICTURE |
| `\tnset{keys}` | document or group policy | — |
| `\tndeclare{atom\|skin\|species}{name}{keys}` | the one extension door | — |

A wire end is an address or `open <dir>`. A command is warranted only when
it declares a record class of its own; a key modifies the record being
declared. The generated reference prints this test beside every row.

### 2.2 Picture and equation keys (13)

| Key | Type | Values | Default | Scope | Diagnostic family |
|---|---|---|---|---|---|
| `rows=` | row-list | — | `{wire}` | picture | `TKZ-PIC-*` |
| `cols=` | integer | — | 3 | picture | `TKZ-PIC-*` |
| `frame=` | frame-spec | `flat` `vertical` `rotate=<deg>` | `flat` | picture, group, atom | `TKZ-FRAME-*` |
| `west=` `east=` `north=` `south=` | small-enum | `open` `none` `trace` `cup` | `open` | picture | `TKZ-SIDE-*` |
| `trace=` | trace-spec | cell-set or `physical` | empty | picture | `TKZ-CELLSET-*` |
| `open=` | cell-set | — | empty | picture | `TKZ-CELLSET-*` |
| `bonds=` | small-enum | `grid` `none` | `grid` | picture | `TKZ-PIC-*` |
| `align=` | row | row number or `midline` | `midline` | picture | `TKZ-PIC-*` |
| `size=` | small-enum | `s` `m` `l` | from math style | picture, equation | `TKZ-SIZE-*` |
| `check=` | check-spec | — | `signature` | equation | `TKZ-EQ-*` |

Every frame contracts adjacent compatible cells by default: `bonds=grid`
holds in chain and lattice frames alike, and `bonds=none` suppresses the
frame-generated bonds.

### 2.3 Atom keys (14)

| Key | Type | Values | Default | Diagnostic family |
|---|---|---|---|---|
| `skin=` | identifier | a declared skin; defaults §2.8 | theme default (`dot`) | `TKZ-SKIN-*` |
| `wide=` | positive-integer | — | 1 | `TKZ-ATOM-*` |
| `wires=` | positive-integer | — | 1 | `TKZ-ATOM-*` |
| `at=` | address | — | next chain cell | `TKZ-ADDR-*` |
| `name=` | identifier | — | generated | `TKZ-NAME-*` |
| `ports=` | typed-port-list | — | from skin | `TKZ-PORT-*` |
| `frame=` | frame-spec | `flat` `rotate=<deg>` | `flat` | `TKZ-FRAME-*` |
| `up=` `down=` | math-list | — | empty | `TKZ-ATOM-*` |
| `species=` | identifier | — | empty | `TKZ-SPECIES-*` |
| `label pos=` | small-enum | compass or `auto` | `auto` | `TKZ-LABEL-*` |
| `nudge=` | pair | quarter-pitch steps | zero | `TKZ-ADDR-*` |
| `conjugate` | flag | — | false | `TKZ-ATOM-*` |
| `void=` | small-enum | `open` `sealed` | unset | `TKZ-ATOM-*` |

`up=`/`down=` speak page-relative: the outward physical face of the row, in
whichever direction the frame sends it. Atom faces themselves are compass
(§3). `void=open` is a hole that preserves indices; `void=sealed` removes the
site and its bonds.

### 2.4 Wire keys (12)

| Key | Type | Values | Default | Diagnostic family |
|---|---|---|---|---|
| `kind=` | small-enum | `index` `string` | `index` | `TKZ-WIRE-*` |
| `route=` | small-enum | `straight` `orth` `arc` | `straight` | `TKZ-ROUTE-*` |
| `via=` | address-list | — | empty | `TKZ-ADDR-*` |
| `bend=` | number | — | metric | `TKZ-ROUTE-*` |
| `weight=` | small-enum | `single` `double` `bundle=n` | `single` | `TKZ-WIRE-*` |
| `species=` | identifier | — | empty | `TKZ-SPECIES-*` |
| `closed` | flag | — | false | `TKZ-WIRE-*` |
| `wind=` | pair | cycle `{p,q}` | zero | `TKZ-WIND-*` |
| `around=` | address-list | — | empty | `TKZ-WIRE-*` |
| `cross=` | crossing-list | — | empty | `TKZ-CROSS-*` |
| `dir=` | small-enum | `to` `from` `none` | `none` | `TKZ-WIRE-*` |
| `name=` | identifier | — | generated | `TKZ-NAME-*` |

`dir=` draws the direction mark of a directed virtual index; it changes no
topology.

### 2.5 Mark keys (7)

| Key | Type | Values | Default |
|---|---|---|---|
| `form=` | small-enum | `brace-above` `brace-below` `enclosure` `cut` `band` `label` `prose` | `label` |
| `slot=` | small-enum | `selected` `secondary` `complement` `collar` `neutral` | `selected` |
| `outline` | flag | — | false |
| `inset=` | number | — | 0 |
| `label pos=` | small-enum | compass or `auto` | `auto` |
| `nudge=` | pair | quarter-pitch steps | zero |
| `name=` | identifier | — | generated |

### 2.6 Setup keys (4)

| Key | Type | Default |
|---|---|---|
| `pitch=` | length | em-relative; the exact ratio is a named row of the metric registry |
| `sizes=` | size-table | bundled table |
| `strict` | flag | false; benchmark and CI set it |
| `theme=` | identifier | `house` |

### 2.7 Value types (24)

flag · integer · number · length · pair · identifier · small-enum ·
math-list · row-list · row · cell-set · address · address-list ·
typed-port-list · crossing-list · port-pair-list · frame-spec · trace-spec ·
check-spec · size-table · hue-source · bond-policy · size-class · void-policy.

The census covers key values; positional label arguments are mathematics and
carry no key type. Every registry row names exactly one value type; a shared
key name has one type and one meaning at every scope that exposes it. The
overload census (§11, meter M6) never rises.

### 2.8 Closed alphabets

| Alphabet | Words |
|---|---|
| side policy | `open` `none` `trace` `cup` |
| routes | `straight` `orth` `arc` |
| weights | `single` `double` `bundle=n` |
| default skins | `dot` `box` `ring` `tri` `dots` `none` |
| mark forms | `brace-above` `brace-below` `enclosure` `cut` `band` `label` `prose` |
| atom faces | `n` `e` `s` `w`, slotted `n@1`, `e@{1,2}` |

An alphabet word names one operation, applied at any scope. `open` opens an
index: as a side word it opens a boundary, as the cell-set key `open=` it
opens the named cells, as `void=open` it opens a hole. `trace` closes to the
same object: as a side word it closes a row to itself, as the cell-set key
`trace=` it closes the named cells. `none` suppresses or seals everywhere:
a sealed side, `bonds=none`, and the skin `none`. `cup` closes adjacent rows
to each other. This is the one-token-one-meaning discipline: a word carries
its operation across scopes and never a second sense. `periodic` and `tail`
are sugar (§9); they are not alphabet words. The skin `none` is the
invisible junction: a nameable point where wires meet without ink.

## 3. Addresses

Positions are addresses, never coordinates. One grammar serves atoms, wire
endpoints, waypoints, and mark targets — nine productions:

```
(r,c)                  cell of the current frame
a                      named record
a.f@k                  face f of a, slot k          % faces are compass n/e/s/w
n <dir> of a           n pitch steps from a          % 2 e of X
midway a and b         midpoint
on w t                 fraction t along wire w       % beads live here
crossing of a and b    the declared intersection of two wires
leg <face> of <cell>   the policy-generated leg wire at that face
<compass> outside      a point on the picture margin
```

Operands compose: in productions four through eight an operand is itself an
address, so `crossing of g and leg n of (1,2)` is well formed. `crossing`
operands must resolve to wires. The slot suffix `@k` is optional when the
face carries one slot: `B.s` means `B.s@1`.

`nudge=` displaces the record that carries it by quarter-pitch steps. It is
the only displacement key. Raw lengths exist solely as `debug at=`, which the
linter flags and the benchmark rejects; a published figure contains no
millimetres.

Address resolution is a dependency graph evaluated in one pass; a cycle is
the coded error `[TKZ-ADDR-CYCLE]`, printed with the cycle.

Open legs are policy, not objects. An unbonded typed port renders as a stub
in the direction of its face; a wire endpoint may be `open <dir>`. There are
no placeholder atoms.
<!-- Consumers of the open-end policy: every former tenkzfree body; e.g.
     rmp-ii-triangle-network, rmp-ii-mpo-sheet, rmp-iii-b-braid-one. -->

## 4. Frames

A frame maps addresses to positions. There are two kinds and no third:

- **Affine**: one 2×2 matrix plus offset. The presets `flat`, `vertical`,
  `plane` (`lean=`, `rise=`, `slant=` subkeys), and `rotate=<degrees>` are
  parameter fills of that single map.
- **`circle`**: cells sit on a circle; `(1,k)` is the k-th station. A circle
  frame is not affine and is the only non-affine frame.

`frame=` acts at picture scope and at group scope. `\tngroup` transforms a
sub-diagram as one object: its records keep their names, its boundary
signature transforms with it, and the transform has its own model record —
the audit compares networks, never silhouettes. Label text never
rotates; glyph ink may.

Consumers, rotation and shear: `rmp-iii-a-pulling-through`,
`rmp-ii-circuit`, `rmp-iii-a-spt-mpo`, `rmp-ii-peps-rg`.
Consumers, circle: `rmp-iv-ground-space-1d`, `rmp-iii-a-mpo-injective`,
`rmp-iii-b-idempotent`, `rmp-workbench-iii-eq51`.
Consumers, groups and `cluster=`: `rmp-app-czx-state`,
`rmp-iii-b-condensation`, `rmp-workbench-iii-ghz-state-workbench`.

## 5. Wires

A wire is one typed index line. `kind=index` is a bond: two typed-port
endpoints, no waypoints, and the type check `[TKZ-PORT-TYPE]` — a virtual
port never meets a physical one. `kind=string` travels: it carries
waypoints, crossings, winding, and beads, and its endpoints may be any
address, cells included. The distinction is a field of the record; both are
one record class and one command.

**Crossings are declared, never emergent.** `cross={over at <address>}` or
`under at <address>` names the crossing and its order; rendering gaps the
under strand by the `crossgap` metric ratio. A crossing may name any wire of
the picture, including the wire being declared; references resolve at
validation, not at reading order. A declared crossing whose paths do not
intersect is `[TKZ-CROSS-NOT-FOUND]`. An undeclared geometric intersection
of two wires is `[TKZ-CROSS-UNDECLARED]`. Both are hard errors: over/under
order is mathematical content and the renderer never guesses it.
<!-- Consumers: rmp-iii-b-braid-one/-two/-three/-four,
     rmp-iii-b-self-braiding, rmp-iii-a-spt-mpo,
     rmp-iii-b-r-tensor-left/-right. -->

**Winding.** `wind={p,q}` records the homotopy class of a closed string on a
frame with traced sides; the rendered path realizes that class or errors.
<!-- Consumers: rmp-iii-a-torus-one/-two/-three, rmp-workbench-iii-eq59. -->

**Detours.** `around=<address list>` routes the wire past the named records
against their measured silhouettes plus daylight — the pulling-through
idiom.
<!-- Consumers: rmp-iii-a-pulling-through, rmp-iii-a-g-injective-projector,
     rmp-workbench-iii-g-injective-pull, rmp-workbench-iii-mpo-injective-white. -->

**Closures.** Side policy words and cell-set keys normalize to wires whose
`origin` field records the policy that generated them (`origin=trace`,
`origin=cup`, ...). Closure is not a separate record class. A generated
closure wire carries a canonical name — `wrap-1` for row 1's trace return,
`cup-1-2` for the cup joining rows 1 and 2. When both opposite sides carry
cups, names are side-qualified (`cup-west-1-2`, `cup-east-1-2`) so every
derived wire remains addressable as one named record;
policy legs are addressed by the `leg` production. Beads and labels attach to
closures by the ordinary address grammar. A closed chain that renders open is
impossible by construction: the closure IS a wire record, and every wire is
drawn or errors.

**Beads.** A small tensor on a string is an atom whose address is
`on <wire> t`. There is no bead vocabulary.

**Weights.** `double` draws the doubled bond; `bundle=n` draws one heavy leg
standing for an index set, and the signature audit reads it (§7).
<!-- Consumers, double: rmp-app-czx-state, rmp-iii-a-spt-mpo,
     rmp-workbench-iii-peps-renormalization-one. Bundle:
     rmp-ii-boundary-lasso, rmp-iv-intersection-lhs-three,
     rmp-iv-intersection-rhs-four. -->

## 6. Marks

A mark is a non-topological record on a target: braces above or below a cell
range, a measured `enclosure` contour around members, a `cut` across a wire,
a shaded `band`, a free `label`, or `prose` (§7). A mark target is a cell
set, a wire place, or an address set — a braced, comma-separated list of
addresses, `{a-2-2, b-2-1, ...}`. Marks never own topology; deleting every
mark changes no contraction.

The enclosure contour derives from its members' silhouettes; `slot=` selects
the semantic tint. `inset=` steps nested contours inward so shared
boundaries stay distinct — the nested-boundary idiom. `outline` draws the
contour without tint.
<!-- Consumers, enclosure: rmp-ii-blocking, rmp-app-czx-state,
     rmp-iii-a-ghz-state. Band: rmp-ii-boundary-lasso, rmp-iii-b-dyon,
     rmp-ii-boundary-region. -->

## 7. Equations: `tenkzeq`

`tenkzeq` composes whole pictures around relation glyphs and is the audit
scope:

1. **One metric context.** All panels share the pitch, the size-class table,
   and the weight table. Within a size class the widest measured label box
   wins for every member — `X` and `X^{-1}` render at one width by
   construction.
2. **Math-style sensing.** Display, text, and script contexts choose the
   density profile; there is no manual compact or inline flag. `\tnpic`
   inherits the sensing.
3. **Axis alignment.** Panels align on the declared wire axis (`align=`).
4. **The signature audit.** `check={signature}` compares the boundary
   signatures of adjacent panels and errors on mismatch with
   `[TKZ-EQ-SIGNATURE]`, printing both signatures. `modulo=bundles` accepts
   declared regroupings: a `bundle=n` leg equals its n constituents.
   Opt-out is per relation and recorded:
   `check={signature, off={2: isometry annihilation}}` — the reason string
   lands in the event stream. There is no undocumented off switch.
5. **Prose panels.** Text in place of a diagram is `\tnmark[form=prose]`,
   and the event stream records it as not-a-diagram. A relation whose side
   is prose fails `check=signature` unless that relation is opted out with a
   reason. Silent text substitution is impossible to commit.
<!-- Consumers: rmp-ii-mpu-brickwork, rmp-iii-a-coproduct,
     rmp-workbench-iii-eq59-now, rmp-ii-mpu-unitarity. -->

## 8. Declarations and the extension gate

`\tndeclare{atom}{\tnprojector}{skin=box, ports={w:virtual, e:virtual, n:physical}}`
creates a one-label atom command. Ports live on any compass face, slotted,
any mix of `virtual` and `physical`. A declared skin
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
| `pairings=` | port-pair-list | `{n@1 > e@1 : R, ...}` pairs of own ports | skin |

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
Teaching text uses sugar freely. Twenty-seven rows:

| Sugar | Expands to |
|---|---|
| `sandwich` | `rows={ket,op,bra}` |
| `physical=up\|down\|updown\|none` | expander: adds the outward physical port to every wire-row atom |
| `boundary=open\|none` | `west=<w>, east=<w>` |
| `boundary=periodic`, `periodic` | `west=trace, east=trace` |
| `west={cup=$m$}` (any side) | side `cup` + `\tn[skin=ring, at=on <cup wire> 0.5]{m}` |
| `west={tail=$m$}` (any side) | side `open` + boundary-skin atom on the stub wire |
| `west label=$m$` etc., `bond label=` | `\tnmark[form=label]{<generated wire>}{m}` |
| `lattice={RxC}` | R wire rows (`rows={wire,...,wire}`), `cols=C` |
| `ring=N` | one wire row, `cols=N, frame=circle, west=trace, east=trace` |
| `surface=torus` | `west=trace, east=trace, north=trace, south=trace` |
| `planes` | two `\tngroup` sheets (ket, bra) + `frame=plane` preset |
| `cluster={RxC}` | `\tngroup` of R×C dot atoms on a quarter-pitch sub-frame, named `<name>-<r>-<c>` |
| `\tnX{m}` | `\tn[skin=ring]{m}` |
| `\tn*[k]{m}` | `\tn[conjugate, k]{m}` |
| `\tnbond[k]{a}{b}` | `\tnwire[kind=index, k]{a}{b}` |
| `\tnstring[k]{verbs}` | `\tnwire[kind=string, ...]` — verb table below |
| `\tnfuse[k]{m}` | prelude fuse atom (`skin=tri`, `wires=`, `ports=`); tenure: 0 benchmark consumers, held by 4 blueprint figures |
| `\tnspan[form]{k}{m}` | `\tnmark[form=...]{(r,c)-(r,c+k-1)}{m}` |
| `\tncut[k]{m}` | `\tnmark[form=cut]{<wire place>}{m}` |
| `\tnregion[k]{members}` | `\tnmark[form=enclosure or band, k]{members}{}` |
| `\tndots` | `\tn[skin=dots]{}` (elision bit read by the audit) |
| `\tnskip` | `\tn[void=open]{}` |
| `\tntree[k]{word}` | expander: fuse atoms + wires from the word |
| `up at= down at= west at= east at=`, `combined=`, `span=` | `ports=` face/slot grammar; `span=` folds into `wires=` |
| `role=` | `species=` (the four prelude species) |
| `\tndeclareatom` | `\tndeclare{atom}` |
| `\tnprose{m}` | `\tnmark[form=prose]{<panel>}{m}` |

Two rows are expanders: their expansion is a rule over the picture, not a
token substitution — `physical=` adds a port per wire-row atom, `\tntree`
builds atoms and wires from the word. Expander output is still pure kernel
records, and the same test class verifies it.

String verb table: `through a` → `via={a}` entering and leaving tangent
ports · `loop a` → `closed, around={a}` · `over w at p` / `under w at p` →
`cross=` · `wind {p,q}` → `wind=` · `bead{m}` → an atom `on <wire> t` ·
`join s at p` → an endpoint `on s p`.

Sugar tenure: a sugar row needs three distinct consumers among the benchmark
cases and blueprint figures; a row below tenure is a mandatory agenda item
at the next shrink session (§11).

## 10. Tombstones

Deleted spellings stay in the registry as tombstones; the linter rejects
them forever with the migration hint. No deleted spelling is ever reused.

| Dead spelling | Migration |
|---|---|
| `tenkzfree`, `tenkzcd`, `tenkzlattice`, `tenkzplanes` | `tenkz` with `lattice=`/`planes` sugar; fusion trees are `\tntree`; commutative diagrams belong to tikz-cd, outside this language |
| `\tnput` | `\tn[at=<address>]` |
| `\tnjoin`, `\tnedge`, `\tnarrow` | `\tnwire`; a directed index is `\tnwire[dir=to]` |
| `\tnsite` | `\tn[at=(r,c)]` |
| `\tnghost{m}` | addresses reference empty cells directly |
| boundary-skin placeholder atoms | open-end policy (§3) |
| `out=`, `in=` | routes and `via=`; arc keeps one `bend=` |
| `route=hv`, `route=vh`, `route=curve` | `route=orth` (+ `via=`), `route=arc` |
| `drop`, `hug` routes | `route=orth, via=` and `around=` |
| `label shift=` | `nudge=` (quarter-pitch) or `label pos=` |
| `col vector= row vector= sheet vector=` | `frame={plane, ...}` subkeys |
| `maps`, `polygon=`, `radius=` | died with `tenkzcd` |
| `tensor style=` | `skin=` |
| `fused` | `weight=double` |
| connection `none` flag | omit the record; `void=sealed` removes a site |
| `wiring=` micro-DSL | skin pairings are wires (§8) |
| `cluster` as a skin | `cluster={RxC}` group sugar — sub-spins must be addressable |
| `enclosure` as a skin | `\tnmark[form=enclosure]`; a boundary operator is a wide atom (§12.7) |
| `poly=k` | waits for three manifested consumers |
| `weight=string` | `kind=string` |
| `trace style=racetrack` | `cap` closures are the default; `loop` remains for looped traces |
| `inline`, `compact` | math-style sensing + `size=` |
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
| M3 | escape usage (`debug at=`, `nudge=` excess) in the corpus | non-increasing; each occurrence names a grammar gap |
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

## 12. Spelling sketches

The seven figures the 0.7 language failed worst, in kernel form. No
millimetres appear; `% sugar:` marks each sugar spelling with its expansion.

### 12.1 Braid (`rmp-iii-b-braid-one`)

```tex
\[\begin{tenkz}[rows={wire,wire}, cols=4, bonds=none]
  \tnwire[kind=string, species=left,  name=a, via={(2,2)}]{(1,1)}{(2,3)}
  \tnwire[kind=string, species=right, name=b, via={(2,3)},
          cross={under at crossing of a and b}]{(1,4)}{(2,2)}
  \tnmark[form=label, label pos=ne]{crossing of a and b}{$R$}
\end{tenkz}\]
```

### 12.2 Torus with wound string (`rmp-iii-a-torus-one`)

```tex
\[\begin{tenkz}[lattice={3x3},          % sugar: rows={wire,wire,wire}, cols=3
              west=trace, east=trace, north=trace, south=trace]
  \tnwire[kind=string, species=flux, closed, wind={1,0},
          via={s outside}]              % the homotopy class is recorded
\end{tenkz}\]
```

### 12.3 Pulling-through (`rmp-iii-a-pulling-through`)

```tex
\begin{tenkzeq}[size=m, check={signature}]
  \begin{tenkz}[rows={ket}, cols=3, physical=up]   % sugar: physical= adds the up ports
    \tnwire[kind=string, species=g,
            via={1 s of (1,2)}]{w outside}{e outside}
  \end{tenkz}
  =
  \begin{tenkz}[rows={ket}, cols=3, physical=up]   % sugar: physical= adds the up ports
    \tnwire[kind=string, species=g, name=g, via={1 n of (1,2)},
            cross={over at crossing of g and leg n of (1,2)}]{w outside}{e outside}
  \end{tenkz}
\end{tenkzeq}
```

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
\[\begin{tenkz}[lattice={2x2}, bonds=none]   % sugar: rows={wire,wire}, cols=2
  \tn[cluster={2x2}, name=a]{} & \tn[cluster={2x2}, name=b]{} \\
  \tn[cluster={2x2}, name=c]{} & \tn[cluster={2x2}, name=d]{}
  % sugar: cluster= expands to a \tngroup of four dot atoms named a-1-1 .. a-2-2
  \tnmark[form=enclosure, slot=selected]{{a-2-2, b-2-1, c-1-2, d-1-1}}{$X$}
\end{tenkz}\]
```

### 12.6 Blocking (`rmp-ii-blocking` family)

```tex
\[\begin{tenkz}[rows={ket}, cols=4, physical=up]   % sugar: physical= adds the up ports
  \tn[up=$i_1$]{A} & \tn[up=$i_2$]{A} & \tn[skin=dots]{} & \tn[up=$i_L$]{A}
  \tnmark[form=enclosure, label pos=w]{(1,1)-(1,4)}{$A^{[L]}$}
\end{tenkz}\]
```

### 12.7 Enclosing operator with wrap (`rmp-iv-intersection-lhs-one`)

```tex
\[\begin{tenkz}[rows={wire,wire}, cols=4, bonds=none]
  \tn[at=(1,2), name=B]{B}   \tn[at=(1,3), name=C]{C}
  \tn[at=(2,2), skin=box, wide=2, wires=2, name=R]{R}  % the wide operator row
  \tnwire{B.s}{R.n@1}        \tnwire{C.s}{R.n@2}
  % B.n and C.n stay unbonded: typed ports render their own stubs.
  \tnwire[kind=string, route=orth, via={1 w of R}]{open n}{R.w}  % wrap west
  \tnwire[kind=string, route=orth, via={1 e of C}]{R.e}{open n}  % out east
\end{tenkz}\]
```

## 13. Grammar rules

1. One picture, one frame chain. Nesting is `\tngroup` or `\tnpic`.
2. Picture options declare topology and policy; they create no hidden atoms.
3. Body order may establish references; it never changes an earlier record.
   Crossing references resolve at validation (§5).
4. Validation finishes before measurement; a renderer never repairs,
   guesses, or silently drops requested ink. Unsupported ink is a coded hard
   error.
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
   tombstone. Wire keys stay at twelve because `end=` is deleted in favor of
   positional `open <dir>` endpoints.
2. **Boundary operators are wide atoms.** The section-IV R operator is a
   `wide=` box ATOM (§12.7), not an enclosure mark — marks own no topology.
   This diverges from the plan's phrasing "enclosure mark + orth/around
   wires"; the enclosure mark keeps the blocking and region consumers (§6).
3. **`leg <face> of <cell>` address production.** Added so strings can cross
   policy-generated legs (§12.3); it raises the address grammar to nine
   productions.
4. **Effectivity.** The 0.7 registry describes the current package until the
   kernel lands; the registry regeneration and the three Session-0 artifacts
   land with this contract's acceptance, and the census then enforces every
   count stated here.
