# tenkz 1.0 — the kernel is the surface

0.7 drew pictures through four front ends. Five environments, seven picture
commands, and four separate key ledgers each said the same few things in a
private dialect: a cell, a wire, a mark, a frame. 1.0 has one environment and
one ledger. Every picture is a kernel picture, the package binds the kernel at
load, and the front ends are gone — 3,154 lines of commutative-diagram stage,
4,393 of free stage, 10,500 of lattice stage, 17,340 of grid stage, retired in
four changes that deleted 35,387 lines against 2,764 added. The registry census
fell from 201 public rows to 86 and the parser-path count from 228 to 75; the
escape ledger, which prices every occurrence of a spelling the core grammar
cannot say, reached zero.

The spellings below are removed outright. 1.0 is a major release and keeps no
alias, compatibility reader, or dual writer for any of them: an old spelling
stops the run with an unknown-key or unknown-command error naming the
vocabulary, and nothing is silently reinterpreted. Every documented replacement
was applied to the blueprint corpus and the 130-case benchmark before its front
end was deleted, and each deletion carried the fixtures whose language died —
the regression corpus went from 264 sources to 9.

## Retired environments

| Old | New |
|---|---|
| `tenkzcd` | plain `tikz-cd`; commutative diagrams are not this language |
| `tenkzfree` | `tenkz` with addressed `\tn`, `\tnwire`, and `\tnmark` records |
| `tenkzlattice` | `tenkz` with `lattice={RxC}`, or a declared `frame={..., basis={...}}` |
| `tenkzplanes` | `tenkz` with the `planes` sugar row |
| `tenkz` (0.7 grid meaning) | `tenkz` — the name survives, the meaning is the kernel picture |

## Retired commands

| Old | New |
|---|---|
| `\tnpic[k]{body}` | `\begin{tenkz}[k] body \end{tenkz}` |
| `\tnarrow` | `\tnwire[dir=to]` |
| `\tnput` | `\tn[at=<address>]` |
| `\tnjoin` | `\tnwire` |
| `\tnedge` | `\tnwire` |
| `\tnsite` | `\tn[at=(r,c)]` |
| `\tnregion` | `\tnmark[form=enclosure]` |
| `\tncut` | `\tnmark[form=enclosure]` or `\tnmark[form=bracket]` |
| `\tnspan[form]{k}{m}` | `\tnmark[form=...]{(r,c) .. (r,c+k-1)}{m}` |
| `\tnX{m}` | `\tn[skin=ring]{m}` |
| `\tndots` | `\tn[skin=dots]{}` |
| `\tnskip` | `\tn[void=open]{}` |
| `\tnghost{m}` | nothing; an address may name an empty cell |

## Retired keys

Commutative-diagram front end:

| Old | New |
|---|---|
| `maps` | — |
| `polygon=`, `radius=` | — |
| `column sep=`, `row sep=` | — |
| `from=`, `to=` | `\tnwire{<end>}{<end>}` |
| `poly=k` | — |

Free front end:

| Old | New |
|---|---|
| `out=`, `in=` | `route=arc` |
| `route=hv`, `route=vh` | `route=orth` |
| `route=curve` | `route=arc` |
| `drop`, `hug` | `route=orth`, `route={<side> of <selector>}` |
| `ports=` (free object row) | `\tn[ports=...]`, the typed-port list |
| `ring`, `circle`, `boundary` | `skin=ring`, `skin=circle`, `skin=boundary` |
| `fused` | — |
| `none` (connection flag) | omit the record, or `void=sealed` to remove the site |
| `group=` | an address set |

Lattice front end:

| Old | New |
|---|---|
| `site=` | — |
| `sheets=`, `sheet sep=` | `frame={plane, basis={...}}` |
| `col vector=`, `row vector=`, `sheet vector=` | `frame=plane` with basis members |
| `plane rise=`, `plane slant=`, `plane lean=` | `frame=plane` subkeys |
| `pairing` | `pairings=` on the declared skin |
| `outer legs=`, `boundary legs` | the side policy |
| `label=` (object) | `\tnmark[form=label]` |
| `size=` (object) | `size=`, the size class |
| `removed=` | `void=sealed` |
| `style=` (edge pass-through) | `stroke=`, or the port type |
| `label at=` (region) | `label pos=` |

Grid front end:

| Old | New |
|---|---|
| `tensor style=` | `skin=` |
| `up=`, `down=` | `ports=` |
| `up at=`, `down at=`, `west at=`, `east at=`, `combined=` | the `ports=` angle and slot grammar |
| `span=` | `wires=` |
| `mpo` | `skin=mpo` |
| `bond dir=` | `dir=` on the wire |
| `bond label={$D$ at 1-2}` | `\tnmark[form=label]{<wire>}{$D$}` |
| `label shift=` | `label pos=` |
| `box` | `\tnmark[form=enclosure]` |
| `brace above` | `\tnmark[form=brace-above]`, `form=brace-below` |
| `label pos` (annotation) | `label pos=` on the mark record |
| `layer sep=` | the metric size classes |
| `trace style=racetrack` | — |
| `inline`, `compact` | math-style sensing and `size=`; `metrics=compact` for a page-constrained picture |
| `wiring=` | `pairings=` on the skin |
| `weight=string` | `kind=string` |
| `cluster` (as a skin) | `cluster={RxC}`, a basis sugar |
| `enclosure` (as a skin) | `\tnmark[form=enclosure]`; a boundary operator is a wide atom |
| `chain axis`, `legs at`, `rows`, `periodic` | `frame=`, `ports=`, `wires=`, `west=trace, east=trace` |
| `leg <face> of <cell>`, `<compass> outside` | the generated leg's own name |
| `(r,c)-(r,c)` | `(r,c) .. (r,c)` |

Spellings inside the kernel tier itself:

| Old | New |
|---|---|
| `outline` (mark flag) | `tint` |
| `physical=` as a picture-wide row topology | `physical=` as a per-cell port policy |
| `\tnset{pitch=...}` in the body | `metrics=compact` |
| hand-written leave and enter angles on a route | `crossing=` for the habit, `cross=` for the exception |
| `\tenkzkernel` | nothing; the kernel is bound at package load |

## Why the front ends died

- **One picture, one language.** The four dialects disagreed about nothing that
  mattered. A cell was a `site`, a `tensor`, or an object with `ports`; a wire
  was an `edge`, a `join`, an `arrow`, or a `bond`; a mark was a `region`, a
  `cut`, a `span`, or a `box`. Each dialect then needed its own parser, its own
  defaults, and its own renderer, and a picture that wanted two of them could
  not be written at all. The kernel has one record for each of the three, and
  the dialects became presets over it.

- **An address, not a cursor.** `\tnput` placed a tensor where the last one
  left off; `\tnsite` placed one at a lattice coordinate; `\tnpic` placed one
  wherever the body's row and column separators had got to. Three ways to say
  where. In 1.0 a picture declares a frame, the frame mints addresses, and
  every record names its addresses. `\tnghost` existed only to advance a cursor
  past an empty cell, so it has nothing to do.

- **A port has a type; a route has ends.** `out=` and `in=` set the raw
  departure and arrival angles of a curve, which meant that moving a tensor
  broke every wire touching it. An arc now leaves and enters along the faces of
  its ends, and the ends are the wire's two arguments rather than `from=` and
  `to=` keys. `fused` and `weight=` chose ink from the author's intent; the
  port type chooses it from the picture.

- **A sheet is a basis member.** `sheets=`, `sheet sep=`, `col vector=`,
  `row vector=`, and `sheet vector=` described a three-dimensional lattice by
  listing its layers and then its lattice vectors separately, so the two could
  disagree. `frame={plane, basis={...}}` states the basis once and the layers
  are members of it. The doubled-plane pictures the lattice front end existed
  for are the `planes` sugar row over that frame.

- **A hyphen is not a range.** `(r,c)-(r,c)` could not be told from a generated
  name containing a hyphen, so a selector was ambiguous exactly where selectors
  are used most. The range operator is `..`.

- **Contour is the default, so paper says so.** The mark flag was `outline`,
  and its absence meant a filled mark. Filled marks are rare, unfilled marks
  are the common case, and a flag should name the exception. The flag is now
  `tint` and its absence means contour only.

## Migration

Per spelling, one substitution each:

```
\tnpic[K]{BODY}       ->  \begin{tenkz}[K] BODY \end{tenkz}
\tnarrow              ->  \tnwire[dir=to]
\tnjoin               ->  \tnwire
\tnedge               ->  \tnwire
\tnX{M}               ->  \tn[skin=ring]{M}
\tndots               ->  \tn[skin=dots]{}
\tnskip               ->  \tn[void=open]{}
\tncut                ->  \tnmark[form=enclosure]
\tnregion             ->  \tnmark[form=enclosure]
tensor style=         ->  skin=
route=curve           ->  route=arc
route=hv | route=vh   ->  route=orth
span=                 ->  wires=
bond dir=             ->  dir=
label shift=          ->  label pos=
label at=             ->  label pos=
removed=              ->  void=sealed
outline               ->  tint
(r,c)-(r,c)           ->  (r,c) .. (r,c)
```

`\tnghost` and the `none` connection flag are deleted, not rewritten. The rest
read better by hand:

- `\tnput{M}` becomes `\tn[at=<address>]{M}` once the picture declares a frame;
  a free picture that relied on placement order must first say where its
  tensors are.
- `\tnsite`, `\tnedge`, and `\tnregion` bodies become `\tn`, `\tnwire`, and
  `\tnmark` records over the same coordinates, with `lattice={RxC}` supplying
  the frame the environment used to supply.
- `out=`/`in=` angle pairs become `route=arc`, and a crossing that the arcs no
  longer resolve is named once with `crossing=` or per wire with `cross=`.
- `up=`/`down=` row topology becomes a `ports=` list per cell.
- A `bond label={$D$ at 1-2}` becomes a `\tnmark[form=label]` record naming the
  wire.
- `\tenkzkernel` may be deleted from a document body: the meanings it bound are
  the package's meanings from the moment it loads. The command is inert rather
  than an error in the 1.0 series, and carries a registry sunset.

## Unchanged

`tenkz` as the environment name, `tenkzeq` and its joiners, `\tn`, `\tnwire`,
`\tnmark`, `\tndeclare` and `\tndeclareatom`, the four side-policy words
(`open`, `none`, `trace`, `cup`) and their `west=`/`east=`/`north=`/`south=`
keys, `frame=` as the one frame key, the cell-set contraction algebra with its
terms, ranges, and `+`/`-` unions, `periodic` as the shorthand for a traced
pair of sides, and the `.tnlog` event surface, whose format version and
compatibility rules are declared in `TNLOG.md`.

## Also in 1.0

- `\tenkzkernel` binds at package load. A document that never wrote the command
  gets the kernel surface; a document that wrote it gets the same surface
  twice. What the swap deleted for a reader is the possibility of a picture in
  the 0.7 grid meaning.
- The plane frame carries a declared basis and an independent physical axis, so
  a projected picture states its own topology instead of inheriting the grid's.
- A physical index may be directed, and a policy leg has the standing of a
  declared one: a generated open end is a named record that a label or a mark
  can name.
- `stroke={solid|dashed|dotted}` spells wire ink, and the direction mark inks
  on every bearing.
- Region selection takes set difference, so a nested window is `A - B` rather
  than two overlapping marks.
- `metrics=compact` names the tighter metric profile that page-constrained
  pictures used to obtain by setting `pitch=` in the body.
- The stock `mpo` and `pill` skins are prelude declarations rather than object
  flags.
- The alias count is zero and no public name carries two value types.

## The version string

`tex/tenkz/tenkz.sty` still declares `v0.7`. The version, its date, this
record's version line, and the event-format declaration in `TNLOG.md` are set
together by the release-preparation change described in `RELEASE-POLICY.md`
§3, and must agree with the tag. Writing them earlier would claim a release
that has not passed its evidence gate.
