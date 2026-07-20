# tenkz 0.6 — one vocabulary

0.6 unifies the key surface. The drawing engine always had one language;
the keys now speak it too: one frame key, one side-policy alphabet, one
contraction cell-set algebra, in every tier. The renames below are
breaking — 0.6 removes the old spellings outright — and every one is a
mechanical rewrite. Applied to the 230-file test corpus by script; the
renders are pixel-identical.

## Renames (old spelling removed)

| Old | New |
|---|---|
| `close west` | `west=cup` |
| `close west={$m$}` | `west={cup=$m$}` |
| `close east` | `east=cup` |
| `close east={$m$}` | `east={cup=$m$}` |
| `periodic style=racetrack\|hooks` | `periodic, trace style=racetrack\|hooks` |
| `orientation=horizontal` | `frame=flat` |
| `orientation=vertical` | `frame=vertical` |
| `plane=flat\|oblique\|slab` (lattice) | `frame=flat\|oblique\|slab` |
| `\tn[pair=trace]` (cell key) | `trace={(physical, c)}` (picture key) |
| `trace={physical at={c1,c2}}` | `trace={(physical, c1-c2)}` |

`\tnfuse[rows=k]` is now spelled `\tnfuse[span=k]`; `rows=` survives as a
documented alias (at picture scope `rows=` types the rows, so `span=` says
what the wedge does without a second meaning).

## Why these five

- **One side, one policy.** A picture side takes exactly one word of the
  policy alphabet: `west=open|none|trace|cup|cup={$m$}`, likewise `east=`
  (and `north=`/`south=` on the lattice). `close west` was a second
  first-class spelling for one letter of that alphabet.
- **How never sets whether.** `periodic style=` chose the closure ink
  *and* silently turned the closure on. The whether is `periodic` (the
  alias for `west=trace, east=trace`); the how is `trace style=`.
- **One frame key.** The grid's `orientation=` and the lattice's `plane=`
  named the same concept — the linear map from logical coordinates to
  paper. Both are `frame=` now, and `chain axis=east|south` remains the
  chain-flavored alias.
- **One addressing algebra.** Contraction is stated in cell sets:
  `trace={(interface, columns)}` and `open={(interface, columns)}` with
  terms, ranges, and `+`/`-` unions, in the grid exactly as in the
  lattice. The word `physical` names the word's self-interface. The
  `pair=trace` cell key and the `at=` micro-sugar were one-off spellings
  of single cell sets.

## Migration

Per spelling, one regex each (the script that swept the corpus):

```
close west={V}            ->  west={cup=V}
close east={V}            ->  east={cup=V}
close west                ->  west=cup
close east                ->  east=cup
periodic style=(X)        ->  periodic, trace style=\1
orientation=horizontal    ->  frame=flat
orientation=vertical      ->  frame=vertical
plane=(flat|oblique|slab) ->  frame=\1
\tnfuse[...rows=k...]     ->  \tnfuse[...span=k...]
```

The two cell-set renames are rarer and read better by hand:
`trace={physical at={4,5}}` becomes `trace={(physical, 4-5)}`, and a
`pair=trace` on the site in column `c` becomes the picture key
`trace={(physical, c)}`.

An old spelling now stops the run with an unknown-key or
unknown-policy-word error naming the vocabulary — nothing is silently
reinterpreted.

## Unchanged sugar (documented aliases)

`boundary=open|none`, `periodic` / `boundary=periodic`,
`chain axis=east|south`, `nopair`, `trace=physical`,
`physical=up|down|updown|none`, `sandwich`, the `:open`/`:none` row
suffixes, `\tnX{m}`, `boundary legs` (lattice), `label at=` (region),
the padded `bond label={$D$ at 1-2}` pattern, `\tnfuse[rows=k]`, the
`tenkzplanes` environment (a preset over `tenkzlattice`:
`sheets={ket,bra}`, the double-layer frame ratios, `outer legs=none`),
and the `on-wire matrix` style name for `ring tensor`.

## Also in 0.6

- `tenkzplanes` lost its private key family: every key it accepts is a
  `/tenkz/lattice` key, and its pictures emit the standard lattice
  header event.
- The lattice takes the four-sided policy (`west=`/`east=`/`north=`/
  `south=`, plus `boundary=` as the all-sides shorthand). Opposing
  `trace` sides close the corresponding virtual axis within each sheet;
  `cup` contracts matching ket-bra boundary indices. One-sided or
  geometrically incomplete closures diagnose the real open endpoints
  without inventing topology.
- The package version string reads v0.6.
- The periodic racetrack drop is per-obstruction: the base clearance
  (0.30 pitch) covers only the glyph silhouette, and open legs, labelled
  leg tips, and dot labels each add their own band. A bare ring hugs its
  row; the old fixed 0.62 budgeted for labels that were often absent.
- The on-wire matrix capsule's corner radius is the named ratio
  `wireglyphcap` (= wireglyph/2). The 0.6-review spelling
  `0.5\tenkz@dim{...}` misparsed in pgf and drew lens-shaped capsules.
