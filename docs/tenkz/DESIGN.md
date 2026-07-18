# tenkz design notes

## The silhouette

Every clearance question in a picture is the same question: how far does
the ink already there reach?  The **silhouette** is the answer, computed
once: `\tenkz_silhouette:nnnnN {row}{col-from}{col-to}{up|down} \dim`
returns the distance from a row's axis to the outermost ink edge over a
column span, on one side.  Closure and annotation ink then sits at

    silhouette + daylight

and nowhere in the package does a consumer predict what another pass
will draw.  A pass that adds a new kind of ink teaches the resolver
once; every consumer inherits the correction.

The resolver reads the same stored cell data the drawing passes read —
the kind, options, and node-name tables plus the row typing — and takes
a per-cell maximum over the actual contributions: the placed node's own
edge anchor (so strut-grown boxes, wide pills, `wires=k` covering
heights and the ellipsis node are measured, not modelled), an open leg
beyond that edge, a label band beyond a labelled leg tip, the
pair-trace wrap loop's cap, an external bead label whose resolved
quadrant faces the queried side, and a fusion bar's overhang.  Leg-tip
and bead labels share one band metric (`dotlabelband`), deliberately:
both are a name hung off ink.

### The one daylight constant

`\tenkz@r@daylight = 0.15` pitch is *pure separation*: the gap that
keeps a return wire or a brace from fusing visually with the ink it
skirts.  It clears nothing — what must be cleared is the silhouette's
business and is measured.  0.15 pitch is about 1.7 mm at the default
11 mm pitch (roughly three wire widths, so it reads at print size) and
still about 1 mm at the inline pitch.  It replaces the former
`traceclear = 0.30`, which budgeted a worst-case glyph inside a fixed
drop, and the braces' unnamed 0.20 offset.

### Converted consumers

- **The periodic racetrack** (`\tenkz_trace_row:nn`): drop = silhouette
  of the traced row's occupied span + daylight.  A bare ring hugs its
  beads; rings over labels clear the labels because the labels are in
  the silhouette, not because the racetrack guessed.
- **Span braces** (`\tenkz_draw_span:nnnnn`): offset = silhouette of
  the braced columns + daylight.  Braces measure over their own columns
  only, so a brace over unlabeled cells is not pushed out by labels
  elsewhere in the row, and a box-mode brace clears the *actual*
  (strut-grown) box edge instead of a nominal minimum.

The former per-consumer scan functions `\tenkz_span_leg_labels:nnnnN`
and `\tenkz_span_dot_labels:nnnnN` are deleted; their logic lives
inside the resolver.

### Planned consumers

- **Cup reach**: today the cup bend protrudes exactly one `stub`, so
  open and cup-closed ends share a silhouette by decree.  Converting
  means asking the side silhouette (the west/east analogue over a row
  pair: stub tips, boundary labels) and bending at silhouette +
  daylight, so a cup around labelled boundary stubs clears the labels.
- **Lattice sheet separation**: the inter-sheet gap becomes the lower
  sheet's up-silhouette plus the upper sheet's down-silhouette plus
  daylight, replacing the fixed sheet-separation ratio that must today
  be tuned against the tallest decorated sheet.
- **Region insets**: a region outline's margin becomes the enclosed
  cells' silhouette toward each edge plus daylight, so outlines hug
  bare beads and step out around legs and labels instead of carrying
  one worst-case margin.
