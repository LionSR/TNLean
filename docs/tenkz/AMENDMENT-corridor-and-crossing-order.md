# Amendment to LANGUAGE-1.0: the corridor, and crossing order

Two proposed amendments to the signed kernel contract. Each is argued from
the benchmark's own demand, each removes more of the language than it adds,
and neither needs a dependency the package does not already load.

## The demand

The verdict ledger records, for every blocked target, what the target needs
before it can be drawn at all. Aggregated over the hundred and thirty:

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

And over all hundred and thirty, the dominant recorded defect is
`wrong-contraction`, twenty-three times: a panel that depicts a network the
source does not. That is the worst place in the benchmark, and the two
amendments below are aimed squarely at it.

Reading the ten "enclosure mark" targets shows they are one family, and that
the label is a misnomer. They are the section-IV intersection figures, and
their notes say *wrap drawn as a crossing*, *wrap routing*, *wrap leg drawn
straight*, *cup routing*. None of them wants a region contour. Every one of
them wants a leg of the R operator to leave the diagram, travel around it,
and come back — and every one of them currently gets a straight line through
the middle of the picture instead, which is why they read as the wrong
contraction.

The nine "crossing order" targets are the braids and the winding strings.
Their notes say *crossing drawn but over/under unmarked*, *over/under
ambiguous*, *a braid with no crossing*, *twist rendered without crossings*.

## Amendment one: the corridor

### What is wrong

The kernel has four separate spellings for one geometric idea:

| spelling | what it says |
|---|---|
| `west=trace` and friends | close each row back on itself around the outside |
| `west={cup=...}` and friends | join two adjacent rows around the outside |
| `around=<addresses>` | detour past the named records |
| `wind={p,q}` | close a string in a homotopy class around the outside |

All four describe a route that leaves the support of the diagram, travels
outside it, and re-enters. They differ only in where it leaves and re-enters,
how far out it travels, and whether it closes. The section-IV wrap is the
fifth member of the family, and it has no spelling at all — which is exactly
why ten targets are blocked.

Four spellings for one idea is the growth the shrink doctrine exists to stop.

### The proposal

Name the thing they share. A picture has an interior, where cells live, and
an exterior **corridor**, which is the picture's own silhouette pushed
outward in lanes. Geometry already computes that silhouette — the support
functions the placement stage uses for occlusion are the corridor's inner
boundary, and a lane is that boundary pushed out by a named ratio.

One route value carries the whole family:

    route=around

A wire routed around leaves its start port on the nearest side, takes a lane
in the corridor, travels to its end port's side, and re-enters. Lanes are
assigned outward in declaration order, so two wraps never overlap and the
author never counts them.

Then the four old spellings become sugar over one kernel form:

| sugar | expands to |
|---|---|
| `west=trace` | one `route=around` wire per row, east port to west port |
| `west={cup=m}` | one `route=around` wire joining two adjacent rows |
| `wind={1,0}` | a `closed` `route=around` wire leaving and re-entering the same row |
| `around={a}` | `route=around` with the corridor lane chosen to clear `a` |

and the section-IV wrap becomes sayable for the first time, in one line:

    \tnwire[route=around]{R.e}{R.w}

### What it costs and what it buys

The side alphabet shrinks from `open none trace cup` to `open none`; `trace`
and `cup` move to the sugar ledger with expansions, which is where the
contract already says such things belong. `wind=` stays as a *claim* about
the resulting homotopy class — the engine still checks the drawn path
realizes it — but it stops being a routing instruction. `around=` retires
into the route.

The corridor also fixes the torus honestly. A winding of one around a lattice
with identified sides is a wire that leaves the east rail at some row and
re-enters at the west rail at the same row. Drawn in the corridor, that is
what appears. Drawn as a circle, which is what the current fixture produces,
it is not a wrapped loop and the picture asserts something false.

### What it reuses

Nothing new is needed. The corridor's inner boundary is the support-function
silhouette the geometry stage already computes. Its turns are `hobby`, which
the string engine already loads. Its arclength and splitting are `spath3`,
likewise already loaded. The lane offset is one named ratio in the metric
registry.

## Amendment two: crossing order is a policy, not a list

### What is wrong

A crossing is resolved today by naming it:

    cross={over at crossing of a and b}

One declaration per crossing, naming both operands and the place. A braid
with n crossings needs n of them. The rule behind it is right and must
survive: *no crossing may be left ambiguous*, enforced by the crossing
police, which refuses a picture whose strands meet without a declared order.

But the cost of obeying the rule grows with the picture, and the benchmark
shows what happens: nine targets simply do not obey it, and their strands
meet with no order at all. The rule is correct and the interface is too
expensive to keep.

### The proposal

Let a string state its habit once, and keep declarations for exceptions.

One new key on a WIRE:

    crossing=over | under | alternate

It is the string's default at every crossing it makes. `alternate` flips at
each crossing in the order the string meets them along its own route — which
is well defined, because the engine already orders a string's crossings by
arclength to place beads. `alternate=under` anchors the first one.

The existing `cross={... at ...}` stays, and means exactly what it means now:
this particular crossing, against the habit.

Three rules keep the guarantee:

1. Every geometric crossing must be resolved by a policy, by an exception, or
   the picture is refused. The police invariant is untouched.
2. Two strings whose policies both claim to pass over the same crossing is an
   error, not a silent winner. The picture must say.
3. A crossing resolved by a policy is recorded in the model exactly as a
   declared one is, so an audit cannot tell the two apart and the events
   carry the same evidence.

A braid becomes one line per strand instead of one line per crossing.

### Why not the shelf

This was checked against the packages that already solve neighbouring
problems.

`knots` resolves crossings by detecting them and applying a global order.
Rejected as an engine because the detection is invisible to the author and
changes under small edits — but its clip-width gap sizing and its draft-mode
crossing numbers are worth stealing and are already noted as such.

`braids` takes generator words. Rejected because a generator word imposes
lane semantics on the picture: strands must live in numbered columns, which
is false for a string crossing a lattice.

`alternate` is neither. It is an explicit statement by the author, anchored
at a defined end, refused when it conflicts, and recorded like any other
declaration.

## What this addresses

The corridor unblocks the ten section-IV targets, the four torus cycles and
the two ring closures. Crossing order unblocks the nine crossing-order
targets, the three braid resolutions and the two multi-strand braids. Between
them, nineteen of the thirty-eight blocked targets, and the greater part of
the twenty-three wrong-contraction defects, which are wrong for precisely
these two reasons: a wrap drawn through the diagram, and a crossing drawn
without an order.

The language gets one new route value and one new key, and gives back two
values from the side alphabet and one wire key. It ends smaller than it
started.
