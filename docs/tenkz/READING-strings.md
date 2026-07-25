# What the benchmark means by strings

The verdict ledger records `strings` against seven blocked targets, and the
nine signed amendments say plainly that none of them supplies it. The word
was never defined. This is the reading that defines it: each of the seven
panels set beside the authors' own figure and beside what the language can
say.

The answer is that the seven are three families, that the largest of them
wants an address the signed contract already carries, and that no new element
is needed. Net element count: **zero added, zero retired.**

## The seven

| target | recorded need | recorded note |
|---|---|---|
| `rmp-iii-a-spt-mpo` | strings | diagonal action frames are now represented; the string geometry remains incomplete |
| `rmp-workbench-iii-g-injective-pull` | pulling-through, strings | g string, hatched legs, U_g node absent |
| `rmp-workbench-iii-mpo-injective-white` | pulling-through, strings | colored strings replaced by boxes |
| `rmp-workbench-iii-eq59` | torus-cycle, strings | torus with wound strings collapsed to a two-box loop |
| `rmp-iii-a-g-injective-projector` | strings, group-average | author panel shows a g-string pulling-through equality, not the declared four-leg group-average projector P_G |
| `rmp-iii-a-f-symbol` | strings | author draws the MPO/anyon-string realization; abstract tree substituted |
| `rmp-workbench-ii-mpu-wrap-second` | strings | inter-row wrap wires absent |

## What the authors drew

Four panels carry all seven.

**The corner cut.** Section III, lines 414–444 and 468–497. A tensor with
four virtual indices and one physical index, drawn in a horizontal plane. A
second curve cuts one corner of it: the curve enters from beyond one arm,
turns once, and leaves beyond the neighbouring arm. It meets two of the five
indices, and at each meeting a small square stands on it. The equality carries
the curve from the north-west corner to the south-east corner; in the variant
at 414–444 a further tensor $U_g$ appears on the physical index.

The two squares are the two tensors of the operator the curve carries. They
are not junctions. The tensor's indices run through them unchanged and the
curve runs through them unchanged; each square is what sits at the point where
the two meet.

**The threaded loop.** Section III, lines 305–327 and 563–603. The group
average $\frac{1}{|G|}\sum_{g\in G}$ over a plaquette carrying $L_g$ on each
of four indices equals a single closed curve carrying four tensors, one at
each of four of its points, with a mark at one corner fixing a starting point.
The torus panel is the same object on a surface: an outer contour and two arcs
give the torus, a closed curve on it is a noncontractible cycle, one box $i$
stands on the cycle, and the half of the cycle the surface hides is not drawn.

**The crossing of two anyon lines.** Section III, lines 249–288. Six labels
$a,b,c,d,e,f$. Two of them, $a$ and $c$, are directed lines crossing at the
centre; the other four are corner curves, one to each quadrant, at a standing
offset from the crossing, both ends of each free at the margin. Nothing stands
on any of the six. Beside it the authors draw the matrix product realization
of the line $a$ as a row of five tensors under the label $a$.

**The turn inside the tensor.** Section II, lines 473–483. Two rows of four
boxes. In each box of the first row a curve enters from above, turns at the
box's centre, and leaves eastward; a second enters from below, turns, and
leaves westward. The second row reverses both turns, and the turns are drawn
over the box outline. Nothing enters or leaves except through the box's own
four faces. These are the tensor's own indices; the turn states which of its
own faces the tensor sends an index out of.

## What the reading established

### The seven are three families

Five targets want a tensor standing at a point of a curve: the two
pulling-through workbench panels, the SPT panel, equation 59, and — once its
pairing is repaired — the projector. The F-symbol wants nothing of the kind.
The MPU wrap is not about a curve at all.

### The largest family wants an address the contract already carries

The signed address grammar has eight productions. Two of them name a point of a
curve rather than a place in the frame:

```
on w t                 fraction t along wire w        % beads live here
crossing of a and b    the declared intersection of two wires
```

The annotation on the first is the contract's own. Both are parsed today. A
tensor standing on a string is

```tex
\tn[skin=box, at=on g 0.4]{}
```

and a tensor at the meeting of a string with an index is

```tex
\tn[skin=box, at=crossing of g and leg n of (1,2)]{}
```

Neither draws. The first has no resolver at all: the node-kind table lists
`cell`, `rel`, `mid`, `record`, `port`, `outside` and `crossing` and falls
through to `TKZ-KERNEL-RENDER-TODO` for `onwire`. The second resolves only
after string geometry exists. The mark pass runs after the string pass and
reads the saved pre-surgery crossing point. Atom placement instead calls the
same crossing resolver before `\tikzpicture` opens and before either string
has been drawn. The resolver then falls back to PGF's live intersection path
and XeLaTeX stops at `\pgf@intersectionofpaths` with the undefined internal
control sequence `\pgf@intersect@next`.

The reason is the order of the passes. Atoms are placed before the picture
opens; a wire has no geometry until it is drawn inside the picture. So a
tensor's place cannot be a point of a curve — not because the language refuses
to say it, but because the two quantities are computed in an order the
contract never promised. Section 3 promises that address resolution is a
dependency graph and names `[TKZ-ADDR-CYCLE]` for a cycle in it. That code
appears in the contract and nowhere in the package, because there is no graph:
there is a fixed order.

The circularity the code exists to catch is real, and it is the one these
panels raise — a curve routed through a tensor whose place is a point of that
curve. The panels do not ask for it. In every one of them the curve's shape is
fixed by the frame: it enters at the margin, turns at addresses, or closes
around a plaquette. The tensors that stand on it are consequences. Resolving
the curves whose shape depends only on the frame, then the atoms that stand on
them, draws all five without touching the grammar.

So the largest family is sayable and undrawn. `strings` is the wrong record
for it. What these five want is a **carried tensor**: a tensor whose place is
a point of a wire.

### The F-symbol is sayable today

Two crossing directed strings with a declared crossing order compile and draw,
and so do wires with both ends open. The four corner curves are wires between
open ends; the two lines are strings crossing once; the six labels are labels.
Every element of the panel exists.

What the case does instead is print an abstract fusion tree where the authors
drew six labelled anyon lines. That is a substitution of one diagram of the
F-symbol for another, not an absent element. The target is settled by drawing
it, not by amending the language.

### The MPU wrap is a property of the tensor

The turn from the north face to the east face is a statement about the tensor,
not about any curve crossing it, and the contract already has the spelling.
The wire record class lists skin pairings among the three origins of a wire,
and the declaration door takes them:

```tex
\tndeclare{skin}{shiftright}{base=box,
  pairings={90@1 > 0@1 : R, 270@1 > 180@1 : R}}
```

That is the first row exactly; the mirrored declaration is the second. It does
not draw — the renderer answers `TKZ-KERNEL-RENDER-TODO` for any declared
skin — but no element is missing. `strings` is simply the wrong need on this
entry; the panel contains no string.

### The wrong-source one does not belong here

The projector's declared source is the pulling-through panel, which already
belongs to three other targets. Its own panel is at lines 305–327 — the only
place in Section III where $\frac{1}{|G|}\sum_{g\in G}$ and $L_g$ appear at
all, and the only one matching the target's declared formula and its archival
output. Against that panel the case draws both halves: four group actions on
four indices on the left, a closed loop threading four tensors with a corner
mark on the right. The loop is spelt as five separate joins rather than one
closed curve, which a closed string with the four tensors named as waypoints
would fix today.

So neither recorded need survives contact with the right panel. The remaining
amendment note counts this target in both lists: among four wrong-source
targets and among seven targets carrying the `strings` need. The direct source
reading resolves that overlap: repair the pairing first; against the right
panel, neither recorded need remains.

### None of the four implemented mechanisms answers it

The selector bounds a set of records, and a carried tensor is not a set. The
offset hull and the route form give the corner cut its shape — `route={nw of
A}` is the authors' red curve — and say nothing about what stands on it. The
crossing habit resolves over and under at each meeting and derives the
crossing set instead of requiring it authored; a derived crossing is a fact
about a wire, and a tensor at that crossing is a fact about an atom.

The division is clean. Those four are all about where curves go. The demand
here is about where tensors stand.

## What should be recorded

No amendment. The recommended ledger changes, for the maintainer's signature:

| target | change |
|---|---|
| `rmp-iii-a-spt-mpo` | `strings` → `carried-tensor` |
| `rmp-workbench-iii-g-injective-pull` | `strings` → `carried-tensor`; keep `pulling-through` |
| `rmp-workbench-iii-mpo-injective-white` | `strings` → `carried-tensor`; keep `pulling-through` |
| `rmp-workbench-iii-eq59` | `strings` → `carried-tensor`; keep `torus-cycle` |
| `rmp-iii-a-f-symbol` | drop `strings`; the panel is sayable and the case draws the wrong diagram |
| `rmp-workbench-ii-mpu-wrap-second` | `strings` → `skin-pairings` |
| `rmp-iii-a-g-injective-projector` | re-pair, then re-review; on the right panel neither `strings` nor `group-average` is missing |

One manifest range is wrong and should move with them:

- `rmp-workbench-iii-g-injective-pull` cites lines 414–444, which is the SPT
  panel's range. Only the SPT panel's formula names $U_g$, and only 414–444
  draws it. The pull belongs at 468–497.

Should a carried tensor ever be argued as a primitive rather than as an
address that already exists, the consumer count is not the obstacle. Beyond
the five above, three further blocked targets record the same object in their
notes: the first torus panel ("a closed one-dimensional MPO word with a marked
tensor"), the third ("one torus loop with insertion i"), and the dyon, whose
charge tile stands along its string. Eight consumers, and no new word.

## What this reading does not settle

Three points want the maintainer's eye.

**The projector's source ownership.** The direct author source at 305–327
draws the four $L_g$ actions and the projector ring, while 468–520 draws two
pulling-through panels. That supports moving
`rmp-iii-a-g-injective-projector` to 305–327. However,
`wave2-targets.md` already assigns 305–328 to the archival
`rmp-workbench-iii-eq59-now` target and assigns the published projector to
468–520. Re-pairing the published target would therefore deliberately share
one author block with its archival counterpart and overturn the existing
inventory. The source evidence is recorded here, but that ownership change
still needs the maintainer's corpus decision.

**The three pulling-through panels.** Section III repeats the same figure
three times at 414–444, 468–497 and 501–520, the last marked *veryold* in the
source and drawing discs where the others draw squares. The assignment above
rests on $U_g$, which fixes the SPT panel and therefore fixes the pull. The
assignment of 501–520 to the white MPO-injective panel is the manifest's own
and has not yet been checked against the archival output; the three targets
should be re-paired together, not one at a time.

**The torus surface.** Equation 59 draws a genuine surface, and a curve on a
surface is drawn only where the surface does not hide it. `wind={p,q}` states
the same class on a lattice with identified sides — the same mathematics in a
different picture. Whether the benchmark demands the authors' surface or
accepts the identified lattice is a judgement about what the benchmark
measures, and the recorded need `torus-cycle` stands either way. One defect
turned up alongside it and belongs to the corridor amendment rather than to
this reading: the winding numbers are read only for their presence, so
`wind={1,0}` and `wind={5,7}` draw the same loop, with no diagnostic.

## Evidence

Compiled against the kernel on `main`, each as a standalone picture.

| what was said | result |
|---|---|
| a string from margin to margin crossing an index, order declared | draws |
| two directed strings crossing each other, order declared | draws |
| a wire with both ends open | draws |
| a closed string through named waypoints | draws |
| a mark at `crossing of g and leg n of (1,2)` | draws |
| an atom at `crossing of g and leg n of (1,2)` | XeLaTeX stops in `\pgf@intersectionofpaths` at undefined `\pgf@intersect@next` |
| an atom at `on g 0.25` | `TKZ-KERNEL-RENDER-TODO`, `'onwire address' does not draw yet` |
| an atom at `on L 0.5` on a closed string | the same |
| an atom with a declared skin carrying `pairings=` | `TKZ-KERNEL-RENDER-TODO` |
