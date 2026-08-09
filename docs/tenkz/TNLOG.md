# The tenkz event stream

Every tenkz run writes one line-oriented event stream to `\jobname.tnlog`.
The stream is a public surface: `DESIGN.md` §Compatibility ownership names it
beside the TeX surface, and a release decision that keeps one compatible cannot
excuse a break in the other. This page declares the format. It states what the
writer emits, what the reader accepts, and — where those two differ — which one
is the contract.

`DESIGN.md` governs where this page and it disagree. The compatibility rules in
§7 are restatements of the `[event_format]` block there.

## 1. Format version

The event format is version **1.0**, meaning the surface this page describes.
No stream carries that number in band. There is no header line, no magic
string, no producer record, and no trailer: the first byte of a `.tnlog` is the
first event, in practice always a `picture` line.

`DESIGN.md` requires an explicit machine-readable version on every stream
before the 0.9 freeze, and assigns the header spelling and the ignorable-kind
marking to #4162 and #4703. Until that change lands, a reader cannot negotiate
and the surface is held by whole-file digest instead: `tests/tenkz/`
`golden-events.sha256` (9 corpus streams), `tests/tenkz/kernel/golden.sha256`
(12 kernel probes), and `tests/tenkz/strings/golden.sha256` (30 string probes)
pin exact bytes. Those digests make field order and spacing part of the pinned
surface even though no schema states them, which is why §4 is normative here.

## 2. Line syntax

```
line   ::= kind ( "|" key "=" value )* LF
kind   ::= bytes containing neither "|" nor "="
key    ::= bytes containing neither "|" nor "="
value  ::= bytes containing no "|"
```

- The separator is a single `|` (U+007C). One precedes every field; none
  follows the last.
- A field splits at its **first** `=`, so a value may contain `=` freely. A
  value may be empty: `kernel-boundary|signature=` and `check|…|interface=`
  both occur.
- **There is no escaping.** No quoting, no backslash, no percent-encoding. A
  `|` inside a value would silently shred the line into extra fields. Nothing
  in the format prevents this; the writers simply never produce one, and any
  new value that could contain `|` needs an escaping change first, which is a
  major change under §7.
- Kernel record values are flattened with `\tl_to_str:n`, so author
  mathematics survives verbatim, including the space TeX inserts after a
  multi-letter control sequence: `label=\overline {A}`.
- Lines are written with `\immediate\write` to a file stream, which is not
  subject to `\maxprintline`, so a line has no length limit. A
  `glyph-geometry` line runs to about 180 bytes.
- Blank lines are legal and ignored. Leading and trailing space around a key
  or a value is stripped.

One writer produces every line, `\tenkz@event` in
`tex/tenkz/tenkz-core.code.tex`. It opens the stream at `\AtBeginDocument` and
closes it at `\AtEndDocument`; an event expanded in the preamble is discarded.
The kernel reaches the writer through a catcode-independent alias and rebinds
it to a suppressor for the duration of its topology prepass, so a stream
records exactly one settled pass.

## 3. Event kinds

Eighteen kinds are emitted and eighteen appear in the reader's table. The two
sets are not equal: `geomprobe` is emitted and untabled, `wire-geometry` is
tabled and unemitted. §8 records both.

The following block is the machine-readable declaration. `tests/tenkz/`
`release-harness/` reads it and the reader's table together, so the two cannot
drift apart unnoticed.

```toml tenkz-event-kinds-v1
schema = 1
version = "1.0"
emitted = [
  "atom",
  "bbox",
  "check",
  "closure-rail",
  "frame",
  "geomprobe",
  "glyph-geometry",
  "ink-use",
  "kernel-boundary",
  "label-use",
  "mark",
  "picture",
  "string",
  "stringbead",
  "stringcross",
  "tree",
  "warning",
  "wire",
]
reader_table = [
  "atom",
  "bbox",
  "check",
  "closure-rail",
  "frame",
  "glyph-geometry",
  "ink-use",
  "kernel-boundary",
  "label-use",
  "mark",
  "picture",
  "string",
  "stringbead",
  "stringcross",
  "tree",
  "warning",
  "wire",
  "wire-geometry",
]
```

### Kernel records

`atom`, `wire`, `mark`, and `frame` share one emitter and therefore one layout:

```
<kind>|id=<class>-<n>|<key>=<value>|<key>=<value>…
```

They carry no `picture=` field. A record belongs to the picture whose header
most recently opened, and a `check` event or the next `picture` header closes
that ownership. Ids come from one counter shared by all four classes, so a
picture's ids interleave: `atom-1, atom-2, mark-3, atom-4`.

| Kind | Fields seen in emitted streams | Meaning |
|---|---|---|
| `atom` | `addr`, `kind`, `label`, `label-pos`, `name`, `node`, `skin`, `ports`, `member`, `cell-row`, `cell-col`, `basis-*`, `populated`, `conjugate`, `cluster-of`, `group`, `species` | one tensor record |
| `wire` | `kind` (`index`, `string`, `pairing`), `from`, `to`, `from-open`, `to-open`, `name`, `origin`, `species`, `cross`, `crossing`, `wind`, `closed`, `row`, `col`, `side`, `top`, `bottom`, `host`, `port-face`, `port-slot`, `port-type` | one index, string, or pairing edge |
| `mark` | `form` (`label`, `enclosure`, `bracket`, `prose`), `label`, `label-pos`, `node`, `members`, `slot` | one annotation record |
| `frame` | `map` (`plane`, `group`, `subframe`), `scope`, `a`, `b`, `c`, `d`, `dx`, `dy`, `transverse-x`, `transverse-y`, `group`, `scale` | one coordinate frame or sub-frame |

The field vocabulary of these four kinds is **open**. A record carries whatever
the model store holds for it, so this table lists what streams contain today
rather than a closed set. The closed part of their contract is the layout: `id`
first, the rest sorted, no `picture=`.

### Explicit-field events

| Kind | Fields, in emitted order | Meaning |
|---|---|---|
| `picture` | `id` (`k<n>`), `lang` (always `kernel`), `metrics` (when a metric profile is declared), `scope` (when inside `tenkzeq`) | opens a picture |
| `kernel-boundary` | `signature` | closes the record block with the picture's exposed-index multiset, comma-space joined, possibly empty |
| `check` | `scope`, then `relation` or `product`, `result`, `modulo`, and result-specific fields | one equation-level verdict, emitted after every picture of its scope |
| `warning` | `picture`, `code`, then code-specific fields | one non-fatal geometry or readability diagnostic |
| `string` | `id`, `kind` (`open`, `closed`, `wind`, `around`), `class`, `pts`, `flank1`, `flank2` | one declared curve |
| `stringbead` | `id`, `t`, `x`, `y` | one bead at parameter `t` on a string |
| `stringcross` | `under`, `over`, `hits` | one over-under crossing |
| `ink-use` | `picture`, `class` (`glyph`, `wire`), `id`, `shape` | opens an ink-owner scope for the geometry that follows |
| `label-use` | `picture` | a label node claimed no ink owner |
| `bbox` | `picture`, `class=label`, `id`, `owner`, `xmin`, `xmax`, `ymin`, `ymax`, `shape`, `radius` | one measured label box, in integer scaled points |
| `glyph-geometry` | `picture`, `owner`, `shape`, `xmin`, `xmax`, `ymin`, `ymax`, `radius`, `stroke`, `x1`, `y1`, `x2`, `y2`, `x3`, `y3` | one measured glyph silhouette, in integer scaled points |
| `closure-rail` | `picture`, `name`, `row`, `side`, `west`, `east`, `stroke`, `clear`, `points` | one traced row's closure: the two virtual ends it joins, or `none` where the row has no site on that side, the half stroke it is drawn with, the standoff the open indices of the rows it passes demand of it, outward from its own row line — `none` for a frame arc, which stands off no row line — and the semicolon-separated polyline it lays, all in integer scaled points |
| `tree` | `picture`, `id`, `style`, `leaves`, `vertices`, `topology`, `role`, `species` | one fusion tree |
| `geomprobe` | `id`, then a caller-supplied payload | one geometry probe, for fixtures |

`check` results are `equal`, `off`, `malformed`, `contracted`, and `mismatch`.
Each fixes further required fields: `equal` needs `relation` and `signature`,
`off` needs `relation` and `reason`, `malformed` needs `reason`, `panels`, and
`relations`, `contracted` needs `product` and `signature`, and `mismatch` needs
`relation` unless it carries `product`.

`x` and `y` on `stringbead` carry a `pt` suffix. Every other coordinate in the
stream is an integer count of scaled points with no unit.

## 4. Order

Order is part of the surface, because the golden digests hash whole files.

1. Fields of a kernel record are `id` first, then the remaining `key=value`
   pairs sorted in ascending order **of the whole pair string**, not of the
   key. This is why `label-pos=180` precedes `label=A`: `-` sorts before `=`.
2. Fields of an explicit-field event follow that event's template, in the order
   given in §3.
3. Within a picture: the header, then the records grouped by class in the order
   `atom`, `wire`, `mark`, `frame`, then `kernel-boundary`, then any geometry
   warnings, then the string, bead, crossing, and measured-ink events of the
   render pass.
4. `check` events follow every picture of their scope.
5. Exactly one `kernel-boundary` per kernel picture.

## 5. What the reader enforces

`scripts/tenkzlib/tnlog.py` is the canonical reader; `HACKING.md` §Shared
parsers requires every checker that needs structured fields to use it. Its
`parse_log` reports through two injected callbacks, `hard` and `advisory`, both
of which default to discarding the finding — a caller that supplies neither
gets silent acceptance. A hard finding also sets `Event.valid = False` and
removes the event from `ParsedLog.valid_events` and from every picture's event
list.

Hard:

- a field with no `=`;
- a repeated key on one line;
- a tabled field whose value fails its validator, on a tabled kind;
- a `check` without `scope` or `result`, or without the fields its result
  requires;
- a `check` carrying `picture=`;
- a tabled kind other than `picture` with no `picture=`, unless it is a kernel
  record inside an open kernel picture;
- a `picture` with a malformed or repeated `id`;
- a reference to an undeclared picture.

Advisory:

- an untabled event kind;
- a `lang` outside the caller's `known_langs`, when the caller supplies one.

## 6. What the writers guarantee and the reader does not check

These hold in every emitted stream and are invisible to `parse_log`. They are
the contract; the reader is merely permissive about them, and a change to any
of them is a change to the surface.

| Invariant | Reader |
|---|---|
| the field order of §4.1 and §4.2 | never inspects order |
| the stream order of §4.3 and §4.4 | checks only that a record follows a header |
| exactly one `kernel-boundary` per kernel picture (§4.5) | permits zero or several; `scripts/tenkz_audit.py` enforces it |
| no value contains `|` | would shred such a line into extra fields |
| picture ids are `k`-prefixed and monotonic | accepts bare integers as well |
| every kind other than the four records carries its documented fields | requires a complete field set for `check` only |
| an untabled field never appears on a tabled kind | accepts any untabled field as opaque |

The last row is the one to read twice. `picture`'s `metrics`, every `warning`
payload field beyond `code`, `check`'s `modulo`, `left-kind`, and `right-kind`,
`string`'s `class`, `flank1`, and `flank2`, and the whole open vocabulary of
the four record kinds all pass through unvalidated. The reader tolerating a
field is not the same as the format having one.

Semantic checking above the parser belongs to `scripts/tenkz_audit.py`, which
checks tree topology against its leaf and vertex counts, rejects empty
pictures, enforces one boundary per kernel picture, fails on a `check` result
of `mismatch` or `malformed`, and audits label overlap, bounding-box coverage,
repeated topology, and equation boundaries. Its own table of emitted kinds is
maintained by hand.

`closure-rail`'s `clear` is the worked example of §7's optional-field rule. It
arrived on a kind that already existed, so the reader validates it when it is
there and asks nothing when it is not, and a stream written before it reads
clean. What the reader cannot then say is whether a live picture stopped
writing it, so that reading is taken where the live library is the thing being
read: `scripts/tenkz_kernel_probes.sh` fails on a closure the kernel wrote
without a standoff, and measures the drawn contour against it there.

## 7. Compatibility

From `DESIGN.md`'s `[event_format]` block:

- A reader accepts every minor revision of its own event major and rejects a
  different major with a direct diagnostic.
- A reader ignores an unknown optional field.
- A reader ignores an unknown event kind only when the schema marks that kind
  explicitly ignorable and skipping it preserves the validity and meaning of
  every recognized record.
- Any addition that cannot meet those conditions increments the event major.

Against the release classes in `RELEASE-POLICY.md` §1: a patch keeps the stream
byte-stable for unchanged input; a minor may add a kind or an optional field,
increments the event minor, and requires the reader to accept both spellings; a
major may break the format and increments the event major.

Two of those four rules are declarations rather than implemented behaviour.
The reader has no version concept at all, so "same major, any minor" is
unimplemented; and it treats **every** unknown kind as ignorable with an
advisory, rather than only explicitly marked ones. The unknown-optional-field
rule is implemented, as §6's last row describes, though by permissiveness
rather than by a declared optional-field set. Closing the gap is #4162 and
#4703's work, and no release may claim the event surface is version-negotiable
before it lands.

## 8. Known defects

Recorded here so a reader of a stream is not surprised, and so the freeze can
decide each one.

- **`geomprobe` is untabled.** The reader gives it an advisory and, because it
  carries no `picture=`, drops it before picture attachment. It survives only
  in `ParsedLog.events`. Fixtures that read probes must read that list.
- **`wire-geometry` is tabled and unemitted.** A complete validator set exists
  for a kind nothing writes.
- **`atom`'s `cell` validator is unreachable.** Kernel atoms carry
  `addr=(r,c)` or `addr=(s,r,c)`; no emitter writes `cell=`. Only the parser's
  own tests exercise that validator.
- **The integer-id picture header has no call site.** `\tenkz@beginpicture` is
  written only by synthetic fixtures, so `\tenkz@pictureid` stays 0 in every
  real run.
- **`tree` and the `sheet-range` warning emit `picture=0`.** For `tree` the
  reader special-cases it. The `sheet-range` warning is not special-cased, so
  were it to fire it would draw a `dangling-picture-ref`. Both follow from the
  previous item.
