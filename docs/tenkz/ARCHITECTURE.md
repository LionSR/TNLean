# tenkz architecture

The implementation target follows the data, in one direction:

```text
language -> model -> style/atoms -> geometry -> dialect layout -> rendering -> events
```

The stages are ownership boundaries, not suggestions.  A later stage may
consume an earlier result; it may not parse public syntax again or change the
topology it received.

## Current migration boundary

The logic-free load map, executable language registry, typed atom extension,
and model-freeze seam are active.  The historical dialect files still
contain substantial parser, geometry, rendering, and event code together,
and many established private controls have not yet moved to the owner-prefixed
form.  They are loaded behind the staged seam to preserve the verified
257-fixture contract while that internal migration proceeds.

Consequently, the stage sections below are normative ownership rules for new
code and the destination for migrated code; they are not a claim that every
legacy implementation path already crosses the normalized model.  Moving a
dialect path across that boundary requires exact event comparison and the
full legacy corpus before its old path can be removed.

## Load map

`tenkz.sty` is a logic-free load map.  It establishes the package identity and
loads the stages in dependency order.  Feature code, state, key registration,
and diagnostics belong to an owning stage.

Every internal file begins with a five-line contract:

```tex
% Input:       records or services consumed from the previous stage
% Output:      records or services promised to the next stage
% Owned state: local and global state for this stage only
% Invariants:  facts established before output is handed on
% Next stage:  the sole downstream consumer of the primary output
```

Private control sequences use `\__tenkz_<owner>_...:`.  The public-symbol
census rejects accidental exports.  A public control sequence exists only
when the language registry declares it.

## 1. Language

The language stage implementation is `tex/tenkz/tenkz-language.code.tex`.  It
owns public environments, commands, keys, compatibility aliases, value types,
defaults, and diagnostics.  Its executable registry,
`tex/tenkz/tenkz-language-registry.tex`, is the single vocabulary source for
parser registration, manual reference generation, linting, and API census.

Language parsing produces declarations.  It must report stable diagnostic
codes with normalized context and an actionable expected-value clause, for
example:

```text
[TKZ-GRID-UNKNOWN-VALUE] picture=3 cell=(2,4) key=frame;
got diagonal; expected horizontal|vertical; try frame=vertical
```

An invalid declaration does not reach the model.  Unsupported requested ink
is an error, never a warning followed by a smaller drawing.

## 2. Model

The model stage owns normalized records for pictures, atoms, connections,
closures, regions, and annotations.  Dialect surface syntax disappears here:
records use common fields and common value types.  References are resolved,
ports are typed, spans and cell sets are checked, and topology is complete
before the model is released.

The model is the shared source for rendering and `.tnlog` emission.  An event
stream reconstructed from pre-normalized syntax is not authoritative.

## 3. Style and atoms

This stage owns the metric, semantic themes, atom descriptors, label policy,
ports, and silhouettes.  A semantic role resolves to a style without changing
an atom's kind.  `\tndeclareatom` registers a typed atom descriptor; it does
not inject drawing code into a picture body.

House themes may rebind semantic ink and typography.  They do not add keys,
connections, or topology.

## 4. Geometry

Geometry owns coordinate frames, measurement, silhouettes, daylight,
obstacle routing, crossings, and measured enclosure contours.  It answers
spatial questions from validated model records and style metrics.

Clearance is measured, not predicted: the silhouette gives the occupied ink
and one daylight constant supplies separation.  Geometry may choose among
declared routes; it may not invent a connection or suppress an obstacle.

## 5. Dialect layout

Each front end translates its layout grammar into requests against the shared
geometry service:

- grid layout for `tenkz`;
- lattice layout, including the `tenkzplanes` preset;
- fusion-tree layout for the standalone `\tntree` atom.

Dialect layout owns only placement rules that are genuinely specific to that
genre.  Shared keys and records are not reimplemented here.

## 6. Rendering

Rendering consumes resolved records and geometry.  It emits ink only.  It
does not parse user tokens, allocate semantic names, mutate topology, or
silently recover from unsupported requests.  Dialect renderers contain only
ink that cannot be expressed by the shared atom, connection, region, and
annotation renderers.

## 7. Events

The events stage serializes the resolved model that rendering consumed.  The
versioned `.tnlog` includes picture identity, atoms, connections, face ports,
closures, boundaries, regions, annotations, and relevant resolved policy.
Changing the event schema changes its version.

Audits compare meaning, not drawing order.  Canonical and compatibility
spellings must normalize to equivalent semantic events.  A renderer and an
auditor disagreeing about a record is an architecture violation, because both
must consume the same resolved model.

## Change discipline

A capability change begins with manifested consumers and the language entry,
then extends the model and only the necessary downstream stages.  It ships
with a teaching example, a coded failure, a negative test, semantic-event
coverage, and visual inspection.  Internal refactors preserve the established
257-fixture render and event behavior unless a separately reviewed contract
change says otherwise.
