# The tenkz language

This file is the normative semantic contract for the public language.  The
generated reference in the manual is the normative inventory of exact
commands, environments, keys, value types, aliases, and defaults.

> A picture chooses one layout; its options declare topology and policy; its
> body declares atoms, connections, regions, and annotations.

That sentence is the whole mental model.  A layout decides how positions are
obtained.  Picture options describe facts shared by the picture.  Body
declarations name the things that inhabit it.  Rendering is a consequence of
those declarations, not a second authoring language.

## Choose one layout

There is one genre.

- `tenkz` is the regular one-dimensional contraction grid.  Rows are layers,
  columns are sites, and adjacent compatible cells contract implicitly.

An irregular typed graph is not a genre of its own: it is addressed
`\tn`, `\tnwire`, and `\tnmark` records of the kernel language.  A
spatial lattice, sheet, or measured region is a kernel picture: a frame
with `lattice=` or `planes` sugar, or a declared basis.

`\tnpic` is not a layout.  It is a composition wrapper that
lets one `tenkz` picture behave as an inline mathematical atom.

Choose the layout from the topology.  Do not choose it from the desired
silhouette, and do not cross into another layout merely to obtain a style.

## The five vocabulary classes

Every public word belongs to exactly one class.

1. **Atoms** declare tensors, matrices, and fusion vertices.
2. **Connections and closures** declare bonds, traces, cups, and cuts.
3. **Regions and annotations** declare measured regions, braces, labels, and
   other non-topological marks.
4. **Composition** places pictures in equations, inline mathematics, or
   aligned families without changing the pictures' models.
5. **Setup and extension** declares document-wide policy, semantic themes,
   species, and typed atom kinds.

A command is warranted only when it declares a new object in one of these
classes or introduces a grammatical class of its own.  A key modifies the
record already being declared.  Thus `\tnwire` is a command because a wire
is a connection record; `species=` is a key because it is a property of
that wire.  This test is documented beside every public command in the
generated reference.

## Grammar rules

1. One picture has one layout environment.  Nesting is composition and must
   use a documented composition form.
2. Picture options declare picture-wide topology or policy.  They do not
   create hidden atoms.
3. Body commands create records.  Declaration order may establish references
   - for example a join may refer only to atoms already named - but it may not
   change the meaning of an earlier record.
4. Validation finishes before measurement.  A renderer never repairs,
   guesses, or silently drops invalid topology.
5. Open ink is mathematical data.  A matrix has open indices, a map keeps its
   input and output legs, and a scalar has none.  `boundary=periodic`, `cup`,
   and `boundary=none` are different mathematical operations.
6. A diagrammatic equation is valid only when corresponding sides have the
   intended boundary signatures.  The `.tnlog` stream records the resolved
   signatures used for rendering.
7. Raw TikZ is not public tenkz syntax.  House styles may change typography
   and semantic hues; they may not add topology or bypass validation.

## Scope and type rules

Scope is explicit at every level.

- **Document scope**: `\tnset{...}` and declarations such as species and atom
  kinds.  These affect later pictures until the surrounding TeX group ends.
- **Picture scope**: the option list of the chosen environment.  Shared key
  names have the same value type and meaning in every genre.
- **Object scope**: the option list of the command that declares the object.
- **Connection scope**: the option list of the command or side policy that
  declares that connection or closure.

A key is not resolved by searching several scopes for a convenient match.
The generated reference names its one legal scope and value type.  Shared
names such as `role`, `species`, `pitch`, and `tensor style` retain one meaning
wherever the registry exposes them.

Free-graph ports and extension ports are typed.  The base kinds are `virtual`
and `physical`; a connection between unequal kinds is an error.  Custom atoms
are introduced by

```tex
\tndeclareatom{\tnprojector}{
  skin=box,
  ports={west:virtual,east:virtual,up:physical}
}
```

The declaration creates a one-label atom command with optional per-use cell
keys.  Faces are `west`, `east`, `up`, and `down`; types are `virtual` and
`physical`.  It supplies a sanctioned skin and the complete typed-port
contract.  Bare anchors are not an extension API.  There is no public
`\tndefine`: repeated whole figures remain ordinary TeX composition, not new
tenkz grammar.

## Canonical spellings and aliases

One concept has one canonical spelling.  Current tutorials, recipes,
benchmarks, and new source use canonical spellings only.  Compatibility
aliases exist solely to read older documents; the generated reference lists
them in a separate appendix and the linter can reject them in canonical-only
sources.

The canonical examples include these distinctions:

- `boundary=periodic` closes each row to itself; `west=cup` or `east=cup`
  connects adjacent layers.
- `boundary=none` seals an object; omitting it retains the canonical open
  boundary when the object is a matrix or map. A side that names its own
  policy overrides the picture's: `boundary=none, east=cup` seals the west
  and bends the east, because the specific statement outranks the general
  one. A cup that finds no pair to bend is an error, not a blank space.
- `route=arc` is canonical; `route=curve` is a compatibility alias.

## Extension gates

The public language grows only from demonstrated mathematical demand.

- A new key needs at least three manifested RMP benchmark consumers.  The
  proposal identifies their target IDs and uses one value type at every
  exposed scope.
- A new command needs a new grammatical class.  If the desired behavior is a
  property of an existing record, it is a key instead.
- Every accepted capability has a registry entry, a standalone teaching
  example of about fifteen lines or fewer, a stable coded diagnostic, a
  negative test, and a cross-review for teachability.
- Unsupported requested ink is a hard error.  A warning followed by silent
  omission is not a partial implementation.

The executable registry is `tex/tenkz/tenkz-language-registry.tex`; the
language-stage implementation is `tex/tenkz/tenkz-language.code.tex`.  The
registry drives parser registration, generated manual tables, lint schemas,
and the public symbol census.  Those consumers may present the data
differently, but they may not maintain independent lists.
