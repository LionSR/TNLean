# The shrink ledger

The language grows through the extension gate and shrinks through this
ledger. Six meters live in `tests/tenkz/census-baseline.json`, computed by
`scripts/tenkz_shrink.py meters` and pinned per commit by
`scripts/tenkz_language.py check`. A shrink session runs at every milestone
close, jointly with the simplification gate (#4158): the machine raises
flags (`tenkz_shrink.py flags`), and the session passes only when the
census strictly decreased or every flag carries a written verdict below
(`tenkz_shrink.py gate`). A keep-because verdict carries an expiry; a
verdict that expires twice either executes or becomes doctrine.

The deadline that gives this mechanism urgency: until 1.0 the whole demand
corpus lives in this repository and every deletion is a same-day rewrite;
after CTAN release there is external userspace, deletions need deprecation
cycles, and the cheap regime is gone. Shrinkage is front-loaded into
0.8-0.9 for exactly this reason.

Ledger vocabulary in the registry status field: `kernel` (hard one-in-one-out
budget; the extension gate is the only exception path) · `sugar(<expansion>)`
(must expand into kernel spellings; tenure needs three demand-corpus
consumers) · `alias(<replacement>; sunset=<milestone>)` (reads old documents
only; the sunset executes as a corpus rewrite) · `escape` (sanctioned raw
geometry, metered by M3; every use names a core-grammar gap).

## Session 0 — 2026-07-23 (baseline; classification of the 0.7 registry)

Classification of all 95 key rows: **76 kernel · 4 sugar · 9 escape ·
6 alias**. Sugar expansions follow the 0.6 alias table (`sandwich`,
`physical=`, `boundary=`, `compact`). `inline` remains kernel because its
label style and clearance effects have no independent target keys. Escape
rows are the raw lengths, angles, and dimension pairs (`label shift`, `out`, `in`,
`col/row/sheet vector`, `plane rise/slant`, `radius`). Commands and
environments carry no registry status field; their ledger lives in this
ledger's tables and in the baseline JSON. Ceilings are set at these
actuals; the ratchet does the aspiring.

Baseline meters: M1 {kernel 76, sugar 4, escape 9, alias 6, commands 18,
environments 5} · M2 145 · M3 296 · M4 15.14 · M5 {7 aliases (six key,
one value), 0 missing sunsets} · M6 {3 multi-typed names, 2 union types,
5 shared enum words}.

M3's 296 escape occurrences are dominated by `out=`/`in=` in the free-graph
benchmark cases — the measured cost of hand-routed arcs, burned down by the
strings landing (#4701, #4705). M6's baseline names the overloads the 1.0
kernel deletes; it must never rise on the way there.

### Verdicts on the 56 baseline flags

Low-consumer rows. The demand corpus is the benchmark plus the blueprint;
rows below three consumers either carry a dated justification or die at
their named landing.

| flag | verdict |
|---|---|
| flag:consumers:command:tncut | dies at S4: a cut is a mark form (`LANGUAGE-1.0` §6); expiry 0.9 |
| flag:consumers:command:tndeclareatom | keep-because: the extension door is used by declarations, not figures; teaching examples are deliberately excluded from demand counting; expiry 1.0 |
| flag:consumers:command:tnfuse | demoted at the language landing: a prelude-declared fuse atom (`LANGUAGE-1.0` §9); expiry 0.9 |
| flag:consumers:command:tnset | keep-because: document-scope policy lives in preambles, which the demand corpus excludes by design; expiry 1.0 |
| flag:consumers:environment:tenkzplanes | sugar preset over the lattice frame; dies as an environment at S4; expiry 0.9 |
| flag:consumers:key:annotation:box | folds into mark form `enclosure` at the language landing; expiry 0.9 |
| flag:consumers:key:annotation:brace above | folds into mark forms `brace-above`/`brace-below` at the language landing; expiry 0.9 |
| flag:consumers:key:annotation:label pos | moves unchanged to the mark record at the language landing; expiry 0.9 |
| flag:consumers:key:atom-declaration:skin | keep-because: rides `\tndeclareatom`, same exclusion; expiry 1.0 |
| flag:consumers:key:connection:distinguished | keep-because: two consumers today, torus redraws add more (#4702); expiry 0.9 |
| flag:consumers:key:connection:fused | respelled `weight=double` at the language landing; expiry 0.9 |
| flag:consumers:key:connection:none | dies at the language landing: omit the wire record, or use atom `void=sealed`; expiry 0.9 |
| flag:consumers:key:connection:style | dies with the lattice edge-style pass-through at S3; expiry 0.9 |
| flag:consumers:key:object:combined | folds into the ports grammar at the language landing; expiry 0.9 |
| flag:consumers:key:object:east at | folds into the ports grammar; expiry 0.9 |
| flag:consumers:key:object:west at | folds into the ports grammar; expiry 0.9 |
| flag:consumers:key:object:name | keep-because: addressing becomes load-bearing for every S2+ landing (wires, marks, groups); expiry 0.9 |
| flag:consumers:key:object:removed | becomes atom `void=sealed` at the language landing; expiry 0.9 |
| flag:consumers:key:object:span | folds into `ports=` and `wires=` at the language landing; expiry 0.9 |
| flag:consumers:key:object:species | keep-because: semantic species is a kernel atom field; role consumers move here at the language landing; expiry 0.9 |
| flag:consumers:key:object:tree style | dies with the cd dialect at S4; expiry 0.9 |
| flag:consumers:key:picture:align | keep-because: the only math-axis control until `tenkzeq` lands (#4703); expiry 0.9 |
| flag:consumers:key:picture:bond dir | tombstoned at S4 in favour of wire `dir=`; expiry 0.9 |
| flag:consumers:key:picture:layer sep | folds into the metric/size classes at the equation landing; expiry 0.9 |
| flag:consumers:key:picture:north | keep-because: the four side policies are one kernel concept and north is required by two-dimensional frames; expiry 0.9 |
| flag:consumers:key:picture:open | keep-because: the cell-set boundary algebra is kernel and gains consumers as `open=` spreads; expiry 0.9 |
| flag:consumers:key:picture:pairing | folds into declared skin pairings and wires at the language landing; expiry 0.9 |
| flag:consumers:key:picture:plane lean | folds into `frame=` subkeys at S3; expiry 0.9 |
| flag:consumers:key:picture:polygon | dies with the cd dialect at S4; expiry 0.9 |
| flag:consumers:key:picture:sheet sep | folds into `frame=` subkeys at S3; expiry 0.9 |
| flag:consumers:key:picture:sheets | keep-because: the 2+1D lattice mechanism; condensation/czx redraws consume it (#4704); expiry 0.9 |
| flag:consumers:key:picture:site | dies with the lattice dialect at S3; frame population creates ordinary atoms; expiry 0.9 |
| flag:consumers:key:picture:south | keep-because: the four side policies are one kernel concept and south is required by two-dimensional frames; expiry 0.9 |
| flag:consumers:key:picture:trace style | dies at S2 when the default flips to the cap idiom; expiry 0.9 |
| flag:consumers:key:region:group | folds into address sets at the language landing; expiry 0.9 |
| flag:consumers:key:region:name | keep-because: same addressing argument as object:name; expiry 0.9 |
| flag:consumers:key:setup:inline | dies at the equation landing (math-style sensing, #4703); expiry 0.9 |
| flag:consumers:key:setup:pitch | keep-because: the metric anchor is set in preambles, excluded from demand counting by design; expiry 1.0 |

Merge candidates and lonely types. The detector confirms the compression
review from the outside: the angle pair and the one-off types are the 0.7
grammar's own testimony against itself.

| flag | verdict |
|---|---|
| flag:cooccur:annotation:box+label pos | confirmed merge: enclosure geometry and label placement become one mark record at the language landing; expiry 0.9 |
| flag:cooccur:connection:from+to | keep-because: source and target are distinct endpoints of one wire record, not duplicate controls; permanent |
| flag:cooccur:connection:in+out | confirmed merge: `out=`/`in=` are one concept (a hand-routed arc) and both die at S4 when declared routes land; expiry 0.9 (#4705) |
| flag:cooccur:object:east at+west at | confirmed merge: the two endpoint selectors become one ports record at the language landing; expiry 0.9 |
| flag:lonely-type:cell-set | keep: the cell-set algebra is kernel and gains consumers as `open=` spreads; expiry 0.9 |
| flag:lonely-type:cell-set\|physical | dies at the language landing with the union type (M6); expiry 0.9 |
| flag:lonely-type:frame-enum | becomes the frame-spec type at the language landing; expiry 0.9 |
| flag:lonely-type:math-and-range | dies with the B10 bond-label keyval at the language landing; expiry 0.9 |
| flag:lonely-type:positive-integer\|role-list | dies at the language landing with the union type (M6); expiry 0.9 |
| flag:lonely-type:row | keep: `align=` holds it until tenkzeq; expiry 0.9 |
| flag:lonely-type:row-list | keep: `rows=` is kernel and audit-load-bearing; permanent |
| flag:lonely-type:style-name | dies with the lattice edge-style pass-through at S3; expiry 0.9 |
| flag:lonely-type:typed-port-list | keep: ports are the kernel's typing mechanism; permanent |

Sugar-shaped commands and sunsets.

| flag | verdict |
|---|---|
| flag:sugar-shaped:command:tndots | folds into `\tn[skin=dots]` at the language landing; expiry 0.9 |
| flag:sugar-shaped:command:tnghost | dies at the language landing because addresses name empty cells directly; expiry 0.9 |
| flag:sugar-shaped:command:tnskip | becomes `\tn[void=open]` at the language landing; expiry 0.9 |
| flag:sugar-shaped:command:tntree | confirmed: the tree expander builds kernel atoms and wires; expiry 0.9 |
| flag:sugar-shaped:command:tnarrow | becomes `\tnwire[dir=to]` at the language landing; expiry 0.9 |
| flag:sunset:picture:periodic | executes at the 1.0 freeze with the alias sweep; until then reads old documents |
| flag:sunset:picture:chain axis | executes at the 1.0 freeze with the alias sweep |
| flag:sunset:object:legs at | executes at the 1.0 freeze with the alias sweep |
| flag:sunset:object:rows | executes at the 1.0 freeze with the alias sweep |
| flag:sunset:picture:boundary legs | executes at the 1.0 freeze with the alias sweep |
| flag:sunset:region:label at | executes at the 1.0 freeze with the alias sweep |

Agenda handed to the 0.8 session: the S2/S3/S4 deaths listed above are
verified against these flag ids; any survivor re-raises automatically.

## Session 0 scope-census correction — 2026-07-24

The original census compared parser spellings without their ownership
scopes. The scoped comparison has 98 key rows: **79 kernel · 4 sugar ·
9 escape · 6 alias**. It adds the distinct object `physical` and `label`
keys and the atom-declaration `ports` key, and assigns `name` to connections,
where its parser lives. Census-correction: #4719. The parser-path count M2
is unchanged; this records previously flattened ownership rather than new
package surface.

Corrected meters: M1 {kernel 79, sugar 4, escape 9, alias 6, commands 18,
environments 5} · M2 145 · M3 296 · M4 15.14 · M5 {7 aliases (six key,
one value), 0 missing sunsets} · M6 {4 multi-typed names, 2 union types,
8 shared enum words}.

### Verdicts on the 56 corrected flags

| flag | verdict |
|---|---|
| flag:consumers:command:tncut | dies at S4: a cut is a mark form (`LANGUAGE-1.0` §6); expiry 0.9 |
| flag:consumers:command:tndeclareatom | keep-because: the extension door is used by declarations, not figures; teaching examples are deliberately excluded from demand counting; expiry 1.0 |
| flag:consumers:command:tnfuse | demoted at the language landing: a prelude-declared fuse atom (`LANGUAGE-1.0` §9); expiry 0.9 |
| flag:consumers:command:tnset | keep-because: document-scope policy lives in preambles, which the demand corpus excludes by design; expiry 1.0 |
| flag:consumers:environment:tenkzplanes | sugar preset over the lattice frame; dies as an environment at S4; expiry 0.9 |
| flag:consumers:key:annotation:box | folds into mark form `enclosure` at the language landing; expiry 0.9 |
| flag:consumers:key:annotation:brace above | folds into mark forms `brace-above`/`brace-below` at the language landing; expiry 0.9 |
| flag:consumers:key:annotation:label pos | moves unchanged to the mark record at the language landing; expiry 0.9 |
| flag:consumers:key:atom-declaration:ports | keep-because: declared atoms require an explicit typed-port schema at the extension door; permanent |
| flag:consumers:key:atom-declaration:skin | keep-because: rides `\tndeclareatom`, same exclusion; expiry 1.0 |
| flag:consumers:key:connection:distinguished | keep-because: two consumers today, torus redraws add more (#4702); expiry 0.9 |
| flag:consumers:key:connection:fused | respelled `weight=double` at the language landing; expiry 0.9 |
| flag:consumers:key:connection:none | dies at the language landing: omit the wire record, or use atom `void=sealed`; expiry 0.9 |
| flag:consumers:key:connection:style | dies with the lattice edge-style pass-through at S3; expiry 0.9 |
| flag:consumers:key:object:combined | folds into the ports grammar at the language landing; expiry 0.9 |
| flag:consumers:key:object:east at | folds into the ports grammar; expiry 0.9 |
| flag:consumers:key:object:west at | folds into the ports grammar; expiry 0.9 |
| flag:consumers:key:object:physical | folds into the typed-port grammar at the language landing; expiry 0.9 |
| flag:consumers:key:object:removed | becomes atom `void=sealed` at the language landing; expiry 0.9 |
| flag:consumers:key:object:span | folds into `ports=` and `wires=` at the language landing; expiry 0.9 |
| flag:consumers:key:object:species | keep-because: semantic species is a kernel atom field; role consumers move here at the language landing; expiry 0.9 |
| flag:consumers:key:object:tree style | dies with the cd dialect at S4; expiry 0.9 |
| flag:consumers:key:picture:align | keep-because: the only math-axis control until `tenkzeq` lands (#4703); expiry 0.9 |
| flag:consumers:key:picture:bond dir | tombstoned at S4 in favour of wire `dir=`; expiry 0.9 |
| flag:consumers:key:picture:layer sep | folds into the metric/size classes at the equation landing; expiry 0.9 |
| flag:consumers:key:picture:north | keep-because: the four side policies are one kernel concept and north is required by two-dimensional frames; expiry 0.9 |
| flag:consumers:key:picture:open | keep-because: the cell-set boundary algebra is kernel and gains consumers as `open=` spreads; expiry 0.9 |
| flag:consumers:key:picture:pairing | folds into declared skin pairings and wires at the language landing; expiry 0.9 |
| flag:consumers:key:picture:plane lean | folds into `frame=` subkeys at S3; expiry 0.9 |
| flag:consumers:key:picture:polygon | dies with the cd dialect at S4; expiry 0.9 |
| flag:consumers:key:picture:sheet sep | folds into `frame=` subkeys at S3; expiry 0.9 |
| flag:consumers:key:picture:sheets | keep-because: the 2+1D lattice mechanism; condensation/czx redraws consume it (#4704); expiry 0.9 |
| flag:consumers:key:picture:site | dies with the lattice dialect at S3; frame population creates ordinary atoms; expiry 0.9 |
| flag:consumers:key:picture:south | keep-because: the four side policies are one kernel concept and south is required by two-dimensional frames; expiry 0.9 |
| flag:consumers:key:picture:trace style | dies at S2 when the default flips to the cap idiom; expiry 0.9 |
| flag:consumers:key:region:group | folds into address sets at the language landing; expiry 0.9 |
| flag:consumers:key:region:name | keep-because: same addressing argument as connection:name; expiry 0.9 |
| flag:consumers:key:setup:inline | dies at the equation landing (math-style sensing, #4703); expiry 0.9 |
| flag:consumers:key:setup:pitch | keep-because: the metric anchor is set in preambles, excluded from demand counting by design; expiry 1.0 |
| flag:cooccur:annotation:box+label pos | confirmed merge: enclosure geometry and label placement become one mark record at the language landing; expiry 0.9 |
| flag:cooccur:connection:from+to | keep-because: source and target are distinct endpoints of one wire record, not duplicate controls; permanent |
| flag:cooccur:connection:in+out | confirmed merge: `out=`/`in=` are one concept (a hand-routed arc) and both die at S4 when declared routes land; expiry 0.9 (#4705) |
| flag:cooccur:object:east at+west at | confirmed merge: the two endpoint selectors become one ports record at the language landing; expiry 0.9 |
| flag:lonely-type:cell-set | keep: the cell-set algebra is kernel and gains consumers as `open=` spreads; expiry 0.9 |
| flag:lonely-type:cell-set\|physical | dies at the language landing with the union type (M6); expiry 0.9 |
| flag:lonely-type:frame-enum | becomes the frame-spec type at the language landing; expiry 0.9 |
| flag:lonely-type:math-and-range | dies with the B10 bond-label keyval at the language landing; expiry 0.9 |
| flag:lonely-type:positive-integer\|role-list | dies at the language landing with the union type (M6); expiry 0.9 |
| flag:lonely-type:row | keep: `align=` holds it until tenkzeq; expiry 0.9 |
| flag:lonely-type:row-list | keep: `rows=` is kernel and audit-load-bearing; permanent |
| flag:lonely-type:style-name | dies with the lattice edge-style pass-through at S3; expiry 0.9 |
| flag:sugar-shaped:command:tndots | folds into `\tn[skin=dots]` at the language landing; expiry 0.9 |
| flag:sugar-shaped:command:tnghost | dies at the language landing because addresses name empty cells directly; expiry 0.9 |
| flag:sugar-shaped:command:tnskip | becomes `\tn[void=open]` at the language landing; expiry 0.9 |
| flag:sugar-shaped:command:tntree | confirmed: the tree expander builds kernel atoms and wires; expiry 0.9 |
| flag:sugar-shaped:command:tnarrow | becomes `\tnwire[dir=to]` at the language landing; expiry 0.9 |

The 1.0 alias sweep also covers the value alias omitted from the original
table:

| flag | verdict |
|---|---|
| flag:sunset:connection:route=curve | executes at the 1.0 freeze with the alias sweep |

## Session note: the kernel language landing (2026-07-24)

The 1.0 kernel surface enters the registry under `Extension-gate: #4687`
after the LANGUAGE-1.0.md sign-off.  Kernel rows cannot hold demand-corpus
tenure before the S4 surface swap gives the corpus kernel spellings, so
each below-tenure flag carries the same dated verdict: consumers arrive
with the swap and the redraw campaign, and any row still naked at the 0.8
close dies there.

| Flag | Verdict |
|---|---|
| flag:consumers:command:tenkzkernel | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tnbond | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tndeclare | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tngroup | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tnmark | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tnprose | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tnwire | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:environment:tenkzeq | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:at | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:cluster | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:conjugate | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:down | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:label pos | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:name | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:nudge | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:ports | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:role | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:skin | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:species | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:up | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:void | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:wide | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:wires | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:lonely-type:bond-policy | keep-because: the picture topology has one generated-bond policy shared by every frame (#4687); expiry 1.0 |
| flag:lonely-type:integer | keep-because: integer is the primitive count type of the ring expander (#4687); expiry 1.0 |
| flag:lonely-type:size-class | keep-because: the equation metric owns one size-class policy across its panels (#4687); expiry 1.0 |
| flag:lonely-type:void-policy | keep-because: open and sealed holes are one atom-topology policy (#4687); expiry 1.0 |
| flag:consumers:key:kernel-declare:base | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-declare:hue | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-declare:pairings | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:form | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:inset | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:label pos | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:name | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:nudge | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:outline | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:slot | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:align | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:bonds | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:boundary | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:check | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:cols | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:east | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:frame | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:lattice | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:north | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:open | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:physical | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:ring | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:rows | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:sandwich | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:size | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:south | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:surface | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:trace | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:west | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-setup:pitch | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-setup:sizes | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-setup:strict | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-setup:theme | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:around | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:bend | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:closed | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:cross | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:dir | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:kind | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:name | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:route | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:species | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:via | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:weight | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:wind | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:lonely-type:check-spec | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:crossing-list | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:frame-spec | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:hue-source | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:port-pair-list | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:size-table | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:sugar-shaped:command:tntree | confirmed by contract: `\tntree` is an expander sugar row (`LANGUAGE-1.0` 9); dies into the kernel at the S4 swap; expiry 0.9 |
| flag:sugar-shaped:command:tnarrow | tombstoned by contract: `\tnarrow` migrates to `\tnwire[dir=to]` (`LANGUAGE-1.0` 10); deleted at the S4 swap; expiry 0.9 |
| flag:sugar-shaped:command:tnskip | confirmed by contract: `\tnskip` is the sugar row `\tn[void=open]` (`LANGUAGE-1.0` 9); dies into the kernel at the S4 swap; expiry 0.9 |
| flag:consumers:command:tncut | dies at S4: a cut is a mark form (`LANGUAGE-1.0` §6); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:command:tndeclareatom | keep-because: the extension door is used by declarations, not figures; teaching examples are deliberately excluded from demand counting; expiry 1.0 (re-affirmed 2026-07-24) |
| flag:consumers:command:tnfuse | demoted at the language landing: a prelude-declared fuse atom (`LANGUAGE-1.0` §9); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:command:tnset | keep-because: document-scope policy lives in preambles, which the demand corpus excludes by design; expiry 1.0 (re-affirmed 2026-07-24) |
| flag:consumers:environment:tenkzplanes | sugar preset over the lattice frame; dies as an environment at S4; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:annotation:box | folds into mark form `enclosure` at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:annotation:brace above | folds into mark forms `brace-above`/`brace-below` at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:annotation:label pos | moves unchanged to the mark record at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:atom-declaration:ports | keep-because: declared atoms require an explicit typed-port schema at the extension door; permanent (re-affirmed 2026-07-24) |
| flag:consumers:key:atom-declaration:skin | keep-because: rides `\tndeclareatom`, same exclusion; expiry 1.0 (re-affirmed 2026-07-24) |
| flag:consumers:key:connection:fused | respelled `weight=double` at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:connection:none | dies at the language landing: omit the wire record, or use atom `void=sealed`; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:connection:style | dies with the lattice edge-style pass-through at S3; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:object:combined | folds into the ports grammar at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:object:east at | folds into the ports grammar; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:object:physical | folds into the typed-port grammar at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:object:removed | becomes atom `void=sealed` at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:object:span | folds into `ports=` and `wires=` at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:object:species | keep-because: semantic species is a kernel atom field; role consumers move here at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:object:tree style | dies with the cd dialect at S4; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:object:west at | folds into the ports grammar; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:align | keep-because: the only math-axis control until `tenkzeq` lands (#4703); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:bond dir | tombstoned at S4 in favour of wire `dir=`; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:layer sep | folds into the metric/size classes at the equation landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:north | keep-because: the four side policies are one kernel concept and north is required by two-dimensional frames; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:open | keep-because: the cell-set boundary algebra is kernel and gains consumers as `open=` spreads; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:pairing | folds into declared skin pairings and wires at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:plane lean | folds into `frame=` subkeys at S3; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:polygon | dies with the cd dialect at S4; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:sheet sep | folds into `frame=` subkeys at S3; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:sheets | keep-because: the 2+1D lattice mechanism; condensation/czx redraws consume it (#4704); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:site | dies with the lattice dialect at S3; frame population creates ordinary atoms; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:south | keep-because: the four side policies are one kernel concept and south is required by two-dimensional frames; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:trace style | dies at S2 when the default flips to the cap idiom; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:region:group | folds into address sets at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:region:name | keep-because: same addressing argument as connection:name; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:setup:inline | dies at the equation landing (math-style sensing, #4703); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:setup:pitch | keep-because: the metric anchor is set in preambles, excluded from demand counting by design; expiry 1.0 (re-affirmed 2026-07-24) |
| flag:cooccur:annotation:box+label pos | confirmed merge: enclosure geometry and label placement become one mark record at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:cooccur:connection:from+to | keep-because: source and target are distinct endpoints of one wire record, not duplicate controls; permanent (re-affirmed 2026-07-24) |
| flag:cooccur:connection:in+out | confirmed merge: `out=`/`in=` are one concept (a hand-routed arc) and both die at S4 when declared routes land; expiry 0.9 (#4705) (re-affirmed 2026-07-24) |
| flag:lonely-type:frame-enum | becomes the frame-spec type at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:lonely-type:math-and-range | dies with the B10 bond-label keyval at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:lonely-type:style-name | dies with the lattice edge-style pass-through at S3; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:sugar-shaped:command:tndots | folds into `\tn[skin=dots]` at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:sugar-shaped:command:tnghost | dies at the language landing because addresses name empty cells directly; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:cooccur:object:east at+west at | confirmed merge: the two endpoint selectors become one ports record at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:lonely-type:cell-set\|physical | dies at the language landing with the union type (M6); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:lonely-type:positive-integer\|role-list | dies at the language landing with the union type (M6); expiry 0.9 (re-affirmed 2026-07-24) |
