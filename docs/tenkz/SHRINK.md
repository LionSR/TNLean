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
| flag:sugar-shaped:command:tngroup | keep-because: a group is the composition grammar for one transform over several atoms and wires, not atom sugar; permanent (re-affirmed 2026-07-25) |

`Extension-gate: #4700` (2026-07-25) adds one shared `frame=` concept at group
and object
scope. The picture spelling already exists; the new parser paths make the
same rotation type composable without adding a second transform vocabulary.


## Session 1 — 2026-07-25 (booking the nine amendments)

The nine amendments were signed on the argument that the language ends
smaller than it started. That promise is kept here or nowhere. This session
books it against the contract's own tables, counts each retirement once, and
refuses every saving that another ledger has already recorded.

### What the contract now says, per ledger

| ledger | before | after | net |
|---|---|---|---|
| kernel key rows (`LANGUAGE-1.0` 2.2 to 2.6) | 50 | 41 | **−9** |
| declaration keys | 3 | 3 | 0 |
| commands | 7 | 6 | **−1** |
| record classes, environments | 4, 2 | 4, 2 | 0 |
| alphabet rows | 6 | 4 | **−2** |
| alphabet values | — | — | **−17** (22 out, 5 in) |
| address productions | 9 | 8 | **−1** |
| sugar rows | 27 | 25 | **−2** |
| value types | 24 | 22 | **−2** (5 out, 3 in) |
| tombstone rows | 23 | 36 | **+13**, which is what a tombstone table is for |
| metric ratios | 45 | 45 | **0** |
| registry census M1 | 191 | 191 | 0 |
| parser paths M2 | 216 | 216 | 0 |

Keys retired, nine: the mark nesting, the atom displacement, the mark
displacement, the wire waypoints, the wire curvature, the wire weight, the
two page-relative atom keys, and the equation audit. Keys added, none. The
tenth retirement the notes name — the mark tint — is one exchange with the
`species=` every other record carries, of net zero, and the two halves are
deferred together to the change that adds the parser row. The promised −9
holds either way, and splitting the exchange would have booked a saving in
one session and its cost in another.

Alphabet values, spelled out: eight face words, five tint words, three weight
words, four mark forms and two frame words leave; two frame words and the
three joiner classes arrive. Value types: the audit specification, the frame
specification, the plain number, the mathematics list and the cell set leave;
the selector, the route's side-of-a-selection family and the angle arrive.
The mathematics list is a departure the notes missed — its only two consumers
were the two page-relative atom keys, and it leaves with them.

**A correction to this table, made under review.** The value-type row first
read minus three, on two arrivals. It is minus two, on three. Retiring the
face words made a label placement an angle as well as a face, and no type in
the list held an angle: the plain number left in this same session, and a
bearing is not a number anyway, because a number is a page quantity with no
frame while an angle is read in a record's own axes and transforms with them.
Typing the placement `number` would have bought the lower count by reviving a
type these amendments retired and by flattening the distinction the
local-axes rule exists to make. The angle is minted, the census gains one,
and the row says so.

Two ledgers do not move with it. The alphabet table gains no row, because an
angle is not a closed alphabet and the four compass words are sugar rather
than an alphabet — and that sugar is the row already attributed below to the
change that lands angle-valued faces, covering faces and label placements by
the same rule. Booking it here for the placement, having declined to book it
here for the face, would be the same error twice.

### What was refused, and why

**The route word.** The batch counts a retired `route=around` among the
alphabet values. It was proposed by the corridor note and withdrawn by its
companion before either was signed, so it never entered the contract's
tables. A value that never arrived cannot depart. Not booked.

**A third frame value.** The batch counts three. The contract's frame
alphabet holds `flat`, `vertical` and `rotate=<degrees>`, and says in as many
words that the projected and circular frames are not public grammar. Two
words leave and two arrive; the saving is that the frame specification stops
being a parameterised type, which is already counted among the value types.
Booked as zero, not as −3.

**The sheet family.** `sheets`, `sheet sep`, `pairing` and `sheet vector` are
0.7 rows the ledger sentenced at Session 0 — two fold into frame subkeys, one
into declared skin pairings, and the fourth is an escape row. The cell basis
executes the one keep-because standing over them, and that verdict is updated
below; no new saving is recorded. The same applies to the plane subkeys, to
`trace style`, and to the annotation folds.

**Two region ratios.** The batch credits the mark tier with `regionmargin`
and `regionnest`. Both are `\def` constants of the legacy lattice tier, not
rows of the metric registry, and retiring them buys the metric ledger
nothing. The real credit there would be `enclosepad`, `enclosetight` and
`regioncorner`, and none of the three has landed.

**The multi-strand capability.** Kept. The note asked for the capability name
to be retired and the one contradicting verdict corrected in the same change.
The contradiction is already gone: the verdict on `rmp-iii-a-spt-mpo` that
read *45-degree double strand as axis-aligned stubs* was replaced on
2026-07-24 by the rotation-frame review, and that target no longer carries
the capability at all. The two targets that still carry it record *winding
strings on lattice reduced to a bare tree* and *a braid with no crossing*,
neither of which names a doubled strand, so nothing blocks the retirement any
more. What does block it here is scope: the name lives in the manifest, in
three case headers, and in the digests those headers are recorded under.
Rewriting them is a corpus change, not a ledger change, and this session does
not touch the corpus. Recorded so the next redraw campaign can execute it.

### The metric registry, plainly

**This ledger does not end negative. It ends at zero.** Forty-five ratios
before and forty-five after. Nothing was minted, which is the whole of what
this session could do about it: the six ratios the designs asked for do not
exist, and three of them must never be minted, because the reference extent
and the slot pitch are columns of the size-class table, which already holds
per-class quantities, and the label clearance is `labelclear`, which already
exists. The ring step derives from `daylight` and the basis member clearance
is `daylight`.

What would have to be given up to make it negative: the two enclosure pads
and the region corner. All three are folded into `daylight` and `corner` by
the offset hull, and the change that retires the first two is open and not
merged, so their saving is not bookable today. Against those three
retirements the wire-width row splits into a virtual and a physical ratio,
which is one arrival. That is the arithmetic behind the −2 the notes claim,
and it becomes true when the hull lands and not before.

### The dangling pointers

Retiring a spelling that another row points at leaves a pointer to nothing,
which is worse than no pointer. Four were found and all four are corrected in
this change:

- the tombstone migrating `fused` to `weight=double`, and the Session-0
  verdict that said the same thing, both now say that the port type decides
  the stroke;
- the tombstone migrating `out=`/`in=` to routes and `via=`, and the two
  route tombstones beside it, now name the route family that survives;
- the tombstone migrating `label shift=` to `nudge=` now names the label
  station;
- the verdict retiring `\tncut` *into* a mark form, now that the form itself
  fails tenure and retires with it.

The tombstone for `col vector`/`row vector`/`sheet vector` was corrected in
the same pass: it pointed at plane subkeys the frame alphabet no longer
carries.

### Where the registry stands

The executable registry is unchanged, and deliberately. Its ledger vocabulary
has four statuses and none of them means *retired, pending the parser*: a
sugar row must expand into kernel tokens that exist, an alias row raises the
alias meter, which may not rise, and an escape row means sanctioned raw
geometry, which none of these keys is. A retirement is booked here as a dated
verdict naming the landing that executes it, and the registry row moves
ledger when the parser row moves — which is how every retirement in this
project has been booked since Session 0, and why nine 0.7 rows sentenced then
are still `kernel` today. Twenty verdicts below change accordingly.

### Verdicts on the 127 flags

| flag | verdict |
|---|---|
| flag:consumers:command:tenkzkernel | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tnbond | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tncut | dies at S4: the cut form has no consumer in the benchmark or the blueprint and fails tenure outright, so the command retires with the form rather than into it; this replaces the verdict making it a mark form (`LANGUAGE-1.0` 6); expiry 0.9 |
| flag:consumers:command:tndeclare | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tndeclareatom | keep-because: the extension door is used by declarations, not figures; teaching examples are deliberately excluded from demand counting; expiry 1.0 (re-affirmed 2026-07-24) |
| flag:consumers:command:tnfuse | demoted at the language landing: a prelude-declared fuse atom (`LANGUAGE-1.0` §9); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:command:tnmark | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:command:tnprose | dies at the S4 swap: mathematics in place of a diagram is a term of unknown signature, refused under strict wherever it stands and not only where an author remembered to mark it (`LANGUAGE-1.0` 7); expiry 0.9 |
| flag:consumers:command:tnset | keep-because: document-scope policy lives in preambles, which the demand corpus excludes by design; expiry 1.0 (re-affirmed 2026-07-24) |
| flag:consumers:command:tnwire | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:environment:tenkzeq | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:environment:tenkzplanes | sugar preset over the lattice frame; dies as an environment at S4; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:annotation:box | folds into mark form `enclosure` at the language landing, whose contour is the offset hull of the selection (`LANGUAGE-1.0` 5, 6); expiry 0.9 |
| flag:consumers:key:annotation:brace above | folds into the one `bracket` mark form at the language landing, the side a bracket speaks from being the side its label sits on; this replaces the verdict naming `brace-above`/`brace-below` (`LANGUAGE-1.0` 6); expiry 0.9 |
| flag:consumers:key:annotation:label pos | moves unchanged to the mark record at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:atom-declaration:ports | keep-because: declared atoms require an explicit typed-port schema at the extension door; permanent (re-affirmed 2026-07-24) |
| flag:consumers:key:atom-declaration:skin | keep-because: rides `\tndeclareatom`, same exclusion; expiry 1.0 (re-affirmed 2026-07-24) |
| flag:consumers:key:connection:fused | dies at the language landing: the index type decides the stroke, so a doubled bond has no spelling of its own; this replaces the verdict respelling it `weight=double`, which the retirement of `weight=` left dangling (`LANGUAGE-1.0` 5, 10); expiry 0.9 |
| flag:consumers:key:connection:none | dies at the language landing: omit the wire record, or use atom `void=sealed`; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:connection:style | dies with the lattice edge-style pass-through at S3; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:kernel-atom:at | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:cluster | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:conjugate | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:down | dies at the S4 swap: the outward physical face is the row's own normal, an angle in the record's axes; the label rides `ports=` (`LANGUAGE-1.0` 2.3, 9); expiry 0.9 |
| flag:consumers:key:kernel-atom:label pos | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:name | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:nudge | dies at the S4 swap: an off-cell record is a frame basis member or an ordinary address (`LANGUAGE-1.0` 3, 4); expiry 0.9 |
| flag:consumers:key:kernel-atom:ports | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:role | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:skin | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:species | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:up | dies at the S4 swap: the outward physical face is the row's own normal, an angle in the record's axes; the label rides `ports=` (`LANGUAGE-1.0` 2.3, 9); expiry 0.9 |
| flag:consumers:key:kernel-atom:void | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:wide | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-atom:wires | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-declare:base | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-declare:hue | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-declare:pairings | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:form | keep-because: the form alphabet closes to `bracket`, `enclosure`, `label` at the S4 swap; three words, one row, and consumers arrive with the redraw campaign (`LANGUAGE-1.0` 2.8, 6); expiry 0.9 |
| flag:consumers:key:kernel-mark:inset | dies at the S4 swap: containment between two selections is a fact the model holds, and concentric order steps the inner contour in by one clearance (`LANGUAGE-1.0` 5, 6); expiry 0.9 |
| flag:consumers:key:kernel-mark:label pos | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:name | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:nudge | dies at the S4 swap: a label takes a station against measured ink (`LANGUAGE-1.0` 6); expiry 0.9 |
| flag:consumers:key:kernel-mark:outline | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-mark:slot | dies at the S4 swap as one exchange with the mark's `species=`, which every other record already carries; net zero, so both halves land together (`LANGUAGE-1.0` 2.5, 14.5); expiry 0.9 |
| flag:consumers:key:kernel-picture:align | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:bonds | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:boundary | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-picture:check | dies at the S4 swap: the audit follows the joiner class and is not the author's to configure (`LANGUAGE-1.0` 7); expiry 0.9 |
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
| flag:consumers:key:kernel-wire:bend | dies at the S4 swap: an arc leaves and enters along its ends' faces, which is how every curve in the corpus is written (`LANGUAGE-1.0` 5); expiry 0.9 |
| flag:consumers:key:kernel-wire:closed | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:cross | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:dir | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:kind | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:name | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:route | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:species | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
| flag:consumers:key:kernel-wire:via | dies at the S4 swap: every waypoint in the contract's own sketches is a side of a selection (`LANGUAGE-1.0` 5); expiry 0.9 |
| flag:consumers:key:kernel-wire:weight | dies at the S4 swap: the port type decides the stroke through two theme ratios, and bundling is a claim the audit already carries; zero authored consumers in the corpus (`LANGUAGE-1.0` 5); expiry 0.9 |
| flag:consumers:key:kernel-wire:wind | keep-because: kernel landing wave (#4687); consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |
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
| flag:consumers:key:picture:polygon | dies with the cd dialect at S4, and its tombstone becomes permanently dead: the consumers arrived and they want angles, not corners (`LANGUAGE-1.0` 10); expiry 0.9 |
| flag:consumers:key:picture:sheet sep | folds into `frame=` subkeys at S3; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:sheets | dies at the language landing: the keep-because is executed, not renewed. A sheet is a basis member of one frame, and the condensation and CZX redraws consume it as a basis (`LANGUAGE-1.0` 4). No new saving is booked here: this row and `sheet sep`, `pairing` and `sheet vector` were sentenced at Session 0; expiry 0.9 |
| flag:consumers:key:picture:site | dies with the lattice dialect at S3; frame population creates ordinary atoms; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:south | keep-because: the four side policies are one kernel concept and south is required by two-dimensional frames; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:picture:trace style | dies at S2 when the default flips to the cap idiom, which is now stated: closure depth follows the selection the closure clears (`LANGUAGE-1.0` 5); expiry 0.9 |
| flag:consumers:key:region:group | folds into address sets at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:region:name | keep-because: same addressing argument as connection:name; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:setup:inline | dies at the equation landing (math-style sensing, #4703); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:consumers:key:setup:pitch | keep-because: the metric anchor is set in preambles, excluded from demand counting by design; expiry 1.0 (re-affirmed 2026-07-24) |
| flag:cooccur:annotation:box+label pos | confirmed merge: enclosure geometry and label placement become one mark record at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:cooccur:connection:from+to | keep-because: source and target are distinct endpoints of one wire record, not duplicate controls; permanent (re-affirmed 2026-07-24) |
| flag:cooccur:connection:in+out | confirmed merge: `out=`/`in=` are one concept (a hand-routed arc) and both die at S4 when declared routes land; expiry 0.9 (#4705) (re-affirmed 2026-07-24) |
| flag:cooccur:object:east at+west at | confirmed merge: the two endpoint selectors become one ports record at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:lonely-type:bond-policy | keep-because: the picture topology has one generated-bond policy shared by every frame (#4687); expiry 1.0 |
| flag:lonely-type:check-spec | dies at the S4 swap with `check=`, which was the condition the Session-0 verdict set (`LANGUAGE-1.0` 7); expiry 0.9 |
| flag:lonely-type:crossing-list | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:hue-source | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:integer | keep-because: integer is the primitive count type of the ring expander (#4687); expiry 1.0 |
| flag:lonely-type:math-and-range | dies with the B10 bond-label keyval at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:lonely-type:port-pair-list | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:positive-integer\|role-list | dies at the language landing with the union type (M6); expiry 0.9 (re-affirmed 2026-07-24) |
| flag:lonely-type:size-class | keep-because: the equation metric owns one size-class policy across its panels (#4687); expiry 1.0 |
| flag:lonely-type:size-table | keep-because: contract type of one contract key (`LANGUAGE-1.0` 2.7); collapses only if its key dies; expiry 1.0 |
| flag:lonely-type:style-name | dies with the lattice edge-style pass-through at S3; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:lonely-type:void-policy | keep-because: open and sealed holes are one atom-topology policy (#4687); expiry 1.0 |
| flag:sugar-shaped:command:tndots | folds into `\tn[skin=dots]` at the language landing; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:sugar-shaped:command:tnghost | dies at the language landing because addresses name empty cells directly; expiry 0.9 (re-affirmed 2026-07-24) |
| flag:sugar-shaped:command:tnskip | confirmed by contract: `\tnskip` is the sugar row `\tn[void=open]` (`LANGUAGE-1.0` 9); dies into the kernel at the S4 swap; expiry 0.9 |
| flag:sugar-shaped:command:tntree | confirmed by contract: `\tntree` is an expander sugar row (`LANGUAGE-1.0` 9); dies into the kernel at the S4 swap; expiry 0.9 |
| flag:sugar-shaped:command:tnarrow | tombstoned by contract: `\tnarrow` migrates to `\tnwire[dir=to]` (`LANGUAGE-1.0` 10); deleted at the S4 swap; expiry 0.9 |
| flag:sugar-shaped:command:tngroup | keep-because: a group is the composition grammar for one transform over several atoms and wires, not atom sugar; permanent (re-affirmed 2026-07-25) |

One arrival is named here and booked elsewhere, so that it is counted once.
Retiring the face words leaves the corpus spelling them, and they survive as
one sugar row naming the four right angles. That row lands with the change
that implements angle-valued faces, and the sugar ledger moves from
twenty-five to twenty-six there. Booking it in this session as well would put
the cost in two ledgers, which is the same error as putting a saving in two
and no more forgivable for running the other way.

Agenda handed to the next session: the mark `species=` row and the nine
parser rows sentenced above; the two enclosure pads and the region corner,
once the hull lands; the face-word sugar row, with the change that lands it;
and the multi-strand capability name, once a redraw campaign is open to carry
the three case headers.

| flag:consumers:key:kernel-wire:crossing | keep-because: amendment two, `Extension-gate: #4779`; consumers arrive with the S4 swap and the redraw campaign; expiry 0.8 |

`Extension-gate: #4779` (2026-07-25) adds `crossing=` at wire scope: the order a
string takes at every crossing it makes, stated once instead of once per
crossing. It arrives with the route that derives a crossing set from the side a
string passes on, and `cross=` stays as the per-crossing exception for the one
crossing that goes against the habit. Consumers: rmp-iii-a-pulling-through,
rmp-workbench-iii-g-injective-pull, rmp-workbench-iii-mpo-injective-white.

### 2026-07-25 — deletions outside the language

This entry is not a shrink session and does not open one. It retires no
registry row, moves no meter and re-examines no flag, so the verdicts above
stand as they are and are not restated here: repeating a hundred and
twenty-eight unchanged rows to satisfy a reader that nothing changed is the
bookkeeping this ledger exists to refuse. What follows is a record of
deletions in the harness around the language and in three implementation
files beneath it, neither of which any meter here measures.

The work subtracts and does nothing else. It takes no position the surface
swap has not already taken: the commutative-diagram, free-placement and
lattice tiers keep their fourteen, eighty-six and seventy-seven benchmark
cases, and they retire after the redraw campaign, not before it. No spelling
was retired, no meter was added, no baseline was re-frozen.

The census is unmoved — 192 before and 192 after — and it should be. The
language was not touched.

#### Tombstones: none are due

Every alias row in the registry carries `sunset=1.0` — `periodic`, `chain
axis`, `legs at`, `rows`, `boundary legs`, `label at`, and the value alias
`route=curve` — and the package is at 0.7. Not one has expired. Nothing was
retired here, and the empty result is recorded so that the next session does
not derive it again.

#### The harness, measured before it was judged

Thirty files carrying 16,709 lines stand beside a package of 24,541. Every
one was traced to its caller: the continuous-integration workflows, another
script, or nothing. Twenty-seven are reached from a workflow step and do work
no other gate repeats — the corpus driver and its provenance and render
tests, the golden and kernel and string pins, the audit, the source lint, the
registry and shrink gates, the manual extraction, the benchmark driver, and
eleven measured-geometry regressions that each assert a different mechanism
(label bands, label overlap, face ports, enclosures, index routing, fusion
trees, the torus, the equation audit and its web layout, the picture
pipeline, the shared parsers). None of them is a second opinion on another's
question. The two census meters that sound alike are not: one counts drawing
ink in the package sources, the other counts rows of public vocabulary.

Three are reached from nowhere. Two of them are kept for reasons recorded
below. The third had no second job either, and it goes.

#### What went

| what | lines | what it was for | why it is no longer needed |
|---|---:|---|---|
| `scripts/tenkz_rmp.sh` | 6 | a shell frontend for the benchmark driver; its whole body was one line handing its arguments to `scripts/tenkz_rmp.py` | both workflows already call the driver directly, so the frontend served only four blocks of documentation, which now name the driver. Its removal also retires a false sentence in the benchmark index, which credited the frontend with defining the generated-index control sequence that the driver defines. |
| `\__tenkz_render_atom:nnn` | 2 | the unscaled atom, forwarding to the scaled one with an empty size | every caller passes the size argument; the forwarding form was never reached. The scaled entry now carries the whole comment. |
| `\__tenkz_render_wire:nnnn` and its two point registers, with the `render-route` diagnostic | 52 | a three-way straight, orthogonal and arc router in the shared render stage | no stage ever called it. Wires reach paper through `\__tenkz_render_stroke:nn` and the string stage's saved routes; the three-way case analysis was written against a routing contract the wire record replaced. The diagnostic it raised had no other raiser and goes with it. |
| `\__tenkz_render_atom_named:nn` | 8 | a named atom placed from a pitch-fraction coordinate | the named atoms that reach paper all take the point-exact entries beside it, because the fraction round trip loses a scaled point and the pixel gate sees it. The comment above those entries says so; this form contradicted it and had no caller. |
| `\__tenkz_render_label:nnnn` and its three dimension registers | 24 | a label placed at an angular offset with its own inner clearance | the kernel calls only the anchor helper above it and computes its own offset. Nothing called the placer. |
| `\__tenkz_geom_require_kind:nnn` | 5 | a three-argument convenience over the frame-kind check | all seven real call sites use the four-argument form, which names the flag it sets. |
| `\__tenkz_geom_corridor_include:nn` and `\__tenkz_geom_corridor_include_bbox:nnnn` | 23 | folding a paper point, and a bounding box's four corners, into the corridor silhouette and transverse interval | a two-function island: the box form's only caller was itself dead, and the point form's only caller was the box form. Cup routing uses the transverse-only fold beside them, which stays. |
| `\__tenkz_geom_corridor_escape:Nnnn` | 16 | displacing a tip out of a forbidden transverse interval | the offset hull does this work now; nothing called the register-adjusting form. |
| `\l__tenkz_geom_xb_tl`, `\l__tenkz_geom_yb_tl` | 1 | a second point in the placement graph | the graph resolves one point at a time into the `a` pair beside them. |
| `\l__tenkz_model_scratch_tl` | 1 | scratch text in the record store | never written and never read. |

Totals: the harness falls from 16,709 lines to 16,703 and from thirty files
to twenty-nine; the package falls from 24,541 lines to 24,407, of which the
render stage gives up 87 of its 290 — thirty parts in a hundred — the
geometry stage 46 of 590, and the record store one.

The ink and decimal censuses are unchanged at 44 and 51, so no baseline was
re-frozen. The deletions took no drawing with them: what left the render
stage never drew, and what left the geometry stage only ever computed.

#### What was considered and kept

| what | verdict |
|---|---|
| `scripts/tenkz_pixelpair.sh` (109 lines) | keep-because: no caller, no documentation, and a manifest of six fixtures against the corpus renderer's two hundred and fifty-seven — but it is the only place the detached true-legacy build is written down, and the redraw campaign is the moment that build is needed. Delete it at the campaign's close, when the last comparison against an old package tree is behind us; expiry 1.0 |
| `scripts/check_tenkz_demolition.py` and its self-test (245 lines, with a workflow of its own) | keep-because: it refuses the retired catalogue's paths and calls in every tracked file. Three days old, and the branches that predate the demolition are still in flight; a restored file that nothing loads compiles clean, which is the one failure no other gate sees. Retire it at the 0.8 close, when those branches have landed or died; expiry 0.8 |
| `scripts/test_tenkz_language.py` (89 lines) | keep-because: no workflow step runs it, and its first probe repeats a step that one does. Its other two do not repeat anything: the typed-port refusal at the extension door, and the equality of the legacy closure word's event stream with the canonical spelling's. Both are dormant, which is a wiring question and not a deletion question; a subtract-only change is the wrong place to settle it. Raise it at the 0.8 close: wire the two probes to a step or retire them; expiry 0.8 |
| `tex/tenkz/tenkz-grid.code.tex` (6,142 lines) | keep: the premise that it holds the drawing path the shared renderer replaced does not survive contact with the file. Twenty-seven of its four hundred and twenty-seven control sequences are called from outside it, the blueprint chapters among the callers, and every one of the remaining four hundred is reachable from those and from the two public entry points at its end. There is no unreachable cluster. The shared render stage is a service beneath the live dialects, not a replacement for them. |
| the leaf keys of the option parsers, and the role-prefixed silhouette styles | keep: their full names appear once each, at their definition, because they are assembled at use from a role word and a suffix, or dispatched by the option machinery from an author's key. Absence of a literal mention is not absence of a consumer. The instrument for those rows is this ledger and the registry gate, never a search. |

Handed to the next session: the three expiries above; and a question this
entry could not answer, which is whether the eleven measured-geometry
regressions want to become one harness with eleven fixtures. They repeat no
assertion, but they repeat a great deal of scaffolding.

### 2026-07-26 — the symmetry redraw raises the escape meter by thirty-six

M3, escape usage, rises from 276 to 312. Every occurrence of an escape
spelling names a gap in the core grammar, so a rise is a measurement rather
than a regression — but it is only honest if the gap it names is written
down, and this one is worth writing down carefully.

The thirty-six are eighteen `out=`/`in=` pairs, which arrive together because
a hand-routed connection states both ends. They are concentrated where the
grammar is thinnest: thirteen pairs in the self-braiding panel, twelve in
pulling through, five each in the idempotent, the left R-tensor and the first
two braids. Those are exactly the figures whose strings leave a site, travel
around something, and return.

The kernel has a word for that. A route travels one clearance outside the
offset hull of a selection, on a named side, and derives the crossings it
makes rather than having them typed. Not one of these panels can say it: the
package does not load the kernel language, so a corpus case speaks the 0.7
genres only, and a string that must go around something is hand-routed with
the two tombstoned keys or not drawn at all.

So the meter is reporting the cost of the surface swap not having happened,
priced in escape-hatch occurrences. It should fall sharply — these eighteen
pairs and most of the standing hundred and fifty-five — when the corpus can
speak the route form, and if it does not fall then, that is the finding.

M4, mean lines per case, rises from 14.48 to 14.70. The twelve redrawn
panels are longer than what they replace because several were drawing less
than the source asserts -- a pumpkin instead of a wrapped word, one side of
an equation instead of two, three strands where the source draws a connected
lattice patch. A figure that gains the indices it was missing gains lines.
The meter exists to catch shrink bought by drawing less, and here it is
reporting the opposite trade, which is the one worth paying.

Census-correction: #4709 — the two meters above are raised under this
verdict, and the gate is amended to accept one. M3 and M4 were hard
ratchets, alone among the six: M1 admits a rise against a written
correction and M2 against an extension citation, while these two refused
every rise whatever its reason. That made them argue against correctness,
since a panel repaired to show the indices its source asserts both gains
lines and, where the grammar cannot route a string, gains escape
occurrences. They now admit a rise on the same terms M1 uses, and refuse
one that carries no verdict — which is the case they exist to catch.

Two flags are raised for the first time by these redraws and are answered
here. The shared `frame=` concept landed at group and object scope under
`Extension-gate: #4700` with no consumers at all; the panels below give it
two at each scope, which is short of tenure and so still flagged.

| flag | verdict |
|---|---|
| flag:consumers:key:group:frame | keep-because: the rotation the anyon panels need is one transform read at three scopes, and the two here are its first demand-corpus consumers; the redraw campaign supplies the rest or the scope dies at the 0.8 close; expiry 0.8 |
| flag:consumers:key:object:frame | keep-because: same concept at atom scope; a single turned tensor is the case a group cannot express, and it earns tenure with the campaign or dies with it; expiry 0.8 |
| flag:consumers:command:tngroup | keep-because: the command carrying that transform, flagged for consumers for the first time now that two panels use it; its shape was already affirmed permanent against the sugar detector, and its tenure follows the same 0.8 close as the two keys above |

No ledger row changes and no other flag verdict is re-examined here.

### 2026-07-26 — the case sweep raises the two demand meters again

M3 rises from 312 to 326 and M4 from 14.70 to 14.88, for the same reasons the
entry above records and against the same verdict.

The section-IV windows and the workbench relations redrawn in this change hand-
route the strings that leave a site, travel around something, and return. The
kernel says that in one word and the corpus cannot speak the kernel, so each
such string is spelt with the two tombstoned keys and each spelling is counted
here. The rise is the surface swap's absence, priced again.

The fidelity meter rises because these panels gained the indices their sources
assert. A figure that stops drawing less than its source gains lines, and this
meter exists to catch the opposite trade.

One further note for whoever lands last: three redraw branches now move these
two meters independently, and none of the three counted the others. The union
needs one recomputation on the final tree, and the number recorded here is
correct for this branch alone.

Census-correction: #4709

### 2026-07-26 — the section-III sweep prices two more gaps

M3, escape usage, rises from 326 to 331. Four of the five occurrences are
two `out=`/`in=` pairs in the historical composite, whose two red boundary
strings each sweep around a panel and must be hand-routed — the same
strings gap the two entries above price, met again in the one figure the
corpus had been drawing as something else entirely. The fifth is one
`plane rise=` override in the anyon pair: the site label has exactly one
bearing, hard-coded to the north-east quadrant, so the only way to clear a
label from an oblique sheet's converging legs is to reshear the whole
sheet. A per-site label bearing would retire that occurrence; the gap is
tracked with the sweep's follow-up issues.

M4, mean lines per case, rises from 14.88 to 15.88. Seven panels were
redrawn against their sources and six of them grew, the GHZ brick patch
most of all: the source builds it from four foreach loops, and the free
genre has no repetition form, so the masonry is transcribed element-wise.
Each of the seven now draws what its source asserts — a doubled string
instead of one, a masonry patch instead of a blocking cartoon, an
orthogonal isometry reduction instead of an invented operator box — and
a figure that stops drawing less than its source gains lines.

Census-correction: #4709

One flag is newly raised by this sweep and answered here. The sweep
removed two of `outer legs=`'s three demand-corpus consumers, because both
spelt a boundary their sources do not draw — the key was standing in for
pictures that have since been redrawn from the sources directly.

| flag | verdict |
|---|---|
| flag:consumers:key:picture:outer legs | keep-because: its one remaining consumer is a manifest-paired fixture, and losing case consumers to *more faithful* drawings is not evidence against the key — it is evidence the two departed cases never needed it; it earns new consumers with the redraw campaign or dies at the 0.8 close; expiry 0.8 |
| flag:consumers:key:object:down at | keep-because: the reduction proof no longer spells its isometry with `down at=`, which drops the key to two consumers on the same more-faithful-drawing grounds as the row above; same tenure terms; expiry 0.8 |
| flag:lonely-type:positive-integer|role-list | keep-because: the union type serves `sheets=` alone now that the condensation panel left the planes genre for the oblique sheet; the type is the planes genre's spelling and follows that genre's fate at the front-end consolidation; expiry 0.8 |

No ledger row changes and no other flag verdict is re-examined here.

### 2026-07-26 — corrections to the symmetry-redraw entry's audit record

The entry "the symmetry redraw raises the escape meter by thirty-six"
above carries two record errors, found in review (#4906). The ledger is
append-only, so the original stands and this section corrects it.

**The per-panel escape breakdown was wrong.** The entry credited thirteen
pairs to the self-braiding panel and five each to the idempotent and the
first two braids; recounted from the pre-redraw tree, those panels gained
nothing. The true breakdown of the eighteen `out=`/`in=` pairs: twelve in
pulling through, three in the fourth braid, two each in the first braid
and both R-tensors, one in the third braid, and four *removed* from the
first torus panel, whose wrapped word no longer hand-routes. The total
the meter recorded was and remains correct.

**The tngroup verdict lacked its machine token.** The prose asserted the
same 0.8 tenure as the two frame keys but omitted the parsable token, and
the lexical lifetime parser satisfied itself on the word "permanent" from
the neighbouring sugar-shape flag's history. The row is re-stated with
the token:

| flag | verdict |
|---|---|
| flag:consumers:command:tngroup | keep-because: the command carrying the group transform, with two demand-corpus consumers from the anyon panels; its shape was already affirmed against the sugar detector, and its consumer tenure follows the same 0.8 close as the two frame keys; expiry 0.8 |

No meters move and no ledger row changes here.

### 2026-07-26 — the torus source correction exposes two curved cycles

M3, escape usage, rises from 331 to 355. The twenty-four occurrences are
twelve `out=`/`in=` pairs in the two curved panels corrected against their
archival figures. Ten pairs draw the literal torus boundary, its opening, and
the two noncontractible MPO cycles that cross at the distinguished tensor.
The remaining two draw the pulling arrow and the short auxiliary closure in
the two-window pulling-through identity.

These are the same free-graph routing gaps recorded in the preceding redraw
entries. The public free genre has no torus surface and no route determined by
a homotopy class, so the source's curved geometry must be stated by its two
endpoint tangents. The rise therefore records the cost of replacing three
cyclically misassigned panels by the figures their sources assert.

M4, mean lines per case, rises from 15.87 to 16.23. The former cases drew a
periodic word, a partial lattice crossing, and a one-box equation under the
wrong citations. Their replacements draw the torus surface and the complete
two-window PEPS relation. The additional lines state mathematical content
that was previously absent.

Census-correction: #4910

### 2026-07-27 — the MPO-word correction synchronizes the line census

PR~#4954 replaces one shared long-bond label by the four adjacent bond labels
shown in the source MPO word. Spelling those four labels wraps the option list
across two non-comment lines and raises the 130-case mean from 16.23 to 16.24.
The increase records that source correction; no package surface or parser
changes here.

Census-correction: #4954

### 2026-07-27 — local site geometry closes three source gaps

The executable compatibility ledger gains two object properties. `size=`
gives a source-corpus object one of the existing small, medium, and large
metric classes; `circle` gives a labelled object a plain circular outline.
Their public parsers add four leaf paths: `label pos=` and `size=` on lattice
sites, and `circle` and `size=` on free atoms. The first path implements an
object property already present in the registry; the other three expose the
two new rows through their relevant compatibility genres. They do not enlarge
the canonical kernel atom or claim picture-size inheritance.

The additions have direct source consumers. The anyon-pair panel places its
three labels in the quadrants drawn by the archival figure. The condensation
panel distinguishes four large endpoints from four small intermediate beads.
Seven occurrences of the \(\lambda\) intertwiner now use a plain inscribed
circle rather than a semantically unrelated ring.

Extension-gate: #4939

Extension-gate: #4940

Extension-gate: #4942

M3 falls from 355 to 354 because the anyon-pair panel no longer reshears its
entire plane merely to move one label. M4 rises from 16.24 to 16.30 because
the source cases now state their local label quadrants and marker sizes
explicitly. The additional lines distinguish geometry that the former
one-size, one-quadrant language could not express.

Census-correction: #4939

One consumer flag is raised by the new local size property:

| flag | verdict |
|---|---|
| flag:consumers:key:object:size | keep-because: the condensation source supplies one manifested panel with eight independent local-size uses, four small and four large; this is repeated demand within one mathematical figure rather than a speculative option, but it remains below the cross-file tenure threshold and must gain two further source-faithful benchmark consumers or be reconsidered at the 1.0 close; expiry 1.0 |

### 2026-07-27 — the structural burn-down raises the fidelity meter alone

M4, mean lines per case, rises from 16.30 to 16.95. Fifteen structural
panels and three unreviewed ones were redrawn against their sources, and
what they gained is exactly what the meter watches for in reverse: closed
rings where open ones stood, a projector layer, a doubling tree's third
level, stacked fusion, the string-order construction. A figure that stops
drawing less than its source gains lines.

M3 does not move. Eighteen files changed and not one reached for an
escape spelling — the drawing pass stayed inside the core grammar, which
is the first structural campaign to do so. The demand the earlier
entries priced remains where it was.

Census-correction: #4709

No ledger row changes and no flag verdict is re-examined here.

### 2026-07-27 — the residual batch prices one reshear

M3 rises from 354 to 355: one `plane slant=` override in the condensation
panel, needed to keep the extended six-row sheet inside the geometry
guard at the readable band. The same gap the anyon sheet priced — a
sheet's shear is picture-global where the demand is local — met once
more. M4 rises from 16.95 to 17.01 as the sheet and its strings extend
to the source's trace.

Census-correction: #4709

No ledger row changes and no flag verdict is re-examined here.

### 2026-07-27 — the condensation endpoint repair prices one sheet vector

M3 rises from 355 to 356.  The six-row condensation panel must keep the
author source's two marked paths interleaved while leaving both paired
endpoints visually distinct and physically open.  The derived plane
separation splits the construction into two disjoint slabs, while the former
`sheet sep=` value overlaps the large endpoint markers and triggers the
interleave and near-coincidence guards.  One expert `sheet vector=` therefore
states the source-measured vertical offset; `row vector=` replaces the former
`plane slant=` escape and preserves its reviewed 0.30/0.45 projection without
a boundary-band warning.

M4 remains 17.01.  The new endpoint and projection data are written without
raising the frozen case-line mean.

Census-correction: #4969

No ledger row changes and no flag verdict is re-examined here.

### 2026-07-27 — wave A retires five blocked demands by drawing

M4 rises from 16.92 to 17.63. Five of the six demands the blocked table
recorded against missing capabilities turned out to be expressible in the
present grammar: two were already drawn (the demands predated the bodies),
and three are drawn now — the group average as mathematics around the
diagram, the projector ring through elbow routes, and the workbench GHZ
checkerboard as the declared equivalence twin of its published sibling.
The masonry twin carries most of the rise. M3 does not move: no new
escape spelling in any of the five.

Census-correction: #4709

No ledger row changes and no flag verdict is re-examined here.

### 2026-07-27 — the route form pays: the escape meter falls by seventy-four

M3 falls from 356 to 282. Nine blocked panels were redrawn through the
kernel bridge -- the braid family's declared crossings, the g-string
pulling-through pair, the F-symbol's anyon-line crossing, the two-shift
MPU, and the CZX site clusters -- and not one of them spells out= or in=.
Every entry since the symmetry redraw priced these occurrences as "the
cost of the surface swap not having happened," and promised the meter
would fall sharply when the corpus could speak the route form. It has,
and by more than the redraw waves added: the meter now reads below the
276 the campaign started from priced against a corpus that draws far
more than it did then.

M4 ticks up from 17.63 to 17.65: the kernel says in a wire declaration
what the hand-routed spelling said in coordinates, and the two
hundredths are the labels and stations the nine panels gained.

Census-correction: #4709

One flag is newly raised and answered here.

| flag | verdict |
|---|---|
| flag:sugar-shaped:command:tenkzkernel | keep-because: the switch is not sugar for anything -- it is the S4 swap's own handle, rebinding the environments to the kernel grammar for the group; it dies at the swap when the kernel becomes the surface and the opt-in has nothing left to opt into; expiry 1.0 |

No ledger row changes and no other flag verdict is re-examined here.

### 2026-07-28 — the route form pays again: M3 reaches 254

M3 falls from 282 to 254. Four more panels -- both remaining R-tensor
braids and the two pulling-through workbench figures -- say their strings
in the kernel and retire twenty-eight more hand-routed occurrences. The
meter has now fallen a hundred and two from its peak and sits well below
the 276 the campaign opened at, while the corpus draws crossings,
windings and pull-throughs it could not say at all then. The prediction
the symmetry-redraw entry recorded is discharged in full.

M4 rises from 17.65 to 18.08: the four panels gained the strings, the
stations and the labels their sources assert.

Census-correction: #4709

Two targets stay blocked with their demands sharpened by the attempt.
The MPU wrap's demand is renamed from `strings` to `skin-pairings`: the
panel contains no string at all, and three spellings were probed and
refused -- the declared skin raises the renderer's own todo, strings
through boxes are painted over by the glyph fill, and the free tier's
arc needs the tombstoned escape pair. The torus cycle keeps its demand:
a kernel attempt drew one loop on a bare grid where the source draws a
torus and two lattice panels, and was refused at review.

No ledger row changes and no flag verdict is re-examined here.

### 2026-07-28 — recorded kernel semantics reach the ink

Species hue and wire direction were already kernel record fields, but the
renderer discarded both. They now resolve at the shared ink boundary:
declared `source:` hues reproduce the cited palette, undeclared named species
use the house cycle, and `dir=` selects the corresponding mid-wire barb.
Unnamed records retain the ordinary theme ink.

The canonical atom gains the existing `size=s|m|l` property and marks gain
the already-specified `species=` property under the extension gate requested
by the source-corpus audit. This raises M1 kernel rows from 136 to 138 and M2
parser leaves from 221 to 223. It does not change M3. M4 rises from 18.08 to
18.20 because eleven source cases now state their cited palettes explicitly
instead of relying on encounter order. The focused regression records all
three size classes, document-stable species hues, mark species, and wire
direction while the ten kernel event streams remain byte-identical.

Extension-gate: #5013

Census-correction: #5013

| flag | verdict |
|---|---|
| flag:consumers:key:kernel-atom:size | keep-because: #4931 records the condensation source's large endpoints and small intermediate beads, while #5013 makes the existing size-class answer reachable from canonical atoms; expiry 1.0 |
| flag:consumers:key:kernel-mark:species | keep-because: #5013 implements the LANGUAGE-1.0 semantic-ink contract at mark scope and pins it in the focused kernel regression; the cited dyon, boundary-lasso, and injectivity-ring consumers migrate in the queued redraw waves; expiry 1.0 |
| flag:sugar-shaped:command:tndeclare | keep-because: a species declaration binds one semantic identity to a cited palette across atoms, wires, and marks; it changes the document-scope descriptor table and cannot expand into picture records; expiry 1.0 |

### 2026-07-28 — accepted arcs shed their angle escapes

M3 falls from 254 to 91. Eighteen accepted cases remove 81 `out=`/`in=`
pairs. The compatibility boundary now derives an arc from named port faces:
ports on different atoms use their outward faces, two ports of one atom use
the inward pairing, and coordinate endpoints use the automatic arc. Explicit
legacy angles retain their former rendering for the three cases assigned to
#5016. The signed-faithful MPU wrap is pixel-identical before and after the
migration.

The condensation case retires its `row vector=` escape in favor of the named
oblique frame. Its source-measured `sheet vector=` remains because the two
paths intentionally interleave; the equivalent `sheet sep=` spelling emits
the public interleave warning. Its projection remains recorded as a cosmetic
gap. M4 remains 18.20.

The residue is concrete rather than near zero: 62 occurrences belong to the
three blocked cases in #5016, one is the intentional condensation sheet
interleave, two preserve a source-faithful detour whose north/south endpoints
need east/west tangents, and 26 were already outside this issue's arc and
vector census.

Census-correction: #5015

No ledger row changes and no flag verdict is re-examined here.

### 2026-07-28 — skin topology and instance crossings separate

A declared skin now retains only reusable own-port pairings. Crossings between
one placed atom's generated pairing and picture-external wires move to the
atom's indexed `pairing cross=` field. This prevents one skin declaration from
copying an instance-specific crossing onto every atom and keeps comma-separated
crossing lists outside the braced `pairings=` parser boundary.

This raises M1 kernel rows from 138 to 139 and M2 parser leaves from 223 to
224. M3 through M6 do not change.

Extension-gate: #5009

Census-correction: #5009

| flag | verdict |
|---|---|
| flag:consumers:key:kernel-atom:pairing cross | keep-because: #5016 consumes instance crossings in the self-braiding redraw, while the kernel pairing fixture pins repeated indexed items and external pairing operands; expiry 1.0 |
| flag:lonely-type:indexed-crossing-list | keep-because: the leading pairing index is the instance-to-generated-wire join and therefore differs from an ordinary wire crossing-list; #5016 consumes it; expiry 1.0 |

### 2026-07-28 — the final blocked RMP cases enter the kernel

M3 falls from 91 to 29. The three cases assigned to #5016 account for the
entire decrease of 62 escape occurrences: the double winding uses a declared
self-crossing, the two MPU rows use reusable skin pairings, and the torus
statement uses an identified lattice with closed `wind={1,0}` and
`wind={0,1}` cycles before its complete two-panel lattice identity.

M4 rises from 18.20 to 18.40 because the refused two-box torus sketch is
replaced by all three source stages, including the pull arrow and the
`g^{-1}`/`g` resolution. The two three-station resolution rails flank `O_h`
and join each other above the marked tensor without terminating the vertical
operator. The blocked count falls from three to zero. The shared event schema
also accepts the `kind=pairing` WIRE records introduced by #5009; the focused
audit regression pins that model-to-auditor contract, including author-facing
pairing operands and inherited paint order between generated pairings.

Census-correction: #5016

No language-ledger row changes and no remaining flag verdict is re-examined
here.

### 2026-07-29 — typed-map spacing enters the escape ledger

A complete blueprint scan found three existing raw geometry occurrences in
`tenkzcd[maps]`: one `column sep=` and two `row sep=` spellings.  They had
passed to the underlying matrix without a registry row and were therefore
absent from M3.  Both spellings now enter the escape ledger, making the
existing geometry debt visible: M1 gains two escape rows, M2 gains their two
explicit parser leaves, and M3 rises from 29 to 32.  Their values preserve the
present figures exactly; the four typed-map figures acquire their permanent
pitch spelling when they leave `tenkzcd` in the chapter 21 migration of #4699.

Extension-gate: #5085

Census-correction: #5085

| flag | verdict |
|---|---|
| flag:consumers:key:picture:column sep | dies with the `tenkzcd` chapter 21 migration in #4699, where typed-map column pitch receives its kernel spelling; expiry 0.8 |
| flag:consumers:key:picture:row sep | dies with the `tenkzcd` chapter 21 migration in #4699, where typed-map row pitch receives its kernel spelling; expiry 0.8 |

### 2026-07-30 — declared cell bases replace measured sub-sites

The frame grammar gains one nested kernel leaf, `basis=`, so M1 kernel rows
rise from 139 to 140 and M2 parser leaves rise from 226 to 227. The leaf is
the shared replacement for off-cell sites expressed through raw millimetres:
it declares an ordered row-kind member table in east/north quarter pitches,
and the existing frame map transports every member through flat and projected
geometry.

This is deliberately placement without invented topology. Selecting `(r,c)`
returns every member, `(r,c,k)` returns one member, and a multi-member basis
requires explicit wires rather than treating coordinate coincidence as a
connection. The CZX contract fixture consumes the leaf immediately, while
the GHZ and PEPS cases remain assigned to the generic motif/topology work;
no case-specific expander is introduced here.

Extension-gate: #5086

Census-correction: #5086

| flag | verdict |
|---|---|
| flag:consumers:key:kernel-frame:basis | keep-because: the CZX fixture consumes the member table now; the GHZ, cluster-state, bilayer, and condensation consumers named by LANGUAGE-1.0 migrate through #5086; expiry 1.0 |
| flag:lonely-type:basis-spec | keep-because: this type alone combines an ordered row-kind list with signed two-axis quarter-pitch offsets; ordinary row-list and selector grammars cannot express that frame-owned structure; expiry 1.0 |

### 2026-08-01 — projected resolver panels restore source topology

The right R-tensor and fourth braid cases now use the shared plane frame. The
former free-graph construction loses its raw millimetre coordinates, while the
fourth braid restores the source ordering of its sites, resolver boxes, lower
rail bead, and outgoing tail. M4 rises from 18.22 to 18.32 because the two
fixtures now record the complete open rails, diagonal transversal, and
continuous resolved strings instead of flattening or omitting that topology.
No parser row, escape, or case-specific geometry control is added.

Census-correction: #5086

No language-ledger row changes and no flag verdict is re-examined here.

### 2026-08-01 — the remaining projected panels state their contractions

M4 rises from 18.32 to 18.50. The projected idempotent case now splits the four
virtual rails at their MPO stations instead of relying on geometric
coincidence. The left R panel names both physical legs, carries its winding
through all four ring tensors and both b stations, starts the i-string at the
marked tensor, and splits every black rail through the tensor ports it meets.
All five idempotent-loop stations are explicit atoms joined face to face; the
marked four-port j atom owns the two loop bonds and the two radial bonds. These
case lines record real contractions without a new parser row, geometric
tolerance, escape, alias, or overload.

Census-correction: #5086

### 2026-08-02 — typed PEPS stars keep source-short physical legs

M4 rises from 18.50 to 18.51. The SPT and white MPO-injective panels now
terminate all four virtual legs on typed faces of the PEPS tensor, while an
unconsumed physical face supplies the shared renderer's short physical stub.
The post-pull SPT panel retains the explicit physical contraction through
the two-port `U_g` station. No parser row or case-specific metric is added.

Census-correction: #5086

### 2026-08-02 — projected R contractions enter the event graph

M4 rises from 18.51 to 18.60. The left R panel now splits each black lattice
carrier and each red operator string at typed ports on its seven string
tensors. Its two horizontal rails, both diagonal ends, and all three lower
operator continuations are semantic open ends. Thus every source contraction
and declared boundary leg is model incidence rather than geometric
coincidence, without changing the public language.

Census-correction: #5086

### 2026-08-02 — the contract-defined `planes` preset reaches the kernel

The kernel gains the contract-defined `planes` sugar from `LANGUAGE-1.0` section
9: one plane frame with ket and bra basis members at their declared
quarter-pitch offsets. The preset owns placement only; callers continue to
state `bonds=none` when a multi-member basis has explicit connectivity. M1
sugar rows rise from 12 to 13 and M2 parser leaves rise from 227 to 228.
Kernel, alias, escape, and overload counts are unchanged.

Extension-gate: #5086

Census-correction: #5086

| flag | verdict |
|---|---|
| flag:consumers:key:kernel-picture:planes | keep-because: `LANGUAGE-1.0` section 9 fixes the bilayer expansion; the kernel equivalence pair lands now and the named bilayer and condensation consumers migrate through #5086; expiry 1.0 |

### 2026-08-02 — basis spacing derives from shared clearance

Distinct basis-member families now receive one finite-window spacing
diagnostic after the complete affine frame map. Geometry minimizes the
centre-bearing support margin of the transformed default beads; the warning
records that member pair and cell translation but changes neither placement,
identity, nor topology. The kernel derives each directional requirement from
the existing `dotdia` body diameter, absolute `wirewidth`, and `daylight`.
The retiring lattice sheet guard draws page-round beads, so those same three
ingredients reduce to `dotdia + wirewidth / pitch + daylight`. The
lattice-local `1.25` multiplier and millimetre-facing report therefore
disappear without minting a replacement ratio.

The metric ledger moves by zero. M1--M6, parser identity, raw-ink census, and
decimal-literal census are unchanged; the removed lattice definition was a
metric-table line already exempt from the latter. Issue #5331 carries the
geometry and event regressions.

### 2026-08-02 — RMP physical dimensions acquire executable owners

Before this change, the final scanner finds 929 active absolute dimensions and
2 comment literals in the 130-case RMP corpus. Afterwards it finds 926 active
dimensions and no comment literals. The active reduction is one metric literal
and two projection/frame literals; the two removed comment pitches are tracked
orthogonally. The anyon pair now inherits the shared lattice metric. Its
lattice, perimeter stubs, and vertical physical legs are source-faithful; the
integer-cell surface cannot express the
two half-grid insertions and the five-position curved string, so the verdict
records a structural gap tracked in #5375. The condensation panel uses the
existing `tenkzplanes` owner for both sheet grids, all 24 inter-sheet physical
pairings, and one marked path per sheet; its measured sheet vector disappears.
No ratio, parser spelling, registry row, or case-specific public syntax is
added.

The RMP driver now classifies every remaining case dimension at its semantic
boundary: 0 metric, 0 projection/frame, 396 route/string, and 530
composition/layout, with 0 in comments. Those aggregate counts are ceilings,
so net removals pass while uncompensated count increases fail. Exact balanced
replacement and ownership-site moves are checked by the per-occurrence gate in
#5378; until then they require manual review. The benchmark book's 28
page-layout dimensions are checked by exact counts in its two fixed owner files
rather than being mistaken for figure geometry. Synthetic perturbations pin
balanced options, comment classification, unknown-owner rejection, every
ceiling, and the book allowlist.

M3 falls from 30 to 29 when the last RMP `sheet vector` escape disappears. M4
falls from 18.60 to 18.55 because the public lattice owners state the complete
grid and boundary policies without repeating their generated incidence in the
cases. The anyon verdict does not trade that shrink for a fidelity claim: its
missing projected physical axis remains explicit in #5375.

Census-correction: #5345

No language-ledger row or flag verdict changes.

### 2026-08-03 — physical labels have one typed-port owner

The canonical kernel retires the atom keys `up=` and `down=`. Physical policy
now registers the outward centre identity and refines any consumed endpoint to
physical; registration itself consumes no port. An explicit matching `ports=`
descriptor therefore follows the ordinary contract: it labels an authored
wire when that identity is consumed, or creates one standard `port-open` leg
and suppresses the duplicate generated policy leg when it is not.

The five canonical fixtures containing the eight retired atom-key uses move
their labels to typed ports. Compatibility examples are intentionally outside
this kernel-only migration. M1 kernel rows fall from 140 to 138 and M2 parser
leaves fall from 228 to 226. The parser identity becomes
`cf87f98fe9af37edd780303541fa1b5cdc35a6a2332c8975678e24bf9fb8f22c`;
M3--M6 are unchanged.

Extension-gate: #5191

Census-correction: #5191

### 2026-08-03 — the affine anyon path states its incidences

M4 rises from 17.87 to 18.02.  The anyon-pair case replaces one coarse
diagonal edge by the source's nine PEPS sites, twelve interior bonds, twelve
perimeter openings, nine physical legs, three string turns, and two marked
crossings.  The additional lines name mathematical incidences that the old
picture omitted.  They add no parser spelling, alias, escape, overload,
page-distance constant, or case-specific metric.

Census-correction: #5375

### 2026-08-04 — the idempotent panel takes the plane physical axis

M4 rises from 18.02 to 18.03.  The idempotent panel
(`rmp-iii-b-idempotent`) migrates off the `ports={90:physical}` workaround
onto the plane `physical=up` axis introduced under #5375, while keeping
the four ported MPO station declarations and the explicit port-bond rail
structure.  The bare side now takes its leg from the plane physical
policy; the loop side keeps a typed physical port because the picture
policy would also leg the five station boxes.  The additional lines name
mathematical incidences that the workaround hid, and they add no parser
spelling, alias, escape, overload, page-distance constant, or
case-specific metric.

Census-correction: #5375

### 2026-08-04 — nine RMP cases enter the kernel with declared species

The boundary-lasso, two-shift, staircase, ZCL-MPDO, MPO-injective,
torus-crossing, G-injective-MPO, MPO-on-PEPS, and dyon cases leave the grid
and free tiers. Each now states its model on the kernel: a flat frame with
canonical addresses, palettes recorded as declared species, and skin
pairings for the two opposite mover rows. The staircase ascends as in the
source after the mirror re-audit; the lasso hues are model species, not
case ink.

The retired spellings take their owned physical dimensions with them: the
census falls from 708 to 478 sites (route/string 396 to 260,
composition/layout 312 to 218), with metric and frame ownership remaining
zero. M4 rises from 18.03 to 18.71 because the kernel cases name the
species, pairings, and bases that the retired tiers implied. No parser
spelling, registry row, alias, escape, or overload is added; the
labelled-mark ink repair expands an existing style before its node reads
it.

Census-correction: #5350

### 2026-08-04 — correction: the idempotent panel's loop side uses the plane physical policy

The idempotent-panel entry of 2026-08-04 describes an intermediate commit
of that migration.  In the merged state, both the loop side and the bare
side of `rmp-iii-b-idempotent` take their upward leg from the plane
`physical=up` policy; no typed physical-port workaround remains on either
side.  The loop side's five station boxes -- `N`, `E`, `S`, `W`, and `J`
-- seal off that policy leg with `void=sealed` and keep their own typed
virtual ports instead
(`tests/tenkz/rmp/section-iii-b/cases/rmp-iii-b-idempotent.tex`, lines 15,
25-33, and 53-54).  The plane `physical=up` axis was introduced under
#5405; #5375 remains the census-correction tag for the migration, not the
axis's origin.  M4 and every other meter are unchanged by this correction.

### 2026-08-04 — the g-injective plaquette turns its labels outward

The g-injective-mpo case corrects its port assignment: the eight sector
labels move onto genuine open boundary half-edges with explicit west and
east open wires, and the four plaquette bonds ride unlabelled inward
ports, as the author plaquette draws them. M4 rises from 18.71 to 18.72
for the four added open-wire lines. No parser spelling, registry row,
alias, escape, or overload changes.

Census-correction: #5477

### 2026-08-05 — the condensation panel derives its doubled plane from the frame

The condensation panel (`rmp-iii-b-condensation`) leaves the lattice tier
for the kernel: one plane frame with the contract bilayer basis (the
`planes` preset) owns both 6x4 sheets, and every site pair, in-sheet bond,
inter-sheet contraction, and perimeter opening is a member-addressed
declaration.  The six interior path marks become portless affine beads --
atoms one fractional pitch step east of their member sites -- and each
sheet's marked string routes through its beads, which closes the
structural gap the 2026-08-03 review recorded against the shared
doubled-plane basis scaffold.  M4 rises from 18.72 to 19.15 because the
kernel case names the 142 incidences the retiring preset implied.  The
scaffold rides the existing frame, basis, and address machinery: no
parser spelling, registry row, alias, escape, overload, page-distance
constant, or case-specific metric is added, and the dimension census is
unchanged.  The regression
`tests/tenkz/kernel/regression/r_planes_doubled_scaffold.tex` pins the
two-sheet population, the claimed member, the per-sheet bead offsets
through the plane map, and the via-routed sheet strings.

Census-correction: #5348

### 2026-08-05 — wave 1B: seven Section-II panels move to the kernel tier

The Section-II spectra-and-canonical-form family — the reduced-density
racetrack, its eig twin, the transfer-operator ladder, the fixed-point
capsule pair, the one-site isometry, the SV17 approximation chain, and
the left-canonical triangle — leaves the grid tier for kernel flat
frames with declared typed ports.  The isometry and state atoms take the
stock pill skin.  The Fable verification pass corrected three renders
against the sources before landing: the two racetracks re-open their
physical legs (grid bonds had contracted every vertical pair the source
leaves open), the SV17 marginal keeps its ket legs up and bra legs down
(an operator, not its trace), and the transfer ladder now draws the
source's cut region as the house enclosure.  The fixed-point pair's fold
draws flush with the capsule edge on the kernel — a rendering regression
from the grid cup, re-graded honestly to a cosmetic gap.

M4 rises from 19.15 to 19.75 because the kernel cases name every port,
rail, and closure that the grid rows and sandwich words implied.  The
physical-dimension census is unchanged at 478 sites (route/string 260,
composition/layout 218); no ceiling moves.  No parser spelling, registry
row, alias, escape, or overload is added or removed.

Census-correction: #5347

### 2026-08-05 — seven Section-III-A workbench panels enter the kernel (wave 2A)

The eq50, eq51, eq52, diagram-two, eq50-reduced, f-symbol-simplified-a,
and mpo-representation cases leave the grid tier. Each now states its
model on the kernel: flat frames with canonical addresses, typed ports on
every mpo atom, and the source-red operator palette recorded as the
declared mpo species on the simplified F-symbol and O_a panels. The
eq50-reduced and O_a panels drop the labels their 0.7 drawings invented,
and the traced chains book the closure-ink residue — identified extended
ends where the sources draw the racetrack return — as one K1 renderer
item on the gap bar (eq51, eq52, diagram-two).

M4 rises from 19.75 to 20.14 because the kernel cases declare the ports,
species, and wires their one-line grid spellings implied. The owned
dimension census is unchanged at 478 sites (route/string 260,
composition/layout 218), and no parser spelling, registry row, alias,
escape, overload, or page-distance constant is added.

Census-correction: #5347

### 2026-08-05 — wave 1A carries seven Section-II panels onto the kernel tier

Seven Section-II cases move to kernel spellings with explicit typed ports:
the MPS marginal, the MPO row, the local purification, the MPU blocking and
brickwork panels, and the workbench V-tensor and boundary-B factorizations.
The vision pass against the author sources restored four source facts the
first draft lost: the marginal's state row points its legs up over an open
chain, the MPO row shows its open west and east stubs, the purification's
X capsules absorb the doubling so one virtual rail is open per outer side
(no equation check off remains), and the conjugate tensors carry their
overlines. The V-tensor's l^(1/2) bead now sits on the west cup arc, and
the boundary-B palette is recovered from the author code's explicit fill
colours as declared charge/flux species, closing that panel's X row. The
blocking panel records hull-routed side closures the renderer does not yet
ink (K1, bar row of 2026-08-05).

M4 rises from 20.14 to 20.77 because the kernel cases spell out the typed
ports, wires, and species that the grid tier implied. The dimension census
is unchanged at 478 sites (route/string 260, composition/layout 218). No
parser spelling, registry row, alias, escape, or overload is added.

The wave's migrations leave `\tnX` with two corpus option signatures, so
the sugar detector now flags it:

| Flag | Verdict |
|---|---|
| flag:sugar-shaped:command:tnX | tombstoned by contract: `\tnX{m}` migrates to `\tn[skin=ring]{m}` (`LANGUAGE-1.0` 10); the kernel cases of this wave already spell the ring skin directly, and the remaining grid-tier uses die at the S4 swap; expiry 0.9 |

Census-correction: #5347

### 2026-08-05 — the six-panel intersection windows state their nested regions

The two Section-IV six-panel cases migrate to the kernel and draw the
source's nested selection: an inner enclosure over the retained two-site
patch inside the outer boundary-window enclosure, replacing the invented
three-by-four lattice. The kernel renders the containment the model
already held: an enclosure whose members nest inside another's steps the
outer contour out by one clearance per containment level, a pierced
physical leg tracks that depth, and an unbonded virtual port cut by a
region window now runs to the innermost containing contour and stops on
it. The swapped source metadata of the two panels is realigned (LHS6 is
the L window over A--B, RHS6 the R window over B--C) and the pairing
digest re-bound. M4 rises from 20.77 to 20.83 because the kernel bodies
name the ports, wire, and both windows the retired lattice preset
implied. No parser spelling, registry row, alias, escape, or overload is
added; the physical-dimension census is unchanged. The regression
`tests/tenkz/kernel/regression/r_nested_regions.tex` pins the stepped-out
outer contour and the cut stub that ends on the inner window.

Census-correction: #5462

### 2026-08-05 — seven Section-III-A panels enter the kernel (wave 2C)

The MPO-tensor, PEPS-tensor, commuting-Hamiltonian, GHZ-tensor, Hadamard,
MPO-action, and torus-two cases leave the grid and free tiers.  Each states
its model on the kernel: flat frames with canonical addresses, typed ports,
declared strings for the red operator level, and the stock pill skin for the
two-site gate.  The Hadamard target is re-adjudicated: its paired author
panel (lines 359-360) is the paper's own H glyph — the filled dot on the
virtual bond that line 1449 equates with the Hadamard matrix — so the
wrong-source pairing closes and the case redraws to the source.  The
GHZ-tensor redraws to the author's glyphless junction, and the MPO-action
panels regain the source's diagonal virtual pair, closing that bar row.

The retired free-tier spellings take their owned physical dimensions with
them: the census falls from 478 to 435 sites (route/string 260 to 244,
composition/layout 218 to 191), with metric and frame ownership remaining
zero, and the ceilings ratchet down with it.  M4 rises from 20.83 to 21.35
because the kernel cases name the atoms, strings, and typed ports the
retired tiers implied, and because the commuting-Hamiltonian and MPO-action
equations now spell both panels explicitly.  No parser spelling, registry
row, alias, escape, or overload is added.

| Flag | Verdict |
|---|---|
| flag:consumers:key:picture:east label | keep-because: the wave-2C respell moved one consumer onto the kernel port-label spelling and the row's two remaining consumers are 0.7 grid-tier cases that retire wholesale at the S4 surface swap; expiry 0.9 |

Census-correction: #5347

### 2026-08-05 — wave 2B moves seven more Section-III-A panels onto the kernel

The seven Section-III-A cases of wave 2B — the upward GHZ copy tensor, the
SPT intertwiner, the u_g pull-through star, the enlarged MPO word, the
string-order loops, and both boundary-algebra words — leave the grid and
free tiers for kernel flat frames with declared typed ports and canonical
addresses. The boundary-algebra family and the enlarged word restore the
source's second physical leg per site and spell their traced returns
through invisible corner junctions, since the single-row trace policy does
not draw its return yet; the star and the loops replace millimetre
placements with cell and port addresses; two archival pairings are
corrected to the panels the cases actually draw (sptintertwin gh.pdf and
Eq60.pdf).

The migrations retire the tiers' owned physical dimensions: the census
falls from 435 to 401 sites (route/string 244 to 224, composition/layout
191 to 177), with metric and frame ownership remaining zero, and the
ceilings tighten to match. M4 rises from 21.35 to 22.22 because the kernel
cases name the ports, junctions, and species their retired sugar implied.
No parser spelling, registry row, alias, escape, or overload is added.

The wave drops the `no legs` key below tenure:

| Flag | Verdict |
|---|---|
| flag:consumers:key:object:no legs | dies at S4 with the 0.7 object ledger: a suppressed policy leg is port ownership, which typed `ports=` already states; wave 2B retired its intertwiner consumers; expiry 0.9 |

Census-correction: #5347

### 2026-08-05 — wave 1C moves seven Section-II panels onto the kernel tier

The Section-II canonical-form and MPDO family — the right-canonical
triangle, both orthogonality words, the boundary-state factorization, the
renormalization isometry, the T/S channel pair, and the periodic MPDO
transfer word — leaves the grid tier for kernel flat frames with declared
typed ports.  The isometry's U takes the stock pill skin and the periodic
word the stock MPO skin.  The Fable verification pass repaired one render
before landing: the boundary state's sigma_partial-R region, which the
migration had reduced to a floating label, is drawn by the range-addressed
enclosure mark — the source's dotted box — retiring the interim
missing-element defect and the grid tier's brace-for-box note.  The two
right-canonical triangles are re-graded honestly to cosmetic gaps: the
sources draw their apexes west (directly in the definition, by
whole-equation mirror in the orthogonality panel) and the kernel triangle
skin has one fixed east apex.  The left-orthogonality word keeps faithful
because the same mirror lands its glyphs on the fixed apex.  The periodic
word's stale extra-element defect is adjudicated against the author
block, which only ever draws one panel; its residue is the flush
single-row trace wrap.

M4 rises from 22.22 to 22.48 because the kernel cases name the ports,
skins, and closures their grid rows and sandwich words implied.  The
owned dimension census is unchanged at 401 sites (route/string 224,
composition/layout 177); no ceiling moves.  No parser spelling, registry
row, alias, escape, or overload is added or removed.

The wave drops two 0.7 spellings below tenure:

| Flag | Verdict |
|---|---|
| flag:consumers:key:object:tri | keep-because: wave 1C retired the canonical-form and orthogonality consumers onto the kernel triangle skin; the two remaining consumers are 0.7 grid-tier cases (the tangent projector and the workbench P_T(A)) that retire wholesale at the S4 surface swap; expiry 0.9 |
| flag:sugar-shaped:command:tnspan | keep-because: wave 1C's enclosure respell of the boundary state dropped the lone brace-above signature, folding the corpus onto two; the span sugar is a 0.7 grid-tier spelling whose remaining consumers retire at the S4 surface swap, the kernel stating ranges through mark addresses; expiry 0.9 |

Census-correction: #5347

### 2026-08-05 — wave 4 closes the Section-IV boundary family onto the kernel

The eleven Section-IV cases of wave 4 — the one-dimensional ground-space
trace and the ten intersection panels — leave the grid and free tiers for
kernel flat frames with declared typed ports and canonical addresses.  The
boundary operators L, R, and X take the stock pill as wide atoms with
their lobe legs at top-face stations, closed through side cups; the
rhs-four operator alone is the wide box atom of the LANGUAGE-1.0 section
14 sign-off, and its respell retires the family's one free-tier body.
The traced ground-space word returns below the row through corner
junctions with the author's square X on the return, resolving the old
small-glyph gap.  The cut virtual ends of the two, three, and four panels
now turn upward through invisible junctions as the sources draw them, and
the rhs-five re-audit retires the recorded mirror: the kernel respell
restores the source embedding and the case is promoted to faithful.

The retired free-tier spelling takes its owned physical dimensions with
it: the census falls from 401 to 383 sites (route/string unchanged at
224, composition/layout 177 to 159), with metric and frame ownership
remaining zero, and the ceilings ratchet down to match.  M4 rises from
22.48 to 22.88 because the kernel cases name the atoms, junctions, and
typed ports the retired tiers implied.  No parser spelling, registry row,
alias, escape, or overload is added or removed.

The wave drops two 0.7 spellings below tenure:

| Flag | Verdict |
|---|---|
| flag:consumers:command:tnskip | keep-because: wave 4 retired the intersection break onto unbonded typed ports and invisible junctions; the two remaining consumers are blueprint MPDO staircase figures (chapters 20 and 21) that migrate with the blueprint's own kernel pass at the S4 surface swap, the kernel stating a skipped cell as `void=open`; expiry 0.9 |
| flag:consumers:key:object:up at | keep-because: wave 4 retired the boundary-operator consumers onto typed top-face stations; the lone remaining consumer is the blueprint physical-blocking figure (chapter 26) that migrates with the blueprint's kernel pass at the S4 surface swap, the kernel stating the leg through `ports=`; expiry 0.9 |

Census-correction: #5347

### 2026-08-05 — wave 3: the two-panel equalities and fusion trees reach the kernel

The nine wave-3 cases — the three MPO-reduction proofs, the coproduct
equation and its workbench twin, the dual-reduction intertwiner, the two
association trees, and the workbench tangent projector — move onto the
kernel tier.  The proofs and the intertwiner leave the free and grid
tiers for kernel flat frames whose spanning V, F, and X boxes take
slotted typed ports, composed in `tenkzeq` with audited equal boundary
signatures; the proofs drop their red house rails for the sources'
all-black ink.  The two coproduct panels spell their closed virtual
words as drawn racetrack returns through invisible corner junctions
(the single-row trace policy does not ink its return yet), recover the
sources' paired physical stubs, and opt their one relation out of the
audit with the recorded arity reason.  The association trees bind the
kernel surface over the unchanged tree expander.  The tangent projector
repairs its structural gap at the archival widths — four columns and the
kernel identity strand against five-plus-four columns — while its
mirrored triangle windows stay on the 0.7 grid tier with the fixed
east-apex kernel skin (#5485) still pending.

The reduction proofs' owned millimetres leave the corpus: the census
falls from 383 to 357 sites (route/string 224 to 208, composition/layout
159 to 149), with metric and frame ownership remaining zero, and the
ceilings and provenance pins tighten to match.  M4 rises from 22.88 to
24.11 because the kernel cases name the ports, junctions, and returns
their retired sugar implied.  No parser spelling, registry row, alias,
escape, or overload is added or removed.

Census-correction: #5347

### 2026-08-05 — wave 5 moves the PEPS sheet family onto the plane frame

Five of the six lattice-tier PEPS sheets — the projection sheet, the
PEPO sheet, the four-panel renormalization figure, the inverse
renormalization pair, and the workbench plaquette — leave the retiring
`tenkzlattice` environment for kernel plane frames.  A sheet is now the
`lattice=` sugar over one plane frame with per-site policy legs; the
projection figure states its sixteen projector regions as enclosure
marks of a declared source-red species and names its |phi) bond through
a port label, the renormalization figure's product tensors take
per-atom half sizes, and its final trace bead closes its virtual ring
through invisible junctions, retiring the crossed rotate-180 hooks with
the tombstoned frame rotation itself.  The workbench plaquette's
pairing is repaired to FigPEPSRG panel (a) (author lines 744-753) with
the caption-stated unitary, closing that ledger's wrong-source row.

The sixth sheet, the PEPS marginal, stays on the lattice tier: the
bilayer basis rejects every physical policy and numeric ports are
in-plane, so the kept sites' open transverse ket-bra legs have no
kernel spelling; the doubled-plane scaffold covers contracted pairs
only.  The blocker is recorded on the verdict and the gap bar, and the
`tenkzplanes` tenure flag below carries it.

M4 rises from 24.11 to 24.27 because the kernel cases name the atoms,
enclosure marks, junctions, and typed ports the retiring preset
implied (+21 lines over the five respelled cases).  The dimension
census is unchanged at 383 owner sites with unchanged ceilings, and no
parser spelling, registry row, alias, escape, or overload is added or
removed.

The wave leaves two 0.7 spellings at reduced tenure:

| Flag | Verdict |
|---|---|
| flag:consumers:environment:tenkzplanes | keep-because: the lone remaining consumer is the blocked PEPS marginal, whose open transverse ket-bra legs the kernel bilayer basis cannot yet spell; the environment retires with the case's migration once a bilayer transverse-physical spelling lands; expiry 0.9 |
| flag:consumers:environment:tenkzlattice | keep-because: wave 5 retired the Section-II sheet consumers onto plane frames; the remaining consumers are 0.7 grid-tier cases outside this family that retire wholesale at the S4 surface swap; expiry 0.9 |
| flag:cooccur:picture:north+south | keep-because: a projected sheet states its whole four-side boundary contract, so every sheet picture names both receding sides; the values differ per picture (the renormalization beads open one and seal the other), so the pair is two independent policies, not one key; expiry 1.0 |

Census-correction: #5348

### 2026-08-05 — wave 6 moves the region-marked panels onto the kernel tier

The six wave-6 cases — the published bulk-boundary region and its archival
workbench twin, the historical four-station composite, the two-dimensional
ground-space window, and the two toric-code blocked tensors — leave the
lattice and free tiers for kernel plane and flat frames.  The two boundary
panels draw their red regions as charge-species enclosure marks over the
5x6 sheet and audit their reductions with the recorded open-leg reason;
the archival twin regains its distinguishing R and R^c names and all-red
rail, having previously duplicated the published A/B spelling.  The
ground-space window nests two range-addressed enclosures with X on the
outer contour; a 900dpi read of both source PDFs retires the ledger's
arrowed-legs claim, the source legs being plain.  The historical composite
respells each four-box ring as one closed operator string through its
lambda corner with the sweeping arcs as via-routed strings.  The toric
pair keeps its mid-side stations as portless kernel atoms with the sheet
as the house enclosure; the dual's dotted diagonals ink solid, the kernel
wire grammar having no stroke-style key.

The retired tnregion, tnedge, tnput, and tnjoin millimetres leave the
corpus: the census falls from 357 to 313 sites (route/string 208 to 192,
composition/layout 149 to 121), with metric and frame ownership remaining
zero, and the ceilings and provenance pins tighten to match.  M4 rises
from 24.27 to 24.62 because the kernel cases name the ports, species, and
waypoints their retired sugar implied.  No parser spelling, registry row,
alias, escape, or overload is added or removed.

The wave drops three 0.7 spellings below tenure:

| Flag | Verdict |
|---|---|
| flag:consumers:key:picture:bond label | dies at S4 with the 0.7 picture ledger: wave 6 retired the boundary pair's bond-label spellings onto kernel wire-point label marks, and the one remaining consumer is a blueprint chapter that respells at the S4 surface swap; expiry 0.9 |
| flag:consumers:key:region:inset | dies at S4 with the 0.7 region ledger: wave 6 respelled the nested ground-space contours through the kernel mark's inset step (#5498), and the two remaining consumers are blueprint chapters that respell at the S4 surface swap; expiry 0.9 |
| flag:sugar-shaped:command:tnedge | keep-because: wave 6 retired the toric diamond and diagonal edges onto kernel wires; the four remaining uses sit in one 0.7 grid-tier case (the PEPS projection) that retires wholesale at the S4 surface swap; expiry 0.9 |

Census-correction: #5347

### 2026-08-05 — wave 7 closes the crossing and ring-closure family onto the kernel

The twelve wave-7 cases — the pulling-through plaquette and its archival
Dia3 twin, the Dia4 coproduct ring, the boxless F crossing, the Eq59
group average, the three pentagon sketches, the SPT intertwiner, the
torus cycle pair, and both PEPS renormalization panels — leave the free
and grid tiers for kernel flat and traced frames.  This retires the last
free-tier bodies of the benchmark: the rotated-frame group of Dia3
respells through angle ports and per-leg `dir=`, the pentagon sketches
are redrawn against the paper's own fig3 pentagon figures with their
crossing orders declared, the torus takes the contract's section 12.2
wound-string spelling, and the F tensor recovers the source's boxless
directed crossing.  Two ledger contradictions close on the way: the SPT
intertwiner regains the source factor order the mirrored spelling had
lost, and the first renormalization panel regains its four edge-centred
sites.  One archival pairing is corrected: the Eq59 group average pairs
with Eq59.pdf, the file named Eq59now.pdf holding the SPT g-pull sketch.

The retired tenkzfree millimetres leave the corpus entirely: the census
falls from 313 to 0 sites (route/string 192 to 0, composition/layout 121
to 0), metric and frame ownership stay zero, and the ceilings and
provenance pins ratchet to zero — a published figure now contains no
millimetres, as the contract demands.  M4 rises from 24.62 to 26.05
because the kernel cases name the ports, junctions, species, and declared
crossings their retired free-graph ink implied.  No parser spelling,
registry row, alias, escape, or overload is added or removed.

The wave drops seven 0.7 spellings below tenure:

| Flag | Verdict |
|---|---|
| flag:consumers:command:tngroup | dies at S4 with the 0.7 group ledger: wave 7 retired the last rotated-frame group (Dia3) onto angle ports, orientation being a consequence of where a record sits; expiry 0.9 |
| flag:consumers:key:group:frame | dies at S4 with the tombstoned `frame={rotate=}`: its last consumer was the Dia3 group wave 7 respelled; expiry 0.9 |
| flag:consumers:key:connection:dir | dies at S4 with the 0.7 connection ledger: wave 7 moved every directed free-tier edge onto the kernel wire's `dir=`; expiry 0.9 |
| flag:consumers:key:connection:fused | dies at S4 with the 0.7 connection ledger: wave 7 retired both renormalization consumers, bundle multiplicity owing no ink under the kernel contract; expiry 0.9 |
| flag:consumers:key:object:circle | dies at S4 with the 0.7 object ledger: wave 7 retired the last `\tnput[circle]` lambda insertions onto the kernel ring-skin bead; expiry 0.9 |
| flag:consumers:key:connection:label | keep-because: wave 7 retired the F-crossing consumer onto kernel wire-point label marks; the lone remaining consumer is a blueprint figure that respells with the blueprint's kernel pass at the S4 surface swap; expiry 0.9 |
| flag:consumers:key:connection:role | keep-because: wave 7 retired the pulling-through and torus consumers onto declared kernel species; the lone remaining consumer is a blueprint figure that respells with the blueprint's kernel pass at the S4 surface swap; expiry 0.9 |

Census-correction: #5349

### 2026-08-05 — wave 8 closes the arrow-composed workbench escapes onto the kernel

The two wave-8 cases — the PEPS fine-graining panel and the archival
historical composite — leave the lattice tier for kernel flat and plane
frames.  Each embedded panel respells through kernel lattice sheets with
declared boundary policies; the composing arrows and panel letters stay
plain math outside the audited kernel scope, the accepted escape idiom,
because the audited multi-panel term grammar remains future work (#5496,
#4703).  Both verdicts promote to faithful against figrenorm2D and the
archival sheet, and one lattice-tier case remains in the benchmark: the
PEPS marginal, blocked until a bilayer transverse-physical spelling
lands.

The census stays at zero sites across every dimension: the retired
lattice bodies carried no millimetres, so the ceilings and provenance
pins hold unchanged.  M4 rises from 26.05 to 26.08 because the kernel
cases spell out the sites, frames, and boundary policies their retired
one-site lattice sugar implied.  No parser spelling, registry row,
alias, escape, or overload is added or removed, and no 0.7 spelling
changes tenure.

Census-correction: #5347

### 2026-08-05 — the bilayer sheet spells its open transverse legs

The plane frame's independent transverse axis gains open ends. A bilayer
member declares an upward or downward physical leg; the end is cut on the
page side its signed transverse vector exits, so panels compare it against
the ordinary physical legs of that side, and it enters the boundary
signature as an ordinary open physical index. The event schema learns the
two transverse directions alongside the page compass.

The PEPS marginal is the demand and the proof: the last non-kernel
benchmark body leaves the lattice tier with its kept sites' ket-bra legs
open and its traced column closing site by site. Every one of the 130
benchmark cases now states its model on the kernel, and no verdict remains
blocked. M4 rises from 26.08 to 26.49 for the declared legs and the closing
loops the retired environment implied. The physical-dimension census stays
at zero.

Census-correction: #5507

| flag | verdict |
|---|---|
| flag:consumers:key:picture:trace | keep-because: the marginal's migration retires the picture-level trace from the doubled sheet, and the two remaining consumers state genuine single-row traces the kernel still owes its drawn return (#5492); the key retires with that ink, expiry 0.9 |
| flag:consumers:environment:tenkzplanes | dies at S4: its lone consumer was the PEPS marginal, which this session migrates onto the kernel bilayer basis; expiry 0.9 |

### 2026-08-05 — a physical index may be directed

The direction mark stops being a virtual privilege. A physical index
carries `dir=` exactly as a virtual one does, and the orientation of a
directed physical open end enters the exposed boundary signature: a space
and its dual no longer pass for one another across a pictured equation.
An internal directed contraction exposes nothing and leaves no entry. The
coded refusal that made the mark a type error retires with it.

Three cases stop paying for that refusal. The MPO and PEPS fat-graph
levels and the mixed pentagon's vertex legs had been typed virtual to
reach the mark; they return to physical ports, and their renders are
unchanged. M4 rises from 26.49 to 26.54 for the recovered typing. The
physical-dimension census stays at zero.

Census-correction: #5360

### 2026-08-05 — the closure draws itself and a site answers the policy

Two changes return the picture body to the size of the idea it draws.

A flat row's traced sides now draw their closure. The rail leaves both
ends, drops by the trace reach, and returns with the source's rounded
corners, instead of running straight along the row it closes. Every
figure that spelled that return by hand -- an invisible junction at each
corner and four wires between them -- says `west=trace, east=trace`
again, and `boundary=periodic`, which is those two words, draws a
periodic chain as the papers draw it.

A site may answer the picture's physical policy for itself. The policy
legs a row's sites; a ring standing between tensors, or an elision,
carries no physical index and now says `physical=none` once instead of
forcing the picture to abandon its policy and list every port of every
atom. `void=sealed` could not serve: a sealed site is a removed site and
loses its bonds.

The boundary-insertion word shows the size of the change: eleven lines of
addresses and ports become three lines that name the row, its closure,
and the two sites that carry no physical index. M4 falls from 26.54 to
26.50 on that one case, and the corpus rewrite that follows will take it
further. The parser gains one leaf, 226 to 227, and the kernel ledger one
row.

| flag | verdict |
|---|---|
| flag:consumers:key:kernel-atom:physical | keep-because: the key lands with the closure fix and the first rewritten word; the rest of its consumers arrive as the corpus returns to the policy spelling it was forced to abandon; expiry 0.9 |

Extension-gate: #5524

Census-correction: #5492

### 2026-08-05 -- the benchmark says its pictures in the language's own words

The migration to the kernel wrote every atom's address and every atom's
port list by hand. It had to: a row holding a gauge ring or an elision
could not declare a physical policy, so the picture abandoned the policy
and spelled the four ports of every site.

Nineteen cases in Sections II and III A now say the same drawings in the
words the language already owns. A picture declares `physical=up`,
`down`, or `updown` once, and the ring, the ellipsis, or the fusion box
that carries no physical index answers `physical=none`. A site standing
in reading order needs no address: `&` chains it along the row. A side
that opens says `west=open, east=open` instead of running a wire to
`open w` and another to `open e`.

The MPO-word figure carries the change. Five sites that each spelled an
address, a name, and four ports become one chained line, and the word
falls from thirty-four lines to twenty-six. The stacked intertwiner falls
from sixty-two to fifty-three, the three-layer reduction from fifty-seven
to fifty-one, and the two-site zero-correlation identity states its
traced physical pairs without a single port.

Every rewritten case renders pixel-for-pixel as it did before at 200 dpi.
The drawings, the labels, the species, and the honest residues are
untouched; only the case hashes move. M4 falls from 26.50 to 25.92. The
parser, the kernel ledger, the escape ledger, and the alias ledger do not
move: this session spends no grammar.

Two rewrites were reverted at the render. The two-shift MPU word hangs
the compiler when a declared skin's pairings meet a chained row break,
and the doubled MPS marginal loses the source's open physical legs
because grid bonding contracts every stacked pair. Both keep their
addresses, and the chain-grammar hang is worth a look on its own.

Hand-spelled closures stay hand-spelled where the source draws them in
its own hue or with square corners: the traced sides draw a black
racetrack, and the boundary-algebra, coproduct, and enlarged-MPO words
draw a red trapezoid or a sharp rectangle. Those returns are ink, not
ceremony.

Census-correction: #5524

### 2026-08-05 — the first blueprint chapters take the kernel

Seventeen blueprint chapters, slide decks, and manual pages respell their
figures on the kernel. Each picture states its row and its column count and
then names its atoms in reading order: the chain runs on the alignment
character, a stacked picture breaks its rows, and the grid bonds the
neighbours it just placed. A word closed on itself says `boundary=periodic`
and lets the closure draw itself; a word open at both ends says
`west=open, east=open`. An address, a name, and a port list survive only
where a later line reads them. The benchmark corpus is untouched, so every
meter but the consumer census stands; the demand corpus loses the retired
grid spellings.

Five figures keep their 0.7 spelling and are named in the disposition
ledger: the operators of the maximally entangled state, the correlation
window, the two channel sandwiches, and the transfer-map slide ride a
generated cup between operator rows, where the on-wire anchor divides the
record chord rather than the drawn arc, so a tensor placed there would read
as sitting on the physical contraction.

The physical policy is a real trade and not a free win. It pays where two or
more sites take an unlabelled leg -- the operator stack, the traced word --
and costs where a single site among many carries the index, because every
other site then has to refuse it. Those pictures keep their port list, which
also keeps them out of the codemod column.

| flag | verdict |
|---|---|
| flag:consumers:key:picture:west label | keep-because: this wave retires the grid consumers it touched; the five that remain all stand a tensor on a generated cup, and they respell when the kernel gains a station on that arc; expiry 0.9 |

Census-correction: #4709

### 2026-08-05 — three equations recover the boundary their sources draw

M4 rises from 25.92 to 25.98. Three benchmark equations declared different
boundaries on their two sides, and the equation audit read the difference
where the reviewer had read the drawing. In every case the source settles
the question, and in two of the three the drawing was wrong as well.

The stacked intertwiner had each of its four operator boxes keep its own
pair of physical stubs, so the fusion move claimed five sites on one side
and four on the other. A column of a stacked word is one site: the two
boxes multiply there and the index between them is summed. The source
strokes that index in one line through both boxes; the case now bonds it,
and the equation reads three sites against three.

The idempotent panel kept a stray in-plane north wire from its typed-port
era. The plane transverse policy already draws the one upward leg the
source strokes, and the wire drew a second black half-edge in a direction
no source line takes. Removing it deletes ink that was never in the
source and leaves both sides reading west, east, southwest, northeast,
the red tail, and the upward leg.

The four-arm coproduct ring is the honest opt-out. Its four boxes are
pierced by the same wire the local map already typed physical, and that
typing is now stated on both sides; but the third coproduct carries one
site to four, so four pierced wires answer one and the arity genuinely
changes. The relation records the waiver with that reason, and the event
stream carries it on the one relation the scope owns.

No parser spelling, registry row, alias, escape, or overload moves. The
four-arm ring renders as before; the other two render closer to their
sources.

Census-correction: #5530

### 2026-08-05 — a cup carries its matrix and a bracket takes its side

Two documented spellings could be written and could not be drawn. The
side alphabet took the bare cup word alone, so `west={cup=$m$}` was
rejected outright; the mark alphabet had no bracket in it, and the
membership pass resolved a selector for one form only, so a bracket over
a cell range had neither ink nor members. Both now draw.

The labelled side word is the documented expansion and nothing more: the
side takes `cup`, and each of its bends carries a ring holding the matrix
the side closes through, addressed half way along the bend. It stands on
the bend rather than inside it because the station on a generated arc
landed one change earlier, which is what the previous session was waiting
for when it left five figures on their 0.7 spelling.

A bracket is the arc of the offset hull an enclosure strokes whole, taken
on the side its label sits on, closing with the two turns that end it.
Both hull forms enter the containment order, so a bracket inside a region
window stands one clearance in from it instead of drawing along its
support. A bracket that names no side speaks from the south, where the
authors put a brace under a span.

Four Section-II cases drop the substitutes they were carrying: three
spelled a bare cup plus a hand-placed bead on the canonical cup wire, and
one spelled a south label at the midpoint of a span where the source
braces it. Six bead declarations fold into the side word each picture
already carried, and eleven lines of apology go with them. M4 falls from
25.98 to 25.94, and `rmp-ii-spectrum-transfer` leaves the cosmetic-gap
bar, its last recorded substitution retired. The parser census and the
overload census stand: the four side keys keep one leaf each and the
bracket shares its word with no other alphabet.

Census-correction: #5482

### 2026-08-05 — the mark inks on every bearing, and a rail may be dashed

A direction mark was a lottery on the bearing. A leg springs from the centre
of the glyph it leaves and the glyph's ink is laid over that centre
afterwards, so the named station — a fraction of the whole leg — fell inside
a silhouette that is wider than it is tall. The same mark that cleared a
south bearing vanished under an east one. The station now rides the leg's
daylight, the stretch between the silhouette and the free tip, and it is the
mark's body that rides it, so the barb never re-enters the silhouette. One
rule, four bearings, both endpoint orders. The four barb styles still share
one named station; two of them now take it as an argument and name it as the
key's default.

A wire also gains the stroke it never had. The sources draw two non-solid
rails and no third: a dashed one for an index the picture draws but does not
contract, a dotted one for a lattice lying under the sheet being drawn. The
alphabet is therefore `solid`, `dashed`, `dotted`, the dash lengths are named
metrics, and the toric-code dual sheet stops inking its original-lattice
diagonals solid. Read beside the published figure at 900dpi, the source
dashes those diagonals where the old note called them dotted; the case
re-pins and promotes to `faithful`.

The new leaf is the one census move: M1 kernel 139 to 140, M2 parser paths
227 to 228, with the parser identity changing accordingly. M4 is unmoved at
25.94 — the dashed spelling costs the case no line.

| flag | verdict |
|---|---|
| flag:consumers:key:kernel-wire:stroke | keep-because: kernel-scope rows count no demand-corpus consumers before the S4 surface swap, as every other kernel-wire row records; the leaf already carries its first benchmark consumer in rmp-app-toric-dual and its Extension-gate in #5543; expiry 0.8 |

Extension-gate: #5543

### 2026-08-05 — the moderate chapters, and the last ghost but one

Nine more blueprint chapters respell onto the kernel. Twenty-nine pictures
move to pure kernel spelling, which is what puts every one of them in the
preserve column: a picture that says `physical=up` or `boundary=periodic`
still reads its topology off a sugar row, and the disposition ledger books
that as a codemod, so the ports and the two side words are written out
instead. The trade is visible in the source: the pictures cost sixteen more
lines than their 0.7 originals and none of that goes on scaffolding, because
the chain still runs on the alignment character and only two atoms in the
whole wave need an address.

Three of the nine chapters carry the figures the previous wave had to leave
behind. A tensor now stands on a generated cup, so the Choi projector, the
correlator window, and their side words are ordinary records: the side takes
`cup`, and the matrix it closes through rides half way along the bend. Those
two figures also lose the ghost atoms that stood in for the empty cells the
cup needed, because a wire row populates nothing and an address reaches an
empty cell directly.

That retirement is what moves the consumer census. Four ghost calls remain in
the blueprint and they are all in one figure, so the command falls below
tenure a milestone before its own verdict said it would. Nothing about the
verdict changes: the command was already booked to die at the language
landing, and it now has one blueprint consumer left to lose.

Four grid figures keep their 0.7 spelling and are named in the disposition
ledger. Two want an even-width centre port, which lies between numbered slots
by construction, and a wide dot whose silhouette grows with its span; one
wants a row separation the kernel does not name; one is a commutative diagram,
which is not this language's to draw. The free graphs, the fusion trees, and
the conjugated layer belong to the redraw waves and are untouched here. The
mean lines per benchmark case is unmoved at 25.94, because the benchmark
corpus is untouched.

| flag | verdict |
|---|---|
| flag:consumers:command:tnghost | dies at the language landing because addresses name empty cells directly; the wave retires all but one blueprint consumer and the tenure it loses is the one this row already spent; expiry 0.9 |

Census-correction: #4709

### 2026-08-06 — a region traces its own cell set

The selector gains a subtracted term and the region contour stops rounding
what it encloses up to a rectangle. Both are the same claim: a mark says which
records it stands over, and the ink says the same thing back. Until now the
grammar could name a rectangle and a braced union and nothing else, and the
contour over a union was the union's bounding box — so a staircase came out a
rectangle, and a region with a site taken out of it came out with the site
back in. Five figures in the PEPS chapters could not be drawn without claiming
a region their theorems do not use.

`A - B` names what A names and B does not. It costs no key: membership is
already a set of records, so the difference is the set difference on those
records, and the operator is a spaced hyphen because an address carries
hyphens of its own. The contour follows: a selection standing on cells that
do not fill their bounding rectangle traces the boundary of those cells, at
the same four standoffs the offset hull already folded, so a selection that
does fill its rectangle traces exactly the rectangle it traced before and
every stream and pixel in the corpus is unmoved. The loops are directed with
the member on the left, which is what lets one even-odd path fill a region
with a site taken out of it as a ring.

The dead flag on a mark is exchanged for a live one. `outline` was signed as
"contour without tint" and no renderer read it, because the tint it presupposed
did not exist; `tint` lays the region's hue over the paper it encloses, and
does it before the wires, in containment order from the outside in. That is
the renderer's class order doing the work a background layer does elsewhere —
this stage keeps no layers. The polarity is inverted on purpose: contour-only
is what the benchmark draws and what its sources draw, so the figures that
want paper say so.

The five slots take the house region palette at last. A mark's `selected` was
inking blue where every source and every 0.7 figure inks the region under
discussion red, and three benchmark cases had spelled themselves `secondary`
to get the red they wanted. The table rotates as a whole so it stays
injective — selected red, secondary blue, complement grey and dashed, collar
violet, neutral plain ink — and those three cases now say the word they meant.
Their ink does not move.

M1 kernel stays at 140 and M2 parser paths at 228: one flag out, one flag in.
The M2 identity moves because one leaf-key spelling changed, which is what the
Extension-gate below is for. M4 is unmoved at 25.94 — the benchmark corpus
gains no line, since the difference term is spelled inside a selector that was
already there.

| flag | verdict |
|---|---|
| flag:consumers:key:kernel-mark:tint | keep-because: kernel-scope rows count no demand-corpus consumers before the S4 surface swap, as every other kernel-mark row records; the leaf carries its first blueprint consumers in the two migrated PEPS chapters and its Extension-gate in #5570; expiry 0.8 |
| flag:sugar-shaped:command:tnsite | dies at the language landing with every 0.7 lattice command; the wave that migrates the PEPS region figures retires two of its six blueprint consumers, and the narrowed option profile the flag reads is that retirement and not new uniformity; expiry 0.9 |

Extension-gate: #5570

### 2026-08-06 — the body restates one generated bond

A lattice draws its bonds from the row and column policy, and until now the
body could not reach one of them. Three spellings were tried and none stated
it: an authored wire over the same pair was recorded first and the generated
bond inked on top of it, the typed-port spelling of that pair raised
`TKZ-PORT-CONSUMED` because the generated bond had already claimed both ports,
and writing out eighty-four wires to give one of them a different ink is not a
spelling anyone will use. Two PEPS panels wanted exactly that sentence — this
edge is the edge being blocked — and were the last two the region wave could
not carry across.

The kernel already held the rule and was not applying it to bonds. Section 4
says the frame populates and the body overrides: an authored atom at a cell
replaces the atom the frame put there, and every address of that cell resolves
to the authored record rather than to coincident population underneath it. A
grid bond is frame population of the same kind. So an authored index wire
joining two adjacent cells IS that pair's bond, with its species, its stroke
and its route, and the frame mints no second one under it. The pair's ports
then have one consumer, which is why the typed-port spelling stops colliding.

The rule costs nothing. M1 stays at 140 kernel rows and 201 total; M2 stays at
228 parser paths with its identity unchanged, because no key, no value, and no
address production was added — the change is a suppression in the generation
loop, reading the wire records the body already left. M4 is unmoved at 25.94:
the benchmark corpus is untouched. Only an index wire retires a bond; a
travelling string carries an operator index, states a different claim, and
retires nothing.

The two panels move, and both lose their last `\tnedge`. The remaining
blueprint consumer of the command and of its `distinguished` flag is the same
one figure, so both rows fall below tenure a milestone before their own
verdicts said they would. Neither verdict changes: both were already booked to
die with the 0.7 lattice dialect, and each now has one blueprint consumer left
to lose. The restated bond is thinner than the 0.7 emphasis stroke and that is
the contract doing its work — the stroke follows the type the port carries and
`weight=` is a tombstone, so emphasis rides the declared species and nothing
else.

| flag | verdict |
|---|---|
| flag:consumers:command:tnedge | dies at the language landing with every 0.7 lattice command: an edge is an ordinary `\tnwire` of kind index, and a generated one is now restatable by the body; the two migrated PEPS panels retire all but one blueprint consumer, and the tenure it loses is the one this row already spent; expiry 0.9 |
| flag:consumers:key:connection:distinguished | dies with `\tnedge` it rides: a distinguished edge is a restated bond carrying a declared `species=`, which is how the two migrated panels now say it; the single remaining blueprint consumer goes with the lattice dialect at S4; expiry 0.9 |

### 2026-08-06 — the commutative diagrams leave the language

The six blueprint `tenkzcd` pictures are respelled onto plain tikz-cd,
which is where the signed contract sends them: commutative diagrams
belong to tikz-cd, outside this language (`LANGUAGE-1.0` §10). The four
typed-map figures keep their ink through one preamble style — a channel
arrow is a headless stroke of wire weight in the marked hue, its label
seated on the stroke — and the two coherence pentagons take the ordinary
category-theorist's spelling, a matrix with blank cells, their `\tntree`
bodies unchanged. Every blueprint `R-cd` row in `DISPOSITIONS.md` is
discharged; the environment's remaining consumers are standalone
fixtures awaiting their own redraws.

M3 falls from 29 to 24: the two `radius=`, one `column sep=`, and two
`row sep=` occurrences that rode the retired pictures were the metered
escapes #5085 left open until this migration. M1 stays at 140 kernel
rows and 201 total, M2 at 228 parser paths, and M4 at 25.94 — the
registry and the benchmark corpus are untouched. Seven rows lose their
last demand-corpus consumers with the respelling and take their
verdicts below.

| flag | verdict |
|---|---|
| flag:consumers:environment:tenkzcd | tombstoned by contract: commutative diagrams belong to tikz-cd, outside this language (`LANGUAGE-1.0` §10); the blueprint respelling leaves only fixture consumers, which go with their own `R-cd` redraws; deleted at the S4 swap; expiry 0.9 |
| flag:consumers:command:tnarrow | tombstoned by contract: `\tnarrow` migrates to `\tnwire[dir=to]` (`LANGUAGE-1.0` §10), and a commutative-diagram arrow is tikz-cd's own `\arrow`, outside the language; the respelling retired its last demand-corpus uses; expiry 0.9 |
| flag:consumers:key:picture:maps | tombstoned by contract: `maps` died with `tenkzcd` (`LANGUAGE-1.0` §10); its only demand-corpus consumers were the respelled typed-map figures; expiry 0.9 |
| flag:consumers:key:connection:from | dies with the `\tnarrow` declarations that addressed it: a tikz-cd arrow names its target cell directly, and a kernel wire names both endpoints as arguments; expiry 0.9 |
| flag:consumers:key:connection:to | dies with the `\tnarrow` declarations that addressed it, exactly as `from=` does; expiry 0.9 |
| flag:consumers:key:connection:species | dies at the S4 swap with the 0.7 connection tier it belongs to; the kernel wire carries its own signed `species=` row, and the respelled arrows carry their type in the preamble style; expiry 0.9 |
| flag:consumers:key:setup:species | dies as a name-list: `\tndeclare{species}{name}{hue=...}` is the one declaration door, the blueprint already declares every species through it, and the last bare name-list rode the retired `tenkzcd` opt-in; expiry 0.9 |

### 2026-08-06 — the conjugate flag is sentenced

`conjugate=` is installed on the kernel atom tier and read by nothing: not
the ink passes, not the boundary-signature fold, not a checker.  A sweep of
the whole tree (issue 5383) finds sixteen atoms across seven section-II
benchmark cases carrying the flag, two kernel regression fixtures spelling
it as a manufactured consumer, and no consumer of the answer anywhere.  The
only trace it leaves is the `conjugate=true` field in those atoms' records.

The issue reserved the row until the directed-signatures design decided who
carries duality.  The contract has since decided: wire `dir=` is the one
spelling for a space against its dual (`LANGUAGE-1.0` section 2.4), so a
second semantic carrier would say the same thing twice.  The presentational
reading fails on the corpus's own evidence: no author panel draws a
conjugate glyph, and every benchmark atom that wants visible conjugation
spells `\overline{...}` in its label — wiring the flag to ink would double
the bar on the three labelled cases, grow a stub bar on the empty-labelled
bra rows, and change renders no figure asked for.  What remains is a flag
that looks semantic, claims to be presentational, and is neither; a stored
answer nobody reads is a key that can silently lie.

So the row is tombstoned.  Per the booking rule in force since session 0,
the ledger status moves with the parser row and not before: the registry row
stays `kernel` with its note reading the sentence, the row is struck from
the contract's atom table into the section-10 tombstones today — as the nine
amendments were at their sentencing — and the deletion itself — the parser
row, the sixteen benchmark spellings, the two fixture spellings, and their
re-pinned record streams — executes as the usual corpus rewrite at the 1.0
freeze.

No meter moves today.  M1 stays at 140 kernel rows and 201 total, M2 at 228
parser paths with an unchanged identity, M4 untouched; the registry note and
this sentence are the whole diff.

| flag | verdict |
|---|---|
| flag:consumers:key:kernel-atom:conjugate | tombstoned: read by nothing, duality already has its one spelling in wire `dir=`, and the conjugate overline is label mathematics already spelled in the corpus; the parser row, the sixteen benchmark spellings, and the two fixture spellings leave in the corpus rewrite at the 1.0 freeze, the status moving with the parser row as booked since session 0; expiry 0.9 |

### 2026-08-06 — the MPS and symmetry chapters leave the grid tier

Thirty-three blueprint pictures across the matrix-product-vector chapter, the
string-order chapter, the symmetry appendix, and the two channel-representation
chapters now carry `\tenkzkernel`. The wave retires the chapters' 0.7
spellings — `sandwich` two-row presets, `periodic` flags, `up=` shorthands,
`role=`, `tensor style=`, `west label=`, `\tnX`, `\tn*`, `\tndots`, and
`\tnspan` — for signed kernel rows: `rows={ket,bra}` ladders with bead
operators on the pairing bonds, typed `ports=` with port labels, `boundary=`
side policy, labelled side cups, and `\tnmark` bracket and enclosure ranges.
One picture stays on the grid tier with its blocker named in the source: the
MPV-overlap ladder needs a per-row trace return that clears the two-row
selection it closes, and the kernel still drops every flat-row return one
clearance below its own row.

All six meters are unchanged: M1 stays at 140 kernel rows, M2 keeps its parser
identity, M3 gains no escape, M4 is untouched at its frozen denominator, and
no alias or overload moves. What moves is demand: three 0.7 rows lose their
last blueprint consumers a milestone before the S4 swap would have taken them.

| flag | verdict |
|---|---|
| flag:consumers:key:annotation:brace below | dies at the S4 swap with the 0.7 annotation tier: the kernel bracket mark speaks from the south by itself, and the two remaining demand-corpus consumers are the blocked MPV-overlap ladder and a fixture booked to the grid dialect's own retirement; expiry 0.9 |
| flag:consumers:key:picture:sandwich | dies at the S4 swap: the 0.7 two-row preset has no consumer left, and the kernel's own `sandwich` row is the three-row preset the sugar ledger signs, so nothing remains for the grid reading to serve; expiry 0.9 |
| flag:cooccur:picture:east label+west label | dies with the 0.7 boundary-label keys they are: the kernel tier carries no side-label row, a boundary pair is named by the mathematics beside the panel or by a port label, and the five shared invocations all ride grid-tier fixtures booked to the dialect's retirement; expiry 0.9 |

### 2026-08-07 — the MPDO and algebraic-FT chapters take the kernel

Four more blueprint chapters respell onto the kernel: the first-site
contractions, the inverse-map factorization, the algebraic foundations,
and the physical blocking. Forty constructs move — thirty-nine pictures
and the blueprint's last `\tnpic`, whose sandwich becomes a scoped
picture term — and every disposition row of the four files lands in the
preserve column, which takes the ledger from 48 preserve, 25 codemod,
128 redraw to 88, 23, and 90. The raw census trades that one command
for one environment, 169 openings and 32 commands, and still reconciles
to 201.

Every picture now states its sides. The grid tier opened all four by
default; a kernel word open at both ends says `west=open, east=open`, a
closed word says `boundary=periodic`, and a single site that carries
the boundary among sites that do not states it through typed `ports=`.
The side-by-side renders lose no leg and recover two truths the 0.7
tier had garbled: the sector-factorization sandwich drops the
mis-anchored `legs at` stroke the old renderer drew as a diagonal
across the operator row, and the transfer-operator equation now writes
the summed index on the wire its own comment always claimed for it.
The pictures shed twenty-two source lines; the eighteen `\tenkzkernel`
lines that carry the temporary opt-in go at the surface swap with
their C-switch row.

M1 stays at 140 kernel rows and 201 total, M2 at 228 parser paths, M3
at 24 metered escapes, and M4 at 25.94 — the registry, the parser, and
the benchmark corpus are untouched. The consumer census moves twice.
The bare `pill` flag falls to one blueprint consumer and takes its
verdict below. The `up at=` key loses its last one exactly as its
standing verdict said it would: the physical-blocking figure now
states its leg through `ports=`, and the key waits out the swap with
no demand-corpus consumer at all.

| flag | verdict |
|---|---|
| flag:consumers:key:object:pill | dies at S4 with the 0.7 object ledger: a kernel atom says the silhouette as the declared `skin=pill`, which is how the four migrated chapters now spell it; the one remaining blueprint consumer is the finite-separation isometry figure, which rides its own redraw row at the surface swap; expiry 0.9 |
| flag:consumers:command:tnX | dies at S4 with the 0.7 command tier: the kernel spells the gauge capsule as `skin=ring`, which is how the migrated chapters now draw every X and X^{-1}; the one remaining blueprint consumer is the finite-separation direct-sum figure at ch20 intro L109, a grid-tier picture booked to the tier's own retirement; expiry 0.9 |

### 2026-08-07 — the miscellaneous free graphs take the kernel

The eight `tenkzfree` pictures outside the PEPS chapters — the two ch13
support schematics, the ch20 direct-sum figure and its three
block-injective panels, the ch21 structure-operator recursion, and the
ch26 fixed-point decomposition — are respelled onto kernel `tenkz`
pictures and land in the preserve column of `DISPOSITIONS.md` as
`P-grid`. Their region marks carry declared species instead of the
retired slot palette, and the ch21 recursion states its compact metric
through the kernel's own `pitch=` setup key where the 0.7 spelling rode
`compact` and raw millimetre coordinates.

M3 falls from 24 to 18: the six `out=`/`in=` arc-angle escapes that rode
the retired free bodies — the two matrix-unit hooks of the ch20 panels
and the terminal trace arc of the ch21 recursion — go with them, each
replaced by a route that leaves and enters along its ends' faces or by
wires meeting at an invisible junction. M1 stays at 140 kernel rows and
201 total, M2 at 228 parser paths, and M4 at 25.94 — the registry and
the benchmark corpus are untouched. Five rows lose demand-corpus
consumers with the respelling and take their verdicts below; every
remaining consumer of the five is a ch24 free-graph figure already
booked `R-free` in the disposition ledger and awaiting its own redraw.

| flag | verdict |
|---|---|
| flag:consumers:key:connection:name | dies at S4 with the 0.7 connection ledger: the kernel wire carries its own signed `name=` row, and the lone remaining consumer is a ch24 free graph booked `R-free` for its own redraw; expiry 0.9 |
| flag:consumers:key:region:label pos | dies at S4 with the 0.7 region ledger it belongs to: `\tnregion` is tombstoned onto `\tnmark[form=enclosure]`, whose signed `label pos=` row this key's one remaining ch24 free-graph consumer takes at its redraw; expiry 0.9 |
| flag:consumers:key:region:outline | dies at S4 with the 0.7 region ledger: a kernel enclosure strokes its contour by default and `tint` adds the wash, so the outline flag owes no kernel spelling; both remaining consumers are ch24 free graphs booked `R-free`; expiry 0.9 |
| flag:cooccur:connection:in+route | confirmed merge, tombstoned by contract: `out=`/`in=` migrate to `route=arc`, which leaves and enters along its ends' faces (`LANGUAGE-1.0` §10); every surviving invocation rides a ch24 free graph awaiting its `R-free` redraw, and the pair dies with the connection tier at S4; expiry 0.9 |
| flag:cooccur:connection:out+route | confirmed merge, tombstoned by contract, exactly as `in=` above: the arc route replaces the pair and the ch24 redraws retire the invocations; expiry 0.9 |

### 2026-08-07 — the blueprint's last lattice regions leave the 0.7 tier

The ch24 PEPS wave (issue #4699, tracker #4709) respelled the chapter set's
twelve `tenkzlattice` and twenty-six `tenkzfree` pictures onto the kernel,
which empties the blueprint of `tenkzlattice` entirely and drops M3 escape
usage from 24 to 6: every removed occurrence was a raw free-graph coordinate
that is now an address.  The `\tnregion` command and its `region` key scope
lose their last authored consumers outside the frozen legacy fixtures, so
the low-consumer and shape flags below all name the same fact: the 0.7
region tier is now dead weight awaiting the S4 swap, its kernel replacement
— `\tnmark[form=enclosure]` over a selector — already carrying every
blueprint region this wave moved.

M1, M2, M5, and M6 do not move.  M4 does not move: the benchmark corpus is
untouched.

| flag | verdict |
|---|---|
| flag:cooccur:region:label pos+name | dies at the S4 swap with the 0.7 region tier it belongs to; the kernel spelling is a `\tnmark[form=enclosure]` record whose label and name are ordinary mark keys, and the blueprint's last `\tnregion` consumers were respelled in this wave; expiry 0.9 |
| flag:cooccur:region:label pos+slot | dies at the S4 swap with the 0.7 region tier; the kernel mark carries the signed `slot=` row and `label pos=` separately, and their 0.7 co-occurrence is an artifact of the six frozen fixture regions; expiry 0.9 |
| flag:cooccur:region:name+slot | dies at the S4 swap with the 0.7 region tier, for the same six frozen fixture regions; expiry 0.9 |
| flag:sugar-shaped:command:tnregion | dies at the S4 swap: `\tnregion` is the 0.7 spelling of `\tnmark[form=enclosure]`, every blueprint consumer now writes the mark, and the six remaining occurrences live in the frozen legacy fixtures the compatibility renderers still read; expiry 0.9 |
| flag:consumers:command:tnregion | dies at the S4 swap: the two remaining demand-corpus consumers are frozen legacy fixtures, and every authored region is a `\tnmark[form=enclosure]` record; expiry 0.9 |
| flag:consumers:command:tnsite | dies at the S4 swap with the `tenkzlattice` tier: its tombstone already names `\tn[at=(r,c)]`, and this wave respelled the blueprint's last `\tnsite`; expiry 0.9 |
| flag:consumers:key:connection:name | dies at the S4 swap with the 0.7 connection tier: the kernel wire carries its own signed `name=` row, and the named `\tnjoin` consumers left with the ch24 free graphs; expiry 0.9 |
| flag:consumers:key:object:label | dies at the S4 swap with the 0.7 object tier: a kernel label is the positional mathematics of the record, and the blueprint no longer writes the key; expiry 0.9 |
| flag:consumers:key:object:ring | dies at the S4 swap with the 0.7 object tier: the kernel spelling is `skin=ring`, and the last blueprint `ring` flags were respelled in this wave; expiry 0.9 |
| flag:consumers:key:region:label | dies at the S4 swap with the 0.7 region tier: a kernel enclosure takes its label positionally; expiry 0.9 |
| flag:consumers:key:region:label pos | dies at the S4 swap with the 0.7 region tier; the kernel mark carries the signed `label pos=` row; expiry 0.9 |
| flag:consumers:key:region:outline | dies at the S4 swap with the 0.7 region tier: the kernel enclosure is outline by default and `tint` opts into the fill, so the flag key has no kernel row to inherit; expiry 0.9 |
| flag:consumers:key:region:slot | dies at the S4 swap with the 0.7 region tier; the kernel mark carries the signed `slot=` row until the deferred slot-for-species exchange executes; expiry 0.9 |
| flag:cooccur:region:label+label pos | dies at the S4 swap with the 0.7 region tier, the same six frozen fixture regions as its siblings above; expiry 0.9 |
| flag:cooccur:region:label+name | dies at the S4 swap with the 0.7 region tier, for the same six frozen fixture regions; expiry 0.9 |
| flag:cooccur:region:label+slot | dies at the S4 swap with the 0.7 region tier, for the same six frozen fixture regions; expiry 0.9 |
| flag:consumers:key:setup:compact | dies at S4 with the 0.7 metric tier: the kernel names no compact profile, and a page-constrained picture states its pitch in the body as the recursion figure now does; the two remaining demand-corpus consumers are grid-tier fixtures booked to the dialect's own retirement; expiry 0.9 |
| flag:consumers:key:object:dot | dies at S4 with the 0.7 object ledger: the kernel spells the silhouette as the declared `skin=dot`, which is how the migrated chapters draw it; no demand-corpus consumer remains and the fixture uses ride the dialect's own retirement; expiry 0.9 |
| flag:consumers:key:object:box | dies at S4 with the 0.7 object ledger: the kernel spells the silhouette as the declared `skin=box`, which is how the migrated chapters draw it; no demand-corpus consumer remains and the fixture uses ride the dialect's own retirement; expiry 0.9 |
| flag:consumers:key:object:boundary | dies at S4 with the 0.7 object ledger: the kernel spells the silhouette as the declared `skin=boundary`, which is how the migrated chapters draw it; no demand-corpus consumer remains and the fixture uses ride the dialect's own retirement; expiry 0.9 |
| flag:consumers:key:connection:route | dies at S4 with the 0.7 connection tier: the kernel wire carries its own route row (registry, kernel-wire), so the grid reading serves nothing once the last grid pictures leave; the fixture uses ride the dialect's own retirement; expiry 0.9 |
| flag:consumers:environment:tenkzfree | dies at S4: the blueprint's last free-graph pictures left with this wave and the ch24 chapters, so the environment's demand-corpus consumers are gone; the front end and its fixtures are booked to the dialect retirement (FIXTURE-RETIREMENT.md); expiry 0.9 |
| flag:consumers:command:tnput | dies at S4 with the 0.7 tier that reads it: the kernel carries its own row where the concept survives, and no demand-corpus consumer remains; the fixture uses ride the dialect's own retirement; expiry 0.9 |
| flag:consumers:command:tnjoin | dies at S4 with the 0.7 tier that reads it: the kernel carries its own row where the concept survives, and no demand-corpus consumer remains; the fixture uses ride the dialect's own retirement; expiry 0.9 |

### 2026-08-08 — the last grid-tier blueprint pictures take the kernel

The six 0.7 grid pictures the earlier waves left behind — the LPDO
local contraction and its doubled-index tensor in the MPDO foundations,
the horizontal canonical form of the doubled tensor and its direct-sum
panel, the finite-separation isometry stack, and the ch26 fixed-point
panel whose right-hand side already rode the kernel — now carry
`\tenkzkernel`. `tensor style=` and the `up=`/`down=` shorthands become
typed `ports=` with the index written on its port; the `\tnfuse` wedges
become the prelude fuse shape the sugar ledger signs, spelled as
`wires=2` atoms whose split legs the frame bonds to the two rows; the
`op:none` row modifier and `legs at=` become slotted `ports=` on a
`wide=3` atom; `\tnX` becomes `skin=ring` and `\tn*` becomes the
overline in the label. The isometry stack takes the stock `skin=pill`
its disposition row demanded. One picture stays on the grid tier, as
before: the MPV-overlap ladder, blocked on a per-row trace return that
clears the two-row selection it closes.

The wave measures three kernel gaps and names them rather than hiding
them. A fuse record inside a kernel picture is refused unplaced, so the
signed `\tnfuse` sugar row has no kernel-tier reading yet and both
migrated wedges spell its expansion by hand — the LPDO panel pays three
source lines over its 0.7 spelling for exactly this reason. A `wires=`
slot span resolves only at a frame cell, so a fuse standing at a
`midway` address loses its second slot and is refused. And a wide
atom's `physical=` policy mints one centre port rather than one per
spanned cell, so a three-legged isometry face spells its three slots by
hand.

All six meters are unchanged from the ch24 wave: M1 stays at 140 kernel
rows and 201 total, M2 at 228 parser paths, M3 at 6 escapes — the new
pictures ride the kernel grammar with none — M4 at its frozen 25.94,
and no alias or overload moves. The blueprint disposition ledger moves
145 preserve, 13 codemod, 43 redraw to 151, 11, and 39 over the
constant 201. Demand moves four times and takes its verdicts below.

| flag | verdict |
|---|---|
| flag:consumers:key:object:up | dies at S4 with the 0.7 object ledger: `up=` is tombstoned onto `ports=` (`LANGUAGE-1.0` §10), the migrated pictures write the physical index on its typed port, and both remaining demand-corpus consumers are ch21 fusion-isometry figures booked `C-picture+C-policy+C-record+R-record` for their own redraw; expiry 0.9 |
| flag:consumers:key:object:down | dies at S4 with the 0.7 object ledger, exactly as `up=` above: the two remaining consumers are the same ch21 fusion-isometry figures awaiting their own redraw; expiry 0.9 |
| flag:consumers:key:setup:tensor style | dies at S4 with the 0.7 setup tier: the kernel names a silhouette per atom through the signed `skin=` row, which is how every migrated picture now spells it; the one remaining consumer is the ch21 refinement-channel picture-term figure, booked to its own redraw row; expiry 0.9 |
| flag:sugar-shaped:command:tnfuse | demoted at the language landing: a prelude-declared fuse atom (`LANGUAGE-1.0` §9); the kernel tier does not yet place a fuse record — the gap this wave measured — so the migrated wedges spell the expansion as `wires=2` atoms bonded by the frame, and all eight remaining occurrences ride the ch21 fusion-isometry figures awaiting their own redraw; expiry 0.9 |

### 2026-08-08 — the cd front end is demolished

The sentence of 2026-08-06 executes: `tenkz-cd.code.tex` is deleted, and
with it the `tenkzcd` environment, the `\tnarrow` command, and the
`maps`, `polygon=`, `radius=`, `column sep=`, `row sep=`, `from=`, and
`to=` parser rows leave the registry, each already tombstoned by
contract (`LANGUAGE-1.0` §10). The fourteen standalone fixtures that
opened the environment leave the corpus with it; every behaviour they
carried is classified in `FIXTURE-RETIREMENT.md` §3 as dying with the
dialect or covered by a named kernel or RMP case, and none is a G1 or
G2 carrier. Commutative diagrams are drawn by plain tikz-cd from now
on, which the package no longer loads: the one blueprint consumer of
tikz-cd is the preamble style in `blueprint/src/macros/diagrams.tex`,
which now loads the package itself.

Extension-gate: #4699 — the parser-leaf identity change is fourteen
removed leaves and one removed environment door, the demolition the
issue's checklist item 6.4 orders; no leaf is added.

M1 falls from 140 kernel rows and 201 total to 136 and 192: four
kernel key rows (`maps`, `polygon`, `from`, `to`), three escape rows
(`radius`, `column sep`, `row sep`), one command, and one environment
leave the ledger. M2 falls from 228 parser paths to 213. M3 stays at
24: the deleted fixtures were corpus, not demand; the metered escapes
died with #5601's respelling. M4 is untouched at 25.94, no alias or
overload moves, and the census decrease is the session's own evidence.
| flag:lonely-type:address | keep: the address grammar is the kernel's placement language itself (`at=` on every atom), lonely only because the cd dialect's arrow endpoints left with their front end; expiry 0.9 |
