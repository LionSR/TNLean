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
| value types | 24 | 21 | **−3** (5 out, 2 in) |
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
the selector and the route's side-of-a-selection family arrive. The
mathematics list is a departure the notes missed — its only two consumers
were the two page-relative atom keys, and it leaves with them.

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
