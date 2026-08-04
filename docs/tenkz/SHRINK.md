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
