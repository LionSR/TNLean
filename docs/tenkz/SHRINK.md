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

Classification of all 95 key rows: **75 kernel · 5 sugar · 9 escape ·
6 alias**. Sugar expansions follow the 0.6 alias table (`sandwich`,
`physical=`, `boundary=`, `compact`, `inline`). Escape rows are the raw
lengths, angles, and dimension pairs (`label shift`, `out`, `in`,
`col/row/sheet vector`, `plane rise/slant`, `radius`). Commands and
environments carry no registry status field; their ledger lives in this
ledger's tables and in the baseline JSON. Ceilings are set at these
actuals; the ratchet does the aspiring.

Baseline meters: M1 {kernel 75, sugar 5, escape 9, alias 6, commands 18,
environments 5} · M2 145 · M3 297 · M4 15.14 · M5 {7 aliases (six key,
one value), 0 missing sunsets} · M6 {3 multi-typed names, 2 union types,
5 shared enum words}.

M3's 297 escape occurrences are dominated by `out=`/`in=` in the free-graph
benchmark cases — the measured cost of hand-routed arcs, burned down by the
strings landing (#4701, #4705). M6's baseline names the overloads the 1.0
kernel deletes; it must never rise on the way there.

### Verdicts on the 55 baseline flags

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
| flag:consumers:key:annotation:brace below | folds into mark form `brace-below` at the language landing; expiry 0.9 |
| flag:consumers:key:annotation:label pos | moves unchanged to the mark record at the language landing; re-measure at 0.9 |
| flag:consumers:key:atom-declaration:skin | keep-because: rides `\tndeclareatom`, same exclusion; expiry 1.0 |
| flag:consumers:key:connection:distinguished | keep-because: two consumers today, torus redraws add more (#4702); re-measure at 0.9 |
| flag:consumers:key:connection:fused | respelled `weight=double` at the language landing; expiry 0.9 |
| flag:consumers:key:connection:none | dies at the language landing: omit the wire record, or use atom `void=sealed`; expiry 0.9 |
| flag:consumers:key:connection:style | dies with the lattice edge-style pass-through at S3; expiry 0.9 |
| flag:consumers:key:object:combined | folds into the ports grammar at the language landing; expiry 0.9 |
| flag:consumers:key:object:east at | folds into the ports grammar; expiry 0.9 |
| flag:consumers:key:object:west at | folds into the ports grammar; expiry 0.9 |
| flag:consumers:key:object:name | keep-because: addressing becomes load-bearing for every S2+ landing (wires, marks, groups); re-measure at 0.9 |
| flag:consumers:key:object:no legs | folds into the skin and typed-port grammar at the language landing; expiry 0.9 |
| flag:consumers:key:object:removed | becomes atom `void=sealed` at the language landing; expiry 0.9 |
| flag:consumers:key:object:span | folds into `ports=` and `wires=` at the language landing; expiry 0.9 |
| flag:consumers:key:object:species | keep-because: semantic species is a kernel atom field; role consumers move here at the language landing; re-measure at 0.9 |
| flag:consumers:key:object:tree style | dies with the cd dialect at S4; expiry 0.9 |
| flag:consumers:key:picture:align | keep-because: the only math-axis control until `tenkzeq` lands (#4703); expiry 0.9 |
| flag:consumers:key:picture:bond dir | tombstoned at S4 in favour of wire `dir=`; expiry 0.9 |
| flag:consumers:key:picture:layer sep | folds into the metric/size classes at the equation landing; expiry 0.9 |
| flag:consumers:key:picture:north | keep-because: the four side policies are one kernel concept and north is required by two-dimensional frames; re-measure at 0.9 |
| flag:consumers:key:picture:open | keep-because: explicit open cell sets are the kernel counterpart of `trace=`; S2 redraws add consumers; re-measure at 0.9 |
| flag:consumers:key:picture:pairing | folds into declared skin pairings and wires at the language landing; expiry 0.9 |
| flag:consumers:key:picture:plane lean | folds into `frame=` subkeys at S3; expiry 0.9 |
| flag:consumers:key:picture:polygon | dies with the cd dialect at S4; expiry 0.9 |
| flag:consumers:key:picture:sheet sep | folds into `frame=` subkeys at S3; expiry 0.9 |
| flag:consumers:key:picture:sheets | keep-because: the 2+1D lattice mechanism; condensation/czx redraws consume it (#4704); re-measure at 0.9 |
| flag:consumers:key:picture:site | dies with the lattice dialect at S3; frame population creates ordinary atoms; expiry 0.9 |
| flag:consumers:key:picture:south | keep-because: the four side policies are one kernel concept and south is required by two-dimensional frames; re-measure at 0.9 |
| flag:consumers:key:picture:trace style | default flips to the cap idiom at S2 and the key dies with it; expiry 0.9 |
| flag:consumers:key:region:group | folds into address sets at the language landing; expiry 0.9 |
| flag:consumers:key:region:name | keep-because: same addressing argument as object:name; re-measure at 0.9 |
| flag:consumers:key:setup:compact | dies at the equation landing (math-style sensing and `size=`, #4703); expiry 0.9 |
| flag:consumers:key:setup:inline | dies at the equation landing (math-style sensing, #4703); expiry 0.9 |
| flag:consumers:key:setup:pitch | keep-because: the metric anchor is set in preambles, excluded from demand counting by design; expiry 1.0 |
| flag:consumers:key:setup:species | moves to `\tndeclare{species}` at the language landing; expiry 0.9 |
| flag:consumers:key:setup:tensor style | becomes atom `skin=` at the language landing; expiry 0.9 |

Merge candidates and lonely types. The detector confirms the compression
review from the outside: the angle pair and the one-off types are the 0.7
grammar's own testimony against itself.

| flag | verdict |
|---|---|
| flag:cooccur:connection:in+out | confirmed merge: `out=`/`in=` are one concept (a hand-routed arc) and both die at S4 when declared routes land; the 38 shared consumers are the redraw queue (#4705) |
| flag:lonely-type:cell-set | keep: the cell-set algebra is kernel and gains consumers as `open=` spreads; re-measure at 0.9 |
| flag:lonely-type:cell-set\|physical | union type dies at the language landing (M6); expiry 0.9 |
| flag:lonely-type:frame-enum | becomes the frame-spec type at the language landing; expiry 0.9 |
| flag:lonely-type:math-and-range | dies with the B10 bond-label keyval at the language landing; expiry 0.9 |
| flag:lonely-type:positive-integer\|role-list | union type dies at the language landing (M6); expiry 0.9 |
| flag:lonely-type:row | keep: `align=` holds it until tenkzeq; expiry 0.9 |
| flag:lonely-type:row-list | keep: `rows=` is kernel and audit-load-bearing; permanent |
| flag:lonely-type:style-name | dies with the lattice edge-style pass-through at S3; expiry 0.9 |
| flag:lonely-type:typed-port-list | keep: ports are the kernel's typing mechanism; permanent |

Sugar-shaped commands and sunsets.

| flag | verdict |
|---|---|
| flag:sugar-shaped:command:tnX | confirmed: `\tnX` is `\tn[ring]` (0.6 alias table); demoted to sugar at the language landing; expiry 0.9 |
| flag:sugar-shaped:command:tnfuse | confirmed: declared fuse atom (see the consumers verdict above); expiry 0.9 |
| flag:sunset:picture:periodic | executes at the 1.0 freeze with the alias sweep; until then reads old documents |
| flag:sunset:picture:chain axis | executes at the 1.0 freeze with the alias sweep |
| flag:sunset:object:legs at | executes at the 1.0 freeze with the alias sweep |
| flag:sunset:object:rows | executes at the 1.0 freeze with the alias sweep |
| flag:sunset:picture:boundary legs | executes at the 1.0 freeze with the alias sweep |
| flag:sunset:region:label at | executes at the 1.0 freeze with the alias sweep |

Agenda handed to the 0.8 session: the S2/S3/S4 deaths listed above are
verified against these flag ids; any survivor re-raises automatically.
