# Blueprint verification: fixed chronological sources

Source revision: `6246647741ce41a55a3897329336055330dd7e6f`.
Pinned QICLean source: `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.
Chapter SHA256: `9923cb59ba6180f33594f068b1135f7fbd34e3b2ed2fc6e58310bb4bd5564085`.

Independent mathematical review covers all nineteen declarations and the new
chapter. The fixed ordered source positions retain their original occurrences
and Euclidean dimensions. The source vectors are precisely the original gate
vectors at the selected local labels, independently of other gate labels. The
actual-word selective factorization retains every crossing source as free and
chooses both contractions before arbitrary vectors are supplied at the free
positions. No finite global party set or nonempty monomial set is assumed.
The mathematical review is recorded separately in `mathematical-review.md`.

All nineteen public declarations occur exactly once in the chapter, with no
additional declaration tags. Formatting, chktex and reader-facing prose checks
pass. Full source synchronization finds 20,286 blueprint references, 20,292
unique reference names and 40,237 Lean declarations. The dependency graph has
7,425 entries and 18,479 edges, with no duplicate labels or directed cycles.
The snapshot contains only the three new Lean modules from this contribution;
QIC-changing source-contraction and Schmidt prototypes are excluded.

The focused PDF has thirty pages. The new section occupies physical pages
27–29; all three were rendered and visually inspected. The formulas, labels,
indices, references and margins are legible and unclipped. The final TeX pass
has no unresolved references or new overfull lines. Only the inherited 0.99 pt
line in the common-source chapter remains. `final-tex.log` records that final
pass separately from the multi-pass build log.

Focused web generation passes without warnings or errors. Browser checks pass
on four pages with 1,697 typeset expressions at desktop and mobile widths.
The exact commands, output hashes, source synchronization and graph records
identify the inspected outputs.

Committed source comparison: 3534 files byte-equal to the source revision.
The focused web entry point is the only replacement of a committed mathematical
render entry point; focused.tex and content-focused.tex are disposable additions.

This verification uses an isolated source copy and changes no Lake or dependency
cache. It is source synchronization and focused rendering, not a local full-root
`leanblueprint checkdecls` run. The separate strict compilation and importing
axiom audit cover the nineteen declarations in the three Lean modules.
