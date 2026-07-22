# Hacking on tenkz

<!-- The operational knowledge a new contributor (human or agent) needs
     before touching tex/tenkz. The design rationale lives in DESIGN.md;
     this file is how not to lose an afternoon. -->

## Canonical invocations

Compile any test or example standalone, from its own directory:

```
timeout 120 env TEXINPUTS="<repo>/tex/tenkz//:" \
  xelatex -interaction=nonstopmode -halt-on-error <file>.tex
```

ALWAYS keep the timeout: expl3 loops on expanded `\q_no_value` (see below)
run forever, and a hung xelatex looks exactly like a slow one. The manual
takes `timeout 150` and two passes, from `docs/tenkz/`:

```
cd docs/tenkz && timeout 150 env TEXINPUTS="../../tex/tenkz//:" \
  xelatex -interaction=nonstopmode -halt-on-error manual2.tex
```

Render for visual review (exit codes do not review figures — eyes do):

```
pdftocairo -png -r 200 -singlefile <file>.pdf <file>
```

For repository-wide review, `scripts/tenkz_corpus.sh --render` compiles and
audits the adopted corpus before producing a complete 200-dpi PNG baseline.
The before/after checksum and visual-review discipline is specified in
`tests/tenkz/README.md`.

Audit the event stream after a compile: `scripts/tenkz_audit.py` over the
produced `.tnlog`. `scripts/tenkz_lint.py` checks source conventions.
The asymmetric-port regression is `python3 scripts/test_tenkz_face_ports.py`;
it checks face arities and contraction multiplicities, not only compilation.

## expl3 and pgf pitfalls that have each shipped a bug here

1. **Never expand `\q_no_value`.** A failed `\prop_get` leaves it in the
   output token list and TeX loops forever. Use `\tenkz_get:NeN` (the
   house accessor in tenkz-grid) or TF-conditional forms.
2. **Integer factors sit RIGHT of `*` in `\dimexpr`**, or use
   `\dim_eval`. And never write `0.5\tenkz@dim{...}` in a pgfkeys VALUE:
   pgf's dimension parser detaches the leading factor from the `\dimexpr`
   and misreads it (this drew lens-shaped capsules once). Name the
   derived ratio in the metric block instead (`wireglyphcap`).
3. **`##1` doubling** inside `\int_step_inline:nnn` bodies within
   `\cs_new_protected`.
4. **Registers are not numbers in prop keys.** Keying a prop with an
   unexpanded int register token silently never matches; normalize with
   `\int_eval:n` first (this disabled label clearance for multi-row
   racetracks once).
5. **Catcode-12 colons.** Document input has catcode-12 `:`, expl3 code
   catcode-11. Str-normalize (`\tl_to_str:n`) before delimited parsing of
   user input (`rows=`, `ports=`), then use `\str_if_in:` etc. —
   `\tl_if_in:` on str-normalized material fails silently.
6. **`\use:e` passes `#` literally** (no doubling) — relevant when
   assembling node option lists.
7. **pgfkeys splits at literal commas only** and truncates an unbraced
   value at a second `=`. Brace any label value that may contain commas
   or `=` (documented at the `trace=` key).
8. **`\iow` writes need explicit `\int_use`** — event lines with bare
   registers write register tokens, not numbers.
9. **Picture ids nest.** `\tenkz@pictureuid` is global, `\tenkz@pictureid`
   group-local; a nested `\tnpic` must not clobber its parent's id.

## The metric doctrine, operationally

One 11mm pitch; every distance is a named `\tenkz@r@*` ratio in
tenkz-core's metric block with a motivation comment. Two constants matter
for clearance work: the **silhouette** (measured ink extent — see
`\tenkz_silhouette:nnnnN` in tenkz-grid and DESIGN.md "The silhouette")
and **daylight** (`\tenkz@r@daylight`, the one separation gap). Never add
a clearance constant that predicts what another pass draws: measure via
the silhouette, separate via daylight.

## Faithfulness discipline for figures

Every figure source states its formula and the ink-to-index
correspondence in `%` comments. Both sides of a pictured equation carry
the same boundary signature (the `.tnlog` `boundary|...` line). No open
legs = a scalar; a map keeps its input/output legs open. The applied
channel is `[sandwich, east={cup=$X$}]` — a west cup feeds the ADJOINT.
When reproducing a paper figure, reproduce its mathematics in house
style; never pixel-mimic, and never draw what the source does not assert.

## Test corpus

The in-repo acceptance set lives in `tex/tenkz/examples/`. The adopted
extended regression corpus lives in `tests/tenkz/`; run
`scripts/tenkz_corpus.sh` for compile-and-audit coverage and add `--render` for
the repository-wide visual baseline. Every package change still requires the
examples and manual to compile and renders of anything touched to be viewed.
