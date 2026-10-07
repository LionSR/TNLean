# Party factorization blueprint verification

The new fragment and the content router were checked at source revision `7edadbfe8cf40ee520349a3f7068e8a48914c2f3`. Their exact SHA256 hashes are in `source-sha256.json`; both matched the live source after verification. The only change made to the worktree by this verification was the authorized latexindent formatting of `ch24_peps_party_factorization.tex`.

All rendering, generated declaration lists, and temporary Git metadata are confined to this disposable directory. The TNLean and pinned QICLean sources were read through read-only-use symlinks. No Lake command or dependency-cache mutation was performed.

## Results

- All 61 public declarations in the seven-module manifest occur exactly once in the new fragment (`tag-coverage.json`).
- Full source synchronization passed: 20,065 blueprint references, no missing declarations, and no duplicate declaration tags (`sync.json.gz`, `sync.log.gz`). The complete source-derived declaration list is preserved as `full-lean-decls.txt.gz`; the focused web renderer subsequently produces its own smaller declaration list.
- Static analysis of the full blueprint found 7,346 theorem-like nodes and 18,298 dependency edges, with no repeated node labels or directed cycles (`dependency-graph.json.gz`).
- The changed-fragment reader-facing prose check, chktex, and the pinned latexindent comparison all passed.
- Focused PDF rendering succeeded, producing 11 pages. Its final LaTeX pass has no warnings, unresolved references, or overfull boxes. Pages 8–10, containing the complete new section, were inspected visually; equations, text, and declaration links are legible and unclipped.
- Web rendering succeeded without warnings. The project's browser checks passed on all four focused pages at the configured desktop and mobile widths, typesetting 556 expressions (`web-reader-check.log`).
- Mathematical comparison with the cited source and all seven modules is recorded in `faithfulness.md`. No source-faithfulness gap was found in the collection of local maps by party. Common source spaces across monomials and unused-pair padding remain separate results.

## Reproduction

The exact commands, working directories, return codes, and elapsed times of the final style, source-synchronization, PDF, bibliography, and web runs are in `commands.json`. The driver is `/tmp/tnlean-party-blueprint-verify.py`.

The rendering environment used `leanblueprint` and `texra-blueprint` from `/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin`, with that directory first on `PATH`. The tenkz TeX files were copied from the verified pinned checkout at revision `08a6493f3605dcf2ca5b512823ccb2698dfc027b`. `TEXINPUTS` points to this disposable directory's tenkz files. The browser command was:

```text
PYTHONPATH=/Users/siruilu/.local/share/uv/tools/texra-blueprint/lib/python3.14/site-packages uv run --no-project --python /opt/homebrew/opt/python@3.14/bin/python3.14 --with playwright python /private/tmp/tnlean-party-blueprint-0_a7c7q8/scoped_web_check.py
```

The focused router includes the unchanged pair-effect and source-preparation fragments followed by the new party-factorization fragment. It uses the project's print preamble, web entry point, and shared plasTeX plugin. The browser driver changes only the test's full-volume page list to the actual focused page list.

This is a blueprint source and rendering check. It is not a local Lake build or the full `leanblueprint checkdecls` command, which requires the complete compiled root library. The independent exact-source imported-module Lean audit supplies the compiled checks of all 61 new declarations at the same revision: `/tmp/tnlean-party-factorization/final-verification-20261007/`. All seven modules passed package options with warnings treated as errors; all 61 declarations use only the standard logical axioms. See its `build-commands.json`, `audit-command.json`, and `axiom-dependencies.json`.

Raw PDF and web logs are preserved as `pdf.log.gz` and `web.log.gz`.
