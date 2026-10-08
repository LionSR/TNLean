# PR #8824 blueprint review repair

The focused PDF and static HTML checks pass for source commit
`ef1be531bdf3ecb8d5fc5f1215f39c5b0de189c0`, relative to
`7c491510e165d44395b657797ca420f08bb23067`.
The [verification record](verification.json) binds the source, tools, artifacts,
review threads, and check results by SHA256. This supplements the existing
evidence; it does not replace or reclassify earlier executions.

## Four requested changes

- The uniform-width theorem's `thm:peps_reset_polylog_width` dependency is
  immediately after `\leanok` in its proof.
- The corollary's `thm:peps_angular_reset_uniform_width` dependency is
  immediately after `\leanok` in its proof.
- The theorem title is **Uniform width at every scale**.
- The conclusion says **every annular layer**.

[checks.py](checks.py) reconstructs exactly these edits from the parent source
and compares the complete resulting leaf byte-for-byte. No mathematical text,
formula, hypothesis, quantifier order, declaration link, or checked marker
changes. The four production Lean declarations are unchanged from the parent.
The scalar estimate remains conditional on the analytic width upper bound;
physical reset, geometry, entropy, and annular induction remain separate.

## Render checks

All five final PDF pages were physically inspected at 120 dpi. The new theorem
title, formulas, statement/proof badges, and annular-layer sentence are legible
and within the margins. The focused wrapper retains its title, contents, and
empty bibliography pages.

The checks cover four declaration links in each of PDF and HTML, seven source
labels, three equation anchors, six HTML pages, and 44 static internal links.
There are no final layout errors, missing anchors, duplicate HTML IDs, or
out-of-page PDF link rectangles. Both document and chapter dependency graphs
contain the intended two solid proof edges and no dashed statement edges.
The emitted DOT was also rendered independently with Graphviz and inspected;
this is not a browser-interaction check.

## Reproduction and limits

The isolated local fixture is `8824-angular-reset-width-review-focused` beside
the checkout. It reuses the earlier focused chapter wrapper and graph
configuration, with current source support files copied from the frozen
revision. Generated PDF, HTML, PNG, and detailed logs remain outside Git.
The earlier fixture's 12 recorded artifacts still match their prior hashes.

With the existing `glm23-blueprint-env.sh` loaded, the recorded build commands
use `latexmk -xelatex`, copy `print.bbl` to `web.bbl`, and run
`plastex -c plastex.cfg web.tex`. After rendering, run:

```sh
python3 docs/provenance/evidence/8766-angular-reset-width/review-repair/checks.py \
  /path/to/repository /path/to/8824-angular-reset-width-review-focused
```

The existing texra-blueprint 0.3.8 environment was used without downloads.
This is focused rendering, not a full-book build. No live browser/MathJax
execution, remote documentation deployment check, Lean/Lake build, or axiom
audit was run by the render reviewer. Compilation and publication are separate
checks owned by the parent task. Nonfatal environment warnings and exact
artifact hashes are recorded in `verification.json`.

Public source checkpoint: `c3e93223e69ea89bc06ea5305c3b8d15a60c8adc`, whose tree `ac9559f8` equals the frozen local source. The checker defaults to this public commit; `SOURCE_REVISION` may override it. Original execution records remain historical.
