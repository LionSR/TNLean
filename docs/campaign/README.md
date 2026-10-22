# Campaign boards

A campaign board is a public progress page for a formalization campaign. A
campaign is a set of issues and pull requests, possibly across several
repositories, that carry one label and hang under one tracking issue. The page
shows the headline
theorems, the proof organized into stages, the paper-gap notes in plain
language, the blocking graph of the issues, activity charts, blueprint
`\leanok` and `sorry` counts, and the full issue and pull-request tables.

The page is written for a reader who knows neither paper. It opens with a
one-line status (main theorems proved, work issues closed, open paper errors),
then gives the theorems, the proof stages and the open gaps. Each stage's record
of Lean work (paper results, merged pull requests, issues) is folded under one
summary line, and resolved gaps are folded after the open ones. The maintainers'
material (next actions, blocking map, charts, tables and file list) is folded
at the end; a link to anything inside a folded part opens it.

The tools in `scripts/campaign_board/` are shared. Each campaign is one
directory here.

| File | Purpose |
|------|---------|
| `config.json` | What the campaign is and how to present it (fields below) |
| `gaps.json` | Plain-language summaries of the campaign's paper-gap notes |
| `intro.html` | Optional campaign-specific section shown after the heading, usually the headline theorems |
| `references.json` | Optional bibliography of the works that `{{cite:Key}}` tokens in the texts cite (fields below) |
| `figures.js` | Optional stage figures: sets `window.campaignFigures` to an object of drawing functions, each filling an empty `<svg>`; only the drawing functions may use browser APIs, since the render evaluates the file outside a page |
| `diagrams/` | Optional tensor-network diagrams: tenkz picture bodies `NAME.tex` and the committed `NAME.svg` compiled from them; `diagrams/inline/` holds the equations displayed inside sentences |

Three campaigns are shown as tabs of one site. The first two share the label
`openai-math`; the third carries the source label `0705.2024`:

| Directory | Campaign | Tracker |
|-----------|----------|---------|
| `openai-area-law-peps-proof/` | Two-dimensional area law and polynomial PEPS approximation | #8733 |
| `one-dimensional-area-law-mps/` | One-dimensional area law and matrix product state approximation, proved on the chain from the repository note `docs/notes/one_dimensional_note` | #9547 |
| `hastings-area-law/` | Hastings' proof of the one-dimensional area law, arXiv:0705.2024 | #9829 |

Each is served at `https://sirui-lu.com/TNLean/<slug>/`. The hourly workflow
`.github/workflows/campaign-board.yml` collects and renders every directory here
that has a `config.json`, so a new campaign needs no workflow change. The
two-dimensional campaign excludes the tracker #9547 and everything below it
(`excludeTrackers`), and the one-dimensional campaigns are each restricted to
their tracker (`scope: "tracker"`).

## Building a board locally

From the TNLean checkout root, with `gh` authenticated and a QICLean clone at
`../QICLean`:

```bash
python3 scripts/campaign_board/collect.py docs/campaign/openai-area-law-peps-proof /tmp/snapshot.json
python3 scripts/campaign_board/render.py docs/campaign/openai-area-law-peps-proof /tmp/snapshot.json /tmp/board/openai-area-law-peps-proof
open /tmp/board/openai-area-law-peps-proof/index.html
```

Render each campaign into a sibling directory named by its slug, as the site
does, so that the tab links between them resolve. Setting `PREVIOUS_SNAPSHOT`
to a published `data.json` reuses its pull-request file statistics.

`scan_gaps.py docs/campaign/openai-area-law-peps-proof --since <time>` lists passages in issue
and pull-request discussions that mention gaps, counterexamples or deviation
markers. Use it to decide whether `gaps.json` needs a new entry.

## `config.json`

| Field | Meaning |
|-------|---------|
| `slug` | Directory name and URL path of the page |
| `pageTitle`, `heading`, `lede`, `description` | Page title, main heading, opening paragraph and meta description |
| `label` | GitHub label carried by the campaign's issues and pull requests |
| `since` | Date the campaign started; unlabelled pull requests in any of the repositories opened since then are included when they cite a campaign issue |
| `repos` | Repositories, each with `name`, `slug`, local `checkout` path and optional `checkoutEnv` override and pull-request `prefix`; exactly one is `primary` and holds the issues. A repository with a `homepage` and `description` is listed at the top of the page and in its library section, with links to its site, blueprint, API docs and GitHub |
| `tabs` | Optional list of sibling campaigns, each with `slug` and `label`, shown as a tab bar at the top of the page; the current campaign's tab is marked, and the others link to `../<slug>/`. List the same tabs in every sibling |
| `tracker` | The overall tracking issue. Its sub-issues that have sub-issues of their own become the streams |
| `streams` | Optional list of stream issues, replacing the rule above; it may name the tracker itself when its sub-issues are the work issues |
| `scope` | Optional; `tracker` keeps only the tracker and the issues below it, and only the labelled pull requests that cite one of them or are listed in `includePRs` |
| `excludeTrackers` | Optional trackers of other campaigns with the same label; they, the issues below them, and the labelled pull requests citing only those issues are left out |
| `excludePathPattern` | Optional regular expression; paper-gap notes and blueprint chapters whose path matches belong to another campaign and are left out even when they match `citationPattern` |
| `includePRs` | Optional pull requests to include, by repository name, such as the one that proved results before the campaign's issues existed |
| `excludePRs` | Optional pull requests to leave out, by repository name, such as one that carries the label but belongs to a sibling campaign |
| `streamNames` | Optional display names for streams, keyed by issue number |
| `papers` | Source papers, keyed by an id, each with a display `name` and the `stream` issue whose body holds its result table |
| `sources` | Link to the pinned sources |
| `citationPattern` | Regular expression that identifies paper-gap notes and blueprint chapters about the sources |
| `leanDirs` | Directories of the primary repository whose Lean files are listed on the page |
| `statementPR` | Optional pull request that states the headline theorems in Lean |
| `resultNames` | Display names for results whose table row gives none, keyed by source label |
| `routes` | The proof as a sequence of stages. A route has an `eyebrow`, `heading`, `intro`, the `paper` whose results it shows, and `stages`, each with a `title`, its `issues`, a `physics` paragraph, what it `delivers`, and optionally the `figure` (a key of `figures.js`) drawn beside the text with its `caption`, and `diagrams`, a list of tensor-network diagrams beside the text, each with `src` (a path such as `diagrams/NAME.svg`), `caption` and optional `alt`. A stage takes the results that share an issue with it, and, when it lists `results` (source labels), only those; each result row is shown once, at the first stage that takes it |
| `glossary` | Pairs of term and definition |

A result table is any markdown table in a stream tracker body whose first two
cells name a numbered result such as `Lemma 2.1` (or a lettered one such as
`Theorem A`) and a backticked source label such as `` `lem:continuity` ``. The
third cell lists the work issues as `#NNNN`. An optional name follows an em dash
after the label, and an optional fourth cell states what completion requires.
Two rows may share a label, for a result and a strengthening of it; their names
tell them apart.

A result proved before its campaign had issues may cite the merged pull request
of the primary repository that proved it in place of an issue, provided the
pull request is collected (labelled, or listed in `includePRs`). A merged pull
request counts as closed work, an open one as in review or draft. The same
holds for the `issues` of a stage and for the `data-target` of a headline card
in `intro.html`.

## Stage figures

A stage figure is a small schematic placed beside the stage text, in the
manner of Tufte's margin figures: hairline range frames instead of boxed axes,
labels next to what they name instead of a legend, small multiples for steps,
and colour only where it carries meaning. Style marks with the `.sfig` classes
in `board.css` (`h`, `g`, `k`, `a`, `c` for strokes; `fa`, `fl`, `fs`, `fk`,
`fm`, `fc` for fills; `t`, `m`, `big`, `on`, `halo` for text) so the figures
follow the light and dark themes. Curves show shapes, not data; the caption
says what is schematic.

Tensor-network diagrams are written in [tenkz](https://github.com/LionSR/tenkz),
the package the blueprint draws its diagrams with, so a tensor, bond or
physical leg looks the same on the board as in the blueprint. An argument that
is a sequence of operations on a few registers (a time evolution, a product of
contractions, a party's private maps) is written as a
[quantikz](https://ctan.org/pkg/quantikz) circuit instead, read left to right;
the build loads both packages. Each
`diagrams/NAME.tex` holds one picture body. Compile them with

```bash
python3 scripts/fetch_tenkz.py
python3 scripts/campaign_board/build_diagrams.py docs/campaign/openai-area-law-peps-proof
```

which needs `xelatex` (with TikZ, `hobby`, `spath3` and `quantikz`) and `pdftocairo`, and
commit the resulting SVGs; the hourly job only inlines them.

A sentence can carry its own diagram equation. Write `{{tn:NAME}}` in a stage's
`physics`, `delivers`, a caption or a gap field, and the equation in
`diagrams/inline/NAME.tex` is displayed on its own line inside that sentence,
as a displayed formula is in a paper; punctuation written right after the token
stays on the equation's line. Lead into the equation with the sentence and
define its symbols there. Inline sources are compiled in running mathematics;
give each picture `size=l` so the names inside its boxes are set at text size. Give every inline source, and every diagram embedded
in `intro.html` through a `{{DIAGRAM:path}}` slot, a first line `% alt: …`
stating the equation in words; it becomes the image's alternative text. Prefer an inline equation to a margin diagram that
would repeat it, and keep margin diagrams for the arguments too large to sit in the text. tenkz audits
equations written with `=` only, so an approximate relation is set as two
pictures with `\approx` between them.

## Citations and `references.json`

A stage or gap text cites earlier work with `{{cite:Key}}` or
`{{cite:Key1,Key2}}` (no spaces), written straight after the phrase that names
the idea and before any punctuation, in a route introduction, a stage's
`physics` or `delivers`, a diagram caption, the caption of a stage figure that
`figures.js` draws, or a gap entry's prose fields. Citations are numbered in reading order (the stages,
then the gap entries) and link to the page's reference list, where each entry
links back to the stages and gaps that cite it. Each key names an entry of
`references.json`:

| Field | Meaning |
|-------|---------|
| `authors` | Short author list, initials first, `et al.` beyond four authors |
| `title`, `year`, `venue` | The work; `venue` is optional |
| `url` | The arXiv abstract page, else the DOI |
| `manuscript` | Whether either manuscript cites the work; `false` marks an earlier source for an idea the manuscripts use without a citation |

Cite only works whose bibliographic data have been checked against arXiv or
the DOI record, and only for an idea they originate or that the proof uses as
stated. A malformed token, a token in any other field, a token naming a
missing key, a cited entry without `authors`, `title`, `year` and `url`, and
a stage figure that `figures.js` does not draw each stop the render. To read
the drawings, `render.py` evaluates `figures.js` with Node, which must be on
the path.

## `gaps.json`

`entries` holds one summary per paper-gap note, identified by the note's path
in `id` and its repository in `repo` (default: the primary repository):

| Field | Meaning |
|-------|---------|
| `kind` | `error` when a printed claim fails as stated; `missing-step` when the argument omits something nontrivial; `narrower` when Lean proves a restricted version for now; `local-correction` when a constant, a typo, or a small step is adjusted and the paper's argument stands; `convention` for the intended reading of a degenerate case |
| `status` | `open`, `resolved-pending` (resolved in an unmerged pull request) or `resolved` |
| `paper`, `result`, `title`, `issue` | Where the gap sits |
| `stage` | Optional stage the entry belongs to, as `routeId:n` with `n` counted from 1; by default the first stage listing `issue` |
| `prs` | Pull requests by repository name |
| `summary` | One sentence a hurried reader needs: is anything wrong with the paper, and how far the Lean work has got |
| `context` | One or two sentences on what the result does in the proof, defining every object it names |
| `claims`, `found`, `impact`, `plan` | What the paper says, what the formalization found, whether it threatens the theorem, and the next step, written for a physicist who does not read Lean |

Write every entry for a physicist who has read neither the papers nor the rest of
the page: name each cited result in words, define each object at first use, and
keep pull-request history out of the prose, since the links appear beside it.

An open entry of kind other than `convention` whose `result` begins with a paper result, as `Lemma 8.2, routing ...`, keeps that result from counting as proved even when every issue of the result is closed.

`checked` lists results whose pull requests report that no gap was found, and
`reviewedAt` records when the summaries were last compared with the notes. A
note that cites the sources and has no entry appears on the page as awaiting a
summary.
