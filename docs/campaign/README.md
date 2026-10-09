# Campaign boards

A campaign board is a public progress page for a formalization campaign. A
campaign is a set of issues and pull requests, possibly across several
repositories, that carry one label and hang under one tracking issue. The page
shows the headline
theorems, the proof organized into stages, the paper-gap notes in plain
language, the blocking graph of the issues, activity charts, blueprint
`\leanok` and `sorry` counts, and the full issue and pull-request tables.

The tools in `scripts/campaign_board/` are shared. Each campaign is one
directory here.

| File | Purpose |
|------|---------|
| `config.json` | What the campaign is and how to present it (fields below) |
| `gaps.json` | Plain-language summaries of the campaign's paper-gap notes |
| `intro.html` | Optional campaign-specific section shown after the heading, usually the headline theorems |
| `figures.js` | Optional stage figures: sets `window.campaignFigures` to an object of drawing functions, each filling an empty `<svg>` |
| `diagrams/` | Optional tensor-network diagrams: tenkz picture bodies `NAME.tex` and the committed `NAME.svg` compiled from them; `diagrams/inline/` holds the word-sized equations set inside sentences |

The area-law and PEPS campaign in `openai-area-law-peps-proof/` is served at
`https://sirui-lu.com/TNLean/openai-area-law-peps-proof/` and regenerated hourly by
`.github/workflows/campaign-board.yml`.

## Building a board locally

From the TNLean checkout root, with `gh` authenticated and a QICLean clone at
`../QICLean`:

```bash
python3 scripts/campaign_board/collect.py docs/campaign/openai-area-law-peps-proof /tmp/snapshot.json
python3 scripts/campaign_board/render.py docs/campaign/openai-area-law-peps-proof /tmp/snapshot.json /tmp/board
open /tmp/board/index.html
```

`scan_gaps.py docs/campaign/openai-area-law-peps-proof --since <time>` lists passages in issue
and pull-request discussions that mention gaps, counterexamples or deviation
markers. Use it to decide whether `gaps.json` needs a new entry.

## `config.json`

| Field | Meaning |
|-------|---------|
| `slug` | Directory name and URL path of the page |
| `pageTitle`, `heading`, `lede`, `description` | Page title, main heading, opening paragraph and meta description |
| `label` | GitHub label carried by the campaign's issues and pull requests |
| `since` | Date the campaign started; unlabelled pull requests in companion repositories opened since then are included when they cite a campaign issue |
| `repos` | Repositories, each with `name`, `slug`, local `checkout` path and optional `checkoutEnv` override and pull-request `prefix`; exactly one is `primary` and holds the issues. A repository with a `homepage` and `description` is listed at the top of the page and in its library section, with links to its site, blueprint, API docs and GitHub |
| `tracker` | The overall tracking issue. Its sub-issues that have sub-issues of their own become the streams |
| `streamNames` | Optional display names for streams, keyed by issue number |
| `papers` | Source papers, keyed by an id, each with a display `name` and the `stream` issue whose body holds its result table |
| `sources` | Link to the pinned sources |
| `citationPattern` | Regular expression that identifies paper-gap notes and blueprint chapters about the sources |
| `leanDirs` | Directories of the primary repository whose Lean files are listed on the page |
| `statementPR` | Optional pull request that states the headline theorems in Lean |
| `resultNames` | Display names for results whose table row gives none, keyed by source label |
| `routes` | The proof as a sequence of stages. A route has an `eyebrow`, `heading`, `intro`, the `paper` whose results it shows, and `stages`, each with a `title`, its `issues`, a `physics` paragraph, what it `delivers`, and optionally the `figure` (a key of `figures.js`) drawn beside the text with its `caption`, and a tensor-network `diagram` (a path such as `diagrams/NAME.svg`) with its `diagramCaption` |
| `glossary` | Pairs of term and definition |

A result table is any markdown table in a stream tracker body whose first two
cells name a numbered result such as `Lemma 2.1` and a backticked source label
such as `` `lem:continuity` ``. The third cell lists the work issues as
`#NNNN`. An optional name follows an em dash after the label, and an optional
fourth cell states what completion requires.

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
physical leg looks the same on the board as in the blueprint. Each
`diagrams/NAME.tex` holds one picture body. Compile them with

```bash
python3 scripts/fetch_tenkz.py
python3 scripts/campaign_board/build_diagrams.py docs/campaign/openai-area-law-peps-proof
```

which needs `xelatex` (with TikZ, `hobby` and `spath3`) and `pdftocairo`, and
commit the resulting SVGs; the hourly job only inlines them.

A sentence can carry its own diagram equation. Write `{{tn:NAME}}` in a stage's
`physics`, `delivers`, or a caption, and the equation in
`diagrams/inline/NAME.tex` is set on the line, the way Tufte sets word-sized
graphics into text. Inline sources are compiled in running mathematics; give
each picture `size=l` so the names inside its boxes are set at text size and
stay legible at word size. Prefer an inline equation to a margin diagram that
would repeat it, and keep margin diagrams for the arguments too tall for a line. tenkz audits
equations written with `=` only, so an approximate relation is set as two
pictures with `\approx` between them.

## `gaps.json`

`entries` holds one summary per paper-gap note, identified by the note's path
in `id` and its repository in `repo` (default: the primary repository):

| Field | Meaning |
|-------|---------|
| `kind` | `error` when a printed claim fails as stated; `missing-step` when the argument omits something nontrivial; `narrower` when Lean proves a restricted version for now; `convention` for the intended reading of a degenerate case |
| `status` | `open`, `resolved-pending` (resolved in an unmerged pull request) or `resolved` |
| `paper`, `result`, `title`, `issue` | Where the gap sits |
| `prs` | Pull requests by repository name |
| `claims`, `found`, `impact`, `plan` | What the paper says, what the formalization found, whether it threatens the theorem, and the next step, written for a physicist who does not read Lean |

`checked` lists results whose pull requests report that no gap was found, and
`reviewedAt` records when the summaries were last compared with the notes. A
note that cites the sources and has no entry appears on the page as awaiting a
summary.
