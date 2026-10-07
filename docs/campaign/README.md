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

The area-law and PEPS campaign in `openai-proof/` is served at
`https://sirui-lu.com/TNLean/openai-proof/` and regenerated hourly by
`.github/workflows/campaign-board.yml`.

## Building a board locally

From the TNLean checkout root, with `gh` authenticated and a QICLean clone at
`../QICLean`:

```bash
python3 scripts/campaign_board/collect.py docs/campaign/openai-proof /tmp/snapshot.json
python3 scripts/campaign_board/render.py docs/campaign/openai-proof /tmp/snapshot.json /tmp/board
open /tmp/board/index.html
```

`scan_gaps.py docs/campaign/openai-proof --since <time>` lists passages in issue
and pull-request discussions that mention gaps, counterexamples or deviation
markers. Use it to decide whether `gaps.json` needs a new entry.

## `config.json`

| Field | Meaning |
|-------|---------|
| `slug` | Directory name and URL path of the page |
| `pageTitle`, `heading`, `lede`, `description` | Page title, main heading, opening paragraph and meta description |
| `label` | GitHub label carried by the campaign's issues and pull requests |
| `since` | Date the campaign started; unlabelled pull requests in companion repositories opened since then are included when they cite a campaign issue |
| `repos` | Repositories, each with `name`, `slug`, local `checkout` path and optional `checkoutEnv` override and pull-request `prefix`; exactly one is `primary` and holds the issues |
| `tracker` | The overall tracking issue. Its sub-issues that have sub-issues of their own become the streams |
| `streamNames` | Optional display names for streams, keyed by issue number |
| `papers` | Source papers, keyed by an id, each with a display `name` and the `stream` issue whose body holds its result table |
| `sources` | Link to the pinned sources |
| `citationPattern` | Regular expression that identifies paper-gap notes and blueprint chapters about the sources |
| `leanDirs` | Directories of the primary repository whose Lean files are listed on the page |
| `statementPR` | Optional pull request that states the headline theorems in Lean |
| `resultNames` | Display names for results whose table row gives none, keyed by source label |
| `routes` | The proof as a sequence of stages. A route has an `eyebrow`, `heading`, `intro`, the `paper` whose results it shows, and `stages`, each with a `title`, its `issues`, a `physics` paragraph and what it `delivers` |
| `glossary` | Pairs of term and definition |

A result table is any markdown table in a stream tracker body whose first two
cells name a numbered result such as `Lemma 2.1` and a backticked source label
such as `` `lem:continuity` ``. The third cell lists the work issues as
`#NNNN`. An optional name follows an em dash after the label, and an optional
fourth cell states what completion requires.

## `gaps.json`

`entries` holds one summary per paper-gap note, keyed by the note's path in
`id`:

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
