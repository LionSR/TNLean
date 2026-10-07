# Reciprocal opponents of actual elementary sides

All three new declarations have passed exact-source canonical verification
and independent mathematical review. Every parent record and historical
evidence file remains preserved.

## Mathematical scope

The noncomputable choice assigns the unique opposing identifier to
an elementary segment of an actual reference fine cell. The assumptions are
a common origin and finite endpoint set, width C ≥ 2, reference index
k ≥ 50,000,000, lower index k₀ ≤ k and actual reference membership. The
dummy neighborhood is one identifier; an actual fine-cell identifier carries
its layer and signed cell index. The lower index k₀ need not be late.

For an actual candidate cell at h ≥ k₀, the contact characterization
uses these same reference hypotheses. The candidate is the selected opponent
exactly when its indexed cell is distinct from the reference and the closed
cell meets the reference elementary segment in two distinct points. No
additional late bound on h is imposed. The contact condition is part of the
conclusion, rather than a supplied assumption.

The reciprocal characterization assumes k₀ ≥ 50,000,000 and two
actual cells at k,h ≥ k₀, so both late bounds follow. A candidate is selected
exactly when it differs from the reference and has an actual elementary slot
on the opposite facing side, with both endpoints reversed, that selects the
reference cell in return. Matching and return selection are proved together;
neither is supplied as a premise. The finite endpoint set need not be assumed
nonempty separately, since actual reference membership supplies the necessary
nonemptiness within the argument.

Primary identifiers, colors, consistent global labels, run interfaces, local
sectors, repairs, descendants, isolated stars, the full two-family partition
and both headline area-law theorems remain further obligations.

## Manuscript and independence

- Manuscript: OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11.
- Pinned source: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Manuscript path:
  `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
- Source label: `prop:two-families`; lines 299–316 for choice and contact,
  and lines 299–323 for reciprocal selection.
- These are original formalizations from mathematical manuscript statements;
  no upstream Lean proof text is reused. The implementation composes existing
  TNLean uniqueness and actual-matching results. OpenAI Codex (GPT-6)
  assistance is disclosed independently of the manuscript attribution.

## New declaration inventory

All three names are in `TNLean.PEPS.AreaLaw.Geometry`, in the new
`ElementarySideReciprocity.lean` module.

| Declaration | Kind | State |
| --- | --- | --- |
| `elementarySideOpponent` | Noncomputable definition | Verified at the exact source below |
| `elementarySideOpponent_eq_some_iff_contact` | Theorem | Verified at the exact source below |
| `elementarySideOpponent_reciprocal_iff` | Theorem | Verified at the exact source below |

All three released signatures agree with the independently approved design.
The direct package-option check passed without diagnostics in 4.62 seconds
(user 1.98 seconds, system 2.85 seconds). Independent full mathematical
review approved the proofs and hypotheses. The module introduction was clarified to state candidate distinctness
and the lower-index conditions explicitly; the checked signatures and proofs are unchanged.

## Exact-source verification

Completed parent: `26786e53a29e1804aae6302916b3068ef6cf12e4`, PR [8892](https://github.com/LionSR/TNLean/pull/8892).
Frozen source: `b8c1e59e88eadf8694530d1a6fc470d8348c237e`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 16.406 s | `2ef020f19813f2568afadf5823f3584df80bb7c1bf94a01da9a3718775ac1f8c` |
| Imported three-name report | `lake env lean docs/provenance/evidence/8758-reciprocal-opponents-axioms.lean` | Passed, exit 0 | 4.288 s | `2670ec6cd99a52b1b23002aabc41902b4bf8049e910b804c2b2d5776bdef4d6a` |

Actual command headers, source, timings, exit codes and complete output are
retained in [the build log](8758-reciprocal-opponents-build.log) and
[the imported kernel log](8758-reciprocal-opponents-axioms.log). All three
reports satisfy the unchanged standard logical-foundation policy; neither
command reports a warning. The existing warm artifacts and shared locked
verification protocol were retained. No parent proof module changed.

Strict promotion passes all 275 rows, adding precisely three original records.
All 272 parent entries and shards and all 116 tracked historical evidence
files are unchanged. No prior record is reverified. The separate unchanged normal provenance policy also passes all 275 rows.

Full source synchronization passes with 20,229 distinct references and
20,223 declaration records, with no missing, stale or duplicate references
and complete changed-declaration reverse coverage. Generated imports cover
2,853 production modules in
75 files. The new scoped chapter contains one
definition, two theorems, three declaration records and two proofs. Formatting
is idempotent; reader-facing prose and module guards pass. The older matching
chapter's closing prose points to the already proved uniqueness theorem;
its mathematical statement and proof remain unchanged. Independent full
review approved the three new signatures and proofs, including the minimal
reference late bound for contact and both derived bounds for reciprocity.
The scoped pattern review is recorded by the coordinating agent.

QICLean remains pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`; toolchain and dependency bytes
match the completed parent. Full CI and compiled whole-book checks remain
pending. The historical local declaration check encountered a missing
pre-existing `TNLean/MPS/Examples/Fibonacci.olean`; its evidence and limitation
remain preserved. A narrow Geometry build proves no whole-book compiled result.

## Immutable parent evidence

The completed parent contains 272 provenance records. This contribution adds
only three new records, for 275 in total, and changes no parent proof module
or provenance record. All 272 parent entries and every parent shard remain
byte-identical. No prior declaration requires reverification.

The separately captured baseline protects every tracked file recursively
under `docs/provenance/evidence`, including Markdown notes, Lean reports,
logs and the nested orthogonalization evidence directory. The exact inventory
contains 116 files, as measured from the completed parent's Git tree.
No earlier baseline is replaced. The strict helper checks the complete Git
inventory and each file hash, all parent ledger bytes and entry hashes,
and the unchanged provenance policy, schema and license before allowing
temporary outputs.

The helper promotes only after actual successful canonical logs bind the
exact frozen source and three report names. It runs the unchanged normal
policy over all 275 rows. It performs no Lean, Lake or cache operation and
writes only the explicitly selected output beneath `/tmp`.
