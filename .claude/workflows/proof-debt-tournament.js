export const meta = {
  name: 'proof-debt-tournament',
  description: 'Find, verify, and rank the top structural proof debts in TNLean',
  phases: [
    { title: 'Find', detail: '10 lenses scan the repo for structural proof debt' },
    { title: 'Merge', detail: 'cluster overlapping findings into distinct debt items' },
    { title: 'Verify', detail: 'evidence-checker + impact-skeptic per debt' },
    { title: 'Rank', detail: 'three-judge panel, Borda aggregation' },
    { title: 'Synthesize', detail: 'final top-10 report with remediation plans' },
  ],
}

const ROOT = '/Users/siruilu/Local/agentFormalization/TNLean'

const CTX = `You are auditing TNLean, a Lean 4 / Mathlib formalization of the Fundamental Theorem of
Matrix Product States, Quantum Wielandt theory, and quantum-channel theory (Wolf's book).
Repo root: ${ROOT}. Source lives in TNLean/ (982 .lean files, ~318k lines).

Module sizes (files / lines): MPS 445/138k, PEPS 187/73k, Channel 184/59k, Algebra 53/13k,
Wielandt 40/12.5k, Analysis 33/10k, Spectral 12/4k, Entropy 7/2k, Archive 4/1.6k, Axioms 5/1.5k,
PiAlgebra 5/1k, QPF 4/0.8k, Topology 3/0.4k.

The task: find PROOF DEBT / ORGANIZATION DEBT — the formalization analogue of tech debt.
NOT sorries (there are only 4, that is not the topic). Debt means: things that make the codebase
harder to scale, review, and extend — duplication, missing abstractions, accretion, bad file
organization, unpromoted tactic patterns, over-specialized statements, dead weight.

Known signals from an initial scout (verify and go deeper, do not just repeat these):
- PEPS/ is a nearly flat directory with numbered-sequel files: TorusWindowChain2..6,
  TorusWindowPeel2..4, TorusFundamentalTheorem2, NormalSquareFundamentalTheorem2,
  CoherentFrameInstance2, ThreeBlockResonate2, UnionInjectivityGeneral2.
- Duplicate top-level theorem/def names across files (rg on '^(theorem|lemma) NAME'):
  AppendixBStructuralData x55, NeighboringTraceFactorization x46, ThreeBlockGeometry x34,
  PosSemidef x33, IsPositiveMap x31, sameMPV x18, GaugeEquiv x18, IsHorizontalCF x14.
- Many files bunch just under 1000 lines (looks like a hard cap causing artificial splits).
- scripts/tactic_pattern_scan.py reports repeated tactic patterns >= rule-of-three not yet
  promoted, e.g. 'apply Finset.sum_congr rfl; intro i _; ...' x9-12 across files,
  a 7-line intro/simp block x5 in Channel/Schwarz/TwoPositive.lean, a 6-line filter/sum block
  x5 across PEPS/RegionBlock files.
- Custom tactics exist in TNLean/MPS/Tactic/Basic.lean (mpv_ext, block_words, transfer_simp);
  the pattern ledger is docs/tactic_patterns.md; conventions in docs/*.md.
- Root import file is TNLean.lean; Archive/ is excluded from root imports; there may be
  orphan files never imported.

Rules for you:
- Work read-only: use rg, find, wc, awk, and the Read tool. NEVER modify files.
- Every finding MUST carry concrete, quantified evidence (file paths, counts, line refs you
  actually verified with a command). No speculation.
- Report the 3-6 LARGEST debts for your lens only. Prefer breadth (many files affected) and
  compounding cost (every future proof pays it) over cosmetic nits.
- Keep each evidence detail to one or two sentences. Max 6 evidence entries per finding.`

const FINDINGS_SCHEMA = {
  type: 'object', required: ['findings'], additionalProperties: false,
  properties: {
    findings: {
      type: 'array', maxItems: 6,
      items: {
        type: 'object', additionalProperties: false,
        required: ['title', 'category', 'description', 'evidence', 'breadth_files', 'why_it_blocks_scaling', 'remediation'],
        properties: {
          title: { type: 'string' },
          category: { type: 'string' },
          description: { type: 'string' },
          evidence: {
            type: 'array', maxItems: 6,
            items: {
              type: 'object', additionalProperties: false, required: ['file', 'detail'],
              properties: { file: { type: 'string' }, detail: { type: 'string' } },
            },
          },
          breadth_files: { type: 'number' },
          why_it_blocks_scaling: { type: 'string' },
          remediation: { type: 'string' },
        },
      },
    },
  },
}

const VERIFY_SCHEMA = {
  type: 'object', additionalProperties: false,
  required: ['confirmed', 'notes', 'impact_1_10', 'effort_1_10'],
  properties: {
    confirmed: { type: 'boolean' },
    notes: { type: 'string' },
    corrected_evidence: { type: 'string' },
    impact_1_10: { type: 'number' },
    effort_1_10: { type: 'number' },
  },
}

const MERGE_SCHEMA = {
  type: 'object', required: ['debts'], additionalProperties: false,
  properties: {
    debts: {
      type: 'array', maxItems: 20,
      items: {
        type: 'object', additionalProperties: false,
        required: ['id', 'title', 'category', 'description', 'evidence_summary', 'breadth_files', 'remediation'],
        properties: {
          id: { type: 'string' },
          title: { type: 'string' },
          category: { type: 'string' },
          description: { type: 'string' },
          evidence_summary: { type: 'string' },
          breadth_files: { type: 'number' },
          remediation: { type: 'string' },
        },
      },
    },
  },
}

const RANK_SCHEMA = {
  type: 'object', required: ['ordering', 'rationale'], additionalProperties: false,
  properties: {
    ordering: { type: 'array', items: { type: 'string' } },
    rationale: { type: 'string' },
  },
}

const FINAL_SCHEMA = {
  type: 'object', required: ['top10'], additionalProperties: false,
  properties: {
    top10: {
      type: 'array', maxItems: 10,
      items: {
        type: 'object', additionalProperties: false,
        required: ['rank', 'id', 'title', 'category', 'what_it_is', 'evidence_summary', 'why_it_blocks_scaling', 'remediation_plan', 'first_week_pr', 'impact_1_10', 'effort_1_10'],
        properties: {
          rank: { type: 'number' },
          id: { type: 'string' },
          title: { type: 'string' },
          category: { type: 'string' },
          what_it_is: { type: 'string' },
          evidence_summary: { type: 'string' },
          why_it_blocks_scaling: { type: 'string' },
          remediation_plan: { type: 'string' },
          first_week_pr: { type: 'string' },
          impact_1_10: { type: 'number' },
          effort_1_10: { type: 'number' },
        },
      },
    },
    honorable_mentions: { type: 'array', items: { type: 'string' } },
  },
}

const LENSES = [
  { key: 'duplication', prompt: `Lens: COPY-PASTE DUPLICATION. Hunt for near-identical lemmas, defs, and structures
repeated across files. Start from the duplicate-name signal (AppendixBStructuralData x55,
NeighboringTraceFactorization x46, ThreeBlockGeometry x34, sameMPV x18...): open several of the
files, diff the statements, and determine whether these are genuinely re-stated/re-proved
per-file (real debt) or distinct namespaced content (not debt). Also hunt for numbered-sequel
file families (TorusWindowChain2..6, TorusWindowPeel2..4, ThreeBlockResonate/2,
UnionInjectivityGeneral/2, CoherentFrameInstance/2, TorusFundamentalTheorem/2): read pairs and
estimate the fraction of duplicated content. Quantify: how many lines exist N times.` },
  { key: 'architecture', prompt: `Lens: FILE & MODULE ORGANIZATION. Assess directory structure and layering. PEPS/ is a
~120-file flat directory — is there a coherent grouping (Cycle*, Torus*, Normal*, Region*)
that is expressed only in filename prefixes instead of directories? Are there files that are
stage-N dumps of a single proof effort rather than reusable modules? Check the import graph:
orphan files never reachable from TNLean.lean (compare 'find TNLean -name *.lean' against
transitive imports, or at least against direct mentions in TNLean.lean and module aggregators);
files in the wrong layer (matrix lemmas buried in MPS/ or PEPS/ that belong in Algebra/);
aggregator/index files that are missing so every file hand-picks deep imports. Quantify.` },
  { key: 'abstraction-gap', prompt: `Lens: MISSING ABSTRACTIONS. Find places where the SAME mathematical idea is re-proved in
specialized forms because a general lemma, structure, or interface is missing. Examples to
investigate: is there a general 'blocking/coarse-graining' interface, or does each of
MPS/Chain, MPS/BNT, PEPS/Blocking, PEPS/NormalBlocking redo it? Is there one transfer-matrix
API shared between Channel/TransferMatrix and MPS transfer matrices? Do the 8+
FundamentalTheorem variants (MPS single-block, Multi, Periodic, Chain, PiAlgebra, PEPS Normal/
Torus/Cycle...) share a common core, or is the argument re-instantiated from scratch each time?
Read representative files and identify the abstraction that would collapse the duplication,
and how many lines/files it would absorb.` },
  { key: 'proof-length', prompt: `Lens: OVERLONG AND BRITTLE PROOFS. Find the longest individual proofs in the repo (use awk or
rg to measure := by ... blocks, or approximate by scanning the largest files:
MPS/ParentHamiltonian/*.lean ~1000 lines each, PEPS/NormalEdgeBlockingTranslated.lean,
Channel/Schwarz/RelativeEntropyConvexity.lean, Channel/KrausCPTP.lean). Read the worst 5-8
proofs and diagnose WHY they are long: missing helper lemmas, manual index bookkeeping,
Finset.sum manipulation done by hand, repeated conv/calc blocks, missing simp lemmas for the
project's own definitions. Report which proof-shortening infrastructure is missing, with
quantified examples (proof X is N lines, of which ~M lines are pattern Y).` },
  { key: 'tactic-infra', prompt: `Lens: TACTIC INFRASTRUCTURE DEBT. Run 'python3 scripts/tactic_pattern_scan.py' in the repo
root and analyze the full output. Cross-check against docs/tactic_patterns.md (the ledger) and
TNLean/MPS/Tactic/Basic.lean (promoted tactics: mpv_ext, block_words, transfer_simp). Per the
project's own rule of three, patterns with >=3 occurrences across >=2 files must be promoted
to a lemma / simp set / tactic. Report: which patterns are past due, how many occurrences and
lines each, whether existing promoted tactics are actually used or hand-written equivalents
still appear (that is a review-blocking style issue by the project's own rules), and whether
the project's simp-set infrastructure (@[simp] discipline on its own defs) is adequate.` },
  { key: 'api-design', prompt: `Lens: DEFINITION/API DESIGN DEBT. Examine the core definitions (MPSTensor, evalWord,
IsInjective, SameMPV / SameMPV₂, GaugeEquiv, transferMap, IsBNTCanonicalForm, cumulativeSpan,
IsNormal in Wielandt/) and their APIs. Look for: parallel variant predicates that force every
downstream theorem to exist twice (SameMPV vs SameMPV₂ and similar pairs); definitions lacking
a simp/ext lemma API so every use site unfolds manually (rg 'unfold' and 'show ... from' and
'simp only [Foo]' counts per definition); structures vs bare functions mismatches; missing
instances forcing repeated boilerplate. Quantify how much downstream friction each API gap
generates (count call sites paying the cost).` },
  { key: 'generality', prompt: `Lens: OVER-SPECIALIZED STATEMENTS. Find theorems stated and proved for a special case in one
file and again for another special case elsewhere, where a single general statement would serve
(dimension-specific versions, square-lattice-only versions next to general-lattice versions,
List-indexed vs Fin-indexed duplicates, results proved for ℂ that hold for any RCLike or field).
Check PiAlgebra/ vs MPS/FundamentalTheorem for parallel developments. Also the reverse debt:
theorems stated with hypotheses they do not need (making reuse impossible). Read candidate
pairs and verify the duplication is real. Quantify.` },
  { key: 'hygiene', prompt: `Lens: BUILD & PROOF HYGIENE. Look for compounding hygiene debt: non-terminal 'simp' without
a lemma list (count 'simp\\b' vs 'simp only' repo-wide and in the worst files); 'classical' /
'decide' / 'norm_num' heavy spots; set_option debris (maxHeartbeats, pp, trace) left in source;
commented-out proof blocks and debug artifacts ('-- sorry', #check/#eval/#print left in files,
'Scratch' content imported from real files); overlong files (how many files exceed the 100-char
line or a healthy size); TODO/FIXME/HACK markers (count and cluster them); deprecated aliases
that were never cleaned. Quantify each repo-wide with rg counts and name the worst offenders.` },
  { key: 'naming-docs', prompt: `Lens: NAMING & DOC CONSISTENCY. The project follows Mathlib conventions (docs/MATHLIB_naming.md,
docs/MATHLIB_doc.md). Sample broadly and find systematic inconsistencies that make search and
review harder at scale: the same concept under different names in different modules (e.g. what
words are used for 'blocking', 'transfer', 'canonical form', 'injective/normal' across MPS,
PEPS, Channel, Wielandt); theorem names violating snake_case or not describing the conclusion;
missing module docstrings (count files without '/-!' headers per directory); missing docstrings
on major defs/theorems; stale docstrings citing wrong sources. Focus on the systematic patterns,
not one-off typos. Quantify per-directory.` },
  { key: 'dead-weight', prompt: `Lens: DEAD WEIGHT. Find code that costs maintenance but serves nothing: files not transitively
imported from TNLean.lean (compute: every file's module name, which files are imported where;
'Scratch' and exploratory files); declarations defined but never used anywhere else in the repo
(sample suspicious areas, e.g. run rg on names of defs in older files); superseded developments
whose replacement exists (a '2' file whose '1' file is still built but no longer used);
Archive/ leakage (is Archive imported by anything?); duplicated counterexample scaffolding;
Examples/ files that drifted from the API. Quantify: how many orphan files / lines.` },
]

phase('Find')
log('Fanning out 10 debt-finder lenses over the repo')
const found = await parallel(LENSES.map(l => () =>
  agent(`${CTX}\n\n${l.prompt}\n\nReturn your 3-6 largest findings for this lens.`,
    { label: `find:${l.key}`, phase: 'Find', schema: FINDINGS_SCHEMA })
))
const allFindings = found.filter(Boolean).flatMap((r, i) =>
  r.findings.map(f => ({ ...f, lens: LENSES[i] ? LENSES[i].key : 'unknown' })))
log(`Collected ${allFindings.length} raw findings across ${found.filter(Boolean).length} lenses`)

phase('Merge')
const merged = await agent(`${CTX}\n\nYou are the MERGE JUDGE of a proof-debt tournament. Below are raw findings from 10
independent audit lenses. Many overlap (the same underlying debt seen through different lenses).
Cluster them into DISTINCT debt items: one item per underlying cause, merging all evidence.
Keep genuinely different debts separate even if in the same directory. Drop findings that are
trivially small (single-file cosmetic issues) — keep only debts worth ranking. Aim for 12-18
distinct debts. Assign ids D1, D2, ... in no particular order. Write evidence_summary as a
compact, quantified paragraph combining the best evidence from all merged findings, and keep
each debt's description self-contained (a reader who has not seen the raw findings must
understand it). You may spot-check evidence in the repo with rg/Read if two findings conflict.

RAW FINDINGS (JSON):\n${JSON.stringify(allFindings, null, 1)}`,
  { label: 'merge-judge', phase: 'Merge', schema: MERGE_SCHEMA })
const debts = merged.debts
log(`Merged into ${debts.length} distinct debt items`)

phase('Verify')
const verified = await parallel(debts.map(d => () =>
  parallel([
    () => agent(`${CTX}\n\nYou are an ADVERSARIAL EVIDENCE CHECKER. A tournament claims the following proof debt
exists. Try to REFUTE it: re-run the searches yourself (rg/find/wc/Read in ${ROOT}), check
whether the claimed duplication/pattern/orphan status is real, whether the counts hold, and
whether there is context that explains it away (e.g. 'duplicates' that are actually distinct
mathematics, 'orphans' that are deliberately excluded like Archive/). Default to
confirmed=false if the central evidence does not hold up. In notes, state what you actually
verified with which commands and correct any wrong counts (also fill corrected_evidence).
Set impact_1_10 and effort_1_10 to 0 (a different judge scores those).

CLAIMED DEBT:\n${JSON.stringify(d, null, 1)}`,
      { label: `check:${d.id}`, phase: 'Verify', schema: VERIFY_SCHEMA }),
    () => agent(`${CTX}\n\nYou are an IMPACT SKEPTIC in a proof-debt tournament. Assume the evidence below is
factually accurate (a separate checker verifies it). Your job: argue this debt does NOT
meaningfully block scaling — maybe it is cheap to live with, localized, or removal would be
churn with little payoff. Only set confirmed=true if your best counterargument fails.
Then score honestly: impact_1_10 = how much removing it improves scalability/reviewability of
future work across the whole repo (10 = transformative), effort_1_10 = how expensive removal
is (10 = months of work, 1 = one small PR). Spot-check the repo if it helps.

DEBT:\n${JSON.stringify(d, null, 1)}`,
      { label: `skeptic:${d.id}`, phase: 'Verify', schema: VERIFY_SCHEMA }),
  ]).then(vs => {
    const [ev, im] = vs
    return { ...d, evCheck: ev, imCheck: im }
  })
))
const surviving = verified.filter(Boolean).filter(v => {
  const evOk = v.evCheck ? v.evCheck.confirmed : true
  const imOk = v.imCheck ? v.imCheck.confirmed : true
  return evOk && imOk
})
log(`${surviving.length}/${debts.length} debts survived adversarial verification`)

phase('Rank')
const compact = surviving.map(v => ({
  id: v.id, title: v.title, category: v.category,
  evidence: v.evCheck && v.evCheck.corrected_evidence ? v.evCheck.corrected_evidence : v.evidence_summary,
  impact: v.imCheck ? v.imCheck.impact_1_10 : null,
  effort: v.imCheck ? v.imCheck.effort_1_10 : null,
  skeptic_notes: v.imCheck ? v.imCheck.notes : '',
}))
const JUDGE_ANGLES = [
  { key: 'scalability', prompt: 'Rank by long-term scalability: which debt, left in place, most slows or corrupts the NEXT 100k lines of formalization? Compounding, load-bearing debts first.' },
  { key: 'value-per-week', prompt: 'Rank by weekly-removable value: impact divided by effort. The debts a small weekly PR cadence can actually burn down, with visible payoff soonest, first. Multi-month moonshots rank lower even if huge.' },
  { key: 'mathematical-clarity', prompt: 'Rank by mathematical clarity and reviewability: which debt most obscures what has actually been proved, hides the structure of the mathematics, or makes review/audit (including paper-faithfulness audits) hardest?' },
]
const rankings = await parallel(JUDGE_ANGLES.map(j => () =>
  agent(`${CTX}\n\nYou are a TOURNAMENT JUDGE. ${j.prompt}\n\nBelow are the verified debts. Return 'ordering':
ALL debt ids, best (rank 1) first, and a rationale for your top 5 choices. Spot-check the repo
if two debts are hard to separate.\n\nDEBTS:\n${JSON.stringify(compact, null, 1)}`,
    { label: `judge:${j.key}`, phase: 'Rank', schema: RANK_SCHEMA })
))
const points = {}
const valid = new Set(compact.map(c => c.id))
for (const r of rankings.filter(Boolean)) {
  const seen = new Set()
  r.ordering.filter(id => valid.has(id)).forEach((id, idx) => {
    if (seen.has(id)) return
    seen.add(id)
    points[id] = (points[id] || 0) + (compact.length - idx)
  })
}
const ranked = compact
  .map(c => ({ ...c, borda: points[c.id] || 0 }))
  .sort((a, b) => b.borda - a.borda || (b.impact || 0) - (a.impact || 0))
log('Borda order: ' + ranked.map(r => `${r.id}(${r.borda})`).join(', '))

phase('Synthesize')
const fullTop = ranked.slice(0, 12).map(r => {
  const v = surviving.find(s => s.id === r.id)
  return { ...r, description: v.description, remediation: v.remediation,
    evidence_notes: v.evCheck ? v.evCheck.notes : '', breadth_files: v.breadth_files }
})
const final = await agent(`${CTX}\n\nYou are the FINAL SYNTHESIZER of the proof-debt tournament. Below are the top debts in
tournament (Borda) order, with verified evidence and judge scores. Produce the definitive
top-10 report. Keep tournament order unless two adjacent items are clearly misordered given
the evidence (you may swap adjacent items only). For each: crisp title, what_it_is (2-3
sentences, self-contained), evidence_summary (quantified, from the verified evidence),
why_it_blocks_scaling (1-2 sentences), remediation_plan (concrete refactor steps, 2-4
sentences, referencing real file paths), and first_week_pr (the single well-scoped PR that
starts the burn-down, sized for one week or less). Use impact/effort scores given. Put items
11-12 in honorable_mentions as one-line strings.

DATA:\n${JSON.stringify(fullTop, null, 1)}`,
  { label: 'synthesizer', phase: 'Synthesize', schema: FINAL_SCHEMA })

return { top10: final.top10, honorable_mentions: final.honorable_mentions || [],
  judge_rationales: rankings.filter(Boolean).map((r, i) => ({ judge: JUDGE_ANGLES[i].key, rationale: r.rationale })),
  surviving_count: surviving.length, raw_findings_count: allFindings.length,
  eliminated: verified.filter(Boolean).filter(v => !surviving.includes(v)).map(v => ({ id: v.id, title: v.title, why: (v.evCheck && !v.evCheck.confirmed) ? v.evCheck.notes : (v.imCheck ? v.imCheck.notes : 'verifier failed') })) }