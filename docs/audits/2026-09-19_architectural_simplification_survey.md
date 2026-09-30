# Architectural simplification survey (2026-09-19)

This note records a repository-wide application of the `find-simplification`
audit at `main` 4973275fe, run as two orchestrated workflows and focused on
architectural shapes rather than zero-reference declarations: layer crossings,
parallel predicate and carrier families with bridges, sequel and staging chains
kept after their capstone, superseded routes, per-example repetition of a
generic construction, import-graph hubs, directory pseudo-modules, and
blueprint anchors on wrappers. The zero-reference lens was declared spent by the
2026-08-30 ninety-area survey; the 268 Lean files added since that survey
(62 under `MPS/FundamentalTheorem/Reduction`, 15 under
`ParentHamiltonian/Martingale`, 9 under `MPU/Examples`) had never been
audited and yielded most of the findings below.

## Method

Twelve read-only finder lenses (fresh Reduction code; other fresh code; layer
crossings; parallel families; superseded routes; sequel chains; import
architecture; duplicated code windows; directory structure; blueprint anchors;
speculative generality; examples and witnesses) produced 48 raw findings.
These were merged by hand into 34 candidates. Each candidate was then checked
by two independent agents: an evidence re-counter that re-ran every consumer
count under the skill's counting rules (final-component search, unicode-safe
matching, control runs, self-inventory subtraction, closure iteration),
rebuilt the blueprint tag census with
`scripts/blueprint_lean_sync.py::_split_lean_decls`, searched the ledger, the
audit notes, the paper-gap notes and `git log -S` for prior rulings, and
recomputed the net line delta; and a policy refuter that attacked the
candidate on settled surfaces, faithfulness, mathematical identity of the
claimed duplicates, net lines, churn, witness modules, deprecation windows and
campaign activity. Claimed Mathlib and QICLean replacements were elaborated in
standalone probe files against the pinned oleans. No repository build was run:
the environment is contended and the checkout's TNLean oleans were stale, so
every verdict below is grep- and probe-proved, not compiler-proved, and each
implementing pull request must root-build.

Nineteen candidates survived both checks in full, six survived in part, and
nine were refuted. The survivors were ranked by compounding cost (breadth times
recurrence for future proofs), then verified net deletable lines, then risk.

## Recorded findings

Ledger entries and issues carry the full evidence; this table gives the
disposition of each survivor.

| Rank | Finding | Disposition | Net lines |
|---|---|---|---:|
| 1 | Four per-ring entrywise embeddings (ℤ, ℤ√2, ℤ[σ], ℤ[ω]) re-prove the `Matrix.map` lemma family and re-define bond products, actions and word evaluation | ledger D16; #7846 | −215 |
| 2 | The literal-CPSV route restates the horizontal-canonical-form chain module by module (8 + 3 twin modules) | #6855 §4 (plan corrected) | −1,000 |
| 3 | D1 residue: `VerticalSectorHypotheses` still spelled out by four theorems; periodic sector-match core repeated at seven sites | #6855 §1 | −295 |
| 4 | Three MPDO carriers restate the twelve vertical-decomposition fields with copy bridges instead of `extends` | ledger D17; #7847 | −115 |
| 5 | Decided gauge-certificate ladder hand-instantiated per block (seven golden, five Eisenstein) | #7845 (scope widened) | −175 |
| 6 | Eleven handwritten directory waypoints plus one shim duplicate the generated aggregator frontier | #4847 | −330 |
| 7 | BiCF derivation core re-derives bilinear-form duality supplied by Mathlib and QICLean | #7850 | −120 |
| 8 | Upstream-shadow batch: nilpotency QICLean shadow, private swap clone, subquotient duplicate, seven single-consumer Mathlib twins, one-file aggregator | #7851 | −125 |
| 9 | Chapter 24 anchors the vertex-injective forwarding layer of `VirtualInsertion.lean` rather than the per-vertex theorems | #7852 | −110 |
| 10 | Blueprint-anchored per-example projection wrappers over the multi-block compression datum (27 of 63 survive) | #7853 | −95 |
| 11 | Three BNT sector-projector theorems re-derive the same three-site closure witnesses | #6855 item 1 | −30 |
| 12 | Promoted-pattern re-derivations: matrix-unit span closing, square-root inverse identities | #7854 | −40 |
| 13 | Thirty declarations carry two blueprint tags against the one-owner convention | #7855; eleven to #7726 | −35 |
| 14 | Torus edge-coordinate pinning case analysis copied verbatim into four theorems | #7856 | −70 |
| 15 | Blocked power-sum route superseded by the unblocked capstone of 2026-09-18 | ledger S17; #7848 | −440 |
| 16 | `ThreeBlockReconcile.lean` is a fully dead nine-declaration closure | S3 slice; #7849 | −366 |
| 17 | `CoarseThreeSiteMul.lean` and three coarse-chain lemmas are a post-capstone seam | S10 closing evidence; #7849 | −242 |
| 18 | Twisted-dimer `(0,0)` special case and per-pair specializations survive beside the uniform theorems | #7829 (closing PR) | −155 |
| 19 | Conditional norm-compression and operator-norm gap branch has no consumer and no source anchor (anticommutator branch stays) | #7857; owner sign-off | −400 |
| 20 | Two structure pairs restate fields instead of extending (three further pairs retained) | #7858 | −20 |
| 21 | Concrete GL(2) gauges hand-recompute their inverse after `mkOfDetNeZero` | #7854 | −25 |
| 22 | PEPS per-vertex scalar product theorem proved twice | #7856 | −28 |
| 23 | Five phase-honest merges of sequel pairs plus four content renames (nine arithmetic merges refuted) | #6855 §10 | −115 |
| 24 | `CZXSecondTupleCertificate` mirrors the first-tuple chain (fiber/placed/finrank part shareable) | #7568; wait for a third tuple | −115 |
| 25 | Three name-scan-dead import edges pin large subtrees into hub cones | #4847 items P6–P8 | −3 |

The verified total is about 4,660 net Lean lines, of which about 1,300 are
in fresh code and about 1,700 in the MPDO literal/horizontal twin chain.

## Rejected candidates

These were refuted by verification and should not be re-proposed without new
evidence.

- **Generic block-ordering and bond-coordinate bijections** (71 hand-written
  `ord`/`τ` tables). The proposed constructor through `Equiv.ofBijective` is
  noncomputable and a probe shows `decide +kernel` gets stuck on its inverse,
  which `Z3AnomalousDefect.lean:244-247` and
  `Z3AnomalousDefectCompression.lean:260-289` need; a `Fintype.bijInv`
  variant decides but its kernel cost inside the 25×25 decisions is
  unmeasured; several listed names are live fields of tagged constructors or
  tagged Σ-carriers. Honest scope is about 22 pairs, deferred until the
  example branches merge, and only with a timed computable-inverse probe.
- **Block-diagonal word evaluation through `toTensorFromBlocks`.**
  `MPOTensor.directSum` and its two lemmas are tagged and used by the tagged
  Z2×Z2 defect definition; the proposed survivor has an MPS carrier and an MPV
  conclusion, so no redirect exists; `trace_eq_sum_blockDiag'` serves a
  block-triangular consumer where `Matrix.trace_blockDiagonal'` does not
  apply. A 10–15-line proof trim in `AssemblyLemmas.lean` is recorded on
  #7844.
- **`PGVWC07CanonicalFormData` as a third client of the D15 base.** It stores a
  reindexing equivalence with real weights, not a coisometry with complex
  weights; folding needs a transport lemma and an existential encoding,
  net-positive and a faithfulness hazard for
  `def:pgvwc07_ti_canonical_representation`. Cross-reference posted on #7661.
- **Shift-example source gates derived three times.** The generic lemma
  already exists (`SourceFactorsTensorProduct.lean:153-212`) and is the sole
  calc step of all six proofs; the residue is per-example, and the six rank
  equivalences differ by orientation-specific prefixes (S11).
- **Two-site ambient-sector maps as instantiations of the generic maps.** Every
  two-site map composes the generic map with the blocked-index reindexing, and
  the Chapter 21 nodes state that composition and the common-denominator
  formula, which no generic theorem states; only six one-site `by exact`
  wrappers redirect faithfully.
- **177 blueprint-tagged pure forwarders.** The machine count collapses to 79
  zero-consumer forwarders, 110 of the 177 bodies apply a bridge lemma, six
  listed names have live consumers, and the forwarder nodes are the
  paper-labelled statements whose targets are TNLean strengthenings; redirecting
  would manufacture the node/anchor mismatches #7726 catalogues.
- **Twenty-two layer-inverting import edges.** A relocation programme with a
  −2 estimate: 35 import edits, six regenerated aggregators, 46 tagged
  declarations moved, no public surface shrinks; the layer table is
  conceptual and contradicted by about 100 further edges. Four
  closure-neutral import lines belong in the next unused-import sweep.
- **The graded quantum-dimer twist carried twice.** The bridge
  `dimerM f = (5/8) • flagMPO f` holds but is not decidable (real-valued
  weights), the decoders are load-bearing in kernel decisions, and the
  Reduction leaf's import cone would grow from 25 to about 160 modules; the
  two carriers are faithful to different note objects.
- **Cyclic window offset as ℕ-modular arithmetic.** A convention change, not a
  deletion: the tagged definitions and the blueprint prose state the
  ℕ-modular form, migration touches 185 statement lines in 24 files, and the
  lemmas were already single-sourced by #5814, #6228 and #6252.

## Retained on purpose

- The `weight_unit_exists : A ≠ 0 → …` premise of the ambient-free RFP
  carrier is CPSV16 line 246 and a hypothesis of two witness claims; the
  structure pair it belongs to stays unmerged.
- Thirteen zero-importer Algebra scalar leaves added 2026-08-31 to 2026-09-05
  are inputs to `\notready` Chapter 28/29 nodes under open trackers, an active
  staged campaign in the sense of S1.
- The four `IsingLetterSector*` and three `TwistedDimerPair*` files are
  kernel-time partitions of one decision and are not pseudo-modules.
- `GoldenInt` and `EisensteinInt` stay hand-rolled: decidable equality is the
  point and Mathlib has no computable ℤ[σ] or ℤ[ω].
- Generic ring, field and index parameters in `Algebra/` are all instantiated
  at ℂ or `Fin n`, but specializing removes no lines.
- Printed-status blueprint nodes are either gated on the owner questions of
  the degenerate-readings program or record genuine source errors.

## Limitations

Every deletion verdict is grep- and probe-proved. Closure claims for the
literal-CPSV twin deletion, the power-sum import pruning, the aggregator
regenerations and the importer re-pointings await a root build; the `extends`
refactors await elaboration of projections in situ; kernel budgets for the
generic word evaluation under the nine-letter decisions and for the
certificate-structure binder order are unmeasured; the QICLean-side lemmas
need a QICLean pull request and pin bump before the TNLean side builds; all
blueprint redirects need `python3 scripts/fetch_tenkz.py && cd blueprint &&
leanblueprint checkdecls` after a regenerated `lean_decls` snapshot. Name
collisions and `private` re-declarations were surveyed only where the
duplicated-window lens reached, so those shapes remain under-surveyed in MPDO
and PEPS. The two-day-old staged files under `Reduction` have six open
follow-ups adding examples in the same shapes, so the corresponding changes
should be sequenced behind them.
