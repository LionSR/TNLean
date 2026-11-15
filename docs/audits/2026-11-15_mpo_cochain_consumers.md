# MPO cochain consumers: migration for #8321

This candidate implements the consumer migration of
[#8321](https://github.com/LionSR/TNLean/issues/8321). It must stay draft and
must not be merged into main while its prerequisites remain unmerged.

## Exact prerequisite sources

The isolated integration branch combines these two unmerged draft heads:

- [#10616](https://github.com/LionSR/TNLean/pull/10616),
  `7c911dcb2911762ea83e5e16dac743af26bf3eab`;
- [#10615](https://github.com/LionSR/TNLean/pull/10615),
  `d6b3712c10cd005a44ed37f3c5de2118a73abcc6`.

Their shared base is `eb588dc15332a3798431015e6c27ecbaf329b2d1`.
The original environment checkout was 257 commits older. The GitHub source API
was used to restore the exact shared base, checking every imported Git object
against its SHA. Applying the prerequisite patches reproduced their published
tree hashes `3710b3e1076f93f0819d65273b78742e523ccef2` and
`c4877329323a0179325133aac7ee3f7990dd3dc2`. Their changes merge without conflict.
The integration commit has both prerequisite heads as parents. No main branch
or prerequisite branch was modified.

After integration, #10616 advanced to
`3ba155b6ea409bfde12e4ee915c0ab702642b455`. Its only change is LaTeX
formatting in the fusion-gauge chapter; its Lean source is identical to the
pinned head. This candidate carries that formatting correction while retaining
the immutable integration base. #10615 remains at the selected head above.

At inspection, both exact heads passed their hosted Lean build jobs, including
the full library build, strict checks, compilation-time checks, style lint, and
compiled blueprint declaration checks. Their web/PDF checks were not all
finished. Those separate builds do not validate this combined consumer candidate.

## Retyped consumers

- `FusionData.omega` now returns
  `groupCohomology.cocycles (Rep.ofMulDistribMulAction G ℂˣ) 3`.
  Normality supplies the proved cocycle equation. Its scalar extraction is
  named `FusionData.associatorScalar`, and all existing scalar computations
  were updated to that name. No deprecated scalar-valued `omega` alias remains.
- `FusionData.relativeScalar` now returns a two-cochain with values in the
  additive coefficient representation. Its differential is the ratio of the
  associators, proved by `d₂₃_relativeScalar`.
- `ActionData.lSymbol` now returns a two-cochain with permutation coefficients
  on the single block. The tensor-derived values use the coordinate change
  supplied by #10615. Its differential is the constant-function image of the
  associator, proved by `d₂₃_lSymbol`.
- The normal-representation anomaly class and its choice-independence
  statements project the certified Mathlib cocycle directly.

Fusion and action tensors retain their existing mathematical definitions.
The theorem hypotheses and conclusions are preserved.

The scalar extractor is required independently of normality: the explicit
group-cocycle MPO construction has non-normal tensors, as proved by its
`not_isNormalRepresentation` theorem. Requiring normality of all fusion tensors
would discard that existing construction. The certified cocycle is constructed
after the pentagon proof, without strengthening `FusionData`.

## Remaining work

The requested consumer definitions are migrated, but #8321 remains open until
the combined candidate passes hosted elaboration and downstream checks. The
common scalar normalization and gauge predicates remain in #8319 and #8320;
scalar computations on the value projections still use those existing facts.
No new cochain or cocycle type was added.

The group-cocycle gate and tensor inputs are Mathlib inhomogeneous cochains.
Their multiplication and fusion results assume the vanishing of Mathlib's
third differential. Arbitrary-cochain gate and contraction identities retain
their original generality. The cyclic, bit, and type-II Klein constructors
return certified Mathlib three-cocycles. Their explicit exponential and sign
formulas are evaluation lemmas. The cyclic class calculations project the
native cocycles directly. The old `cyclicCocycleSubtype` declaration is removed;
`cyclicCocycle_inv` is replaced by `cyclicCocycle_neg`, equality in the additive
group of native cocycles. All production uses and blueprint tags are updated.

The public computation rule `scalarCocycleValue₃_mk` takes a native
inhomogeneous cochain and a proof of its zero differential. The intermediate
adapter-specific `scalarCocycleValue₃_toCocycles` declaration is removed.
Cyclic constructors now call Mathlib's `cocyclesMk` directly. Their private
scalar formulas supply the explicit values and existing closure proofs.

The generic permuted-block L-symbol now also takes values in the permutation
representation. The coefficient action and coordinate equivalences allow
arbitrary universes of block labels and coefficients. Its differential theorem
uses Mathlib's inhomogeneous differential, which permits this generality,
without imposing the smaller universe required by the cohomology quotient.
All block gauge, domain-wall, and CZX scalar computations evaluate the native
two-cochain through the inverse coordinate change. No block-label universe
was narrowed. Hosted validation of this extension is pending.

## Verification

Local Lean execution cannot start: `lake` and `lean` are absent, there is no
`.lake` dependency cache, and the environment reports an enforced disabled
network policy. A direct GitHub fetch returns proxy HTTP 403. No Mathlib source
build was attempted. Source restoration used the authorized connected GitHub
tools; it did not change the environment's network policy.

The generic CI log filter suppresses the repeated module-system import notice
from the preparatory build console, retaining the full build log and every
strict warning-as-error check. All 57 existing CI-selection tests pass. No
per-module workflow step or path entry was added.

Generated-import completeness, reader-facing prose, blueprint mathematical
roles, module-policy checks, whitespace checks, and proof-integrity scans are
run on the combined source tree. Source-level blueprint checks find the new
declarations. Their full-tree report also contains references into unavailable
Mathlib/QICLean dependency checkouts, so it is not a substitute for compiled
declaration checking.

Hosted consumer compilation and downstream checking remain required. The
candidate must not be described as validated until those checks pass on its
actual combined source tree.

The [hosted build at `5197337`](https://github.com/LionSR/TNLean/actions/runs/43745039062/job/132907421071)
compiled both foundations together, `Associator`, `AssociatorCohomology`, the
dagger-fusion modules, and several Klein and cyclic anomaly examples. It found
an inference error in the single-block L-symbol evaluation: the coefficient
group was inferred as complex numbers instead of complex units. The explicit
complex-unit parameter fixed that module: the hosted build at `99805c4`
compiled `AnomalyObstruction` as well as the associator and its cohomology
projection. Its strict checks later failed in `DomainWall` and
`CZXPermutedBlocks`. That earlier complete log could not be retrieved through
the connector (transport closed). Subsequent runs use the console filter
above, and their complete diagnostics are readable.

The combined-source run at `159c93d` compiled the new scalar-evaluation
module, the native cyclic, bit, and Klein constructors, and the cyclic
domain-wall calculations. It found three remaining proof reductions: tuple
indices in the generic differential, the value projection in the cyclic class
criterion, and associativity in the gate phase calculation. Their explicit
proof corrections are included in the follow-up. Full latest-head validation
remains required. Run results are kept current in the draft PR description;
the compilation records here describe the revisions named above.

The combined-source run at `ed95ce2` passed strict checking of the native
constructors, gates, generic block differential, gauge calculations, and all
changed Z₃ consumers. Its only strict failure was an unused trailing `rfl` in
the CZX block-action proof, which is removed in the follow-up. Full downstream
and latest-head validation remain pending.

Prepared with OpenAI Codex (GPT-6); maintainer review is required.
