# Lean 4 Code-Quality Audit: `TNLean/MPS/CanonicalForm` and `TNLean/MPS/FundamentalTheorem`

## Scope and method

- Scope:
  - `TNLean/MPS/CanonicalForm/` (all 12 files)
  - `TNLean/MPS/FundamentalTheorem/` (all 14 files)
- Metrics collected per file:
  - line count
  - actual proof-line `sorry` count (`^\s*sorry\b`, so prose mentions of “sorry” are excluded)
  - top-level declaration spans used as a proxy for “proofs >50 lines”
- Review criteria:
  - long proofs
  - dead code / commented-out blocks
  - stale status comments
  - duplicated logic / proof boilerplate
  - unnecessary imports
  - dependency tangles
  - closable `sorry`s
  - naming consistency
  - `decide` / `native_decide`
  - `simp` patterns

## Executive summary

- The biggest spaghetti risks are not raw theorem correctness; they are structural:
  - `TNLean/MPS/FundamentalTheorem/Full.lean` is too large and contains two monolithic proofs of ~838 and ~339 lines.
  - `TNLean/MPS/CanonicalForm/Assembly.lean` mixes at least four responsibilities in one 1121-line file.
  - `TNLean/MPS/FundamentalTheorem/PeriodicOverlap.lean` has 7 actual `sorry`s and several proof-outline comment blocks standing in for implementations.
  - `TNLean/MPS/CanonicalForm/NormalReduction.lean` and `TNLean/MPS/CanonicalForm/CyclicSectors.lean` are also carrying too much proof and packaging logic per file.
- Literal circular imports are absent, as expected in Lean, but there is clear layer inversion:
  - canonical-form files import deep fundamental-theorem files
  - periodic FT files import canonical-form assembly back again
- Global checks:
  - `TODO` / `FIXME` / `HACK`: none found in the audited files
  - `decide` / `native_decide`: none found
  - actual `sorry`: only `TNLean/MPS/FundamentalTheorem/PeriodicOverlap.lean`
- Naming convention mismatch is systemic:
  - the repo docs say theorem names should be `snake_case`
  - many theorem names here are camel/mixed-case, e.g. `fundamentalTheorem_singleBlock`, `sameMPV_of_sameMPVFrom_of_injective`, `exists_CFII_data_of_TP_of_isIrreducibleTensor`

## Cross-cutting architectural findings

### 1. Layering is tangled

- `TNLean/MPS/CanonicalForm/NormalReduction.lean` imports `TNLean.MPS.FundamentalTheorem.TransferNormalization`.
- `TNLean/MPS/CanonicalForm/BNTGrouping.lean` imports `TNLean.MPS.FundamentalTheorem.SectorDecomposition`.
- The former `TNLean/MPS/CanonicalForm/EqualNormBridge.lean` branch has been retired; the
  surviving common-sector comparison code imports the source-facing FT modules directly.
- `TNLean/MPS/CanonicalForm/Assembly.lean` imports `TNLean.MPS.FundamentalTheorem.Full`.
- `TNLean/MPS/FundamentalTheorem/PeriodicOverlap.lean` imports both `TNLean.MPS.FundamentalTheorem.Full` and `TNLean.MPS.CanonicalForm.Assembly`.

This is not a literal cycle, but it does create a dependency knot. The canonical-form pipeline is no longer a lower layer; it reaches into deep FT results. Then periodic FT reaches back into canonical-form assembly. That increases rebuild surface and makes refactors harder than necessary.

### 2. Proof boilerplate is repeated instead of packaged

The same simplification and limit-comparison idioms recur many times:

- `Full.lean` repeats:
  - `convert (...).norm using 1; simp only [norm_one]` / `norm_zero`
  - `simp only [Fin.lt_def]` positivity boilerplate
  - `intro N; simp only [mpvOverlap]`
- `FiniteLength.lean` repeats long `Matrix.trace` linearization `simp only` blocks.
- The retired equal/proportional Fundamental Theorem file and `Full.lean`
  both repeated the same `WithLp.ofLp_sum` / `Finset.sum_apply` /
  `Pi.smul_apply` expansion pattern.
- `SectorIrreducibility.lean` repeats orbit/shift `pow_succ'` arguments.

These are good candidates for local helper lemmas.

### 3. Confirmed unnecessary imports

Verified by removing the import in a temporary copy and running `lake env lean`:

- `TNLean/MPS/CanonicalForm/CyclicSectors.lean`
  - `import Mathlib.Analysis.Matrix.Spectrum`
  - `import Mathlib.Logic.Equiv.Sum`

Both appear removable.

## File-by-file audit

### `TNLean/MPS/CanonicalForm/BNTGrouping.lean`

- Size: 484 lines
- Actual `sorry`: 0
- Long proofs:
  - `exists_bnt_grouping` at `413-484` (~72 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - sorting and regrouping logic overlaps conceptually with `NormalReduction.sort_blocks_by_weight_norm` and later sector-packaging code
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - imports `FundamentalTheorem.SectorDecomposition`, so canonical-form grouping depends on FT-side decomposition machinery
- Closable `sorry`:
  - none
- Naming:
  - `exists_sortedNCF_of_distinct_norms` is mixed-case and acronym-heavy
- `decide` / `native_decide`:
  - none
- `simp` style:
  - acceptable; no obvious oversized simp sets

### `TNLean/MPS/CanonicalForm/Reduction.lean`

- Size: 234 lines
- Actual `sorry`: 0
- Long proofs:
  - `exists_irreducible_blockDecomp` at `107-234` (~128 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - repeated left/right `combinedBlocks` rewrites at `164`, `169`, `212`, `218`
- Unnecessary imports:
  - import set is minimal
- Dependency tangle:
  - none beyond normal canonical-form layering
- Closable `sorry`:
  - none
- Naming:
  - mostly fine
- `decide` / `native_decide`:
  - none
- `simp` style:
  - fine

### `TNLean/MPS/CanonicalForm/BlockingViaAdjoint.lean`

- Size: 394 lines
- Actual `sorry`: 0
- Long proofs:
  - `IsPrimitive.adjoint_iff` at `116-201` (~86 lines)
  - `exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor` at `277-380` (~104 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - adjoint/conjugate-transpose bridge steps could likely be factored more aggressively
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - reasonable for this file
- Closable `sorry`:
  - none
- Naming:
  - theorem names are mostly coherent, though some are long
- `decide` / `native_decide`:
  - none
- `simp` style:
  - mostly controlled

### `TNLean/MPS/CanonicalForm/Existence.lean`

- Size: 547 lines
- Actual `sorry`: 0
- Long proofs:
  - `exists_irreducible_blockDecomp_liveBlocks` at `439-547` (~109 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - this file mixes several independent construction stages: CFII data, primitive blocking, zero-block elimination, live-block decomposition
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - broad import set; this is already functioning as a mini-assembly file
- Closable `sorry`:
  - none
- Naming:
  - examples like `exists_CFII_data_of_TP_of_isIrreducibleTensor` and `zeroMPSTensor` do not fit the stated theorem naming convention cleanly
- `decide` / `native_decide`:
  - none
- `simp` style:
  - acceptable

### Retired equal-norm bridge branch

The old equal-norm bridge file is no longer part of the present development.
Its bridge belonged to the former proportional-MPV branch and should not be
treated as a source-facing formalization of the heterogeneous Fundamental
Theorem. The surviving common-sector comparison material now lives under
`TNLean/MPS/CanonicalForm/SectorComparison/`.

### `TNLean/MPS/CanonicalForm/SectorIrreducibility.lean`

- Size: 407 lines
- Actual `sorry`: 0
- Long proofs:
  - `orbit_iterate_supported_on_shifted_sector` at `210-283` (~74 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - repeated orbit-step boilerplate around `pow_succ'` and shifted-sector calculations at `195`, `250`, `256`, `263`, `268`, `350`, `358`
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - reasonable
- Closable `sorry`:
  - none
- Naming:
  - mostly fine
- `decide` / `native_decide`:
  - none
- `simp` style:
  - many local simplifications, but not obviously problematic

### `TNLean/MPS/CanonicalForm/NormalReduction.lean`

- Size: 692 lines
- Actual `sorry`: 0
- Long proofs:
  - `exists_tp_gauge_blockwise` at `146-292` (~147 lines)
  - `sort_blocks_by_weight_norm` at `390-506` (~117 lines)
  - `exists_blocked_normal_data_of_primitive_blockDecomp` at `507-567` (~61 lines)
- Dead code / stale comments:
  - stale comment at `139-145`: it says `exists_tp_gauge_blockwise` is “currently unused”, but the file uses it at `667`
- Duplicated logic:
  - several “blocking by 1” wrappers (`blockTensor_one_apply`, `mpv_blockTensor_one`, `isIrreducibleTensor_blockTensor_one`, `leftCanonical_blockTensor_one`) look like packaging boilerplate that could be hidden in a more neutral helper module
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - imports both `CanonicalForm.Existence` and `FundamentalTheorem.TransferNormalization`
  - this makes a canonical-form packaging file depend on FT normalization helpers
- Closable `sorry`:
  - none
- Naming:
  - mixed-case theorem names throughout
- `decide` / `native_decide`:
  - none
- `simp` style:
  - mostly okay

### `TNLean/MPS/CanonicalForm/Assembly.lean`

- Size: 1121 lines
- Actual `sorry`: 0
- Long proofs:
  - `exists_tp_primitive_blockDecomp_after_blocking` at `140-246` (~107 lines)
  - `weakFundamentalTheorem_conditional` at `622-703` (~82 lines)
  - `exists_cyclic_sector_decomp_after_blocking` at `845-922` (~78 lines)
  - `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` at `968-1062` (~95 lines)
- Dead code / stale comments:
  - redundant commented block at `1035-1048` restates a theorem that is already proved above; this is documentation drift waiting to happen
- Duplicated logic:
  - file combines reduction, normality preservation, cyclic-sector decomposition, and FT-facing wrapper code in one place
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - strongest canonical-form hotspot
  - imports `FundamentalTheorem.Full`, so a core canonical-form assembly module depends on the full heterogeneous FT
- Closable `sorry`:
  - none
- Naming:
  - theorem names are readable but mostly mixed-case
- `decide` / `native_decide`:
  - none
- `simp` style:
  - not the main issue here

### `TNLean/MPS/CanonicalForm/FromPrimitive.lean`

- Size: 43 lines
- Actual `sorry`: 0
- Long proofs:
  - none
- Dead code / stale comments:
  - none
- Duplicated logic:
  - none significant
- Unnecessary imports:
  - none obvious
- Dependency tangle:
  - light wrapper
- Closable `sorry`:
  - none
- Naming:
  - acceptable
- `decide` / `native_decide`:
  - none
- `simp` style:
  - clean

### `TNLean/MPS/CanonicalForm/CyclicSectorAssembly.lean`

- Size: 75 lines
- Actual `sorry`: 0
- Long proofs:
  - none
- Dead code / stale comments:
  - none
- Duplicated logic:
  - none significant
- Unnecessary imports:
  - none obvious
- Dependency tangle:
  - low
- Closable `sorry`:
  - none
- Naming:
  - acceptable
- `decide` / `native_decide`:
  - none
- `simp` style:
  - clean

### `TNLean/MPS/CanonicalForm/FromPeripheralPrimitive.lean`

- Size: 42 lines
- Actual `sorry`: 0
- Long proofs:
  - none
- Dead code / stale comments:
  - none
- Duplicated logic:
  - none significant
- Unnecessary imports:
  - none obvious
- Dependency tangle:
  - low
- Closable `sorry`:
  - none
- Naming:
  - acceptable
- `decide` / `native_decide`:
  - none
- `simp` style:
  - clean

### `TNLean/MPS/CanonicalForm/CyclicSectors.lean`

- Size: 615 lines
- Actual `sorry`: 0
- Long proofs:
  - `exists_compressedTensor_of_supported_projection` at `121-461` (~341 lines)
  - `exists_blockDecomp_of_commuting_projections` at `517-571` (~55 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - repeated `Sum.inl` / `Sum.inr` casework around `220-231`, `381-430`
  - this should probably be broken into smaller helper lemmas over block matrices
- Unnecessary imports:
  - confirmed removable:
    - `Mathlib.Analysis.Matrix.Spectrum`
    - `Mathlib.Logic.Equiv.Sum`
- Dependency tangle:
  - moderate
- Closable `sorry`:
  - none
- Naming:
  - mostly okay
- `decide` / `native_decide`:
  - none
- `simp` style:
  - controlled, but the file is large enough that proof splitting matters more

### `TNLean/MPS/FundamentalTheorem/Basic.lean`

- Size: 74 lines
- Actual `sorry`: 0
- Long proofs:
  - none
- Dead code / stale comments:
  - none
- Duplicated logic:
  - none significant
- Unnecessary imports:
  - import set looks appropriate
- Dependency tangle:
  - low
- Closable `sorry`:
  - none
- Naming:
  - `fundamentalTheorem_singleBlock` is not `snake_case`
- `decide` / `native_decide`:
  - none
- `simp` style:
  - clean

### `TNLean/MPS/FundamentalTheorem/OverlapConsequences.lean`

- Size: 300 lines
- Actual `sorry`: 0
- Long proofs:
  - the private eventually-proportional overlap argument occupies the main proof block
- Dead code / stale comments:
  - none known after the public proportional-overlap corollaries were deleted
- Duplicated logic:
  - some overlap/spectral normalization arguments are repeated in wrapper files
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - moderate
- Closable `sorry`:
  - none
- Naming:
  - mixed-case theorem names remain in inherited declarations
- `decide` / `native_decide`:
  - none
- `simp` style:
  - mostly fine

### Retired proportional primitive wrapper

This wrapper file has been deleted. Its old purpose was tied to the
proportional-MPV branch, which is now separated from the source-facing
formalization rather than being presented as part of arXiv:1606.00608,
Theorem II.1.

### `TNLean/MPS/FundamentalTheorem/Multi.lean`

- Size: 292 lines
- Actual `sorry`: 0
- Long proofs:
  - none over the 50-line threshold by declaration-span proxy
- Dead code / stale comments:
  - none
- Duplicated logic:
  - several nearby block-diagonal rewrites (`97-110`, `149-160`) could share small helpers
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - moderate but justified
- Closable `sorry`:
  - none
- Naming:
  - mixed-case theorem names throughout
- `decide` / `native_decide`:
  - none
- `simp` style:
  - acceptable

### `TNLean/MPS/FundamentalTheorem/OverlapConvergenceAux.lean`

- Size: 92 lines
- Actual `sorry`: 0
- Long proofs:
  - none
- Dead code / stale comments:
  - none
- Duplicated logic:
  - none significant
- Unnecessary imports:
  - none obvious
- Dependency tangle:
  - low
- Closable `sorry`:
  - none
- Naming:
  - acceptable
- `decide` / `native_decide`:
  - none
- `simp` style:
  - clean

### `TNLean/MPS/FundamentalTheorem/FiniteLength.lean`

- Size: 304 lines
- Actual `sorry`: 0
- Long proofs:
  - `sameMPV_of_sameMPVFrom_of_injective` at `147-286` (~140 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - repeated `Matrix.trace`/linear-map simplification blocks at `225-240`, `234-241`, `268-276`
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - reasonable
- Closable `sorry`:
  - none
- Naming:
  - `SameMPV.sameMPVFrom`, `sameMPVFrom_zero_iff`, `sameMPV_of_sameMPVFrom_of_injective` are mixed-case and inconsistent with the repo’s theorem naming guidance
- `decide` / `native_decide`:
  - none
- `simp` style:
  - some large local `simp only` sets would benefit from helper lemmas

### `TNLean/MPS/FundamentalTheorem/Applications.lean`

- Size: 295 lines
- Actual `sorry`: 0
- Long proofs:
  - none over threshold
- Dead code / stale comments:
  - none
- Duplicated logic:
  - `rotatePhysical_*` lemmas form a coherent cluster; no serious duplication problem
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - acceptable
- Closable `sorry`:
  - none
- Naming:
  - many mixed-case names: `rotatePhysical`, `sameMPV₂_rotatePhysical`, `isIrreducibleForm_rotatePhysical`
- `decide` / `native_decide`:
  - none
- `simp` style:
  - reasonable

### `TNLean/MPS/FundamentalTheorem/TransferNormalization.lean`

- Size: 176 lines
- Actual `sorry`: 0
- Long proofs:
  - none
- Dead code / stale comments:
  - none
- Duplicated logic:
  - none major
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - mild structural smell: this file imports `Multi.lean` just to use `toTensorFromBlocks` / `mpv_toTensorFromBlocks_eq_sum`
  - because `NormalReduction.lean` imports this file, canonical-form packaging inherits that FT dependency
- Closable `sorry`:
  - none
- Naming:
  - acceptable, though theorem names are mixed-case
- `decide` / `native_decide`:
  - none
- `simp` style:
  - controlled

### `TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean`

- Size: 611 lines
- Actual `sorry`: 0
- Long proofs:
  - none over threshold by declaration-span proxy
- Dead code / stale comments:
  - none
- Duplicated logic:
  - repeated coefficient-expansion/sum-manipulation patterns at `263`, `332`, `433-434`, `468`, `474`
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - moderate but understandable
- Closable `sorry`:
  - none
- Naming:
  - mostly acceptable
- `decide` / `native_decide`:
  - none
- `simp` style:
  - wide `simp only` expansion at `433-434`

### Retired equal/proportional Fundamental Theorem file

- Size: 506 lines
- Actual `sorry`: 0
- Long proofs:
  - `fundamentalTheorem_equalMPV_full` at `316-480` (~165 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - `WithLp.ofLp_sum` / `Pi.smul_apply` simplification pattern at `370-371` is repeated later in `Full.lean`
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - moderate
- Closable `sorry`:
  - none
- Naming:
  - mixed-case theorem names throughout
- `decide` / `native_decide`:
  - none
- `simp` style:
  - some large local `simp only` expansions

### `TNLean/MPS/FundamentalTheorem/Full.lean`

- Size: 1344 lines
- Actual `sorry`: 0
- Long proofs:
  - `exists_nondecaying_overlap_of_sameMPV₂_CFBNT` at `152-989` (~838 lines)
  - `blocks_match_of_sameMPV₂_CFBNT` at `990-1328` (~339 lines)
- Dead code / stale comments:
  - none, but the file is far beyond the “should probably split” threshold
- Duplicated logic:
  - repeated `Fin.lt_def` boilerplate at `254`, `267`, `311`, `343`, `592`, `599`, `680`
  - repeated `convert (...).norm using 1; simp only [norm_one/norm_zero]` blocks at `392`, `395`, `398`, `444`, `477`, `480`, `483`, `516`, `561`, `564`, `652`, `653`, `1130`, `1133`, `1188`, `1232`, `1235`, `1275`
  - repeated `intro N; simp only [mpvOverlap]` shells at `409`, `493`, `1147`, `1249`
- Unnecessary imports:
  - none obvious
- Dependency tangle:
  - this is the main FT sink; many other files depend on it
- Closable `sorry`:
  - none
- Naming:
  - mixed-case theorem names
- `decide` / `native_decide`:
  - none
- `simp` style:
  - large `simp only` set at `1019-1022`
- Overall:
  - this is the largest spaghetti hotspot in the audited scope, even though it is sorry-free

### `TNLean/MPS/FundamentalTheorem/CoefficientConvergence.lean`

- Size: 285 lines
- Actual `sorry`: 0
- Long proofs:
  - `proportional_normalized_of_proportional` at `187-243` (~57 lines)
- Dead code / stale comments:
  - none
- Duplicated logic:
  - normalization/renormalization pattern overlaps with `TransferNormalization.lean`
- Unnecessary imports:
  - structural smell rather than unused import: this file imports `Full.lean`, which is heavy for what is partly coefficient algebra
- Dependency tangle:
  - moderate
- Closable `sorry`:
  - none
- Naming:
  - mixed-case theorem names
- `decide` / `native_decide`:
  - none
- `simp` style:
  - acceptable

### `TNLean/MPS/FundamentalTheorem/Periodic.lean`

- Size: 372 lines
- Actual `sorry`: 0
- Long proofs:
  - `fundamentalTheorem_periodic_proportional` at `138-209` (~72 lines)
- Dead code / stale comments:
  - no dead code, but the status comments around “#81 is not yet merged” and “Conditional on #81” are maintenance-sensitive and can go stale
- Duplicated logic:
  - none major
- Unnecessary imports:
  - none obvious
- Dependency tangle:
  - sits on top of heavy `Full` + `SectorDecomposition` infrastructure
- Closable `sorry`:
  - none
- Naming:
  - mixed-case theorem names
- `decide` / `native_decide`:
  - none
- `simp` style:
  - fine

### `TNLean/MPS/FundamentalTheorem/PeriodicOverlap.lean`

- Size: 774 lines
- Actual `sorry`: 7
  - `208`
  - `394`
  - `452`
  - `516`
  - `582`
  - `631`
  - `687`
- Long proofs / unfinished blocks:
  - `exists_cyclic_sector_decomp_after_blocking_of_isPeriodic` at `111-203` (~93 lines)
  - `sectorBlocked_isNormal_of_isPeriodic` at `379-394` (~16 lines, but unfinished)
  - `periodicOverlap_tendsto_zero_of_no_sector_match` at `416-452` (~37 lines, unfinished)
  - `sectorMatch_propagation` at `477-516` (~40 lines, unfinished)
  - `sectorTensor_proportional_of_blockedMatch` at `540-582` (~43 lines, unfinished)
  - `periodicOverlap_gaugeEquiv_of_sector_match` at `599-631` (~33 lines, unfinished)
  - `periodicOverlapDichotomy` at `657-687` (~31 lines, unfinished)
- Dead code / stale comments:
  - no commented-out code blocks, but multiple large proof-outline comment blocks are placeholders rather than finished proofs:
    - `447-451`
    - `574-581`
    - `629-630`
    - `680-686`
- Duplicated logic:
  - the file repeats case analysis in prose and then again in theorem wrappers
  - several theorems are thin orchestrators over missing helper lemmas; once helpers exist, wrappers should be very short
- Unnecessary imports:
  - not confirmed
- Dependency tangle:
  - strongest knot in the audited scope
  - imports both `FundamentalTheorem.Full` and `CanonicalForm.Assembly`
  - `CanonicalForm.Assembly` already imports `FundamentalTheorem.Full`
- Closable `sorry` assessment:
  - most closable:
    - `sectorBlocked_isNormal_of_isPeriodic` (`379-394`)
      - likely derivable from existing cyclic-sector decomposition lemmas in `CanonicalForm/CyclicSectors.lean` plus normality lemmas already present in `Assembly.lean`
    - `periodicOverlap_gaugeEquiv_of_sector_match` (`599-631`)
      - wrapper theorem; should collapse once the two case-3 helpers are proved
    - `periodicOverlapDichotomy` (`657-687`)
      - pure orchestration once case lemmas are available
  - plausible but not obviously short:
    - `periodicSelfOverlap_tendsto` (`204-208`)
      - looks reachable from existing periodic spectral decomposition, but I would not call it a one-lemma close
  - genuinely hard core missing pieces:
    - `periodicOverlap_tendsto_zero_of_no_sector_match`
    - `sectorMatch_propagation`
    - `sectorTensor_proportional_of_blockedMatch`
- Naming:
  - mixed-case theorem names throughout
- `decide` / `native_decide`:
  - none
- `simp` style:
  - not the main issue; unfinished core arguments dominate
- Overall:
  - this is the main unfinished hotspot and the most obvious source of technical debt

## Priority refactor list

1. Split `TNLean/MPS/FundamentalTheorem/Full.lean`.
   - Suggested split:
     - nondecaying-overlap existence
     - block matching / permutation extraction
     - final theorem wrappers

2. Split `TNLean/MPS/CanonicalForm/Assembly.lean`.
   - Suggested split:
     - arbitrary-input reduction
     - blocking/normality preservation
     - cyclic-sector decomposition
     - FT-facing structural wrappers

3. Finish or isolate `TNLean/MPS/FundamentalTheorem/PeriodicOverlap.lean`.
   - At minimum, push the incomplete case-2/case-3 helpers into a dedicated “work in progress” module so the file stops pretending to be near-finished theory.

4. Extract proof helpers for repeated limit/overlap boilerplate from
   `Full.lean`, the retired equal/proportional Fundamental Theorem file, and
   `FiniteLength.lean`.

5. Clean the stale and redundant comments:
   - `NormalReduction.lean:139-145`
   - `Assembly.lean:1035-1048`

6. Remove confirmed unused imports from `CyclicSectors.lean`.

7. Decide whether the repo actually wants theorem names in `snake_case` or whether the docs need to be updated.
   - Right now the code and the documented convention are diverging.
