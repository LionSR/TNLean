# Tactic Pattern Ledger

Living registry of repeated proof patterns, maintained under the process in
[`docs/tactic_development.md`](tactic_development.md). Agents and contributors:
**consult the promoted section before writing proofs; append candidates when
you meet repetition; promote when the criteria are met.**

Entry format:

```markdown
### <short-name> — <status>
- **Pattern:** the repeated tactic block (fenced code)
- **Seen:** N occurrences (representative `file:line` list, or scanner output date)
- **Abstraction:** the promoted declaration, or the proposed one for candidates
- **Notes:** goal shape, caveats, line delta after refactor
```

Statuses: `candidate` (recorded, below promotion threshold or not yet
implemented), `promoted` (abstraction exists; call sites refactored),
`retired` (abstraction removed), `rejected` (examined and deliberately not
abstracted — record why, so it is not re-proposed).

---

## Promoted

### mpv_ext — promoted
- **Pattern:** `intro N σ` / `intro N hN σ` prelude for `SameMPV₂` /
  `SameMPV₂Pos` goals.
- **Abstraction:** `mpv_ext` (elab tactic, `TNLean/MPS/Tactic/Basic.lean`).
- **Notes:** elab rather than macro because it inspects the goal to
  distinguish the two predicate forms.

### block_words — promoted
- **Pattern:** repeated `simp only [...]` lists normalizing direct/iterated
  blocking maps and `wordOfBlock` expressions.
- **Abstraction:** `@[mps_block_words]` simp set + `block_words` macro
  (`TNLean/MPS/Tactic/Basic.lean`).
- **Notes:** used across `MPS/Core/Blocking.lean`,
  `MPS/Core/BlockingInfrastructure.lean`, `MPS/ParentHamiltonian/BlockStrip.lean`.

### transfer_simp — promoted
- **Pattern:** unfolding `transferMap A X` to `∑ i, A i * X * (A i)ᴴ`.
- **Abstraction:** `@[mps_transfer]` simp set + `transfer_simp` macro
  (`TNLean/MPS/Tactic/Basic.lean`).

---

## Candidates

Seeded from `scripts/tactic_pattern_scan.py` (2026-07-18 scan; re-run for
current counts and full location lists).

### product_span_transport — candidate
- **Pattern:** transport membership in the span of fixed-length products through
  a linear map that preserves the identity and the relevant products, using
  `Submodule.span_induction` with separate generator, zero, addition, and scalar
  cases.
- **Seen:** 2 occurrences: the reindexing step in
  `IsPositiveMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span`
  and the block-diagonal step in
  `IsPositiveDirectSumMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span`
  (2026-07-19). This is below the rule-of-three promotion threshold.
- **Abstraction (proposed):** a lemma transporting a product-span membership
  statement through a linear map, parameterized by the product-compatibility
  equation. Scout Mathlib's `Submodule.map_span` and `Submodule.map_mono` API
  before introducing a project lemma.
- **Notes:** The two current instances use matrix reindexing and block-diagonal
  embedding. Record before a third coordinate-transport proof appears; confirm
  that their product-family goal shapes agree before promotion.

### matrix_entry_cases — candidate
- **Pattern:**
  ```
  ext i j
  by_cases hij : i = j
  · subst hij
    ...
  ```
- **Seen:** 10 occurrences across >= 4 files
  (`TNLean/Algebra/HermitianHelpers.lean:115`,
  `TNLean/Algebra/HermitianHelpers.lean:144`,
  `TNLean/Channel/ChoiJamiolkowski.lean:407`,
  `TNLean/Channel/ChoiTypeMap.lean:308`, +6 more).
- **Abstraction (proposed):** cross-cutting macro `matrix_entry_cases`
  (in a new `TNLean/Tactic/Basic.lean`) that performs the entrywise
  extensionality plus diagonal/off-diagonal split, leaving the two goals
  named. Check first whether the diagonal-matrix Mathlib API
  (`Matrix.diagonal_apply_ne` etc.) turns specific call sites into lemmas
  instead. Also try `ext i j <;> grind` at a few call sites (with
  `Matrix.diagonal_apply`-family lemmas `@[grind =]`-tagged if needed) —
  the case split and entry arithmetic are squarely in `grind`'s scope;
  unverified pending a build-capable session.

### clm_norm_instances — candidate
- **Pattern:**
  ```
  letI : NormedAddCommGroup (V →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
  letI : SeminormedRing (V →L[ℂ] V) := ContinuousLinearMap.toSeminormedRing
  letI : NormedRing (V →L[ℂ] V) := ContinuousLinearMap.toNormedRing
  letI : NormedSpace ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
  letI : NormedAlgebra ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedAlgebra
  ```
- **Seen:** 5 occurrences (`TNLean/MPS/RFP/BNTOrthogonality.lean:423`,
  `TNLean/Spectral/MPVOverlapDecay.lean:174`,
  `TNLean/Spectral/PrimitiveOverlap.lean:101`,
  `TNLean/Spectral/TransferOperatorGap.lean:459`, +1).
- **Abstraction (proposed):** not a tactic — investigate why these instances
  need `letI` at all (likely an instance-resolution gap); either fix the
  underlying instance visibility once in a shared file, or provide a
  `clm_norm_instances` macro expanding to the block.

### peps_prod_entry_congr — candidate
- **Pattern:**
  ```
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  ```
- **Seen:** 12 occurrences across PEPS files
  (`TNLean/PEPS/NormalFundamentalTheorem.lean:106`,
  `TNLean/PEPS/RegionBlock/InsertResidual.lean:468`,
  `TNLean/PEPS/RegionBlock/Recovery.lean:239`, +9 more).
- **Abstraction (proposed):** likely a missing congruence lemma for
  PEPS region products rather than a tactic; state it once in
  `TNLean/PEPS/RegionBlock/` and `apply` it.

### filter_sum_split — candidate
- **Pattern:**
  ```
  · refine Finset.sum_congr rfl (fun η hη => ?_)
    rw [Finset.mem_filter] at hη
    rw [if_pos hη.2]
  · refine Finset.sum_eq_zero (fun η hη => ?_)
    rw [Finset.mem_filter] at hη
    rw [if_neg hη.2, smul_zero]
  ```
- **Seen:** 5 occurrences in `TNLean/PEPS/RegionBlock/`
  (`ThreeBlockResonate.lean:682`, `ThreeBlockResonate2.lean:452`,
  `UnionInjectivityGeneral.lean:505`, +2).
- **Abstraction (proposed):** a lemma of the shape
  `∑ η in s.filter p, (if p η then f η else 0) • g η = ...` — scout
  Mathlib's `Finset.sum_filter` / `Finset.sum_ite_of_true` family first.

### two_positive_bilinear_checks — candidate
- **Pattern:** alternating `· intro i / simp` and
  `· intro i u v / simp [mul_assoc, mul_add]` blocks discharging
  bilinearity side goals.
- **Seen:** 9 occurrences, all in `TNLean/Channel/Schwarz/TwoPositive.lean`
  (lines 359-396).
- **Abstraction (proposed):** single-file duplication — restructure the
  underlying definition to take a bundled bilinear map, or a local
  `macro`/`have` inside the file. Below cross-file threshold; promote only
  if the pattern escapes `TwoPositive.lean`. Note: `grind` is unlikely to
  close these directly (matrix multiplication is noncommutative and its
  ring solver is commutative); the bundled-bilinear-map restructuring is
  the better bet.

### region_cover_union_cases — candidate
- **Pattern:**
  ```
  rcases Finset.mem_union.mp hcover with hrb | hc
  · rcases Finset.mem_union.mp hrb with hr | hbl
  · exact absurd hr hwnotred
  ```
- **Seen:** 9 occurrences in `TNLean/PEPS/RegionBlock/`
  (`CoarseThreeSite3.lean:89`, `ThreeBlockReconcile.lean:244`,
  `ThreeBlockResonate.lean:96`, +6).
- **Abstraction (proposed):** a case-elimination lemma on the three-region
  cover (membership in red/blue/crossing regions) stated once in the
  RegionBlock development.

### spectral_double_sum_continuity — candidate
- **Pattern:**
  ```
  apply continuousOn_finsetSum Finset.univ
  intro i _
  apply continuousOn_finsetSum Finset.univ
  intro j _ t ht
  have ht0 : 0 < t := ht
  have hα : 0 < α i := hA.eigenvalues_pos i
  have hβ : 0 < β j := hB.eigenvalues_pos j
  have hden : α i + t * β j ≠ 0 := by positivity
  ```
- **Seen:** 3 occurrences in
  `TNLean/Analysis/RelativeEntropyResolventIntegral.lean` (lines 608, 637,
  and 846 in the initial scan).
- **Abstraction (proposed):** a local lemma reducing continuity of a finite
  spectral double sum on `(0, ∞)` to continuity of one summand, while supplying
  positivity of the two eigenvalues and nonvanishing of
  `α i + t * β j`.  The repetition is presently confined to one file, so
  retain it as a candidate rather than adding a general tactic.

---

## Rejected

(none yet)

## Retired

### invariant-subspace two-block fork — retired
- **Pattern:** the general and strict invariant-subspace decompositions repeated the
  spectral split, block construction, and MPV calculation.
- **Seen:** 2 full proof paths in
  `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean`.
- **Abstraction:** the private semantic construction
  `exists_twoBlock_decomp_of_lowerZero_aux`; the strict public theorem adds only
  positivity and arithmetic for the strict dimension bounds.
- **Notes:** Counting proof lines inclusively from `:= by` through the final proof line,
  the two public implementations had 307 + 243 = 550 lines. The shared construction
  and two projections have 342 + 4 + 8 = 354 lines, a net reduction of 196 lines
  (35.6%). Both public theorem statements are unchanged.
