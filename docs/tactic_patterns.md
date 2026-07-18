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

---

## Rejected

(none yet)

## Retired

(none yet)
