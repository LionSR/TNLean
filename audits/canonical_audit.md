# Canonical-form chapters: read-only audit

Scope: blueprint chapters `ch08_canonical.tex`, `ch09_block_perm.tex`,
`ch11b_after_blocking.tex` and their Lean files. No files modified.

---

## 1. Summary (~10 lines)

* The PGVWC07 stack (one `structure` + 14 `exists_pgvwc07_*` theorems across
  `NormalReduction/TPGauge.lean` and `NormalReduction/WeightNormalization.lean`)
  is **entirely orphan**: no Lean file outside `NormalReduction/` and no
  blueprint chapter outside `ch08_canonical.tex` consumes any `exists_pgvwc07_*`
  or `PGVWC07PositiveLengthWitness.*` declaration. It exists solely to match
  the literal statement of \cite[Th:TIcanonical]{PerezGarcia2007Matrix}.
* The FT proof (`ch11_fundamental_theorem_proof.tex`) reaches Chapter 9 only
  through `thm:tp_gauge_arbitrary` →
  `thm:exists_common_blocked_cyclic_sector_family*` →
  `thm:has_primitive_irreducible_cyclic_sectors_tp_irr`. None of those go
  through PGVWC07.
* Within the PGVWC07 stack a chain of seven intermediate "with_zeroTail",
  "_bondDimBound", "_posMPV_bondDimBound", "_or_forall_pos_mpv_eq_zero",
  "_allow_empty" theorems is exposed in the blueprint; only one
  (`_allow_empty`) is plausibly worth a public statement.
* Chapter 11b has four parallel `ft_after_blocking_*` theorems
  (`_per_block_cyclic`, `_common_blocked_cyclic`, `_reindexed_common_sector`,
  `_common_length_common_sector`) and one `_structural`. Only
  `_common_length_common_sector_theorem` is consumed by Chapter 13's FT proof
  (transitively through ch11's `unconditional_common_primitive_irreducible_blocks`).
* `thm:cpgsv_canonical_form_source` in ch08 is `\notready` and unreferenced.
* The Lean module `SectorComparison/CommonSectorTransport.lean` (679 lines) is
  largely glue between `_of_blockwise / _of_word_eq /
  _of_groupedBlockCastAgrees / _of_reindexed` formulations. After the
  unconditional `flattenWordOfBlock_cast_eq` is proved the four are
  interderivable; only one needs to be public.
* Recommended action: keep
  `thm:pgvwc07_ti_canonical_form` (= `_allow_empty`) as the single
  blueprint-visible PGVWC07 statement; demote the rest to file-local Lean
  lemmas. Delete `thm:cpgsv_canonical_form_source`. Collapse the
  `ft_after_blocking_*` cluster around
  `_common_length_common_sector_theorem`. Inline the
  `_of_blockwise/_of_word_eq/_of_groupedBlockCastAgrees` triplets into the
  single `_of_reindexed` form.

---

## 2. PGVWC07 stack classification

Convention: **PRIMARY** = blueprint-visible, mathematically distinct;
**INTERMEDIATE PLUMBING** = used only by the next member of the stack;
**LEGACY DEAD BRANCH** = no consumers at all (Lean-file or blueprint).

The dependency edges below were verified with
`grep -rn 'NAME' TNLean blueprint/src` for each declaration. None of the
listed declarations is consumed in `TNLean/MPS/FundamentalTheorem/**`,
`TNLean/MPS/CanonicalForm/SectorComparison/**`,
`TNLean/MPS/CanonicalForm/CyclicSectors/**`,
`TNLean/MPS/BNT/**`, or in any blueprint chapter other than
`ch08_canonical.tex`.

| Lean name | Blueprint label | Classification | Downstream consumers |
|---|---|---|---|
| `exists_pgvwc07_unital_dualDiag_data_of_irreducible` | `thm:pgvwc07_irreducible_unital_dual_package` | INTERMEDIATE PLUMBING | only `exists_pgvwc07_unital_dualDiag_blockwise` (Lean) |
| `exists_pgvwc07_unital_dualDiag_blockwise` | `thm:pgvwc07_blockwise_unital_dual_package` | INTERMEDIATE PLUMBING | only `exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail` |
| `exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail` | `thm:pgvwc07_arbitrary_zero_tail_unital_dual_package` | INTERMEDIATE PLUMBING | only `_with_zeroTail_bondDimBound` |
| `exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound` | `thm:pgvwc07_arbitrary_zero_tail_unital_dual_bond_dim_bound` | INTERMEDIATE PLUMBING | only `_posMPV_bondDimBound` and `exists_pgvwc07_normalized_exact_form_after_rescaling_with_zeroTail` |
| `exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound` | `thm:pgvwc07_arbitrary_positive_length_unital_dual_bond_dim_bound` | INTERMEDIATE PLUMBING | only `exists_pgvwc07_positiveLengthWitness` |
| `exists_pgvwc07_positiveLengthWitness` | `thm:pgvwc07_positive_length_witness` | INTERMEDIATE PLUMBING | only `WeightNormalization.lean` (witness packaging) |
| `PGVWC07PositiveLengthWitness` (`structure`) | `def:pgvwc07_positive_length_witness` | INTERMEDIATE PLUMBING (data tuple bundling all witness fields; never used outside `NormalReduction/`) | only `WeightNormalization.lean` |
| `PGVWC07PositiveLengthWitness.weight_ne_zero` | `lem:pgvwc07_positive_length_witness_weight_ne_zero` | LEGACY DEAD BRANCH | unreferenced (grep result: only its definition site). Inlinable in one line. |
| `PGVWC07PositiveLengthWitness.exists_weight_normalization` | `thm:pgvwc07_positive_length_witness_weight_normalization` | INTERMEDIATE PLUMBING | only `_projective`, `_exact_form_after_rescaling_of_exists_ne_zero_mpv`, `_with_zeroTail` |
| `PGVWC07PositiveLengthWitness.exists_weight_normalization_projective` | `thm:pgvwc07_positive_length_witness_weight_normalization_projective` | INTERMEDIATE PLUMBING | only `exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv` |
| `PGVWC07PositiveLengthWitness.block_count_pos_of_exists_ne_zero_mpv` | `lem:pgvwc07_positive_length_witness_nonempty_of_nonzero_mpv` | INTERMEDIATE PLUMBING | only the `_of_exists_ne_zero_mpv` projective and exact-form theorems |
| `exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv` | `thm:pgvwc07_nonzero_normalized_projective_form` | INTERMEDIATE PLUMBING | only `_projective_form_or_forall_pos_mpv_eq_zero` |
| `exists_pgvwc07_normalized_exact_form_after_rescaling_of_exists_ne_zero_mpv` | `thm:pgvwc07_nonzero_normalized_exact_rescaled_form` | INTERMEDIATE PLUMBING | only `_or_forall_pos_mpv_eq_zero` |
| `exists_pgvwc07_normalized_exact_form_after_rescaling_or_forall_pos_mpv_eq_zero` | `thm:pgvwc07_exact_rescaled_form_zero_nonzero_dichotomy` | INTERMEDIATE PLUMBING | only `_allow_empty` |
| `exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty` | `thm:pgvwc07_ti_canonical_form` (the chosen primary) | **PRIMARY** | source-faithful PGVWC07 statement; not consumed by FT path but is the headline theorem for the chapter |
| `exists_pgvwc07_normalized_exact_form_after_rescaling_with_zeroTail` | `thm:pgvwc07_exact_rescaled_form_with_zero_tail` | LEGACY DEAD BRANCH | grep: not referenced in any other Lean file nor in any later blueprint chapter; ch08 mentions it only in a forward reference from the primary theorem's narrative |
| `exists_pgvwc07_normalized_projective_form_or_forall_pos_mpv_eq_zero` | `thm:pgvwc07_projective_form_zero_nonzero_dichotomy` | LEGACY DEAD BRANCH | grep: only the file that defines it; no Lean or blueprint consumer |

Verification commands run for the LEGACY DEAD BRANCH entries:

```
grep -rn 'exists_pgvwc07_normalized_exact_form_after_rescaling_with_zeroTail'  TNLean blueprint
grep -rn 'exists_pgvwc07_normalized_projective_form_or_forall_pos_mpv_eq_zero' TNLean blueprint
grep -rn 'PGVWC07PositiveLengthWitness.weight_ne_zero'                         TNLean blueprint
```

Each returned only the definition site (plus the import-summary docstring of
`NormalReduction.lean` and the `thm:pgvwc07_*` blueprint entries that refer
to them).

**Refactor recommendation for the PGVWC07 stack.** Keep exactly one
blueprint-visible PGVWC07 statement (`thm:pgvwc07_ti_canonical_form`,
Lean: `exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty`).
Demote every other entry in this stack to a Lean-internal lemma without a
`\lean{...}` blueprint tag — they are private to the proof of
`_allow_empty`. The `with_zeroTail` and `_projective_form_or_forall_pos_mpv_eq_zero`
variants are unused and can be deleted.

---

## 3. Duplicate / parallel naming clusters

### Cluster A — PGVWC07 weight-normalization variants

| Member | Differs from primary by |
|---|---|
| `exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty` | **(primary)** |
| `_after_rescaling_with_zeroTail` | retains an explicit zero block summand in the conclusion |
| `_projective_form_or_forall_pos_mpv_eq_zero` | proportional MPV instead of exact after global scalar |
| `_or_forall_pos_mpv_eq_zero` | nonzero/zero dichotomy unstapled from the empty-family conclusion |
| `_of_exists_ne_zero_mpv` (exact and projective) | hypothesis `∃ N σ, V^{(N)}(A)_σ ≠ 0` instead of the empty-block escape |

**Primary entry point to remember:** `_after_rescaling_allow_empty`.
Drop the four others from the blueprint (they remain available in the Lean
source as local lemmas, or can be deleted; cf. §2).

### Cluster B — PGVWC07 unital-dualDiag chain

| Member | Differs from primary by |
|---|---|
| `_data_of_irreducible` | single-block input |
| `_blockwise` | finite-direct-sum input, unit weights |
| `_from_arbitrary_with_zeroTail` | arbitrary input, zero block kept |
| `_from_arbitrary_with_zeroTail_bondDimBound` | adds the length-zero `D_0 + Σ D_k = D` identity |
| `_from_arbitrary_posMPV_bondDimBound` | strips the zero block, keeps the bound on `N ≥ 1` |

**Primary entry point to remember:** `_from_arbitrary_posMPV_bondDimBound`
(this is what feeds `exists_pgvwc07_positiveLengthWitness`).
All preceding ones should be Lean-internal `private` / file-local lemmas
without blueprint entries.

### Cluster C — `cyclic_sector_decomp_*` triple

| Member | Lean name | Public role |
|---|---|---|
| `thm:cyclic_sector_decomp_after_blocking` | `exists_cyclic_sector_decomp_after_blocking` | the underlying constructor (used by `_irr_tp` and `_prim_irr`) |
| `thm:cyclic_sector_decomp_irr_tp` | `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` | LEGACY: unused outside `CyclicSectorDecomposition.lean` |
| `thm:cyclic_sector_decomp_irr_tp_prim_irr` | `exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` | feeds `hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor` (the actual FT-path input) |

**Primary entry point to remember:** `_prim_irr`. The `_irr_tp` version is
strictly weaker and is not used anywhere downstream — propose demoting to
private.

### Cluster D — `ft_after_blocking_*` family

| Member | Position in dep chain | External consumer? |
|---|---|---|
| `thm:ft_after_blocking_structural` | duplicates `thm:tp_primitive_blockdecomp` for two tensors | no (only `\notready` narrative references) |
| `thm:ft_after_blocking_per_block_cyclic_live_zero_tail` | input to `_common_blocked_cyclic` and `_common_length_common_sector` | only inside ch11b |
| `thm:ft_after_blocking_common_blocked_cyclic_live_zero_tail` | input to `_reindexed_common_sector` | only inside ch11b |
| `thm:ft_after_blocking_reindexed_common_sector_live_zero_tail` | **never used** (verified by grep) | LEGACY DEAD |
| `thm:ft_after_blocking_common_length_common_sector_theorem` | **the consumed one** | used by `thm:after_blocking_common_primitive_irreducible_blocks_reindexed` and (transitively) by ch11's `thm:unconditional_common_primitive_irreducible_blocks` |
| `thm:ft_after_blocking_common_length_common_sector_reindexed` | restates the above with a word identification baked in | LEGACY DEAD (no consumer) |

**Primary entry point to remember:** `_common_length_common_sector_theorem`.
The `_per_block_cyclic_live_zero_tail` and
`_common_blocked_cyclic_live_zero_tail` members are intermediate; they are
fine to keep as proof steps but should not carry their own blueprint
theorem entries (they should be folded into the proof of
`_common_length_common_sector_theorem`).

### Cluster E — zero-tail transport quadruple
(`TNLean/MPS/CanonicalForm/SectorComparison/CommonSectorTransport.lean`,
all four variants exposed via `\lean{...}` in
`thm:zero_tail_common_flat_of_blocked_word_comparison`)

| Lean name | Differs from primary by |
|---|---|
| `zeroTail_commonFlat_of_blockwise` | takes a per-block `SameMPV₂` hypothesis |
| `zeroTail_commonFlat_of_word_eq` | takes a per-block word-equation hypothesis |
| `zeroTail_commonFlat_of_groupedBlockCastAgrees` | takes the `groupedBlockCastAgrees` predicate |
| `zeroTail_commonFlat_of_reindexed` | takes a `SameMPV₂` between two `toTensorFromBlocks` expressions (the form actually used downstream) |

The other three are intermediate lemmas. Once
`CommonGroupedBlockCastHypothesis.of_flattenWordOfBlock_cast_eq` is proved
(it is — unconditionally), only `_of_reindexed` is needed externally.
**Primary entry point:** `_of_reindexed`; the other three should be
private. Symmetric for the `_commonFlatAt_*` and
`_blockTensor_commonFlatAt_*` `\lean{...}` lists in the same blueprint
theorem.

### Cluster F — repeated bracket of "MPV phase cover" lemmas in ch11
(`lem:common_phase_cover_of_block_matching`,
`lem:common_phase_cover_of_equiv_phase`,
`lem:nonzero_block_span_eq_of_common_phase_cover`,
`lem:mpv_common_phase_cover_span_eq`,
`lem:nonzero_block_span_eq_of_block_matching`,
`lem:nonzero_block_span_eq_of_equiv_phase`)

The pair `_of_block_matching` / `_of_equiv_phase` exists in three flavours
(common-phase-cover, span-equality, and combined). Only the
`_of_block_matching` chain is consumed by
`thm:bnt_sectorDecomp_pair_overlapSpan_of_commonPhaseCover`. The
`_of_equiv_phase` chain is not consumed by ch11/ch13. Recommend marking the
`_of_equiv_phase` variants as auxiliary (no blueprint entry).

---

## 4. CPGSV17a Fundamental-Theorem bridge map

### 4.1 What the FT proof actually consumes

Tracing `\uses{...}` from `ch11_fundamental_theorem_proof.tex` outward:

```
ch11_fundamental_theorem_proof.tex
├── thm:unconditional_common_primitive_irreducible_blocks  [line 858]
│   └── thm:after_blocking_common_primitive_irreducible_blocks_reindexed  [ch11b, line 822]
│       └── thm:ft_after_blocking_common_length_common_sector_theorem  [ch11b, line 660]
│           ├── thm:ft_after_blocking_per_block_cyclic_live_zero_tail  [ch11b, line 511]
│           │   ├── thm:tp_gauge_arbitrary               [ch08, line 1359]
│           │   │   ├── thm:zero_block_separation       [ch11b, line 52]
│           │   │   │   └── thm:irred_decomp             [ch08, line 441]
│           │   │   └── thm:tp_data_irreducible          [ch08]
│           │   ├── thm:nonzero_block_zero_tail_identity [ch11b, line 405]
│           │   └── thm:has_primitive_irreducible_cyclic_sectors_tp_irr [ch08, line 2004]
│           │       └── thm:cyclic_sector_decomp_irr_tp_prim_irr [ch08, line 1481]
│           ├── thm:exists_common_blocked_cyclic_sector_family_common_multiple [ch08, line 2072]
│           ├── thm:zero_tail_to_tensor_from_blocks_block_power [ch11b]
│           ├── thm:nonzero_block_block_power_zero_tail_identity [ch11b]
│           ├── thm:common_blocked_cyclic_sector_reindexed_samempv [ch08]
│           └── thm:common_blocked_cyclic_sector_derived_properties [ch08]
└── (BNT comparison lemmas, all internal to ch11/ch10)
```

### 4.2 Bridge questions answered

* **Does `thm:pgvwc07_ti_canonical_form` feed into the FT proof?**
  **No.** The label appears in `ch08_canonical.tex` only.
  `grep -rn 'thm:pgvwc07_ti_canonical_form' blueprint/src` returns only
  its own definition site and one self-referential paragraph. There is
  no `\uses{thm:pgvwc07_ti_canonical_form}` anywhere in `blueprint/src/`.

* **Is the only path used by the FT proof through `thm:tp_primitive_blockdecomp`?**
  Almost. The FT proof reaches the same content one level higher, via
  `thm:after_blocking_common_primitive_irreducible_blocks_reindexed`,
  which uses `thm:ft_after_blocking_common_length_common_sector_theorem`,
  not `thm:tp_primitive_blockdecomp` directly. (The two share the same
  upstream theorems `thm:tp_gauge_arbitrary`, `thm:common_blocking_period`,
  `thm:zero_tail_to_tensor_from_blocks_block_power`.)
  `thm:tp_primitive_blockdecomp` is itself only consumed by the
  one-tensor-flavoured `thm:ft_after_blocking_structural`, which is
  unconsumed (see Cluster D).

* **Does the PGVWC07 stack join the CPSV stack anywhere?**
  No. The two stacks share only the shallow common dependencies
  `def:irreducible_tensor`, `def:tp_kraus`, `def:transfer_map`,
  `def:same_mpv2`, and `thm:irred_decomp`. The PGVWC07 stack uses the
  **unital** orientation `Σ A^i (A^i)†=Id`; the CPSV / FT stack uses the
  **left-canonical** TP orientation `Σ (A^i)† A^i=Id`. There is no
  blueprint or Lean reduction that takes a PGVWC07 conclusion as a
  hypothesis of a downstream theorem in ch11b or ch11.

**Conclusion: the PGVWC07 stack is parallel and not bridged to the
CPGSV17a FT chain.** The chapter preface should state this explicitly:
the PGVWC07 stack reproduces the literal statement of
\cite[Th:TIcanonical]{PerezGarcia2007Matrix} as a source-faithful target,
and the canonical-form reduction used by Chapter 13's FT proof goes
through Chapter 12 / `thm:tp_primitive_blockdecomp` /
`thm:tp_gauge_arbitrary` / `thm:common_blocking_period` /
`thm:has_primitive_irreducible_cyclic_sectors_tp_irr` instead.

### 4.3 `thm:cpgsv_canonical_form_source` (ch08 line 108, `\notready`)

* Grep result: defined once, referenced twice in the same chapter
  (lines 172 and 185), nowhere else.
* **No downstream `\uses{thm:cpgsv_canonical_form_source}` anywhere in
  `blueprint/src/`.**
* Recommendation: replace the `\begin{theorem}...\notready` block with
  a `\begin{remark}` that cites
  \cite[Section~II.C]{Cirac2017MPDO_AnnPhys} as the source statement,
  and points the reader at `thm:tp_primitive_blockdecomp` /
  `thm:paperbnt_supplier_after_blocking` as the closest checked
  formalizations.

---

## 5. Concrete refactor actions, ordered by safety

The orchestrator should apply these in this order; each step is locally
verifiable.

### Step 5.1 — blueprint-only (safest, no Lean recompile)

1. **Delete `thm:cpgsv_canonical_form_source`** (`ch08_canonical.tex`
   lines 108–168). Replace with a `\begin{remark}` of two sentences
   citing \cite[Section~II.C]{Cirac2017MPDO_AnnPhys} and pointing at
   `thm:tp_primitive_blockdecomp` and
   `thm:paperbnt_supplier_after_blocking`. Update the two intra-chapter
   references at lines 172 and 185.
2. **Demote 11 of the 14 PGVWC07 blueprint entries** (those classified
   INTERMEDIATE PLUMBING or LEGACY DEAD BRANCH in §2). For each:
   * Remove the `\begin{theorem}...\end{theorem}` block and its
     companion `\begin{proof}...\end{proof}`.
   * Leave the corresponding Lean theorem in place (it remains a
     well-named internal lemma).
   * Re-state the closure as a single sentence in the proof sketch of
     `thm:pgvwc07_ti_canonical_form`.
   Specifically, drop from the blueprint:
   ```
   thm:pgvwc07_irreducible_unital_dual_package
   thm:pgvwc07_blockwise_unital_dual_package
   thm:pgvwc07_arbitrary_zero_tail_unital_dual_package
   thm:pgvwc07_arbitrary_zero_tail_unital_dual_bond_dim_bound
   thm:pgvwc07_arbitrary_positive_length_unital_dual_bond_dim_bound
   thm:pgvwc07_positive_length_witness
   thm:pgvwc07_positive_length_witness_weight_normalization
   thm:pgvwc07_positive_length_witness_weight_normalization_projective
   thm:pgvwc07_nonzero_normalized_projective_form
   thm:pgvwc07_nonzero_normalized_exact_rescaled_form
   thm:pgvwc07_exact_rescaled_form_zero_nonzero_dichotomy
   thm:pgvwc07_exact_rescaled_form_with_zero_tail
   thm:pgvwc07_projective_form_zero_nonzero_dichotomy
   lem:pgvwc07_positive_length_witness_weight_ne_zero
   lem:pgvwc07_positive_length_witness_nonempty_of_nonzero_mpv
   def:pgvwc07_positive_length_witness   ← this is the bundled `structure`; demote to Lean-only
   ```
   Keep `thm:pgvwc07_ti_canonical_form` (the `_allow_empty` headline).
3. **Demote `thm:ft_after_blocking_reindexed_common_sector_live_zero_tail`
   and `thm:ft_after_blocking_common_length_common_sector_reindexed`**
   (both unconsumed; see Cluster D in §3). Delete their blueprint
   entries; leave Lean declarations in place.
4. **Demote `thm:ft_after_blocking_structural`** (line 261 of ch11b)
   to a remark. Its Lean counterpart
   `afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂` is unused
   outside its definition file.
5. **Tighten the chapter prefaces** of `ch08_canonical.tex`,
   `ch09_block_perm.tex`, `ch11b_after_blocking.tex` per
   `docs/prose_style.md`:
   * `ch08`: replace the four meta-paragraphs (lines 1–185) with a
     single `\section{Scope}` (about 8 lines): names the source
     theorem, states the unital vs left-canonical orientation
     convention, and lists the headline statements of the chapter
     (`thm:pgvwc07_ti_canonical_form`, `thm:irred_decomp`,
     `thm:CFII_data`, `thm:cyclic_sector_decomp_irr_tp_prim_irr`,
     `thm:tp_gauge_arbitrary`, `thm:exists_normal_canonical_form`).
     Drop banned words "package" (occurs in three theorem titles —
     `pgvwc07_irreducible_unital_dual_package`,
     `pgvwc07_blockwise_unital_dual_package`,
     `pgvwc07_arbitrary_zero_tail_unital_dual_package` — already
     scheduled for removal in 5.1.2).
   * `ch09`: cut the footnote on line 17 (move to a LaTeX comment;
     paper-gap reference belongs in a comment, not in chapter prose).
     The "scope distinction" sentence currently spans lines 7–18 and
     repeats itself in `rem:pgvwc07_vs_local_cf` (line 340) — keep
     only the remark.
   * `ch11b`: lines 3–14 contain a five-sentence preface ending in
     "those chapters no longer provide hypotheses for the
     Fundamental-Theorem comparison." This phrasing repeats the
     equivalent paragraph at the top of ch11. Replace with one
     `\section{Scope}` of three sentences naming the two outputs
     of the chapter: `thm:tp_primitive_blockdecomp` and
     `thm:ft_after_blocking_common_length_common_sector_theorem`.
6. **Sweep the "package" / "data" / "assembly" wording.** Per
   `docs/prose_style.md` §2 these are banned. Affected blueprint
   theorem titles (verified by grep `Definition\[.*[Dd]ata` and
   `[Pp]ackage` in the three chapters):
   * "unital and dual-diagonal data" → already removed in 5.1.2.
   * `thm:pgvwc07_irreducible_unital_dual_package`,
     `thm:pgvwc07_blockwise_unital_dual_package`,
     `thm:pgvwc07_arbitrary_zero_tail_unital_dual_package` →
     already removed in 5.1.2.
   * `def:pgvwc07_positive_length_witness` "positive-length PGVWC07
     canonical-form witness" — the bundled structure stays in Lean,
     but the blueprint definition is removed (see 5.1.2).
   * In ch11_fundamental_theorem_proof.tex the term "MPV phase cover
     data" appears in the `def:mpv_common_phase_cover` definition
     paragraph (line 605–615); the surrounding paragraphs use "data"
     non-vaguely (it refers to the bundled tuple); per
     `docs/prose_style.md` §3 this is allowed.

### Step 5.2 — Lean refactor (touches no math content)

7. **Move PGVWC07 declarations to a Lean-internal namespace.** Rename
   `NormalReduction/TPGauge.lean` decls that are no longer
   blueprint-visible into a `namespace MPSTensor.PGVWC07` and prefix
   with `_aux_` (or move into a new file
   `NormalReduction/Internal/PGVWC07Stack.lean`). This leaves the
   public API as exactly
   * `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty`
     (kept; matches `thm:pgvwc07_ti_canonical_form`).
   * `MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail` (kept;
     consumed by `CommonSectorData.lean` and `TPPrimitiveReduction.lean`).
   No compile risk: every non-exported declaration loses only its
   blueprint tag, not its Lean callers (which are all in the same
   sub-folder).
8. **Inline the three duplicate `zeroTail_commonFlat_of_*` lemmas.**
   In `SectorComparison/CommonSectorTransport.lean`, mark
   `zeroTail_commonFlat_of_blockwise`,
   `zeroTail_commonFlat_of_word_eq`, and
   `zeroTail_commonFlat_of_groupedBlockCastAgrees` `private`
   (and likewise their `_commonFlatAt_*` and `sameMPV₂Pos_*` siblings).
   The only public statement needed is `_of_reindexed`. Update the
   `\lean{...}` block of
   `thm:zero_tail_common_flat_of_blocked_word_comparison` to list one
   declaration. Compile risk: low — the three "_of_blockwise/_of_word_eq
   /_of_groupedBlockCastAgrees" variants are not referenced outside
   the same file (verified by `grep -rn ... TNLean`).
9. **Demote `exists_blockTensor_isPrimitive` and
   `exists_blockTensor_leftCanonical_isPrimitive`** in
   `CanonicalForm/Existence.lean` lines 216, 232 — these are `NeZero`-
   wrappers around `exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor`
   and are unused outside that file. Either inline at the one call
   site or make them `private`. No blueprint impact (they carry no
   `\lean{...}` blueprint tag).
10. **Demote `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`**
    (`SectorComparison/CyclicSectorDecomposition.lean` line 79). It is
    unused outside its definition file; the consumed entry is
    `exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`.
    Mark `private` or delete; drop the blueprint entry
    `thm:cyclic_sector_decomp_irr_tp` (Cluster C in §3).
11. **Reduce the `CommonSectorRelabelingHypothesis` /
    `CommonGroupedBlockCastHypothesis` pair to one definition.**
    `CommonSectorTransport.lean` lines 365 and 381 both define a
    `Prop`-level abbreviation; their relationship is captured by
    `CommonGroupedBlockCastHypothesis.toRelabelingHypothesis` and
    `of_flattenWordOfBlock_cast_eq` proves the latter unconditionally.
    Recommend collapsing to a single `private abbrev` and inlining the
    proof of `unconditional_commonPrimitiveIrreducibleBlocks` so it
    does not pass through the abbrev at all.

### Step 5.3 — deletions (only after Steps 5.1–5.2 land)

12. After Step 5.1, **delete the dead Lean theorems** identified as
    LEGACY DEAD BRANCH in §2 once nothing references their `\lean{...}`
    tags from the blueprint:
    * `exists_pgvwc07_normalized_exact_form_after_rescaling_with_zeroTail`
    * `exists_pgvwc07_normalized_projective_form_or_forall_pos_mpv_eq_zero`
    * `PGVWC07PositiveLengthWitness.weight_ne_zero`
    Compile risk: none after Step 5.1.2 (these are file-local).
13. **Delete the dead Lean theorems behind the Cluster D entries:**
    * `MPSTensor.afterBlocking_reindexedCommonSectorDataWithZeroTail_of_sameMPV₂`
      (`SectorComparison/CommonSectorData.lean`)
    * `MPSTensor.afterBlocking_commonLengthCommonSectorData_of_reindexed`
      (`SectorComparison/CommonSectorTransport.lean`)
    * `MPSTensor.afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂`
      (`SectorComparison/StructuralData.lean`)
    Compile risk: low — `grep -rn` over `TNLean` returns only their
    definition files.

---

## 6. Per-action file / label / replacement-name lists

### 6.1 Files and labels for Step 5.1 (blueprint deletions)

| File | Range / Label | Action | Replacement | Compile risk |
|---|---|---|---|---|
| `blueprint/src/chapter/ch08_canonical.tex` | lines 108–168 (`thm:cpgsv_canonical_form_source`) | delete | `\begin{remark}[CPSV blocked canonical form]\label{rem:cpgsv_canonical_form_source} …\end{remark}` with two-sentence pointer | none (blueprint only) |
| `blueprint/src/chapter/ch08_canonical.tex` | `thm:pgvwc07_irreducible_unital_dual_package` (≈ line 802) | delete entry; inline into proof sketch of `thm:pgvwc07_ti_canonical_form` | n/a (no replacement label) | none |
| same | `thm:pgvwc07_blockwise_unital_dual_package` (≈ 844) | delete | n/a | none |
| same | `thm:pgvwc07_arbitrary_zero_tail_unital_dual_package` (≈ 882) | delete | n/a | none |
| same | `thm:pgvwc07_arbitrary_zero_tail_unital_dual_bond_dim_bound` (≈ 924) | delete | n/a | none |
| same | `thm:pgvwc07_arbitrary_positive_length_unital_dual_bond_dim_bound` (≈ 950) | delete | n/a | none |
| same | `def:pgvwc07_positive_length_witness` (≈ 985) | delete from blueprint; structure stays Lean-only | n/a | none |
| same | `lem:pgvwc07_positive_length_witness_weight_ne_zero` (≈ 1002) | delete | n/a | none |
| same | `thm:pgvwc07_positive_length_witness_weight_normalization` (≈ 1030) | delete | n/a | none |
| same | `thm:pgvwc07_positive_length_witness_weight_normalization_projective` (≈ 1061) | delete | n/a | none |
| same | `lem:pgvwc07_positive_length_witness_nonempty_of_nonzero_mpv` (≈ 1092) | delete | n/a | none |
| same | `thm:pgvwc07_nonzero_normalized_projective_form` (≈ 1112) | delete | n/a | none |
| same | `thm:pgvwc07_nonzero_normalized_exact_rescaled_form` (≈ 1140) | delete | n/a | none |
| same | `thm:pgvwc07_exact_rescaled_form_zero_nonzero_dichotomy` (≈ 1173) | delete | n/a | none |
| same | `thm:pgvwc07_exact_rescaled_form_with_zero_tail` (≈ 1216) | delete | n/a | none |
| same | `thm:pgvwc07_projective_form_zero_nonzero_dichotomy` (≈ 1246) | delete | n/a | none |
| same | `thm:pgvwc07_ti_canonical_form` (≈ 41) | **keep**; trim the `% Source anchors` block (lines 46–60) into a single bibliographic citation; remove forward reference to the now-deleted `thm:pgvwc07_exact_rescaled_form_with_zero_tail` (line 85). | replace forward reference by a remark | none |
| `blueprint/src/chapter/ch11b_after_blocking.tex` | `thm:ft_after_blocking_structural` (line 261) | demote to remark | `\begin{remark}…` cites `thm:tp_primitive_blockdecomp` | none |
| same | `thm:ft_after_blocking_reindexed_common_sector_live_zero_tail` (line 614) | delete | n/a | none |
| same | `thm:ft_after_blocking_common_length_common_sector_reindexed` (line 1011) | delete | n/a | none |
| `blueprint/src/chapter/ch09_block_perm.tex` | preface (lines 1–18) and `rem:pgvwc07_vs_local_cf` (line 340) | consolidate into one `\section{Scope}` + one `\begin{remark}` | scope statement names the chapter's three outputs (`thm:pi_auto_decomp`, `thm:pi_linear_ext`, `lem:block_sep`/`lem:block_sep_normal`/`lem:ft_canonical`) | none |

### 6.2 Files and decl names for Step 5.2 (Lean refactor)

| File | Declaration | Action | Replacement / new name | Compile risk |
|---|---|---|---|---|
| `TNLean/MPS/CanonicalForm/NormalReduction/TPGauge.lean` | `exists_pgvwc07_unital_dualDiag_data_of_irreducible` | `private` (or rename to `MPSTensor.PGVWC07.unital_dualDiag_single_block`) | keep call sites | none — file-local |
| same | `exists_pgvwc07_unital_dualDiag_blockwise` | `private` | `MPSTensor.PGVWC07.unital_dualDiag_blockwise` | none |
| same | `exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail` | `private` | `MPSTensor.PGVWC07.unital_dualDiag_arbitrary_with_zeroTail` | none |
| same | `exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound` | `private` | rename to `…_bondDim_total_eq` (the conclusion is `D_0 + Σ = D`, not a bound) | none |
| same | `exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound` | `private` | rename to `…_positive_length` | none |
| same | `exists_pgvwc07_positiveLengthWitness` | `private` | `MPSTensor.PGVWC07.positiveLengthWitness` | none |
| same | `PGVWC07PositiveLengthWitness` (`structure`) | move to `namespace MPSTensor.PGVWC07`; rename to `Internal.PositiveLengthWitness` | keep all field names | none |
| `TNLean/MPS/CanonicalForm/NormalReduction/WeightNormalization.lean` | all `_normalized_*` theorems except `_allow_empty` | `private` | drop `pgvwc07_` from the names since the file is already `NormalReduction/` | none |
| `TNLean/MPS/CanonicalForm/Existence.lean` | `exists_blockTensor_isPrimitive` (line 216), `exists_blockTensor_leftCanonical_isPrimitive` (line 232) | `private` (or delete and inline) | n/a | none — file-local |
| `TNLean/MPS/CanonicalForm/SectorComparison/CyclicSectorDecomposition.lean` | `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` (line 79) | `private` | n/a | none — file-local |
| `TNLean/MPS/CanonicalForm/SectorComparison/CommonSectorTransport.lean` | `zeroTail_commonFlat_of_blockwise`, `_of_word_eq`, `_of_groupedBlockCastAgrees`, and their `_commonFlatAt_*` and `sameMPV₂Pos_blockTensor_commonFlatAt_*` companions | `private` | keep public: `_of_reindexed`, `_commonFlatAt_of_reindexed`, `sameMPV₂Pos_blockTensor_commonFlatAt_of_reindexed`, `zeroTail_commonFlat_transport_of_reindexed`, and the abbrev pair | none — all callers in same file |
| `TNLean/MPS/CanonicalForm/CommonPeriodCyclicSectors.lean` | `commonPeriodBlocking_apply` (`rfl`-lemma, line 60) | mark `@[simp]` or delete | n/a | none |

### 6.3 Files and decl names for Step 5.3 (Lean deletions)

| File | Declaration | Action | Compile risk |
|---|---|---|---|
| `TNLean/MPS/CanonicalForm/NormalReduction/WeightNormalization.lean` | `exists_pgvwc07_normalized_exact_form_after_rescaling_with_zeroTail`, `exists_pgvwc07_normalized_projective_form_or_forall_pos_mpv_eq_zero` | delete | none — verified zero external references |
| `TNLean/MPS/CanonicalForm/NormalReduction/TPGauge.lean` | `PGVWC07PositiveLengthWitness.weight_ne_zero` (after the `structure` move in 5.2) | delete (inline at single use) | none |
| `TNLean/MPS/CanonicalForm/SectorComparison/CommonSectorData.lean` | `afterBlocking_reindexedCommonSectorDataWithZeroTail_of_sameMPV₂` | delete | none |
| `TNLean/MPS/CanonicalForm/SectorComparison/CommonSectorTransport.lean` | `afterBlocking_commonLengthCommonSectorData_of_reindexed` | delete | none |
| `TNLean/MPS/CanonicalForm/SectorComparison/StructuralData.lean` | `afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂` (line 185) | delete | none — only consumer is the now-removed blueprint entry `thm:ft_after_blocking_structural` |

### 6.4 Replacement-name guidance per `docs/blueprint_style_guide.md` + `docs/prose_style.md`

* Banned in titles: "package", "assembly", "data" (as bare noun),
  "wiring", "bridge", "plumbing". The current titles
  "Single irreducible-block PGVWC07 canonical-form theorem" (line 802)
  → after removal becomes a proof step "Single-block normalization" inside
  the proof of `thm:pgvwc07_ti_canonical_form`. No new heading needed.
* Theorem heading style: keep "Translation-invariant canonical form"
  (line 41) — already source-faithful; remove the trailing
  `% Source anchors` block (16 lines of LaTeX comments) and replace
  with one `\cite[Theorem~Th:TIcanonical]{PerezGarcia2007Matrix}` in the
  body.
* Lean section names with "Assembly" — verified via
  `grep -rn 'section Assembly' TNLean/MPS/CanonicalForm` (no matches).
  The Lean code is already clean on this point.

---

## 7. Verification log

The following grep commands were used to verify the consumer claims in
§2 and §4. The reported counts are the number of lines returned at audit
time; the orchestrator can re-run them after applying each step.

```
grep -rn 'exists_pgvwc07_' TNLean blueprint
    →  every hit is in NormalReduction/TPGauge.lean,
       NormalReduction/WeightNormalization.lean,
       NormalReduction.lean (import summary),
       ch08_canonical.tex, or docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex.
       Zero hits in FundamentalTheorem/, BNT/, SectorComparison/,
       CyclicSectors/, ch09_block_perm.tex, ch11b_after_blocking.tex,
       ch11_fundamental_theorem_proof.tex, ch10_bnt.tex, ch13_*.tex,
       Periodic/, ParentHamiltonian/, Symmetry/.

grep -rn 'thm:cpgsv_canonical_form_source' blueprint
    →  3 hits, all in ch08_canonical.tex (definition + 2 self-references).

grep -rn '\\uses{thm:pgvwc07' blueprint
    →  0 hits.

grep -rn 'thm:ft_after_blocking_common_length_common_sector_theorem' blueprint
    → 6 hits, all in ch11b_after_blocking.tex (as expected — internal
      chain) plus 1 indirect consumer through
      thm:after_blocking_common_primitive_irreducible_blocks_reindexed,
      which is `\uses`-cited by ch11_fundamental_theorem_proof.tex
      line 862.

grep -rn 'exists_tp_gauge_from_arbitrary_with_zeroTail' TNLean
    →  consumed by SectorComparison/CommonSectorData.lean,
       SectorComparison/TPPrimitiveReduction.lean, and listed in
       StructuralData.lean's docstring. This is the actual
       canonical-form input fed into Chapter 12's primitive
       block decomposition.
```

The single canonical "bridge declaration" the user is looking for is
`MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail`
(`thm:tp_gauge_arbitrary`). The PGVWC07 stack is **parallel** to this
bridge, not part of it.
