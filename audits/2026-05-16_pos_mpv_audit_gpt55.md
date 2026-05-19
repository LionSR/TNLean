# Audit: feasibility of arbitrary-input SectorBNT supplier path via `SameMPV₂Pos`

**Date:** 2026-05-16  
**Scope:** scout only; no Lean source edits.  
**Target stack:** `TNLean/MPS/FundamentalTheorem/SectorBNT/`, plus the arbitrary-input reduction chain under `TNLean/MPS/CanonicalForm/Reduction.lean`, `TNLean/MPS/CanonicalForm/Existence.lean`, and `TNLean/MPS/CanonicalForm/SectorComparison/*.lean`.

## Executive summary

The `SectorBNT` equal-MPV stack does **not** materially use the `N = 0` case of `SameMPV₂` in the mathematical argument.  The few proof-body uses of `hEqual N σ` occur inside eventual/asymptotic arguments, or in symmetry wrappers.  I found no `hEqual 0` call and no hidden `funext`/`mpv_ext` proof in `SectorBNT` that needs length zero.

Refactoring the equal-FT path from `SameMPV₂` to `SameMPV₂Pos` is therefore feasible and low-to-moderate risk.  The only non-mechanical work is converting three pointwise/all-`N` proof subblocks to eventual/positive-length subblocks:

1. `DominantMatch.lean`: the overlap identity currently stated for all `N`.
2. `CoeffIdentity.lean`: two coefficient-substitution identities currently proved by `Filter.Eventually.of_forall`.
3. symmetric wrappers in `StrongMatch.lean`: change `fun N σ => ...` to `fun N hN σ => ...`.

The arbitrary-input chain already exposes the key positive-length interface: after zero-tail removal it naturally produces `SameMPV₂Pos`, not full `SameMPV₂`.  The closest existing theorem is `unconditional_commonPrimitiveIrreducibleBlocks` in `CommonSectorTransport.lean`, which gives common blocked nonzero parts with `SameMPV₂Pos` and TP/primitive/irreducible blocks.  What is still missing for a full arbitrary-input `SectorBNT` supplier is not primarily the `N = 0` issue; it is:

* packaging a one-sided version (or extracting one side) from the two-sided common-sector theorem;
* adding a finite common injective reblocking and transporting the positive-length MPV equality;
* satisfying the `SectorBNT.Supplier` normalization inputs `‖μ k‖ ≤ 1` and `∃ k, ‖μ k‖ = 1` without changing exact positive-length MPVs;
* handling all-zero inputs / empty nonzero block families;
* if the result is intended to feed the current equal-FT theorems, supplying the per-block unit witnesses required by those FT theorem statements.

My recommendation is **Option C in implementation form**: add `SameMPV₂Pos` variants as the primary/core equal-FT theorems, and keep the current `SameMPV₂` theorems as thin compatibility wrappers.  This preserves existing callers while enabling the arbitrary-input supplier path to use the paper-faithful positive-length equality relation.

---

## 1. Inventory of `SameMPV₂` usage in `SectorBNT`

### 1.1 Code-level usages

| File:line | Identifier / local item | Kind | Current use |
|---|---|---:|---|
| `DominantMatch.lean:113` | `SameMPV₂.toEventuallyNonzeroProportionalMPV₂` | theorem declaration | Converts full equality to eventual nonzero proportionality. |
| `DominantMatch.lean:115` | `SameMPV₂.toEventuallyNonzeroProportionalMPV₂` | hypothesis type | `(h : SameMPV₂ A B)`. |
| `DominantMatch.lean:134` | `exists_nondecaying_overlap_pair_of_sameMPV` | hypothesis type | Equal-MPV specialization of weak existential. |
| `DominantMatch.lean:139` | `exists_nondecaying_overlap_pair_of_sameMPV` | proof call | Passes `hEqual.toEventuallyNonzeroProportionalMPV₂`. |
| `DominantMatch.lean:195` | `exists_block_match_of_sameMPV` | hypothesis type | Main block-match theorem takes `hEqual`. |
| `DominantMatch.lean:258` | local `hOverlap_identity` | proof-body direct use | Rewrites one summand by `rw [hEqual N σ]`. |
| `StrongMatch.lean:193` | `forall_k_exists_j_nondecaying_overlap_of_sameMPV` | hypothesis type | Strong existential takes `hEqual`. |
| `StrongMatch.lean:208` | local `hEqual_symm` | local type | Constructs symmetric `SameMPV₂ Q.toTensor P.toTensor`. |
| `StrongMatch.lean:209` | local `hEqual_symm` | proof-body direct use | `fun N σ => (hEqual N σ).symm`. |
| `StrongMatch.lean:325` | `bijective_match_of_sameMPV` | hypothesis type | Bijective match takes `hEqual`. |
| `StrongMatch.lean:337` | local `hEqual_symm` | local type | Constructs symmetric `SameMPV₂ Q.toTensor P.toTensor`. |
| `StrongMatch.lean:338` | local `hEqual_symm` | proof-body direct use | `fun N σ => (hEqual N σ).symm`. |
| `CoeffIdentity.lean:95` | `coeff_identity_via_matched_mpv_phase` | hypothesis type | Coefficient identity takes `hEqual`. |
| `CoeffIdentity.lean:137` | local `hStateEq` | proof-body direct use | `simpa ... using hEqual N σ`. |
| `CoeffIdentity.lean:217` | `coeff_identity_via_global_gauge` | hypothesis type | Wrapper coefficient identity takes `hEqual`. |
| `CoeffIdentity.lean:276` | local `hStateEq` | proof-body direct use | `simpa ... using hEqual N σ`. |
| `Fundamental.lean:92` | `ft_sector_bnt_equal_sector_data` | hypothesis type | Top-level sector-data theorem takes `hEqual`. |
| `Fundamental.lean:101` | `ft_sector_bnt_equal_sector_data` | proof call | Passes `hEqual` to `bijective_match_of_sameMPV`. |
| `Fundamental.lean:107` | `ft_sector_bnt_equal_sector_data` | proof call | Passes `hEqual` to `coeff_identity_via_global_gauge`. |
| `Fundamental.lean:161` | `ft_sector_bnt_equal_global_gauge` | hypothesis type | Global-gauge witness theorem takes `hEqual`. |
| `Fundamental.lean:190` | `ft_sector_bnt_equal_global_gauge` | proof call | Passes `hEqual` to `bijective_match_of_sameMPV`. |
| `Fundamental.lean:217` | `ft_sector_bnt_equal_global_gauge` | proof call | Passes `hEqual` to `coeff_identity_via_matched_mpv_phase`. |
| `FundamentalCoord.lean:93` | `ft_sector_bnt_equal_mps_gaugeEquiv_witnesses` | hypothesis type | Witness bundle takes `hEqual`. |
| `FundamentalCoord.lean:123` | `ft_sector_bnt_equal_mps_gaugeEquiv_witnesses` | proof call | Passes `hEqual` to `ft_sector_bnt_equal_global_gauge`. |
| `FundamentalCoord.lean:149` | `ft_sector_bnt_equal_mps_gaugeEquiv` | hypothesis type | Matched-coordinate gauge theorem takes `hEqual`. |
| `FundamentalCoord.lean:167` | `ft_sector_bnt_equal_mps_gaugeEquiv` | proof call | Passes `hEqual` to witness theorem. |
| `FundamentalCoord.lean:466` | `ft_sector_bnt_equal_mps_gaugeEquiv_literal` | hypothesis type | Literal cast-of-`P.toTensor` theorem takes `hEqual`. |
| `FundamentalCoord.lean:479` | `ft_sector_bnt_equal_mps_gaugeEquiv_literal` | proof call | Passes `hEqual` to witness theorem. |
| `Supplier.lean:140` | `exists_isBNTCanonicalForm_of_tp_primitive_irr_injective_blocks` | conclusion type | Prepared-block supplier returns full `SameMPV₂`. |
| `Supplier.lean:168` | local `hSame` | local type | Uses `collapsedBntSectorDecomp_sameMPV₂`, exact for prepared blocks. |

### 1.2 Doc/comment-only mentions

These are descriptive only and have no proof dependency, but they should be updated if names or statement surfaces change:

| File | Lines |
|---|---|
| `DominantMatch.lean` | 17, 21, 25, 103, 105, 119, 124, 143, 151, 169, 229 |
| `StrongMatch.lean` | 71 |
| `CoeffIdentity.lean` | 82, 205 |
| `Supplier.lean` | 38 |

### 1.3 Non-usages worth noting

* `WeakExistential.lean` is already formulated using `EventuallyNonzeroProportionalMPV₂`; it does not require full all-length equality.
* `ProportionalMatch.lean` is already formulated using `EventuallyNonzeroProportionalMPV₂`; it is not directly affected by the equal-MPV `N = 0` issue.
* `Api.lean`, `Basic.lean`, `WeightEquiv.lean`, `CesaroNonDecay.lean`, `EqualModulus.lean`, and `Examples.lean` contain no code-level `SameMPV₂` dependency.

---

## 2. Per-usage `N = 0` dependency assessment

### 2.1 Search result for explicit `N = 0` uses

I searched for direct patterns such as `hEqual 0`, `hSame 0`, and related uses in `TNLean/MPS/FundamentalTheorem/SectorBNT/`.  There is **no proof-body `hEqual 0` use** in `SectorBNT`.  The only match was a doc-comment sentence in `DominantMatch.lean:169`.

### 2.2 Direct proof-body uses

| Location | Current shape | Is `N` provably positive? | `N = 0` dependency? | Refactor note |
|---|---|---:|---:|---|
| `DominantMatch.lean:139` | `hEqual.toEventuallyNonzeroProportionalMPV₂` | Eventually yes | No mathematical dependence | Add a `SameMPV₂Pos.toEventuallyNonzeroProportionalMPV₂` theorem using the eventual filter fact `∀ᶠ N in atTop, 0 < N`. |
| `DominantMatch.lean:258` | `rw [hEqual N σ]` inside `hOverlap_identity : ∀ N, ...` | Not in the local pointwise statement, but the identity is only consumed by a `Tendsto` proof at `atTop` | No essential dependence | Change `hOverlap_identity` to an eventual identity, or keep a pointwise identity with an extra `0 < N` argument. Then use eventual congr/squeeze from `N ≥ 1`. |
| `StrongMatch.lean:209` | `fun N σ => (hEqual N σ).symm` | Under a Pos relation, supplied as argument | No | Change local type to `SameMPV₂Pos Q.toTensor P.toTensor` and body to `fun N hN σ => (hEqual N hN σ).symm`. |
| `StrongMatch.lean:338` | same as above | Under a Pos relation, supplied as argument | No | Same mechanical change. |
| `CoeffIdentity.lean:137` | `simpa [mpvState_apply, mpv] using hEqual N σ` inside `Filter.Eventually.of_forall` | Not in current all-`N` proof, but the surrounding coefficient result is eventual | No essential dependence | Replace `Filter.Eventually.of_forall` by an eventual block over `N ≥ 1`, or combine with existing `hLI` tail. Pass `hNpos : 0 < N` to `hEqual`. |
| `CoeffIdentity.lean:276` | same pattern in `coeff_identity_via_global_gauge` | Same | No essential dependence | Same eventification patch. |
| `Fundamental*.lean` pass-throughs | Pass `hEqual` to downstream lemmas | N/A | No | Follow type changes only. |
| `Supplier.lean:168` | exact prepared-block `hSame` | All `N`, including zero, genuinely holds for this prepared regrouping | No blocker | Can remain full `SameMPV₂`; optional `SameMPV₂Pos` projection for arbitrary path. |

### 2.3 Implicit `N = 0` through tactics / extensionality

The only potentially suspicious patterns are:

* `CoeffIdentity.lean:116` and `CoeffIdentity.lean:255`: `Filter.Eventually.of_forall` proves the vector identity for every `N`, including zero.  This is stronger than needed because the subsequent `coefficient_eventually_eq_of_eventually_linearIndependent` consumes only eventual equality.  This should be changed to an eventual-positive proof, not treated as a semantic dependence on `N = 0`.
* `CoeffIdentity.lean:135`, `148`, `274`, `287`: `PiLp.ext` is only over spin configurations `σ : Fin N → Fin d` for a fixed `N`; it does not quantify over `N = 0` by itself.
* `DominantMatch.lean:233-259`: the pointwise `hOverlap_identity : ∀ N` currently includes `N = 0`, but it is later used only in asymptotic statements (`Tendsto ... atTop`).  Replacing it by an eventual identity is mathematically sufficient.
* `Fundamental.lean` has `funext i` for physical-site tensor equality, unrelated to MPV length.

Conclusion: no tactic secretly needs the length-zero equality; the current all-`N` proofs simply overspecify eventual facts.

---

## 3. Recommended path

### Option A: weaken equal-FT theorems to `SameMPV₂Pos`

**Scope.** Change the equal-MPV FT path so the main hypotheses are:

```lean
hEqual : SameMPV₂Pos P.toTensor Q.toTensor
```

rather than full `SameMPV₂ P.toTensor Q.toTensor`.

**Type-signature updates.** About 11 equal-FT theorem statements in `SectorBNT` should change, plus one new converter theorem:

1. `exists_nondecaying_overlap_pair_of_sameMPV`
2. `exists_block_match_of_sameMPV`
3. `forall_k_exists_j_nondecaying_overlap_of_sameMPV`
4. `bijective_match_of_sameMPV`
5. `coeff_identity_via_matched_mpv_phase`
6. `coeff_identity_via_global_gauge`
7. `ft_sector_bnt_equal_sector_data`
8. `ft_sector_bnt_equal_global_gauge`
9. `ft_sector_bnt_equal_mps_gaugeEquiv_witnesses`
10. `ft_sector_bnt_equal_mps_gaugeEquiv`
11. `ft_sector_bnt_equal_mps_gaugeEquiv_literal`

The existing `SameMPV₂.toEventuallyNonzeroProportionalMPV₂` can be kept for compatibility; add a sibling theorem for `SameMPV₂Pos` rather than deleting it.

**Body updates.** Approximately 6 direct proof-body call sites need an added positive-length proof or eventification:

* `DominantMatch.lean:139`: replace converter.
* `DominantMatch.lean:258`: add `0 < N` or eventual identity.
* `StrongMatch.lean:209`, `338`: symmetric `SameMPV₂Pos` wrapper.
* `CoeffIdentity.lean:137`, `276`: pass `0 < N` in the eventual coefficient-substitution proof.

**Difficulty.** Low-to-moderate.  The only nontrivial patch is making the overlap/coefficient equalities eventual instead of pointwise all-`N`.  The needed positivity is trivial from `atTop` tails (`N ≥ 1`) or from existing strict inequalities `N > N₀` after possibly increasing `N₀`.

**Pros.** Most paper-faithful: the FT does not pretend that the unobservable empty chain fixes the bond dimension.  It directly matches the zero-tail output of the arbitrary-input reduction chain.

**Cons.** Breaks existing callers unless wrappers are added; theorem names containing `sameMPV` become mildly misleading if their hypothesis is `SameMPV₂Pos`.

### Option B: keep `SameMPV₂`, build supplier with a no-zero-block hypothesis or extension trick

There are two conceivable variants:

1. **No-zero-tail hypothesis.** Require the arbitrary-input reduction to have `zeroTailDim = 0`, or equivalently no all-zero leftover block.  Then the nonzero part can satisfy full `SameMPV₂` to the original blocked tensor.
2. **Extension/padding trick.** Keep a zero-tail summand outside the BNT decomposition so that the total bond dimension is restored at `N = 0`.

**Assessment.** I do not recommend this as the main path.

* The no-zero-tail hypothesis excludes exactly the arbitrary-input cases that motivated this audit.
* A zero-tail summand is not a valid `IsBNTCanonicalForm` sector: its tensor is all zero, fails left-canonical normalization in positive dimension, and cannot satisfy the nonzero-weight sector-data contract.
* Padding the BNT tensor by an external zero block would require a new theorem surface that says "BNT plus zero tail", not the current `IsBNTCanonicalForm P` FT surface.
* The resulting theorem would still be less source-faithful than simply ignoring the degenerate empty-chain coefficient.

**Cost/risk.** Medium-to-high, and it leaves the main conceptual mismatch intact.

### Option C: dual-form FT theorems (`SameMPV₂Pos` core + `SameMPV₂` wrappers)

This is my recommended implementation strategy.

**Plan.** Add new core theorems with `SameMPV₂Pos` hypotheses, for example:

```lean
theorem exists_block_match_of_sameMPVPos ...
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) : ...
```

Then keep the existing `SameMPV₂` theorem names as wrappers:

```lean
theorem exists_block_match_of_sameMPV ...
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) : ... :=
  exists_block_match_of_sameMPVPos ... (fun N hN σ => hEqual N σ)
```

The same pattern applies upward through `StrongMatch`, `CoeffIdentity`, `Fundamental`, and `FundamentalCoord`.

**Why this is best.** It gives the arbitrary-input supplier path the positive-length theorem it needs, keeps current callers stable, and allows a later cleanup to decide whether to rename the Pos variants as canonical.

**Effort estimate.** About 200-350 LoC for the FT refactor including wrappers and doc updates.  Risk is low-to-moderate; most failures should be local type mismatches.

---

## 4. Arbitrary-input chain inventory

### 4.1 Definitions confirming the length-zero issue

* `TNLean/MPS/Defs.lean:90-91` defines `SameMPV₂ A B` as equality for all `N : ℕ` and all `σ : Fin N → Fin d`.
* `TNLean/MPS/Defs.lean:99-100` defines `SameMPV₂Pos A B` as equality for `0 < N` only.
* `TNLean/MPS/Defs.lean:70-71` defines `mpv A σ` as `coeff A (List.ofFn σ)`.
* `TNLean/MPS/CanonicalForm/Existence.lean:476-478` proves, for `σ : Fin 0 → Fin d`, `mpv A σ = (D : ℂ)`.
* I also checked this with a temporary `/tmp` Lean file: `lake env lean /tmp/mpv_zero_check.lean` verified
  ```lean
  example {d D : ℕ} (A : MPSTensor d D) (σ : Fin 0 → Fin d) :
      mpv A σ = (D : ℂ) := by
    simp [mpv, coeff, Matrix.trace_one, Fintype.card_fin]
  ```
  and verified that `SameMPV₂ A B` implies `(D₁ : ℂ) = (D₂ : ℂ)` by applying it at `N = 0`.

So the premise in the task is correct: full `SameMPV₂` remembers the total bond dimension at the empty chain.

### 4.2 One-sided arbitrary-input reduction pieces

| File:line | Theorem | Output relevant to supplier path | Gap / note |
|---|---|---|---|
| `Reduction.lean:123` | `exists_irreducible_blockDecomp` | Arbitrary `A` is full-`SameMPV₂` to a unit-weight direct sum of irreducible blocks. | Includes zero blocks, so exact length-zero dimension is retained before stripping. |
| `Existence.lean:502` | `exists_irreducible_blockDecomp_nonzeroBlocks` | Splits arbitrary `A` into `zeroMPSTensor z +` nonzero irreducible blocks, with an exact equation for all `N`. | The nonzero part is only `SameMPV₂Pos` to `A` unless `z = 0`; this is the intended zero-tail interface. |
| `NormalReduction/TPGauge.lean:297` | `exists_tp_gauge_from_arbitrary_with_zeroTail` | Produces zero tail plus TP-gauged irreducible nonzero weighted blocks with positive dimensions and nonzero weights. | Still before period removal / primitive blocking. |
| `SectorComparison/TPPrimitiveReduction.lean:130` | `exists_tp_primitive_blockDecomp_after_blocking` | Produces `p > 0`, zero tail, and TP primitive blocks after blocking, with nonzero weights and positive dimensions. | Statement does not provide tensor irreducibility for the blocked blocks; docs explicitly note blocking irreducibility is not automatic here. |
| `SectorComparison/CyclicSectorDecomposition.lean:590` | `exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` | For a TP irreducible block, after period removal gives primitive irreducible sector blocks. | One block at a time; used by common-sector family machinery. |
| `SectorComparison/CommonBlockedCyclicSectorConstruction.lean:200` | `exists_commonBlockedCyclicSectorFamily_of_hasPrimitiveIrreducibleCyclicSectors` | Packages per-block cyclic-sector data into one common blocked sector family. | One-sided, but lower-level than the final arbitrary-input theorem. |
| `SectorComparison/CommonSectorTransport.lean:624` | `unconditional_commonPrimitiveIrreducibleBlocks` | For two tensors with `SameMPV₂ A B`, produces common `p > 0`, zero-tail equations, `SameMPV₂Pos` from each blocked tensor to its nonzero part, `SameMPV₂Pos` between nonzero parts, and TP/primitive/irreducible blocks with positive dimensions and nonzero weights. | Closest existing arbitrary-input chain.  It is two-sided and does not yet supply injectivity or SectorBNT normalization. |

### 4.3 Pairwise sector-comparison pieces

| File:line | Theorem | Role |
|---|---|---|
| `ZeroTailTransport.lean:182` | `sameMPV₂Pos_of_zeroTail_eq` | Converts a zero-tail decomposition into positive-length equality between the original tensor and the live part. |
| `ZeroTailTransport.lean:202` | `sameMPV₂_live_of_sameMPV₂_with_zeroTail_eq` | Recovers full `SameMPV₂` between live parts only if zero-tail dimensions agree.  This is exactly the length-zero obstruction. |
| `NonzeroBlockComparison.lean:47` | `nonzeroBlock_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂` | From full `SameMPV₂ A B` plus two zero-tail decompositions, obtains positive-length equality of nonzero parts and a separate length-zero zero-tail identity. |
| `NonzeroBlockComparison.lean:95` | `nonzeroBlock_blockPower_positive_sameMPV₂_and_zeroTail_identity_of_sameMPV₂` | Same after common blocking. |
| `NonzeroBlockComparison.lean:156` | `nonzeroBlock_sameMPV₂_of_sameMPV₂_of_zeroTail_eq` | Full live-part equality under explicit zero-tail equality. |
| `BasicSectorComparison.lean:39` | `afterBlocking_sectorComparison_zeroTail_of_blockSpan` | Older/sector-comparison route: with `hZeroTail : zeroTailA = zeroTailB` and span hypotheses, obtains full `SameMPV₂ P.toTensor Q.toTensor` for old-style sector data. |
| `CommonSectorData.lean:62`, `130`, `298`, `443` | common-sector after-blocking theorems | Preserve both positive-length nonzero equality and separate zero-tail identities through common blocking/reindexing. |
| `CommonSectorTransport.lean:417` | `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` | Conditional version of the closest common primitive/irreducible theorem. |
| `CommonSectorTransport.lean:624` | `unconditional_commonPrimitiveIrreducibleBlocks` | Unconditional version after the grouped-block cast identity is supplied. |

### 4.4 Missing glue for `exists_isBNTCanonicalForm_afterBlocking`

I did **not** find an existing theorem of the form

```lean
∀ A : MPSTensor d D, ∃ p P,
  0 < p ∧ IsBNTCanonicalForm P ∧ SameMPV₂Pos (blockTensor A p) P.toTensor
```

or a fully prepared-block theorem producing `IsBNTCanonicalForm` from arbitrary input.

The closest path would be:

1. Use the common-sector/arbitrary-input chain (preferably one-sided; currently easiest to extract from `unconditional_commonPrimitiveIrreducibleBlocks A A (fun N σ => rfl)` or to factor a one-sided theorem) to obtain TP/primitive/irreducible nonzero blocks and `SameMPV₂Pos` to the blocked input.
2. Apply per-block injective reblocking using:
   * `exists_pos_blockTensor_isInjective_of_tp_primitive_irreducible` (`NormalityChain.lean:193`), and
   * `tp_primitive_irreducible_extra_blocking` (`PrimitiveBlocks.lean:203`) to preserve TP/primitive/irreducible under the extra positive blocking.
3. Transport weights and positive-length equality through the extra common blocking using `sameMPV₂Pos_blockTensor` and `sameMPV₂Pos_toTensorFromBlocks_blockPower` from `Core/BlockingInfrastructure.lean:222` and `:240`.
4. Feed the prepared family to `SectorBNT.Supplier.exists_isBNTCanonicalForm_of_tp_primitive_irr_injective_blocks` (`Supplier.lean:127`).

The unresolved inputs at step 4 are the weight normalization assumptions:

```lean
hμLe   : ∀ k, ‖μ k‖ ≤ 1
hμUnit : ∃ k, ‖μ k‖ = 1
```

The current arbitrary-input chain gives only `μ k ≠ 0`.  A naive global rescaling of all weights to make the maximum norm equal to one changes the MPV by a length-dependent scalar unless one also rescales the basis tensors; but rescaling the basis tensors generally breaks the left-canonical/self-overlap normalization required by `IsBNTCanonicalForm`.  Thus the normalization bridge is a genuine remaining design point, not a Lean bookkeeping issue.

There is also an all-zero edge case: if the stripped nonzero family is empty, `IsBNTCanonicalForm` cannot be constructed because it contains the global witness `weight_unit_exists : ∃ j q, ‖P.weight j q‖ = 1`.

---

## 5. Estimated LoC + risk for the full arbitrary-input supplier PR

### 5.1 FT `SameMPV₂Pos` refactor

**Estimated size:** 200-350 LoC.

**Files likely touched:**

* `TNLean/MPS/Defs.lean` or `SectorBNT/DominantMatch.lean` for helper lemmas:
  * `SameMPV₂.toSameMPV₂Pos`
  * `SameMPV₂Pos.symm`
  * `SameMPV₂Pos.toEventuallyNonzeroProportionalMPV₂`
* `SectorBNT/DominantMatch.lean`
* `SectorBNT/StrongMatch.lean`
* `SectorBNT/CoeffIdentity.lean`
* `SectorBNT/Fundamental.lean`
* `SectorBNT/FundamentalCoord.lean`

**Risk:** low-to-moderate.  No mathematical obstruction found.  The main Lean risk is eventifying equalities currently proved with `Filter.Eventually.of_forall` and avoiding stale theorem names / wrappers.

### 5.2 Conditional arbitrary-input SectorBNT supplier

If scoped as a conditional supplier that assumes or obtains normalized weights and excludes the all-zero case:

**Estimated size:** 600-1000 LoC.

Likely components:

* one-sided extraction theorem from `unconditional_commonPrimitiveIrreducibleBlocks` or a factored one-sided version: 150-250 LoC;
* finite common injective reblocking for TP/primitive/irreducible families: 200-350 LoC;
* positive-length MPV transport through the extra blocking: 100-200 LoC;
* call to `SectorBNT.Supplier.exists_isBNTCanonicalForm_of_tp_primitive_irr_injective_blocks` plus packaging as `SameMPV₂Pos (blockTensor A p) P.toTensor`: 100-200 LoC;
* docs/audit/blueprint updates: 50-150 LoC.

**Risk:** medium.  Most ingredients exist, but the dependent reindexing and additional blocking over finite families will be tedious.

### 5.3 Unconditional arbitrary-input SectorBNT supplier

If the goal is a truly unconditional theorem for every `A : MPSTensor d D`, with exact positive-length MPV equality to a normalized `IsBNTCanonicalForm`:

**Estimated size:** 1200-2000+ LoC and high mathematical/design risk.

Remaining blockers:

1. **Normalization of weights.** Current arbitrary reductions do not prove `‖μ k‖ ≤ 1` or a unit witness.  Global rescaling is not exact-MPV-neutral under the current left-canonical `IsBNTCanonicalForm` surface.
2. **All-zero input.** No nonzero BNT sector exists, but `IsBNTCanonicalForm` requires a unit-modulus weight witness.
3. **Per-block unit witnesses for FT consumers.** The equal-FT theorems still require `∀ j, ∃ q, ‖P.weight j q‖ = 1` as explicit theorem-level hypotheses.  A general BNT decomposition with decaying sectors will not satisfy this without restricting to a peripheral/unit-block subfamily or changing the FT theorem surface.
4. **One-sided vs two-sided packaging.** The best current arbitrary-input theorem is two-sided (`unconditional_commonPrimitiveIrreducibleBlocks`); a supplier should not require a second tensor.

### 5.4 Recommended next PR sequence

1. **Add `SameMPV₂Pos` FT variants and wrappers** (Option C).  This directly removes the zero-tail / `N = 0` blocker and is well-scoped.
2. **Add a small one-sided positive-length supplier skeleton** that stops at TP/primitive/irreducible blocks and explicitly states the missing normalization/injectivity inputs if necessary.
3. **Add finite common injective reblocking** for a prepared TP/primitive/irreducible family and feed it into `SectorBNT.Supplier` under explicit normalization assumptions.
4. Only after that, decide whether the normalization problem should be handled by extra theorem hypotheses, a proportional-MPV supplier, or a revised normalized-canonical-form surface.

**Bottom line:** the `SameMPV₂ → SameMPV₂Pos` refactor is feasible and should be done.  It removes the zero-tail obstacle cleanly.  It does not, by itself, complete the arbitrary-input SectorBNT supplier; the remaining hard part is normalized prepared-block data, especially exact-MPV-compatible weight normalization.
