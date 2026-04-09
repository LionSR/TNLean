/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction
import TNLean.MPS.SharedInfra.SectorDecomposition

open scoped Matrix BigOperators

/-!
# BNT grouping step for the canonical form existence reduction

This file provides the **BNT grouping / sorting** step that bridges the output of the
canonical form existence reduction (blocks with nonzero weights, not necessarily strictly
ordered by norm) with the `IsNormalCanonicalForm` predicate (which requires
`StrictAnti (fun k => ‖μ k‖)`).

## Background: Gap 2 in the existence reduction

The existence reduction (in `Assembly.lean`) produces a weighted block family
`(μ k, blocks k)` with `μ k ≠ 0` for all `k`, but does **not** guarantee pairwise
distinct norms `‖μ j‖ ≠ ‖μ k‖` for `j ≠ k`.  In particular, after blocking by
period `P` the weights become `(μ₀ k)^P`, and two distinct original weights `μ₀ j`,
`μ₀ k` can satisfy `|(μ₀ j)^P| = |(μ₀ k)^P|` even when `|μ₀ j| ≠ |μ₀ k|`.

`IsNormalCanonicalForm` requires `StrictAnti (fun k => ‖μ k‖)`, which in particular
implies all norms are pairwise distinct.  Two resolutions are possible:

* **(a)** Relax the predicate to match the paper's canonical form definition.
* **(b)** Add a BNT grouping/sorting step.

This file implements strategy **(b)** for the common case and states the full result
for the equal-norm case.

## Main results

### §1 Sorting step: distinct norms → strictly decreasing permutation

* `exists_sorted_reindexing` — If the norms `‖μ k‖` are pairwise distinct, there exists
  a bijection `e : Fin r ≃ Fin r` with `StrictAnti (fun k => ‖μ (e k)‖)`.  This is a
  pure combinatorial sorting result.

* `exists_sorted_blockDecomp_of_distinct_norms` — Combines sorting with
  `sameMPV₂_toTensorFromBlocks_perm` to produce a permuted block family that
  (i) has `SameMPV₂` to the original family and (ii) has strictly decreasing norms.

### §2 NCF construction from unsorted distinct-norm data

* `exists_sortedNCF_of_distinct_norms` — If blocks satisfy all `IsNormalCanonicalForm`
  conditions except norm ordering (norms distinct but not yet decreasing), there exists
  a permutation `e` such that `(μ ∘ e, blocks ∘ e)` is a proper `IsNormalCanonicalForm`
  and the assembled tensor is `SameMPV₂`-equivalent to the original.  This is the key
  bridging step from the reduction output to the canonical form.

### §3 Trivial sector decomposition for the sorted distinct-norm case

* `exists_trivialSectorDecomp_of_sorted_distinct_norms` — Packages a sorted
  distinct-norm block family as a `SectorDecomposition` with all multiplicities
  `copies j = 1`.

### §4 BNT grouping for possibly-equal norms (proved via norm-class enumeration)

* `exists_bnt_grouping` — For blocks with possibly equal norms, given that equal-norm
  blocks have the same dimension and the same MPV function (consequences of BNT
  uniqueness, not yet fully formalized), there exists a `SectorDecomposition` whose
  assembled tensor is `SameMPV₂`-equivalent to the original and whose BNT-level norms
  are strictly decreasing.  The proof constructs a SectorDecomposition from norm-class enumeration.

## References

- [CPGSV17, Definition 2.6, Proposition 2.7]: BNT minimality condition and grouping.
- [CPGSV21, §IV.A]: Existence of canonical form.
- `formalization_goal_analysis.md`, Gap 2.
-/

namespace MPSTensor

variable {d : ℕ}

/-! ### §1. Sorting permutation -/

/-- **Sorting permutation for a distinct-norm weight family.**

Given `μ : Fin r → ℂ` with pairwise distinct norms, there exists a bijection
`e : Fin r ≃ Fin r` such that `‖μ (e k)‖` is strictly decreasing.

**Proof**: The image `S = Finset.univ.image (‖μ ·‖)` is an `r`-element finset of reals
(norm injectivity gives `S.card = r`).  `S.orderEmbOfFin hs ∘ Fin.rev` lists the
elements in strictly decreasing order.  We then choose, for each position `i`, a block
index `e i` with `‖μ (e i)‖` equal to the `i`-th target value; the choice is injective
(hence bijective on a finite type). -/
theorem exists_sorted_reindexing
    {r : ℕ}
    (μ : Fin r → ℂ)
    (hDistinct : ∀ j k : Fin r, j ≠ k → ‖μ j‖ ≠ ‖μ k‖) :
    ∃ e : Fin r ≃ Fin r, StrictAnti (fun k => ‖μ (e k)‖) := by
  classical
  -- The norm function is injective on Fin r, so its image has cardinality r.
  let f : Fin r → ℝ := fun k => ‖μ k‖
  have hf_inj : Function.Injective f := by
    intro j k hfjk
    by_contra hjk
    exact hDistinct j k hjk hfjk
  let s : Finset ℝ := Finset.univ.image f
  have hs : s.card = r := by
    simpa [s] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin r))) hf_inj)
  -- Target values: strictly decreasing listing of the elements of s.
  let vals : Fin r → ℝ := fun i => s.orderEmbOfFin hs (Fin.rev i)
  have hvals_strict : StrictAnti vals := by
    have hsmono : StrictMono (s.orderEmbOfFin hs) := (s.orderEmbOfFin hs).strictMono
    simpa [vals] using hsmono.comp_strictAnti (Fin.rev_strictAnti : StrictAnti (@Fin.rev r))
  have hvals_mem : ∀ i, vals i ∈ s := fun i =>
    Finset.orderEmbOfFin_mem s hs (Fin.rev i)
  -- For each target value, there is a block index with that norm.
  have hex : ∀ i : Fin r, ∃ k : Fin r, f k = vals i := by
    intro i
    have hmem : vals i ∈ Finset.univ.image f := by simpa [s] using hvals_mem i
    rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
    exact ⟨k, hk⟩
  -- Choose the preimage injectively.
  let e₀ : Fin r → Fin r := fun i => Classical.choose (hex i)
  have he₀_spec : ∀ i, f (e₀ i) = vals i := fun i => Classical.choose_spec (hex i)
  have he₀_inj : Function.Injective e₀ := by
    intro i j hij
    apply hvals_strict.injective
    calc vals i = f (e₀ i) := (he₀_spec i).symm
      _ = f (e₀ j) := by rw [hij]
      _ = vals j   := he₀_spec j
  -- Injective on a finite type is bijective.
  let e : Fin r ≃ Fin r :=
    Equiv.ofBijective e₀ ⟨he₀_inj, Finite.surjective_of_injective he₀_inj⟩
  refine ⟨e, fun i j hij => ?_⟩
  have hi : ‖μ (e i)‖ = vals i := by simpa [f, e] using he₀_spec i
  have hj : ‖μ (e j)‖ = vals j := by simpa [f, e] using he₀_spec j
  calc ‖μ (e j)‖ = vals j     := hj
    _ < vals i               := hvals_strict hij
    _ = ‖μ (e i)‖             := hi.symm

/-! ### §2. MPV-preserving sorted block decomposition -/

/-- **Sorted block decomposition with preserved MPV.**

Given a weighted block family `(μ, blocks)` with pairwise distinct norms,
`exists_sorted_reindexing` yields a permutation `e` such that the permuted
family `(μ ∘ e, blocks ∘ e)` has `SameMPV₂` to the original and has strictly
decreasing norms.

The `SameMPV₂` step uses `sameMPV₂_toTensorFromBlocks_perm` from `Multi.lean`. -/
theorem exists_sorted_blockDecomp_of_distinct_norms
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDistinct : ∀ j k : Fin r, j ≠ k → ‖μ j‖ ≠ ‖μ k‖) :
    ∃ e : Fin r ≃ Fin r,
      SameMPV₂
        (toTensorFromBlocks (d := d) (μ := μ) blocks)
        (toTensorFromBlocks (d := d) (μ := fun k => μ (e k)) (fun k => blocks (e k))) ∧
      StrictAnti (fun k : Fin r => ‖μ (e k)‖) := by
  obtain ⟨e, he_anti⟩ := exists_sorted_reindexing μ hDistinct
  refine ⟨e, fun N σ => ?_, he_anti⟩
  -- sameMPV₂_toTensorFromBlocks_perm (with rA = rB = r, perm = e) gives
  --   SameMPV₂ (toTensorFromBlocks (fun k => μ (e k)) (fun k => blocks (e k)))
  --             (toTensorFromBlocks μ blocks).
  -- We need the symmetric direction.
  exact (sameMPV₂_toTensorFromBlocks_perm μ blocks e N σ).symm

/-! ### §3. Normal canonical form from unsorted distinct-norm block data -/

/-- **Lift unsorted distinct-norm block data to `IsNormalCanonicalForm`.**

Starting from a weighted block family satisfying all `IsNormalCanonicalForm` conditions
*except* that the norms `‖μ k‖` are distinct but not yet ordered, this theorem produces:
* a sorting permutation `e : Fin r ≃ Fin r`,
* a `SameMPV₂` equivalence between the original and the permuted assembled tensors,
* an `IsNormalCanonicalForm` certificate for the permuted family `(μ ∘ e, blocks ∘ e)`.

This is the key reduction bridging step: it takes output from the TP-gauge / blocking
reduction (where distinct norms are known but ordering is not guaranteed) and packages
it as a proper normal canonical form.

**Note on types**: The permutation changes the bond-dimension type from
`∑ k, dim k` to `∑ k, dim (e k)`; these are equal as natural numbers (via
`Equiv.sum_comp`) but the assembled tensors live in different types in Lean.
`SameMPV₂` is the right heterogeneous equivalence for comparing them.

**Proof**: `exists_sorted_reindexing` gives `e` with `StrictAnti (‖μ ∘ e‖)`.
`sameMPV₂_toTensorFromBlocks_perm` gives `SameMPV₂`.  All `IsNormalCanonicalForm`
fields for the permuted family are satisfied by `hIrr (e k)`, `hTP (e k)`, etc. -/
theorem exists_sortedNCF_of_distinct_norms
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hDistinct : ∀ j k : Fin r, j ≠ k → ‖μ j‖ ≠ ‖μ k‖)
    (hμne : ∀ k, μ k ≠ 0)
    (hDim : ∀ k, 0 < dim k) :
    ∃ e : Fin r ≃ Fin r,
      SameMPV₂
        (toTensorFromBlocks (d := d) (μ := μ) blocks)
        (toTensorFromBlocks (d := d) (μ := fun k => μ (e k)) (fun k => blocks (e k))) ∧
      IsNormalCanonicalForm (d := d) (μ := fun k => μ (e k)) (fun k => blocks (e k)) := by
  -- Step 1: Get the sorting permutation and SameMPV₂.
  obtain ⟨e, hSame, he_anti⟩ :=
    exists_sorted_blockDecomp_of_distinct_norms μ blocks hDistinct
  -- Step 2: Package as IsNormalCanonicalForm.
  -- All conditions for the permuted family at index k reduce to the original conditions
  -- at index (e k), because (fun k => blocks (e k)) k = blocks (e k).
  exact ⟨e, hSame, {
    block_irreducible := fun k => hIrr (e k)
    leftCanonical     := fun k => hTP (e k)
    block_primitive   := fun k => hPrim (e k)
    mu_strict_anti    := he_anti
    mu_ne_zero        := fun k => hμne (e k)
    dim_pos           := fun k => hDim (e k)
  }⟩

/-! ### §4. Trivial sector decomposition for the sorted distinct-norm case -/

/-- **Trivial `SectorDecomposition` from a sorted block family.**

Given a block family `(μ, blocks)` with sorted (strictly decreasing) norms and
nonzero weights, package it as a `SectorDecomposition` with `copies j = 1` for all
`j`.  The BNT-level norm ordering condition (§ 4 in the docstring) holds trivially:
each group has exactly one weight `μ j`, and those are already strictly decreasing.

The assembled `P.toTensor` has `SameMPV₂` with `toTensorFromBlocks μ blocks`, proved
by expanding both sides via the decomposition formulas:

  `mpv P.toTensor σ = ∑ j, P.coeff N j * mpv (blocks j) σ`
                    `= ∑ j, (μ j)^N * mpv (blocks j) σ`
                    `= mpv (toTensorFromBlocks μ blocks) σ`.

Here `P.coeff N j = ∑ q : Fin 1, (μ j)^N = (μ j)^N` because `copies j = 1`. -/
theorem exists_trivialSectorDecomp_of_sorted_distinct_norms
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0)
    (hAnti : StrictAnti (fun k : Fin r => ‖μ k‖)) :
    ∃ P : SectorDecomposition d,
      P.basisCount = r ∧
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      StrictAnti (fun j : Fin P.basisCount =>
        ‖P.sectors.weight j ⟨0, P.sectors.copies_pos j⟩‖) := by
  -- Construct the trivial sector decomposition: one copy per block.
  let sectors : SectorWeightData r := {
    copies         := fun _ => 1
    copies_pos     := fun _ => Nat.one_pos
    weight         := fun j _ => μ j
    weight_ne_zero := fun j _ => hμne j
  }
  let P : SectorDecomposition d := {
    basisCount := r
    basisDim   := dim
    basis      := blocks
    sectors    := sectors
  }
  refine ⟨P, rfl, ?_, ?_⟩
  · -- SameMPV₂ P.toTensor (toTensorFromBlocks μ blocks).
    -- Expand both sides using the sector decomposition and blocks formulas.
    intro N σ
    calc mpv P.toTensor σ
        = ∑ j : Fin r, P.coeff N j * mpv (P.basis j) σ :=
            P.mpv_toTensor_eq_sum_coeff σ
      _ = ∑ j : Fin r, (μ j) ^ N * mpv (blocks j) σ := by
            -- P.coeff N j = ∑ q : Fin (sectors.copies j), (sectors.weight j q)^N
            --             = ∑ q : Fin 1, (μ j)^N = (μ j)^N.
            refine Finset.sum_congr rfl fun j _ => congr_arg₂ _ ?_ rfl
            simp [SectorDecomposition.coeff, SectorWeightData.coeff, P, sectors]
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
            symm
            simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ
  · -- StrictAnti on BNT-level norms.
    -- sectors.weight j 0 = μ j by definition, so the condition is exactly hAnti.
    intro i j hij
    change ‖P.sectors.weight j ⟨0, P.sectors.copies_pos j⟩‖ <
      ‖P.sectors.weight i ⟨0, P.sectors.copies_pos i⟩‖
    simp only [P, sectors]
    exact hAnti hij

/-! ### §5. BNT grouping for blocks with possibly equal norms -/

/-- Shared norm-class enumeration used by the BNT grouping constructions. -/
structure NormClassGroupingData {r : ℕ} (μ : Fin r → ℂ) where
  g : ℕ
  vals : Fin g → ℝ
  vals_strictAnti : StrictAnti vals
  copies : Fin g → ℕ
  copies_pos : ∀ j, 0 < copies j
  enum : (j : Fin g) → Fin (copies j) → Fin r
  enum_norm : ∀ j q, ‖μ (enum j q)‖ = vals j
  regroup : ∀ f : Fin r → ℂ, ∑ j : Fin g, ∑ q : Fin (copies j), f (enum j q) = ∑ k : Fin r, f k

/-- Enumerate the norm classes of `μ` in strictly decreasing order of norm. -/
noncomputable def normClassGroupingData {r : ℕ} (μ : Fin r → ℂ) :
    NormClassGroupingData μ := by
  classical
  let normImage : Finset ℝ := Finset.univ.image (fun k : Fin r => ‖μ k‖)
  let g := normImage.card
  let vals : Fin g → ℝ := fun j => normImage.orderEmbOfFin rfl (Fin.rev j)
  have hvals_anti : StrictAnti vals :=
    (normImage.orderEmbOfFin rfl).strictMono.comp_strictAnti Fin.rev_strictAnti
  have hvals_inj : Function.Injective vals := hvals_anti.injective
  have hvals_mem : ∀ j, vals j ∈ normImage :=
    fun j => Finset.orderEmbOfFin_mem normImage rfl (Fin.rev j)
  let normClass : Fin g → Finset (Fin r) :=
    fun j => Finset.univ.filter (fun k => ‖μ k‖ = vals j)
  have hClass_nonempty : ∀ j, (normClass j).Nonempty := by
    intro j
    have hmem := hvals_mem j
    simp only [normImage, Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  have hClass_disj :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin g)) : Set (Fin g)) normClass := by
    intro j₁ _ j₂ _ hne
    apply Finset.disjoint_left.mpr
    intro k hk1 hk2
    exact hne (hvals_inj
      ((Finset.mem_filter.mp hk1).2.symm.trans (Finset.mem_filter.mp hk2).2))
  have hClass_cover : Finset.biUnion Finset.univ normClass = Finset.univ := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    have hmem : ‖μ k‖ ∈ normImage :=
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    rw [← Finset.image_orderEmbOfFin_univ normImage rfl] at hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    refine ⟨Fin.rev i, ?_⟩
    change k ∈ Finset.univ.filter (fun k => ‖μ k‖ = vals (Fin.rev i))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change ‖μ k‖ = normImage.orderEmbOfFin rfl (Fin.rev (Fin.rev i))
    rw [Fin.rev_rev]
    exact hi.symm
  let copiesFn : Fin g → ℕ := fun j => (normClass j).card
  have hcopies_pos : ∀ j, 0 < copiesFn j :=
    fun j => Finset.card_pos.mpr (hClass_nonempty j)
  let enumFn : (j : Fin g) → Fin (copiesFn j) → Fin r :=
    fun j => (normClass j).orderEmbOfFin rfl
  have hEnum_norm : ∀ j q, ‖μ (enumFn j q)‖ = vals j := fun j q =>
    (Finset.mem_filter.mp ((normClass j).orderEmbOfFin_mem rfl q)).2
  have hRegroup : ∀ (f : Fin r → ℂ),
      ∑ j : Fin g, ∑ q : Fin (copiesFn j), f (enumFn j q) = ∑ k : Fin r, f k := by
    intro f
    have inner_eq : ∀ j : Fin g,
        ∑ q : Fin (copiesFn j), f (enumFn j q) = ∑ k ∈ normClass j, f k := by
      intro j
      rw [← Finset.map_orderEmbOfFin_univ (normClass j) rfl, Finset.sum_map]
      rfl
    simp_rw [inner_eq]
    calc ∑ j : Fin g, ∑ k ∈ normClass j, f k
        = ∑ k ∈ Finset.biUnion Finset.univ normClass, f k :=
            (Finset.sum_biUnion hClass_disj).symm
      _ = ∑ k ∈ Finset.univ, f k := by rw [hClass_cover]
      _ = ∑ k : Fin r, f k := rfl
  exact {
    g := g
    vals := vals
    vals_strictAnti := hvals_anti
    copies := copiesFn
    copies_pos := hcopies_pos
    enum := enumFn
    enum_norm := hEnum_norm
    regroup := hRegroup
  }

/-- **BNT grouping step (equal-norm case, proved via norm-class enumeration).**

Given a weighted block family `(μ, blocks)` where some blocks may share the same norm
`‖μ j‖ = ‖μ k‖`, and given that equal-norm blocks share the same dimension and the
same MPV function (hypotheses that follow from BNT uniqueness in the full
formalization), there exists a `SectorDecomposition P` with:

1. `SameMPV₂ P.toTensor (toTensorFromBlocks μ blocks)`.
2. `StrictAnti` on the BNT-level norms (one norm value per group).

**Hypotheses**:
- `hμne`: all weights are nonzero.
- `hDimEq`: equal-norm blocks have the same bond dimension (so that `P.basisDim j`
  is well-defined as `dim (repr j)` for any representative of norm class `j`).
- `hMPVEq`: equal-norm blocks have the same MPV function, i.e., `SameMPV₂ (blocks j) (blocks k)`.
  This is needed so `P.basis j` (a single tensor) can stand in for all blocks in
  norm class `j`.

**Why these hypotheses arise in the full theory**:
In the BNT theory (CPGSV17, §2.3), two blocks with the same weight norm are
gauge-phase equivalent, hence have the same MPV and the same bond dimension.  In the
existence reduction, these properties would be derived after applying the BNT uniqueness
theorem.  Since BNT uniqueness is not yet fully formalized, the hypotheses are stated
explicitly.

**Proof:**
1. Let `S = Finset.univ.image (‖μ ·‖)`, `g = S.card`.
2. Order the norms: `v₀ > v₁ > ... > v_{g-1}` (via `orderEmbOfFin ∘ Fin.rev`).
3. For each `j : Fin g`:
   - `repr j ∈ Fin r`: pick any block with `‖μ (repr j)‖ = v_j`.
   - `classOf j = {k | ‖μ k‖ = v_j}`, `copies j = #classOf j ≥ 1`.
   - Enumerate class: `enum j : Fin (copies j) → Fin r`.
   - `P.basis j = blocks (repr j)`, `P.basisDim j = dim (repr j) = dim k` for all
     `k ∈ classOf j` (well-defined by `hDimEq`).
   - `P.weight j q = μ (enum j q)`.
4. **SameMPV₂**:
   `mpv P.toTensor σ = ∑ j ∑ q, (weight j q)^N · mpv (basis j) σ`
   `= ∑ j ∑_{k ∈ classOf j}, (μ k)^N · mpv (blocks (repr j)) σ`   (def of weight)
   `= ∑ j ∑_{k ∈ classOf j}, (μ k)^N · mpv (blocks k) σ`          (hMPVEq)
   `= ∑_k (μ k)^N · mpv (blocks k) σ`                             (regroup)
   `= mpv (toTensorFromBlocks μ blocks) σ`.
5. **StrictAnti** holds because the `v_j` are strictly decreasing and
   `‖P.weight j ⟨0, _⟩‖ = ‖μ (enum j 0)‖ = v_j`. -/
theorem exists_bnt_grouping
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0)
    -- Equal-norm blocks have the same bond dimension.
    (_hDimEq : ∀ j k : Fin r, ‖μ j‖ = ‖μ k‖ → dim j = dim k)
    -- Equal-norm blocks have the same MPV function (use SameMPV₂ to allow different dims).
    (hMPVEq : ∀ j k : Fin r, ‖μ j‖ = ‖μ k‖ → SameMPV₂ (blocks j) (blocks k)) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      StrictAnti (fun j : Fin P.basisCount =>
        ‖P.sectors.weight j ⟨0, P.sectors.copies_pos j⟩‖) := by
  classical
  let classes := normClassGroupingData μ
  let reprFn : Fin classes.g → Fin r := fun j => classes.enum j ⟨0, classes.copies_pos j⟩
  have hRepr_norm : ∀ j, ‖μ (reprFn j)‖ = classes.vals j :=
    fun j => classes.enum_norm j ⟨0, classes.copies_pos j⟩
  let sectors : SectorWeightData classes.g := {
    copies         := classes.copies
    copies_pos     := classes.copies_pos
    weight         := fun j q => μ (classes.enum j q)
    weight_ne_zero := fun j q => hμne (classes.enum j q)
  }
  let P : SectorDecomposition d := {
    basisCount := classes.g
    basisDim   := fun j => dim (reprFn j)
    basis      := fun j => blocks (reprFn j)
    sectors    := sectors
  }
  refine ⟨P, ?_, ?_⟩
  · -- ── SameMPV₂ proof ──────────────────────────────────────────────────────
    -- We show mpv P.toTensor σ = mpv (toTensorFromBlocks μ blocks) σ for all N, σ.
    intro N σ
    -- Main calculation using the decomposition formula.
    calc mpv P.toTensor σ
        -- Expand via sector decomposition formula.
        = ∑ j : Fin P.basisCount,
            ∑ q : Fin (P.copies j), (P.weight j q) ^ N * mpv (P.basis j) σ :=
            P.mpv_toTensor_eq_sum_sectors σ
      -- Unfold P fields (definitional equalities via let-bindings).
      _ = ∑ j : Fin classes.g,
            ∑ q : Fin (classes.copies j),
              (μ (classes.enum j q)) ^ N * mpv (blocks (reprFn j)) σ := rfl
      -- Replace mpv (blocks (reprFn j)) by mpv (blocks (enumFn j q)) using hMPVEq.
      _ = ∑ j : Fin classes.g,
            ∑ q : Fin (classes.copies j),
              (μ (classes.enum j q)) ^ N * mpv (blocks (classes.enum j q)) σ := by
              refine Finset.sum_congr rfl (fun j _ =>
                Finset.sum_congr rfl (fun q _ => ?_))
              congr 1
              -- Both reprFn j and enumFn j q have norm vals j.
              exact hMPVEq (reprFn j) (classes.enum j q)
                (hRepr_norm j |>.trans (classes.enum_norm j q).symm) N σ
      -- Regroup the double sum over (j, q) into a single sum over Fin r.
      _ = ∑ k : Fin r, (μ k) ^ N * mpv (blocks k) σ :=
            classes.regroup (fun k => (μ k) ^ N * mpv (blocks k) σ)
      -- Recognize as mpv of toTensorFromBlocks.
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
              symm
              simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ
  · -- ── StrictAnti proof ────────────────────────────────────────────────────
    -- P.sectors.weight j ⟨0, _⟩ = μ (enumFn j ⟨0, _⟩) (definitional), with norm vals j.
    intro i j hij
    -- Unfold definitionally: P.sectors.weight j q = μ (enumFn j q).
    change ‖μ (classes.enum j ⟨0, classes.copies_pos j⟩)‖ <
      ‖μ (classes.enum i ⟨0, classes.copies_pos i⟩)‖
    rw [classes.enum_norm j ⟨0, classes.copies_pos j⟩,
      classes.enum_norm i ⟨0, classes.copies_pos i⟩]
    exact classes.vals_strictAnti hij

end MPSTensor
