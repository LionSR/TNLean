/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.PrimitiveBlocks

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Common blocked cyclic-sector families

**Auxiliary record.**  After period removal each nonzero-weight
block splits into cyclic sectors; the sectors from different blocks may
have different physical alphabets.  This file provides the common-reblocking
data that reblocks every sector to a single shared physical blocking length
so that all sectors can be compared in a uniform canonical form.

The structure and its derived theorems are intermediate constructions — they
record reindexing, flattening, and common-alphabet transport.  They are
not independent results of 1606.00608 or 2011.12127.
-/

namespace MPSTensor

/-- **Internal record**: common reblocking data for the cyclic sectors of a finite
nonzero-weight block family.

After period removal, each original block is decomposed into cyclic sectors;
these are then reblocked so that every sector is expressed over one common
blocked physical alphabet.  The record bundles the period-removal lengths, the
additional positive blocking lengths, the primitive irreducible sector tensors,
and the MPV compatibility between the iterated block and the corresponding
unit-weight sum of reblocked cyclic sectors.

This is an auxiliary construction: the flattened common-sector family is derived
canonically from these data, and all attached theorems are properties of the
record's fields.  There is no theorem in CPSV that this record directly
instantiates; it is consumed by the normal canonical-form existence proof chain. -/
structure CommonBlockedCyclicSectorFamily {d r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) where
  /-- The common physical blocking length. -/
  p : ℕ
  /-- The common physical blocking length is positive. -/
  p_pos : 0 < p
  /-- The period-removal length of each original nonzero-weight block. -/
  period : Fin r → ℕ
  /-- Every period-removal length is positive. -/
  period_pos : ∀ k, 0 < period k
  /-- The later reblocking length applied after period removal. -/
  extra : Fin r → ℕ
  /-- Every later reblocking length is positive. -/
  extra_pos : ∀ k, 0 < extra k
  /-- The common length factors as period removal followed by later reblocking. -/
  p_eq_period_mul_extra : ∀ k, p = period k * extra k
  /-- Bond dimensions of the cyclic sector blocks before later reblocking. -/
  sectorDim : (k : Fin r) → Fin (period k) → ℕ
  /-- Cyclic sector blocks before later reblocking. -/
  sectorBlocks : (k : Fin r) → (s : Fin (period k)) →
    MPSTensor (blockPhysDim d (period k)) (sectorDim k s)
  /-- The sector blocks are trace-preserving before later reblocking. -/
  sector_tp : ∀ k s,
    ∑ i : Fin (blockPhysDim d (period k)), (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1
  /-- Each period-blocked nonzero-weight block is represented by its unit-weight cyclic sectors. -/
  sector_same : ∀ k,
    SameMPV₂ (blockTensor (d := d) (D := dim k) (blocks k) (period k))
      (toTensorFromBlocks (d := blockPhysDim d (period k))
        (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k))
  /-- The sector transfer maps are primitive before later reblocking. -/
  sector_primitive : ∀ k s,
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d (period k)) (D := sectorDim k s)
        (sectorBlocks k s))
  /-- The sector blocks are tensor-irreducible before later reblocking. -/
  sector_irreducible : ∀ k s, IsIrreducibleTensor (sectorBlocks k s)
  /-- The sector bond dimensions are positive before later reblocking. -/
  sector_dim_pos : ∀ k s, 0 < sectorDim k s
  /-- The iterated blocked physical alphabet is propositionally the common alphabet. -/
  blockPhysDim_nested_eq : ∀ k,
    blockPhysDim (blockPhysDim d (period k)) (extra k) = blockPhysDim d p
  /-- The checked MPV compatibility condition for each original nonzero-weight block
  after later reblocking. -/
  nested_same : ∀ k,
    SameMPV₂
      (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (blockPhysDim_nested_eq k))
        (blockTensor (d := blockPhysDim d (period k)) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) (period k)) (extra k)))
      (toTensorFromBlocks (d := blockPhysDim d p)
        (μ := fun _ : Fin (period k) => (1 : ℂ))
        (fun s => cast
          (congr_arg (fun d' => MPSTensor d' (sectorDim k s)) (blockPhysDim_nested_eq k))
          (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
            (sectorBlocks k s) (extra k))))

namespace CommonBlockedCyclicSectorFamily

variable {d r : ℕ} {dim : Fin r → ℕ}
variable {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-- Decode a flattened common-sector index as an original block and a cyclic sector. -/
noncomputable def flatKey (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) : (k : Fin r) × Fin (F.period k) :=
  finSigmaFinEquiv.symm x

/-- The flattened sectors produced by `CommonBlockedCyclicSectorFamily` carry unit weights. -/
def flatWeight (F : CommonBlockedCyclicSectorFamily blocks) :
    Fin (∑ k : Fin r, F.period k) → ℂ :=
  fun _ => 1

/-- The common-alphabet sector obtained by later reblocking one cyclic sector. -/
noncomputable def commonSectorBlock (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    MPSTensor (blockPhysDim d F.p) (F.sectorDim k s) :=
  cast (congr_arg (fun d' => MPSTensor d' (F.sectorDim k s))
      (F.blockPhysDim_nested_eq k))
    (blockTensor (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
      (F.sectorBlocks k s) (F.extra k))

/-- Bond dimensions of the derived flattened common-sector family. -/
noncomputable def commonFlatDim (F : CommonBlockedCyclicSectorFamily blocks) :
    Fin (∑ k : Fin r, F.period k) → ℕ :=
  fun x =>
    let y := F.flatKey x
    F.sectorDim y.1 y.2

/-- The derived flattened common-sector family, indexed by `Fin (∑ k, F.period k)`. -/
noncomputable def commonFlatBlocks (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) :
    MPSTensor (blockPhysDim d F.p) (F.commonFlatDim x) :=
  let y := F.flatKey x
  show MPSTensor (blockPhysDim d F.p) (F.sectorDim y.1 y.2) from
    F.commonSectorBlock y.1 y.2

/-- The common-alphabet sector tensor for one original nonzero-weight block. -/
noncomputable def commonSectorTensor (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : MPSTensor (blockPhysDim d F.p) (∑ s : Fin (F.period k), F.sectorDim k s) :=
  toTensorFromBlocks (d := blockPhysDim d F.p)
    (μ := fun _ : Fin (F.period k) => (1 : ℂ)) (F.commonSectorBlock k)

/-- The common blocked tensor obtained by reindexing blocked physical words from
iterated blocking to the ambient blocked alphabet. -/
noncomputable def commonReindexedBlock (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : MPSTensor (blockPhysDim d F.p) (dim k) :=
  cast (congr_arg (fun d' => MPSTensor d' (dim k)) (F.blockPhysDim_nested_eq k))
    (reindexPhysical (iteratedBlockIndex d (F.period k) (F.extra k))
      (blockTensor (d := d) (D := dim k) (blocks k) (F.period k * F.extra k)))

/-- The derived flattened sector weights obtained from the original nonzero weights after
blocking by the common length. -/
noncomputable def commonFlatWeight (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) : Fin (∑ k : Fin r, F.period k) → ℂ :=
  fun x => (μ (F.flatKey x).1) ^ F.p

/-- Flattened sector weights remain nonzero after common blocking. -/
theorem commonFlatWeight_ne_zero (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (x : Fin (∑ k : Fin r, F.period k)) : F.commonFlatWeight μ x ≠ 0 :=
  pow_ne_zero F.p (hμ (F.flatKey x).1)

private theorem commonSectorBlock_structural (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    (∑ i : Fin (blockPhysDim d F.p),
      (F.commonSectorBlock k s i)ᴴ * F.commonSectorBlock k s i = 1) ∧
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d F.p) (D := F.sectorDim k s)
        (F.commonSectorBlock k s)) ∧
    IsIrreducibleTensor (F.commonSectorBlock k s) := by
  haveI : NeZero (F.sectorDim k s) := ⟨Nat.ne_of_gt (F.sector_dim_pos k s)⟩
  have hExtra := tp_primitive_irreducible_extra_blocking
    (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
    (A := F.sectorBlocks k s) (F.sector_tp k s) (F.sector_primitive k s)
    (F.sector_irreducible k s) (hk := F.extra_pos k)
  refine ⟨?_, ?_, ?_⟩
  · have hcast := (leftCanonical_cast_physDim (F.blockPhysDim_nested_eq k)
      (A := blockTensor (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
        (F.sectorBlocks k s) (F.extra k))).2 hExtra.1
    simpa [commonSectorBlock] using hcast
  · have hcast := (isPrimitive_transferMap_cast_physDim (F.blockPhysDim_nested_eq k)
      (A := blockTensor (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
        (F.sectorBlocks k s) (F.extra k))).2 hExtra.2.1
    simpa [commonSectorBlock] using hcast
  · have hcast := (isIrreducibleTensor_cast_physDim (F.blockPhysDim_nested_eq k)
      (A := blockTensor (d := blockPhysDim d (F.period k)) (D := F.sectorDim k s)
        (F.sectorBlocks k s) (F.extra k))).2 hExtra.2.2
    simpa [commonSectorBlock] using hcast

/-- The iterated blocked tensor `(B_k^{[m_k]})^{[e_k]}` agrees with the directly blocked
tensor `B_k^{[p]}` after transport to the common blocked alphabet.

By definition, `commonReindexedBlock k` is the direct $p$-blocked tensor of
block $k$, transported to the common physical alphabet $d^{[p]}$ by the canonical
reindexing. -/
theorem reindexed_sameMPV₂
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) :
    SameMPV₂
      (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (F.blockPhysDim_nested_eq k))
        (blockTensor (d := blockPhysDim d (F.period k)) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) (F.period k)) (F.extra k)))
      (F.commonReindexedBlock k) := by
  have h := sameMPV₂_blockTensor_blockTensor_mul_reindex
    (d := d) (D := dim k) (A := blocks k) (m := F.period k) (n := F.extra k)
  exact (sameMPV₂_cast_physDim (F.blockPhysDim_nested_eq k)
    (A := blockTensor (d := blockPhysDim d (F.period k)) (D := dim k)
      (blockTensor (d := d) (D := dim k) (blocks k) (F.period k)) (F.extra k))
    (B := reindexPhysical (iteratedBlockIndex d (F.period k) (F.extra k))
      (blockTensor (d := d) (D := dim k) (blocks k) (F.period k * F.extra k)))).2 h

/-- A relabeled nonzero-weight block is represented by its common-alphabet cyclic sectors. -/
private theorem commonReindexedBlock_sameMPV₂_commonSectorTensor
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) :
    SameMPV₂ (F.commonReindexedBlock k) (F.commonSectorTensor k) := by
  intro N σ
  calc
    mpv (F.commonReindexedBlock k) σ =
        mpv (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (F.blockPhysDim_nested_eq k))
          (blockTensor (d := blockPhysDim d (F.period k)) (D := dim k)
            (blockTensor (d := d) (D := dim k) (blocks k) (F.period k)) (F.extra k))) σ :=
      ((F.reindexed_sameMPV₂ k) N σ).symm
    _ = mpv (F.commonSectorTensor k) σ := by
      simpa [commonSectorTensor, commonSectorBlock] using F.nested_same k N σ

/-- Weighted nonzero blocks with explicit relabelings flatten to the common-sector family. -/
private theorem sameMPV₂_weightedCommonReindexedBlock_commonFlat
    (F : CommonBlockedCyclicSectorFamily blocks) (μ : Fin r → ℂ) :
    SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) (F.commonReindexedBlock))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) (F.commonFlatBlocks)) := by
  intro N σ
  let gSigma : ((k : Fin r) × Fin (F.period k)) → ℂ := fun y =>
    ((μ y.1) ^ F.p) ^ N * mpv (F.commonSectorBlock y.1 y.2) σ
  calc
    mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) (F.commonReindexedBlock)) σ
        = ∑ k : Fin r, ((μ k) ^ F.p) ^ N •
            mpv (F.commonReindexedBlock k) σ :=
          mpv_toTensorFromBlocks_eq_sum (fun k : Fin r => (μ k) ^ F.p)
            (F.commonReindexedBlock) σ
    _ = ∑ k : Fin r, ((μ k) ^ F.p) ^ N • mpv (F.commonSectorTensor k) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [F.commonReindexedBlock_sameMPV₂_commonSectorTensor k N σ]
    _ = ∑ k : Fin r, ∑ s : Fin (F.period k),
          ((μ k) ^ F.p) ^ N • mpv (F.commonSectorBlock k s) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          change ((μ k) ^ F.p) ^ N •
              mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
                (fun _ : Fin (F.period k) => (1 : ℂ)) (F.commonSectorBlock k)) σ =
            ∑ s : Fin (F.period k),
              ((μ k) ^ F.p) ^ N • mpv (F.commonSectorBlock k s) σ
          rw [mpv_toTensorFromBlocks_eq_sum
            (fun _ : Fin (F.period k) => (1 : ℂ)) (F.commonSectorBlock k) σ]
          simp [smul_eq_mul, Finset.mul_sum]
    _ = ∑ y : ((k : Fin r) × Fin (F.period k)),
          ((μ y.1) ^ F.p) ^ N • mpv (F.commonSectorBlock y.1 y.2) σ :=
          (Fintype.sum_sigma'
            (fun k s => ((μ k) ^ F.p) ^ N • mpv (F.commonSectorBlock k s) σ)).symm
    _ = ∑ x : Fin (∑ k : Fin r, F.period k),
          (F.commonFlatWeight μ x) ^ N • mpv (F.commonFlatBlocks x) σ := by
          have h := (Equiv.sum_comp
            (finSigmaFinEquiv.symm :
              Fin (∑ k : Fin r, F.period k) ≃ ((k : Fin r) × Fin (F.period k)))
            gSigma).symm
          simpa [gSigma, commonFlatWeight, commonFlatBlocks, commonFlatDim, flatKey,
            smul_eq_mul] using h
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) (F.commonFlatBlocks)) σ :=
          (mpv_toTensorFromBlocks_eq_sum (F.commonFlatWeight μ) (F.commonFlatBlocks) σ).symm

/-! ### Direct-vs-iterated blocking identifications (internal intermediate construction)

The remaining theorems compare the directly-blocked and iteratively-blocked
forms of each nonzero-weight block.  They verify that the canonical
identification of blocked physical words is compatible with the consecutive
grouping of digits.  These are internal to the common-blocking construction
and do not correspond to independent results of CPSV.
-/

/-- The canonical identification from the common blocked alphabet to one iterated blocked alphabet
agrees with the map obtained by grouping a direct blocked word into consecutive blocks. -/
private def groupedBlockCastAgrees
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) : Prop :=
  ∀ i : Fin (blockPhysDim d F.p),
    Fin.cast ((F.blockPhysDim_nested_eq k).symm) i =
      directToIteratedBlockIndex d (F.period k) (F.extra k)
        (Fin.cast (congr_arg (blockPhysDim d) (F.p_eq_period_mul_extra k)) i)

/-- The grouped-block cast predicate is equivalently the assertion that flattening the
order-preserving cast from the common blocked alphabet gives the corresponding direct
blocked index.  This isolates the remaining point as a comparison between the `Fin.cast`
identification and the canonical direct/iterated blocking equivalence. -/
private theorem groupedBlockCastAgrees_iff_iteratedBlockIndex_cast
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) :
    F.groupedBlockCastAgrees k ↔
      ∀ i : Fin (blockPhysDim d F.p),
        iteratedBlockIndex d (F.period k) (F.extra k)
          (Fin.cast ((F.blockPhysDim_nested_eq k).symm) i) =
          Fin.cast (congr_arg (blockPhysDim d) (F.p_eq_period_mul_extra k)) i := by
  constructor
  · intro hCast i
    rw [hCast i, iteratedBlockIndex_directToIteratedBlockIndex]
  · intro hIndex i
    calc
      Fin.cast ((F.blockPhysDim_nested_eq k).symm) i =
          directToIteratedBlockIndex d (F.period k) (F.extra k)
            (iteratedBlockIndex d (F.period k) (F.extra k)
              (Fin.cast ((F.blockPhysDim_nested_eq k).symm) i)) := by
            rw [directToIteratedBlockIndex_iteratedBlockIndex]
      _ = directToIteratedBlockIndex d (F.period k) (F.extra k)
          (Fin.cast (congr_arg (blockPhysDim d) (F.p_eq_period_mul_extra k)) i) := by
            rw [hIndex i]

/-- Reading the `t`th base-`d` digit inside the `j`th block of length `m`
is the same as reading digit `m*j+t` directly. -/
private lemma Nat.div_pow_mod_pow_block (x d m j t : ℕ) (ht : t < m) :
    x / (d ^ m) ^ j % d ^ m / d ^ t % d =
      x / d ^ (m * j + t) % d := by
  have ht_le : t ≤ m := Nat.le_of_lt ht
  have hpow : d ^ m = d ^ (t : ℕ) * d ^ (m - (t : ℕ)) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le ht_le]
  nth_rewrite 2 [hpow]
  rw [Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd]
  · rw [Nat.div_div_eq_div_mul]
    have hden : (d ^ m) ^ j * d ^ t = d ^ (m * j + t) := by
      rw [← Nat.pow_mul, ← Nat.pow_add]
    rw [hden]
  · simpa using Nat.pow_dvd_pow d (by omega : 1 ≤ m - t)

/-- Flattening the explicit length-`n` blocked decoding of a length-`m*n` index agrees with
the direct length-`m*n` decoding. -/
private theorem flattenWordOfBlock_cast_eq {d m n p : ℕ}
    (hp_eq : p = m * n) (h_card : blockPhysDim (blockPhysDim d m) n = blockPhysDim d p)
    (i : Fin (blockPhysDim d p)) :
    flattenBlockedWord d m
      (wordOfBlock (blockPhysDim d m) n (Fin.cast h_card.symm i)) =
    wordOfBlock d p i := by
  subst hp_eq
  simp only [flattenBlockedWord, wordOfBlock, decodeBlock, List.map_ofFn, Function.comp_apply]
  rw [List.ofFn_mul']
  apply congrArg List.flatten
  exact congrArg List.ofFn (funext fun j => by
    simp only [wordOfBlock, decodeBlock, Fin.cast_cast, Function.comp_apply]
    exact congrArg List.ofFn (funext fun t => by
      apply Fin.ext
      simpa [blockPhysDim_eq_pow] using
        Nat.div_pow_mod_pow_block (x := (i : ℕ)) (d := d) (m := m)
          (j := (j : ℕ)) (t := (t : ℕ)) t.isLt))

/-- The global grouping-cast hypothesis applied to a specific family reduces to the
core Fintype-level assertion. -/
private theorem groupedBlockCastAgrees_of_flattenWordOfBlock_cast_eq
    {d : ℕ} (h_flatten : ∀ {m n p : ℕ} (_ : p = m * n)
      (h_card : blockPhysDim (blockPhysDim d m) n = blockPhysDim d p)
      (i : Fin (blockPhysDim d p)),
      flattenBlockedWord d m
        (wordOfBlock (blockPhysDim d m) n (Fin.cast h_card.symm i)) =
      wordOfBlock d p i)
    {r : ℕ} {dim : Fin r → ℕ}
    {blocks : (k : Fin r) → MPSTensor d (dim k)}
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) :
    F.groupedBlockCastAgrees k := by
  rw [F.groupedBlockCastAgrees_iff_iteratedBlockIndex_cast k]
  intro i
  let m := F.period k
  let n := F.extra k
  have hp_eq : F.p = m * n := F.p_eq_period_mul_extra k
  have hcard_symm : blockPhysDim d F.p = blockPhysDim (blockPhysDim d m) n :=
    (F.blockPhysDim_nested_eq k).symm
  have hcast_eq : iteratedBlockIndex d m n (Fin.cast hcard_symm i) =
      Fin.cast (congr_arg (blockPhysDim d) hp_eq) i := by
    apply wordOfBlock_injective d (m * n)
    calc
      wordOfBlock d (m * n)
        (iteratedBlockIndex d m n (Fin.cast hcard_symm i)) =
        flattenBlockedWord d m
          (wordOfBlock (blockPhysDim d m) n (Fin.cast hcard_symm i)) := by
        rw [wordOfBlock_iteratedBlockIndex]
      _ = wordOfBlock d F.p i := by
        simpa [hcard_symm, hp_eq] using h_flatten hp_eq (F.blockPhysDim_nested_eq k) i
      _ = wordOfBlock d (m * n)
          (Fin.cast (congr_arg (blockPhysDim d) hp_eq) i) :=
        (wordOfBlock_cast_length d hp_eq i).symm
  simpa using hcast_eq

/-- The blocked-word comparison follows if the canonical identification from the common
alphabet to an iterated alphabet agrees with the grouping map that reads a direct word in
consecutive blocks of length $m_k$ (the period of block $k$). -/
private theorem wordOfBlock_eq_iteratedBlockIndex_of_groupedBlockCastAgrees
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r)
    (hCast : F.groupedBlockCastAgrees k) :
    ∀ i : Fin (blockPhysDim d F.p),
      wordOfBlock d F.p i =
        wordOfBlock d (F.period k * F.extra k)
          (iteratedBlockIndex d (F.period k) (F.extra k)
            (Fin.cast ((F.blockPhysDim_nested_eq k).symm) i)) := by
  intro i
  calc
    wordOfBlock d F.p i =
        wordOfBlock d (F.period k * F.extra k)
          (Fin.cast (congr_arg (blockPhysDim d) (F.p_eq_period_mul_extra k)) i) :=
      (wordOfBlock_cast_length d (F.p_eq_period_mul_extra k) i).symm
    _ = wordOfBlock d (F.period k * F.extra k)
        (iteratedBlockIndex d (F.period k) (F.extra k)
          (directToIteratedBlockIndex d (F.period k) (F.extra k)
            (Fin.cast (congr_arg (blockPhysDim d) (F.p_eq_period_mul_extra k)) i))) :=
      (wordOfBlock_iteratedBlockIndex_directToIteratedBlockIndex
        d (F.period k) (F.extra k)
        (Fin.cast (congr_arg (blockPhysDim d) (F.p_eq_period_mul_extra k)) i)).symm
    _ = wordOfBlock d (F.period k * F.extra k)
        (iteratedBlockIndex d (F.period k) (F.extra k)
          (Fin.cast ((F.blockPhysDim_nested_eq k).symm) i)) := by
          rw [← hCast i]

/-- If the two decodings of each blocked physical word agree, then directly blocking
one original block gives the corresponding block obtained through iterated blocking.

The hypothesis compares the word read from the common block alphabet with the word
read after first viewing the same index as an iterated block and then flattening it. -/
private theorem blockTensor_eq_commonReindexedBlock_of_word_eq
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r)
    (hWord : ∀ i : Fin (blockPhysDim d F.p),
      wordOfBlock d F.p i =
        wordOfBlock d (F.period k * F.extra k)
          (iteratedBlockIndex d (F.period k) (F.extra k)
            (Fin.cast ((F.blockPhysDim_nested_eq k).symm) i))) :
    blockTensor (d := d) (D := dim k) (blocks k) F.p = F.commonReindexedBlock k := by
  funext i
  rw [commonReindexedBlock, cast_physDim_apply (F.blockPhysDim_nested_eq k)]
  simp [reindexPhysical, blockTensor, hWord i]

/-- Direct blocking of one original block is the relabeled common block when the
canonical identification with the iterated alphabet agrees with consecutive grouping of the
direct word. -/
private theorem blockTensor_eq_commonReindexedBlock_of_groupedBlockCastAgrees
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r)
    (hCast : F.groupedBlockCastAgrees k) :
    blockTensor (d := d) (D := dim k) (blocks k) F.p = F.commonReindexedBlock k :=
  F.blockTensor_eq_commonReindexedBlock_of_word_eq k
    (F.wordOfBlock_eq_iteratedBlockIndex_of_groupedBlockCastAgrees k hCast)

/-- Direct and iterated common blocking of one original block have the same MPV family
when the canonical identification with the iterated alphabet agrees with consecutive grouping. -/
private theorem blockTensor_sameMPV₂_commonReindexedBlock_of_groupedBlockCastAgrees
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r)
    (hCast : F.groupedBlockCastAgrees k) :
    SameMPV₂
      (blockTensor (d := d) (D := dim k) (blocks k) F.p)
      (F.commonReindexedBlock k) := by
  rw [F.blockTensor_eq_commonReindexedBlock_of_groupedBlockCastAgrees k hCast]
  intro N σ
  rfl

/-- Blockwise MPV comparisons assemble over the weighted direct sum after common blocking. -/
private theorem sameMPV₂_weightedCanonicalBlock_commonReindexedBlock_of_blockwise
    (F : CommonBlockedCyclicSectorFamily blocks) (μ : Fin r → ℂ)
    (hBlock : ∀ k : Fin r,
      SameMPV₂
        (blockTensor (d := d) (D := dim k) (blocks k) F.p)
        (F.commonReindexedBlock k)) :
    SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) F.commonReindexedBlock) := by
  intro N σ
  calc
    mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p)) σ
        = ∑ k : Fin r, ((μ k) ^ F.p) ^ N •
            mpv (blockTensor (d := d) (D := dim k) (blocks k) F.p) σ :=
          mpv_toTensorFromBlocks_eq_sum (fun k : Fin r => (μ k) ^ F.p)
            (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p) σ
    _ = ∑ k : Fin r, ((μ k) ^ F.p) ^ N • mpv (F.commonReindexedBlock k) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hBlock k N σ]
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p) F.commonReindexedBlock) σ :=
          (mpv_toTensorFromBlocks_eq_sum (fun k : Fin r => (μ k) ^ F.p)
            F.commonReindexedBlock σ).symm

/-- Each sector tensor in the common reblocked cyclic-sector family is trace-preserving,
has primitive transfer map, is tensor-irreducible, and has positive bond dimension. -/
theorem derived_properties (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    (∑ i : Fin (blockPhysDim d F.p),
        (F.commonSectorBlock k s i)ᴴ * F.commonSectorBlock k s i = 1) ∧
    _root_.IsPrimitive
        (transferMap (d := blockPhysDim d F.p) (D := F.sectorDim k s)
          (F.commonSectorBlock k s)) ∧
    IsIrreducibleTensor (F.commonSectorBlock k s) ∧
    0 < F.sectorDim k s := by
  have h := commonSectorBlock_structural F k s
  exact ⟨h.1, h.2.1, h.2.2, F.sector_dim_pos k s⟩

/-- The direct $p$-blocked tensor $B_k^{[p]}$ has the same MPV family as its image in the
common alphabet via `commonReindexedBlock`. This is the unconditional common-alphabet
comparison used by `reindexed_nonzero_part`. -/
theorem blockTensor_sameMPV₂_commonReindexedBlock
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) :
    SameMPV₂
      (blockTensor (d := d) (D := dim k) (blocks k) F.p)
      (F.commonReindexedBlock k) :=
  F.blockTensor_sameMPV₂_commonReindexedBlock_of_groupedBlockCastAgrees k
    (groupedBlockCastAgrees_of_flattenWordOfBlock_cast_eq
      (fun hp_eq => flattenWordOfBlock_cast_eq hp_eq) F k)

/-- The nonzero-part decomposition of a weighted block sum $\bigoplus_k \mu_k B_k$
transports through the common-alphabet identification: the common-alphabet sectors
have the same nonzero-part decomposition as the direct $p$-blocked tensors. After
blocking by length $p$, the per-block scalar weights $\mu_k$ become $\mu_k^{p}$ since
each $B_k^{[p]}$ is a $p$-fold matrix product. -/
theorem reindexed_nonzero_part (F : CommonBlockedCyclicSectorFamily blocks) (μ : Fin r → ℂ) :
    SameMPV₂
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => blockTensor (d := d) (D := dim k) (blocks k) F.p))
      (toTensorFromBlocks (d := blockPhysDim d F.p)
        (μ := F.commonFlatWeight μ) (F.commonFlatBlocks)) := by
  intro N σ
  exact (F.sameMPV₂_weightedCanonicalBlock_commonReindexedBlock_of_blockwise μ
      (fun k => F.blockTensor_sameMPV₂_commonReindexedBlock k) N σ).trans
    (F.sameMPV₂_weightedCommonReindexedBlock_commonFlat μ N σ)

end CommonBlockedCyclicSectorFamily

end MPSTensor
