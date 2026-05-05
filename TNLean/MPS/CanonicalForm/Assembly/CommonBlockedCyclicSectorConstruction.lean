/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.CyclicSectorDecomposition

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Common blocked cyclic-sector construction

This file constructs the common blocked cyclic-sector family used in the
canonical-form reduction.  The cyclic-sector decomposition itself lives in
`CyclicSectorDecomposition`; this module packages the one-block period-removal
data and chooses a common physical blocking length for a finite block family.
-/

namespace MPSTensor

variable {d D : ℕ}

section CommonBlockedConstruction

/-- One-block period-removal data with primitive irreducible sectors.

`HasPrimitiveIrreducibleCyclicSectors A` means that some positive period `m`
removes the cyclic peripheral structure of `A`: the blocked tensor `A^[m]` is
represented by unit-weight sector blocks, each of which is trace-preserving, has
primitive transfer map, is tensor-irreducible, and has positive bond dimension.
The later common-refinement or Wielandt/injectivity blocking length is deliberately
not part of this predicate. -/
def HasPrimitiveIrreducibleCyclicSectors {d D : ℕ} (A : MPSTensor d D) : Prop :=
  ∃ (m : ℕ), 0 < m ∧
  ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
    (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
    SameMPV₂ (blockTensor (d := d) (D := D) A m)
      (toTensorFromBlocks (d := blockPhysDim d m) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
    (∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d m) (D := dim k) (blocks k))) ∧
    (∀ k, IsIrreducibleTensor (blocks k)) ∧
    (∀ k, 0 < dim k)

/-- Trace-preserving irreducible tensors have primitive irreducible cyclic sectors. -/
theorem hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A) :
    HasPrimitiveIrreducibleCyclicSectors A := by
  simpa [HasPrimitiveIrreducibleCyclicSectors] using
    exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor
      (d := d) (D := D) A hTP hIrr

/-- A finite family of nonzero-weight blocks with per-block primitive irreducible cyclic sectors
admits a prescribed common physical blocking length, provided that the prescribed
length is a positive multiple of every period-removal length.

This variant is used for two-sided constructions: one first chooses a common
multiple of the period-removal lengths on both sides, then builds each one-sided
cyclic sector family at that same physical length. -/
theorem exists_commonBlockedCyclicSectorFamily_of_commonMultiple
    {d r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hcyc : ∀ k, HasPrimitiveIrreducibleCyclicSectors (blocks k))
    (p : ℕ) (hp : 0 < p)
    (hperiod_dvd : ∀ k, (hcyc k).choose ∣ p) :
    Nonempty { F : CommonBlockedCyclicSectorFamily blocks // F.p = p } := by
  classical
  let period : Fin r → ℕ := fun k => (hcyc k).choose
  have period_pos : ∀ k, 0 < period k := fun k => (hcyc k).choose_spec.1
  let sectorDim : (k : Fin r) → Fin (period k) → ℕ :=
    fun k => (hcyc k).choose_spec.2.choose
  let sectorBlocks : (k : Fin r) → (s : Fin (period k)) →
      MPSTensor (blockPhysDim d (period k)) (sectorDim k s) :=
    fun k => (hcyc k).choose_spec.2.choose_spec.choose
  have hSector : ∀ k,
      (∀ s, ∑ i : Fin (blockPhysDim d (period k)),
        (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1) ∧
      SameMPV₂ (blockTensor (d := d) (D := dim k) (blocks k) (period k))
        (toTensorFromBlocks (d := blockPhysDim d (period k))
          (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k)) ∧
      (∀ s, _root_.IsPrimitive
        (transferMap (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s))) ∧
      (∀ s, IsIrreducibleTensor (sectorBlocks k s)) ∧
      (∀ s, 0 < sectorDim k s) := by
    intro k
    exact (hcyc k).choose_spec.2.choose_spec.choose_spec
  have sector_tp : ∀ k s,
      ∑ i : Fin (blockPhysDim d (period k)),
        (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1 := fun k => (hSector k).1
  have sector_same : ∀ k,
      SameMPV₂ (blockTensor (d := d) (D := dim k) (blocks k) (period k))
        (toTensorFromBlocks (d := blockPhysDim d (period k))
          (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k)) :=
    fun k => (hSector k).2.1
  have sector_primitive : ∀ k s,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s)) := fun k => (hSector k).2.2.1
  have sector_irreducible : ∀ k s, IsIrreducibleTensor (sectorBlocks k s) :=
    fun k => (hSector k).2.2.2.1
  have sector_dim_pos : ∀ k s, 0 < sectorDim k s :=
    fun k => (hSector k).2.2.2.2
  let extra : Fin r → ℕ := fun k => (hperiod_dvd k).choose
  have p_eq_period_mul_extra : ∀ k, p = period k * extra k :=
    fun k => (hperiod_dvd k).choose_spec
  have extra_pos : ∀ k, 0 < extra k := by
    intro k
    have hmul_pos : 0 < period k * extra k := by
      simpa [p_eq_period_mul_extra k] using hp
    exact Nat.pos_of_mul_pos_left hmul_pos
  have hPhys : ∀ k,
      blockPhysDim (blockPhysDim d (period k)) (extra k) = blockPhysDim d p := by
    intro k
    simpa [p_eq_period_mul_extra k] using
      (blockPhysDim_blockPhysDim d (period k) (extra k))
  have hExtra : ∀ k s,
      (∑ i : Fin (blockPhysDim (blockPhysDim d (period k)) (extra k)),
        (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s) (extra k) i)ᴴ *
          blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
            (sectorBlocks k s) (extra k) i = 1) ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim (blockPhysDim d (period k)) (extra k))
          (D := sectorDim k s)
          (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
            (sectorBlocks k s) (extra k))) ∧
      IsIrreducibleTensor
        (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s) (extra k)) := by
    intro k s
    haveI : NeZero (sectorDim k s) := ⟨Nat.ne_of_gt (sector_dim_pos k s)⟩
    exact tp_primitive_irreducible_extra_blocking
      (d := blockPhysDim d (period k)) (D := sectorDim k s)
      (A := sectorBlocks k s) (sector_tp k s) (sector_primitive k s)
      (sector_irreducible k s) (hk := extra_pos k)
  have nested_same : ∀ k,
      SameMPV₂
        (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (hPhys k))
          (blockTensor (d := blockPhysDim d (period k)) (D := dim k)
            (blockTensor (d := d) (D := dim k) (blocks k) (period k)) (extra k)))
        (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (fun s => cast
            (congr_arg (fun d' => MPSTensor d' (sectorDim k s)) (hPhys k))
            (blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
              (sectorBlocks k s) (extra k)))) := by
    intro k
    have hNested : SameMPV₂
        (blockTensor (d := blockPhysDim d (period k)) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) (period k)) (extra k))
        (toTensorFromBlocks (d := blockPhysDim (blockPhysDim d (period k)) (extra k))
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (fun s => blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
            (sectorBlocks k s) (extra k))) := by
      simpa using
        (sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks
          (d := blockPhysDim d (period k)) (D := dim k)
          (A := blockTensor (d := d) (D := dim k) (blocks k) (period k))
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (blocks := sectorBlocks k) (hSame := sector_same k) (p := extra k))
    have hCast := (sameMPV₂_cast_physDim (hPhys k)
      (A := blockTensor (d := blockPhysDim d (period k)) (D := dim k)
        (blockTensor (d := d) (D := dim k) (blocks k) (period k)) (extra k))
      (B := toTensorFromBlocks (d := blockPhysDim (blockPhysDim d (period k)) (extra k))
        (μ := fun _ : Fin (period k) => (1 : ℂ))
        (fun s => blockTensor (d := blockPhysDim d (period k)) (D := sectorDim k s)
          (sectorBlocks k s) (extra k)))).2 hNested
    rw [toTensorFromBlocks_cast_physDim (h := hPhys k)] at hCast
    simpa using hCast
  exact ⟨⟨{
    p := p
    p_pos := hp
    period := period
    period_pos := period_pos
    extra := extra
    extra_pos := extra_pos
    p_eq_period_mul_extra := p_eq_period_mul_extra
    sectorDim := sectorDim
    sectorBlocks := sectorBlocks
    sector_tp := sector_tp
    sector_same := sector_same
    sector_primitive := sector_primitive
    sector_irreducible := sector_irreducible
    sector_dim_pos := sector_dim_pos
    blockPhysDim_nested_eq := hPhys
    nested_same := nested_same }, rfl⟩⟩

/-- A finite family of nonzero-weight blocks with per-block primitive irreducible cyclic sectors
admits one common physical blocking length for all those sectors.

This theorem chooses the least common multiple of the per-block period-removal
lengths.  Each cyclic sector is then blocked by the corresponding quotient,
identified with the common physical alphabet, and collected into one finite
flattened family.  Trace preservation, primitive transfer maps, tensor
irreducibility, positive bond dimensions, nonzero unit weights, and the per-block
iterated-blocking MPV compatibility conditions are all retained. -/
theorem exists_commonBlockedCyclicSectorFamily_of_hasPrimitiveIrreducibleCyclicSectors
    {d r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hcyc : ∀ k, HasPrimitiveIrreducibleCyclicSectors (blocks k)) :
    Nonempty (CommonBlockedCyclicSectorFamily blocks) := by
  classical
  let period : Fin r → ℕ := fun k => (hcyc k).choose
  have period_pos : ∀ k, 0 < period k := fun k => (hcyc k).choose_spec.1
  obtain ⟨F, _hFp⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_commonMultiple
      blocks hcyc (lcmPeriod period) (lcmPeriod_pos period_pos) (by
        intro k
        simpa [period] using (dvd_lcmPeriod period k))
  exact ⟨F⟩

end CommonBlockedConstruction

end MPSTensor
