/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.CyclicSectorDecomposition
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.CommonBlockedCyclicSectorFamily

/-!
# Common blocked cyclic-sector construction

This file constructs the common blocked cyclic-sector family used in the
canonical-form reduction.  The cyclic-sector decomposition itself lives in
`CyclicSectorDecomposition`; this module encodes the one-block period-removal
data and chooses a common physical blocking length for a finite block family.

It also contains the following results.

* `MPSTensor.afterBlocking_perBlockCyclicData_of_sameMPV₂Pos`,
  `MPSTensor.afterBlocking_commonLengthCommonSectorData_of_sameMPV₂Pos`: common-sector witnesses for
  the after-blocking reduction.
* `MPSTensor.unconditional_commonPrimitiveIrreducibleBlocks`: common-sector transport after
  canonical-form blocking.
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

namespace MPSTensor

section CommonBlockedCyclicSectorConstruction

variable {α : Type*} [Fintype α] {D : ℕ}

section CommonBlockedConstruction

/-- One-block period-removal data with primitive irreducible sectors.

`HasPrimitiveIrreducibleCyclicSectors A` means that some positive period `m`
removes the cyclic peripheral structure of `A`: the blocked tensor `A^[m]` is
represented by unit-weight sector blocks, each of which is trace-preserving, has
primitive transfer map, is tensor-irreducible, and has positive bond dimension.
The later common-refinement or Wielandt/injectivity blocking length is deliberately
not part of this predicate. -/
def HasPrimitiveIrreducibleCyclicSectors {α : Type*} [Fintype α] {D : ℕ} (A : MPTensor α (Fin D)) : Prop :=
  ∃ (m : ℕ), 0 < m ∧
  ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPTensor (Fin m → α) (Fin (dim k))),
    (∀ k, ∑ i : (Fin m → α), (blocks k i)ᴴ * blocks k i = 1) ∧
    SameMPV₂ (Kraus.block A m)
      (toTensorFromBlocks (α := (Fin m → α)) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
    (∀ k, _root_.IsPrimitive
      (Kraus.transferMap (ι := (Fin m → α)) (n := Fin (dim k)) (blocks k))) ∧
    (∀ k, Kraus.IsIrreducibleFamily (blocks k)) ∧
    (∀ k, 0 < dim k)

/-- A finite family of nonzero-weight blocks with per-block primitive irreducible cyclic sectors
admits a prescribed common physical blocking length, provided that the prescribed
length is a positive multiple of every period-removal length.

This variant is used for two-sided constructions: one first chooses a common
multiple of the period-removal lengths on both sides, then builds each one-sided
cyclic sector family at that same physical length. -/
theorem exists_commonBlockedCyclicSectorFamily_of_commonMultiple
    {α : Type*} [Fintype α] {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
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
      MPTensor (Fin (period k) → α) (Fin (sectorDim k s)) :=
    fun k => (hcyc k).choose_spec.2.choose_spec.choose
  have hSector : ∀ k,
      (∀ s, ∑ i : (Fin (period k) → α),
        (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1) ∧
      SameMPV₂ (Kraus.block (blocks k) (period k))
        (toTensorFromBlocks (α := (Fin (period k) → α))
          (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k)) ∧
      (∀ s, _root_.IsPrimitive
        (Kraus.transferMap (ι := (Fin (period k) → α)) (n := Fin (sectorDim k s))
          (sectorBlocks k s))) ∧
      (∀ s, Kraus.IsIrreducibleFamily (sectorBlocks k s)) ∧
      (∀ s, 0 < sectorDim k s) := by
    intro k
    exact (hcyc k).choose_spec.2.choose_spec.choose_spec
  have sector_tp : ∀ k s,
      ∑ i : (Fin (period k) → α),
        (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1 := fun k => (hSector k).1
  have sector_same : ∀ k,
      SameMPV₂ (Kraus.block (blocks k) (period k))
        (toTensorFromBlocks (α := (Fin (period k) → α))
          (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k)) :=
    fun k => (hSector k).2.1
  have sector_primitive : ∀ k s,
      _root_.IsPrimitive
        (Kraus.transferMap (ι := (Fin (period k) → α)) (n := Fin (sectorDim k s))
          (sectorBlocks k s)) := fun k => (hSector k).2.2.1
  have sector_irreducible : ∀ k s, Kraus.IsIrreducibleFamily (sectorBlocks k s) :=
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
        (Kraus.block (d := blockPhysDim d (period k)) (n := Fin (sectorDim k s))
          (sectorBlocks k s) (extra k) i)ᴴ *
          Kraus.block (d := blockPhysDim d (period k)) (n := Fin (sectorDim k s))
            (sectorBlocks k s) (extra k) i = 1) ∧
      _root_.IsPrimitive
        (Kraus.transferMap (ι := Fin (blockPhysDim (blockPhysDim d (period k)) (extra k)))
          (n := Fin (sectorDim k s))
          (Kraus.block (d := blockPhysDim d (period k)) (n := Fin (sectorDim k s))
            (sectorBlocks k s) (extra k))) ∧
      Kraus.IsIrreducibleFamily
        (Kraus.block (d := blockPhysDim d (period k)) (n := Fin (sectorDim k s))
          (sectorBlocks k s) (extra k)) := by
    intro k s
    have : NeZero (sectorDim k s) := ⟨Nat.ne_of_gt (sector_dim_pos k s)⟩
    exact Kraus.tp_primitive_irreducible_extra_blocking
      (d := blockPhysDim d (period k)) (D := sectorDim k s)
      (A := sectorBlocks k s) (sector_tp k s) (sector_primitive k s)
      (sector_irreducible k s) (hk := extra_pos k)
  have nested_same : ∀ k,
      SameMPV₂
        (cast (congr_arg (fun d' => MPSTensor d' (dim k)) (hPhys k))
          (Kraus.block (d := blockPhysDim d (period k)) (n := Fin (dim k))
            (Kraus.block (blocks k) (period k)) (extra k)))
        (toTensorFromBlocks (α := (Fin p → α))
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (fun s => cast
            (congr_arg (fun d' => MPSTensor d' (sectorDim k s)) (hPhys k))
            (Kraus.block (d := blockPhysDim d (period k)) (n := Fin (sectorDim k s))
              (sectorBlocks k s) (extra k)))) := by
    intro k
    have hNested : SameMPV₂
        (Kraus.block (d := blockPhysDim d (period k)) (n := Fin (dim k))
          (Kraus.block (blocks k) (period k)) (extra k))
        (toTensorFromBlocks (α := Fin (blockPhysDim (blockPhysDim d (period k)) (extra k)))
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (fun s => Kraus.block (d := blockPhysDim d (period k)) (n := Fin (sectorDim k s))
            (sectorBlocks k s) (extra k))) := by
      simpa using
        (sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks
          (d := blockPhysDim d (period k)) (D := dim k)
          (A := Kraus.block (blocks k) (period k))
          (μ := fun _ : Fin (period k) => (1 : ℂ))
          (blocks := sectorBlocks k) (hSame := sector_same k) (p := extra k))
    have hCast := (sameMPV₂_cast_physDim (hPhys k)
      (A := Kraus.block (d := blockPhysDim d (period k)) (n := Fin (dim k))
        (Kraus.block (blocks k) (period k)) (extra k))
      (B := toTensorFromBlocks (α := Fin (blockPhysDim (blockPhysDim d (period k)) (extra k)))
        (μ := fun _ : Fin (period k) => (1 : ℂ))
        (fun s => Kraus.block (d := blockPhysDim d (period k)) (n := Fin (sectorDim k s))
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
    {α : Type*} [Fintype α] {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
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

end CommonBlockedCyclicSectorConstruction

section CommonSectorData

/-!
## Common-sector witnesses for the after-blocking reduction

This file collects the common-sector continuation of the structural
canonical-form reduction following arXiv:1606.00608. Starting from the
nonzero irreducible decomposition and its trace-preserving gauge, it records the per-block
weights, blocks, and positive-length agreements of the nonzero part, chooses
common blocking lengths, and states the relabeled common-sector families needed
to compare the resulting sector families.

### Main statements

* `afterBlocking_perBlockCyclicData_of_sameMPV₂Pos` — per-block weights, blocks,
  cyclic-sector decompositions, and positive-length nonzero-sector identities.
* `afterBlocking_commonLengthCommonSectorData_of_sameMPV₂Pos` — a two-sided
  common blocking length with common-sector families.

### References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

### Tags

matrix product states, canonical form, common sectors, blocking
-/

variable {α : Type*} [Fintype α] {D : ℕ}

section FundamentalTheoremAfterBlocking

/-- **Per-block cyclic-sector decomposition after removing zero blocks.**

This is the faithful predecessor to the common nonzero-sector statement. From
`SameMPV₂Pos A B`, it discards the all-zero blocks at positive lengths and then
applies the TP gauge to obtain irreducible nonzero-weight blocks on both sides. It then removes the
period of each block separately, producing primitive irreducible cyclic sectors for every
nonzero-weight block. The tensor on each side agrees with its nonzero part at every positive
length, and the two nonzero parts agree at every positive length.

The theorem intentionally keeps the per-block period-removal lengths inside
`HasPrimitiveIrreducibleCyclicSectors`. It does not conflate those lengths with a
later common-refinement or Wielandt/injectivity blocking length; assembling the
per-block cyclic sectors at one physical blocking level is the next formal
statement in the reduction chain.

Source: Pérez-García, Verstraete, Wolf, and Cirac, Theorem `Th:TIcanonical`, proof lines
761--832, for the nonzero irreducible canonical blocks; arXiv:1606.00608, equation
`eq:II_Aiplusk1`, Section II.C, and Appendix A, for removing zero blocks and resolving periodic
blocks into cyclic sectors. The positive-length convention is recorded in
`docs/paper-gaps/cpsv16_zero_tail_length_zero_decomposition.tex`. -/
theorem afterBlocking_perBlockCyclicData_of_sameMPV₂Pos
    {α : Type*} [Fintype α] {D₁ D₂ : ℕ}
    (A : MPTensor α (Fin D₁)) (B : MPTensor α (Fin D₂))
    (hSame : SameMPV₂Pos A B) :
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPTensor α (Fin (dimA k))),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPTensor α (Fin (dimB k))),
      (∀ k, Kraus.IsIrreducibleFamily (blocksA k)) ∧
      (∀ k, Kraus.IsIrreducibleFamily (blocksB k)) ∧
      (∀ k, ∑ i : α, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i : α, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) ∧
      SameMPV₂Pos A (toTensorFromBlocks (α := α) (μ := μA) blocksA) ∧
      SameMPV₂Pos B (toTensorFromBlocks (α := α) (μ := μB) blocksB) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (α := α) (μ := μA) blocksA)
        (toTensorFromBlocks (α := α) (μ := μB) blocksB) ∧
      (∀ k, HasPrimitiveIrreducibleCyclicSectors (blocksA k)) ∧
      (∀ k, HasPrimitiveIrreducibleCyclicSectors (blocksB k)) := by
  obtain ⟨rA, dimA, μA, blocksA,
      hIrrA, hTPA, hμPosA, hDimA, hAPos, _hDimBoundA⟩ :=
    exists_tp_gauge_from_arbitrary (α := α) (D := D₁) A
  obtain ⟨rB, dimB, μB, blocksB,
      hIrrB, hTPB, hμPosB, hDimB, hBPos, _hDimBoundB⟩ :=
    exists_tp_gauge_from_arbitrary (α := α) (D := D₂) B
  have hμA : ∀ k, μA k ≠ 0 := fun k => ne_of_gt (hμPosA k)
  have hμB : ∀ k, μB k ≠ 0 := fun k => ne_of_gt (hμPosB k)
  -- The two nonzero parts agree at positive length: chain through the common MPV family.
  have hBook : SameMPV₂Pos
      (toTensorFromBlocks (α := α) (μ := μA) blocksA)
      (toTensorFromBlocks (α := α) (μ := μB) blocksB) :=
    (hAPos.symm.trans hSame).trans hBPos
  refine ⟨rA, dimA, μA, blocksA, rB, dimB, μB, blocksB,
    hIrrA, hIrrB, hTPA, hTPB, hμA, hμB, hDimA, hDimB, hAPos, hBPos,
    hBook, ?_, ?_⟩
  · intro k
    let : NeZero (dimA k) := ⟨Nat.ne_of_gt (hDimA k)⟩
    simpa [HasPrimitiveIrreducibleCyclicSectors] using
      exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleFamily
        (α := α) (D := dimA k) (blocksA k) (hTPA k) (hIrrA k)
  · intro k
    let : NeZero (dimB k) := ⟨Nat.ne_of_gt (hDimB k)⟩
    simpa [HasPrimitiveIrreducibleCyclicSectors] using
      exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleFamily
        (α := α) (D := dimB k) (blocksB k) (hTPB k) (hIrrB k)

/-- **Two-sided common-length relabeled cyclic-sector theorem.**

Starting from `SameMPV₂Pos A B`, this theorem chooses one positive physical blocking
length for both sides.  At that common length it gives, for each side, the
positive-length equality between the blocked tensor and its weighted nonzero part,
the positive-length equality of the two nonzero parts, the relabeled
cyclic-sector families produced by `CommonBlockedCyclicSectorFamily`, and the
structural hypotheses for their flattened sector blocks. -/
theorem afterBlocking_commonLengthCommonSectorData_of_sameMPV₂Pos
    {α : Type*} [Fintype α] {D₁ D₂ : ℕ}
    (A : MPTensor α (Fin D₁)) (B : MPTensor α (Fin D₂))
    (hSame : SameMPV₂Pos A B) :
    ∃ (p : ℕ), 0 < p ∧
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPTensor α (Fin (dimA k))),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPTensor α (Fin (dimB k))),
    ∃ (familyA : CommonBlockedCyclicSectorFamily blocksA),
    ∃ (familyB : CommonBlockedCyclicSectorFamily blocksB),
      familyA.p = p ∧
      familyB.p = p ∧
      SameMPV₂Pos
        (Kraus.block A p)
        (toTensorFromBlocks (α := (Fin p → α))
          (fun k => (μA k) ^ p)
          (fun k => Kraus.block (blocksA k) p)) ∧
      SameMPV₂Pos
        (Kraus.block B p)
        (toTensorFromBlocks (α := (Fin p → α))
          (fun k => (μB k) ^ p)
          (fun k => Kraus.block (blocksB k) p)) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (α := (Fin p → α))
          (fun k => (μA k) ^ p)
          (fun k => Kraus.block (blocksA k) p))
        (toTensorFromBlocks (α := (Fin p → α))
          (fun k => (μB k) ^ p)
          (fun k => Kraus.block (blocksB k) p)) ∧
      (∀ x, familyA.commonFlatWeight μA x ≠ 0) ∧
      (∀ x, familyB.commonFlatWeight μB x ≠ 0) ∧
      (∀ x, ∑ i : (Fin familyA.p → α),
        (familyA.commonFlatBlocks x i)ᴴ * familyA.commonFlatBlocks x i = 1) ∧
      (∀ x, ∑ i : (Fin familyB.p → α),
        (familyB.commonFlatBlocks x i)ᴴ * familyB.commonFlatBlocks x i = 1) ∧
      (∀ x, _root_.IsPrimitive
        (Kraus.transferMap (ι := (Fin familyA.p → α))
          (n := Fin (familyA.commonFlatDim x))
          (familyA.commonFlatBlocks x))) ∧
      (∀ x, _root_.IsPrimitive
        (Kraus.transferMap (ι := (Fin familyB.p → α))
          (n := Fin (familyB.commonFlatDim x))
          (familyB.commonFlatBlocks x))) ∧
      (∀ x, Kraus.IsIrreducibleFamily (familyA.commonFlatBlocks x)) ∧
      (∀ x, Kraus.IsIrreducibleFamily (familyB.commonFlatBlocks x)) ∧
      (∀ x, 0 < familyA.commonFlatDim x) ∧
      (∀ x, 0 < familyB.commonFlatDim x) := by
  obtain ⟨rA, dimA, μA, blocksA,
      rB, dimB, μB, blocksB,
      _hIrrA, _hIrrB, _hTPA, _hTPB, hμA, hμB, _hDimA, _hDimB,
      hAPos, hBPos, hPos, hCycA, hCycB⟩ :=
    afterBlocking_perBlockCyclicData_of_sameMPV₂Pos A B hSame
  let periodA : Fin rA → ℕ := fun k => (hCycA k).choose
  let periodB : Fin rB → ℕ := fun k => (hCycB k).choose
  have periodA_pos : ∀ k, 0 < periodA k := fun k => (hCycA k).choose_spec.1
  have periodB_pos : ∀ k, 0 < periodB k := fun k => (hCycB k).choose_spec.1
  let pA : ℕ := lcmPeriod periodA
  let pB : ℕ := lcmPeriod periodB
  let p : ℕ := Nat.lcm pA pB
  have hpA : 0 < pA := lcmPeriod_pos periodA_pos
  have hpB : 0 < pB := lcmPeriod_pos periodB_pos
  have hp : 0 < p := Nat.lcm_pos hpA hpB
  have hDvdA : ∀ k, (hCycA k).choose ∣ p := by
    intro k
    have h₁ : periodA k ∣ pA := dvd_lcmPeriod periodA k
    have h₂ : periodA k ∣ p :=
      Nat.dvd_trans h₁ (Nat.dvd_lcm_left pA pB)
    simpa [periodA] using h₂
  have hDvdB : ∀ k, (hCycB k).choose ∣ p := by
    intro k
    have h₁ : periodB k ∣ pB := dvd_lcmPeriod periodB k
    have h₂ : periodB k ∣ p :=
      Nat.dvd_trans h₁ (Nat.dvd_lcm_right pA pB)
    simpa [periodB] using h₂
  obtain ⟨⟨familyA, hFamilyA⟩⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_commonMultiple
      blocksA hCycA p hp hDvdA
  obtain ⟨⟨familyB, hFamilyB⟩⟩ :=
    exists_commonBlockedCyclicSectorFamily_of_commonMultiple
      blocksB hCycB p hp hDvdB
  have hAPosCanon :=
    sameMPV₂Pos_blockTensor_toTensorFromBlocks
      (α := α) A μA blocksA hAPos p hp
  have hBPosCanon :=
    sameMPV₂Pos_blockTensor_toTensorFromBlocks
      (α := α) B μB blocksB hBPos p hp
  have hBook :=
    sameMPV₂Pos_toTensorFromBlocks_blockPower
      (α := α) μA blocksA μB blocksB hPos p hp
  refine ⟨p, hp, rA, dimA, μA, blocksA,
    rB, dimB, μB, blocksB, familyA, familyB,
    hFamilyA, hFamilyB, hAPosCanon, hBPosCanon, hBook, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x
    exact pow_ne_zero familyA.p (hμA (familyA.flatKey x).1)
  · intro x
    exact pow_ne_zero familyB.p (hμB (familyB.flatKey x).1)
  · intro x
    let y := familyA.flatKey x
    change ∑ i : (Fin familyA.p → α),
      (familyA.commonSectorBlock y.1 y.2 i)ᴴ * familyA.commonSectorBlock y.1 y.2 i = 1
    exact (familyA.derived_properties y.1 y.2).1
  · intro x
    let y := familyB.flatKey x
    change ∑ i : (Fin familyB.p → α),
      (familyB.commonSectorBlock y.1 y.2 i)ᴴ * familyB.commonSectorBlock y.1 y.2 i = 1
    exact (familyB.derived_properties y.1 y.2).1
  · intro x
    let y := familyA.flatKey x
    change _root_.IsPrimitive
      (Kraus.transferMap (ι := (Fin familyA.p → α))
        (n := Fin (familyA.sectorDim y.1 y.2))
        (familyA.commonSectorBlock y.1 y.2))
    exact (familyA.derived_properties y.1 y.2).2.1
  · intro x
    let y := familyB.flatKey x
    change _root_.IsPrimitive
      (Kraus.transferMap (ι := (Fin familyB.p → α))
        (n := Fin (familyB.sectorDim y.1 y.2))
        (familyB.commonSectorBlock y.1 y.2))
    exact (familyB.derived_properties y.1 y.2).2.1
  · intro x
    let y := familyA.flatKey x
    change Kraus.IsIrreducibleFamily (familyA.commonSectorBlock y.1 y.2)
    exact (familyA.derived_properties y.1 y.2).2.2.1
  · intro x
    let y := familyB.flatKey x
    change Kraus.IsIrreducibleFamily (familyB.commonSectorBlock y.1 y.2)
    exact (familyB.derived_properties y.1 y.2).2.2.1
  · intro x
    let y := familyA.flatKey x
    change 0 < familyA.sectorDim y.1 y.2
    exact (familyA.derived_properties y.1 y.2).2.2.2
  · intro x
    let y := familyB.flatKey x
    change 0 < familyB.sectorDim y.1 y.2
    exact (familyB.derived_properties y.1 y.2).2.2.2

/-!
### What remains for the full 1606.00608 Fundamental Theorem

The complete fundamental theorem should take two tensors `A, B` with `SameMPV₂Pos A B`
and pass from the blocked reduction witnesses to the CPSV basis-of-normal-tensors
sector comparison. The one-sided phase-class BNT construction is available as
`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`; the remaining overlap/span
hypotheses are supplied at the two-sided comparison layer.
The sector matching extraction is available from primitive overlap-rigidity
hypotheses through `SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching`.

The comparison hypotheses match the CPSV boundary: blocked-word relabeling,
finite-length nonzero-block span comparison, and BNT sector
matching.

The blocked-word relabeling and common primitive irreducible nonzero-block
decompositions are now part of this file's structural reduction. The remaining
formal work for the completely unconditional
`fundamentalTheorem_after_blocking_sector` is therefore narrower:

1. one-site injectivity of the nonzero-weight blocks, or a blocked replacement of the
   rigidity hypothesis; and
2. equality of the finite-length MPV spans for the original nonzero-weight block families
   (or directly for the two BNT bases), equivalently a common phase/BNT comparison,
   followed by the final global gauge construction of the equal-case FT.

Thus the common-period arithmetic, the blocked-word relabeling, the common
primitive irreducible nonzero-sector families, and the abstract sector-matching
witness have already been supplied. What remains is the CPSV derivation of the
listed injectivity and span/comparison facts for the actual sector
tensors produced by the after-blocking reduction.
-/

end FundamentalTheoremAfterBlocking

end CommonSectorData

section CommonSectorTransport

/-!
## Common-sector transport after canonical-form blocking

This module contains the common-sector transport theorem used after the structural
canonical-form reduction has produced common cyclic-sector families.

### Main statements

* `unconditional_commonPrimitiveIrreducibleBlocks` turns the structural common-sector
  families into common primitive irreducible block decompositions.

### References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

### Tags

matrix product states, canonical form, common sectors
-/

/-- **Unconditional common primitive irreducible block decompositions.**

Two tensors with the same MPV family at every positive length have one common positive blocking
length
whose nonzero parts are weighted families of trace-preserving, primitive,
tensor-irreducible blocks with positive bond dimensions and nonzero weights. At
every positive length each blocked tensor equals its nonzero part, and the two
nonzero parts equal each other. All-zero blocks are omitted because they vanish
at every positive length.

The proof uses the family-level common-alphabet nonzero-part identity directly,
rather than passing through a separate relabeling hypothesis.

Source: arXiv:1606.00608, Appendix A and Section II.C, where the nonnormal
canonical-form reduction is blocked to primitive sector families before the
multi-block comparison. -/
theorem unconditional_commonPrimitiveIrreducibleBlocks
    {α : Type*} [Fintype α] {D₁ D₂ : ℕ}
    (A : MPTensor α (Fin D₁)) (B : MPTensor α (Fin D₂))
    (hSame : SameMPV₂Pos A B) :
    ∃ p : ℕ, 0 < p ∧
    ∃ (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (x : Fin rA) → MPTensor (Fin p → α) (Fin (dimA x))),
    ∃ (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (x : Fin rB) → MPTensor (Fin p → α) (Fin (dimB x))),
      SameMPV₂Pos (Kraus.block A p)
        (toTensorFromBlocks (α := (Fin p → α)) (μ := μA) blocksA) ∧
      SameMPV₂Pos (Kraus.block B p)
        (toTensorFromBlocks (α := (Fin p → α)) (μ := μB) blocksB) ∧
      SameMPV₂Pos
        (toTensorFromBlocks (α := (Fin p → α)) (μ := μA) blocksA)
        (toTensorFromBlocks (α := (Fin p → α)) (μ := μB) blocksB) ∧
      (∀ x, μA x ≠ 0) ∧
      (∀ x, μB x ≠ 0) ∧
      (∀ x, ∑ i : (Fin p → α), (blocksA x i)ᴴ * blocksA x i = 1) ∧
      (∀ x, ∑ i : (Fin p → α), (blocksB x i)ᴴ * blocksB x i = 1) ∧
      (∀ x, _root_.IsPrimitive
        (Kraus.transferMap (ι := (Fin p → α)) (n := Fin (dimA x)) (blocksA x))) ∧
      (∀ x, _root_.IsPrimitive
        (Kraus.transferMap (ι := (Fin p → α)) (n := Fin (dimB x)) (blocksB x))) ∧
      (∀ x, Kraus.IsIrreducibleFamily (blocksA x)) ∧
      (∀ x, Kraus.IsIrreducibleFamily (blocksB x)) ∧
      (∀ x, 0 < dimA x) ∧
      (∀ x, 0 < dimB x) := by
  obtain ⟨p, hp, rA₀, dimA₀, μA₀, blocksA₀,
      rB₀, dimB₀, μB₀, blocksB₀, familyA, familyB,
      hFamilyA, hFamilyB, hAPosCanon, hBPosCanon, hPosCanon,
      hμA, hμB, hTPA, hTPB, hPrimA, hPrimB, hIrrA, hIrrB, hDimA, hDimB⟩ :=
    afterBlocking_commonLengthCommonSectorData_of_sameMPV₂Pos A B hSame
  have hFlatA_raw := familyA.reindexed_nonzero_part μA₀
  have hFlatB_raw := familyB.reindexed_nonzero_part μB₀
  let flatBlocksA : (x : Fin (∑ k : Fin rA₀, familyA.period k)) →
      MPTensor (Fin p → α) (Fin (familyA.commonFlatDim x)) :=
    fun x => cast (congr_arg (fun q => MPSTensor (blockPhysDim d q)
      (familyA.commonFlatDim x)) hFamilyA) (familyA.commonFlatBlocks x)
  let flatBlocksB : (x : Fin (∑ k : Fin rB₀, familyB.period k)) →
      MPTensor (Fin p → α) (Fin (familyB.commonFlatDim x)) :=
    fun x => cast (congr_arg (fun q => MPSTensor (blockPhysDim d q)
      (familyB.commonFlatDim x)) hFamilyB) (familyB.commonFlatBlocks x)
  let nonzeroA := toTensorFromBlocks (α := (Fin p → α))
    (μ := familyA.commonFlatWeight μA₀) flatBlocksA
  let nonzeroB := toTensorFromBlocks (α := (Fin p → α))
    (μ := familyB.commonFlatWeight μB₀) flatBlocksB
  have hFlatA : SameMPV₂
      (toTensorFromBlocks (α := (Fin p → α))
        (μ := fun k : Fin rA₀ => (μA₀ k) ^ p)
        (fun k => Kraus.block (blocksA₀ k) p))
      nonzeroA := by
    cases hFamilyA
    simpa [flatBlocksA, nonzeroA] using hFlatA_raw
  have hFlatB : SameMPV₂
      (toTensorFromBlocks (α := (Fin p → α))
        (μ := fun k : Fin rB₀ => (μB₀ k) ^ p)
        (fun k => Kraus.block (blocksB₀ k) p))
      nonzeroB := by
    cases hFamilyB
    simpa [flatBlocksB, nonzeroB] using hFlatB_raw
  have hAPos : SameMPV₂Pos (Kraus.block A p) nonzeroA := by
    intro N hN σ
    exact (hAPosCanon N hN σ).trans (hFlatA N σ)
  have hBPos : SameMPV₂Pos (Kraus.block B p) nonzeroB := by
    intro N hN σ
    exact (hBPosCanon N hN σ).trans (hFlatB N σ)
  have hNonzeroPos : SameMPV₂Pos nonzeroA nonzeroB := by
    intro N hN σ
    calc
      mpv nonzeroA σ =
          mpv (toTensorFromBlocks (α := (Fin p → α))
            (fun k : Fin rA₀ => (μA₀ k) ^ p)
            (fun k => Kraus.block (blocksA₀ k) p)) σ :=
        (hFlatA N σ).symm
      _ = mpv (toTensorFromBlocks (α := (Fin p → α))
            (fun k : Fin rB₀ => (μB₀ k) ^ p)
            (fun k => Kraus.block (blocksB₀ k) p)) σ :=
        hPosCanon N hN σ
      _ = mpv nonzeroB σ := hFlatB N σ
  have hTPA' : ∀ x,
      ∑ i : (Fin p → α), (flatBlocksA x i)ᴴ * flatBlocksA x i = 1 := by
    intro x
    cases hFamilyA
    simpa [flatBlocksA] using hTPA x
  have hTPB' : ∀ x,
      ∑ i : (Fin p → α), (flatBlocksB x i)ᴴ * flatBlocksB x i = 1 := by
    intro x
    cases hFamilyB
    simpa [flatBlocksB] using hTPB x
  have hPrimA' : ∀ x, _root_.IsPrimitive
      (Kraus.transferMap (ι := (Fin p → α)) (n := Fin (familyA.commonFlatDim x))
        (flatBlocksA x)) := by
    intro x
    cases hFamilyA
    simpa [flatBlocksA] using hPrimA x
  have hPrimB' : ∀ x, _root_.IsPrimitive
      (Kraus.transferMap (ι := (Fin p → α)) (n := Fin (familyB.commonFlatDim x))
        (flatBlocksB x)) := by
    intro x
    cases hFamilyB
    simpa [flatBlocksB] using hPrimB x
  have hIrrA' : ∀ x, Kraus.IsIrreducibleFamily (flatBlocksA x) := by
    intro x
    cases hFamilyA
    simpa [flatBlocksA] using hIrrA x
  have hIrrB' : ∀ x, Kraus.IsIrreducibleFamily (flatBlocksB x) := by
    intro x
    cases hFamilyB
    simpa [flatBlocksB] using hIrrB x
  refine ⟨p, hp,
    (∑ k : Fin rA₀, familyA.period k), familyA.commonFlatDim, familyA.commonFlatWeight μA₀,
    flatBlocksA,
    (∑ k : Fin rB₀, familyB.period k), familyB.commonFlatDim, familyB.commonFlatWeight μB₀,
    flatBlocksB,
    hAPos, hBPos, hNonzeroPos,
    hμA, hμB, hTPA', hTPB', hPrimA', hPrimB', hIrrA', hIrrB', hDimA, hDimB⟩

end CommonSectorTransport

end MPSTensor
