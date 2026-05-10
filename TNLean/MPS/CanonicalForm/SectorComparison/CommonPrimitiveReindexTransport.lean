/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.CommonPrimitiveProportionalData
import TNLean.MPS.Core.PhysicalReindexTransport

/-!
# Physical reindexing for common primitive BNT hypotheses

This file transports the normal-form and BNT hypotheses used in the common primitive
comparison along a bijection of physical alphabets.

## Main statements

* `IsNormalCanonicalForm.reindexPhysical_equiv` — normal canonical form is preserved by
  reindexing all physical letters.
* `BlocksNotGaugePhaseEquiv.reindexPhysical_equiv` and
  `IsNormalCanonicalFormBNT.reindexPhysical_equiv` — BNT separation and normal-CF-BNT
  hypotheses are preserved.
* `ProportionalDecompositionData.reindexPhysical_equiv` — proportional-decomposition
  proofs are transported by evaluating on the relabelled physical configuration.
* `CommonPrimitiveBNTCoverHypotheses.reindexPhysical_equiv` — the full common primitive
  BNT hypotheses are transported across a physical alphabet equivalence.
* `CommonPrimitiveBNTCoverHypotheses.reindexPhysical_directIteratedBlockEquiv` — the
  preceding transport specialized to `directIteratedBlockEquiv`, turning iterated blocked
  hypotheses into flattened iterated hypotheses on the direct length-`p * L` alphabet.
-/

open scoped BigOperators

namespace MPSTensor

namespace IsNormalCanonicalForm

/-- Transport a normal canonical form proof along a physical-index equivalence. -/
def reindexPhysical_equiv
    {d₁ d₂ r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    {A : (k : Fin r) → MPSTensor d₂ (dim k)}
    (h : IsNormalCanonicalForm (d := d₂) μ A) (e : Fin d₁ ≃ Fin d₂) :
    IsNormalCanonicalForm (d := d₁) μ (fun k => reindexPhysical e (A k)) where
  block_irreducible := fun k =>
    (isIrreducibleTensor_reindexPhysical_equiv e (A k)).mpr (h.block_irreducible k)
  leftCanonical := fun k =>
    (leftCanonical_reindexPhysical_equiv e (A k)).mpr (h.leftCanonical k)
  block_primitive := fun k =>
    (isPrimitive_transferMap_reindexPhysical_equiv e (A k)).mpr (h.block_primitive k)
  mu_antitone := h.mu_antitone
  mu_ne_zero := h.mu_ne_zero
  dim_pos := h.dim_pos

end IsNormalCanonicalForm

namespace BlocksNotGaugePhaseEquiv

/-- Transport BNT separation along a physical-index equivalence. -/
theorem reindexPhysical_equiv
    {d₁ d₂ r : ℕ} {dim : Fin r → ℕ}
    {A : (k : Fin r) → MPSTensor d₂ (dim k)}
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d₂) A) (e : Fin d₁ ≃ Fin d₂) :
    BlocksNotGaugePhaseEquiv (d := d₁) (fun k => reindexPhysical e (A k)) := by
  intro j k hjk hdim hG
  apply hBlocks j k hjk hdim
  have hG' : GaugePhaseEquiv
      (reindexPhysical e (cast (congr_arg (MPSTensor d₂) hdim) (A j)))
      (reindexPhysical e (A k)) := by
    rw [reindexPhysical_cast_dim e hdim (A j)]
    exact hG
  exact (gaugePhaseEquiv_reindexPhysical_equiv e
    (cast (congr_arg (MPSTensor d₂) hdim) (A j)) (A k)).mp hG'

end BlocksNotGaugePhaseEquiv

namespace IsNormalCanonicalFormBNT

/-- Transport a normal-CF-BNT proof along a physical-index equivalence. -/
def reindexPhysical_equiv
    {d₁ d₂ r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    {A : (k : Fin r) → MPSTensor d₂ (dim k)}
    (h : IsNormalCanonicalFormBNT (d := d₂) μ A) (e : Fin d₁ ≃ Fin d₂) :
    IsNormalCanonicalFormBNT (d := d₁) μ (fun k => reindexPhysical e (A k)) where
  toIsNormalCanonicalForm := h.toIsNormalCanonicalForm.reindexPhysical_equiv e
  mu_strict_anti := h.mu_strict_anti
  blocks_not_equiv := BlocksNotGaugePhaseEquiv.reindexPhysical_equiv h.blocks_not_equiv e

end IsNormalCanonicalFormBNT

namespace ProportionalDecompositionData

/-- Transport a proportional-decomposition proof along a physical-index equivalence. -/
noncomputable def reindexPhysical_equiv
    {d₁ d₂ rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {A : (j : Fin rA) → MPSTensor d₂ (dimA j)}
    {B : (k : Fin rB) → MPSTensor d₂ (dimB k)}
    {DtotA DtotB : ℕ}
    (h : ProportionalDecompositionData (d := d₂) A B DtotA DtotB)
    (e : Fin d₁ ≃ Fin d₂) :
    ProportionalDecompositionData (d := d₁)
      (fun j => reindexPhysical e (A j))
      (fun k => reindexPhysical e (B k)) DtotA DtotB where
  A_total := reindexPhysical e h.A_total
  B_total := reindexPhysical e h.B_total
  aCoeff := h.aCoeff
  bCoeff := h.bCoeff
  aLim := h.aLim
  bLim := h.bLim
  c := h.c
  cLim := h.cLim
  hA_decomp := fun N σ => by
    rw [mpv_reindexPhysical]
    calc
      mpv h.A_total (fun n => e (σ n)) =
          ∑ j : Fin rA, h.aCoeff N j * mpv (A j) (fun n => e (σ n)) :=
        h.hA_decomp N (fun n => e (σ n))
      _ = ∑ j : Fin rA, h.aCoeff N j * mpv (reindexPhysical e (A j)) σ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mpv_reindexPhysical]
  hB_decomp := fun N σ => by
    rw [mpv_reindexPhysical]
    calc
      mpv h.B_total (fun n => e (σ n)) =
          ∑ k : Fin rB, h.bCoeff N k * mpv (B k) (fun n => e (σ n)) :=
        h.hB_decomp N (fun n => e (σ n))
      _ = ∑ k : Fin rB, h.bCoeff N k * mpv (reindexPhysical e (B k)) σ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mpv_reindexPhysical]
  haCoeff := h.haCoeff
  hbCoeff := h.hbCoeff
  haLim_ne := h.haLim_ne
  hbLim_ne := h.hbLim_ne
  hProp := fun N σ => by
    rw [mpv_reindexPhysical, mpv_reindexPhysical]
    exact h.hProp N (fun n => e (σ n))
  hc := h.hc
  hcLim_ne := h.hcLim_ne

end ProportionalDecompositionData

namespace CommonPrimitiveBNTCoverHypotheses

/-- Transport primitive BNT-cover hypotheses along a physical-index equivalence. -/
noncomputable def reindexPhysical_equiv
    {d₁ p₁ d₂ p₂ rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d₂ p₂) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d₂ p₂) (dimB x)}
    (h : CommonPrimitiveBNTCoverHypotheses (d := d₂) (p := p₂)
      (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB blocksA blocksB)
    (e : Fin (blockPhysDim d₁ p₁) ≃ Fin (blockPhysDim d₂ p₂)) :
    CommonPrimitiveBNTCoverHypotheses (d := d₁) (p := p₁)
      (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB
      (fun x => reindexPhysical e (blocksA x))
      (fun x => reindexPhysical e (blocksB x)) where
  ncfA := h.ncfA.reindexPhysical_equiv e
  ncfB := h.ncfB.reindexPhysical_equiv e
  notGpeA := BlocksNotGaugePhaseEquiv.reindexPhysical_equiv h.notGpeA e
  notGpeB := BlocksNotGaugePhaseEquiv.reindexPhysical_equiv h.notGpeB e
  zeroTail_eq := h.zeroTail_eq
  left_injective := fun x =>
    (isInjective_reindexPhysical_equiv e (blocksA x)).mpr (h.left_injective x)
  right_injective := fun x =>
    (isInjective_reindexPhysical_equiv e (blocksB x)).mpr (h.right_injective x)
  decompData := h.decompData.reindexPhysical_equiv e

/-- Transport an iterated-block BNT cover to the flattened `p * L` physical alphabet. -/
noncomputable def reindexPhysical_directIteratedBlockEquiv
    {d p L rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {zeroTailA zeroTailB DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitiveBNTCoverHypotheses (d := blockPhysDim d p) (p := L)
      (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB
      (fun x => blockTensor (d := blockPhysDim d p) (D := dimA x) (blocksA x) L)
      (fun x => blockTensor (d := blockPhysDim d p) (D := dimB x) (blocksB x) L)) :
    CommonPrimitiveBNTCoverHypotheses (d := d) (p := p * L)
      (zeroTailA := zeroTailA) (zeroTailB := zeroTailB)
      (DtotA := DtotA) (DtotB := DtotB) μA μB
      (fun x => flattenedIteratedBlockTensor (d := d) (p := p) (D := dimA x)
        (blocksA x) L)
      (fun x => flattenedIteratedBlockTensor (d := d) (p := p) (D := dimB x)
        (blocksB x) L) := by
  simpa [flattenedIteratedBlockTensor] using
    h.reindexPhysical_equiv (d₁ := d) (p₁ := p * L)
      (d₂ := blockPhysDim d p) (p₂ := L) (directIteratedBlockEquiv d p L)

end CommonPrimitiveBNTCoverHypotheses

end MPSTensor
