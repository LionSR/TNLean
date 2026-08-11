/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ActiveBlocks
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.FundamentalTheorem.SectorBNT.Supplier

/-!
# CPSV canonical forms as SectorBNT decompositions

A normalized nonzero CPSV canonical form determines a SectorBNT decomposition of its active
blocks. Each active normal block is first put into a trace-preserving gauge, after which the
prepared-block constructor groups phase-equivalent copies into BNT sectors.

Source: arXiv:2011.12127, lines 1831--1885; arXiv:1606.00608, lines 237--301 and
1135--1146.
-/
open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- A normalized nonzero CPSV canonical form has a SectorBNT decomposition whose total bond
dimension is the sum of its active block dimensions.

The conclusion concerns only the active direct sum. Zero-weight displayed blocks and unused
ambient coordinates do not contribute to this dimension.

Source: arXiv:2011.12127, lines 1831--1885; arXiv:1606.00608, lines 237--301 and
1135--1146. -/
theorem exists_active_isBNTCanonicalForm
    (data : CPSVCanonicalFormData A)
    (hNorm : data.IsWeightNormalized)
    (hA : A ≠ 0) :
    ∃ P : SectorDecomposition d,
      IsBNTCanonicalForm P ∧
      SameMPV₂Pos A P.toTensor ∧
      P.totalDim = ∑ k : data.Active, data.dim k.1 := by
  classical
  haveI : ∀ k, NeZero (data.activeDim k) :=
    fun k => ⟨(data.dim_pos (data.activeEquiv k)).ne'⟩
  choose σ hσ hσfix hTP hGauge hPrim hIrr using
    fun k => (data.blocks_normal (data.activeEquiv k)).exists_tpGauge
  let prepared := fun k => tpGauge (data.blocks (data.activeEquiv k)) (σ k)
  have hDim : ∀ k, 0 < data.dim (data.activeEquiv k) := by
    intro k
    exact data.dim_pos (data.activeEquiv k)
  have hPreparedTP : ∀ k, IsLeftCanonical (prepared k) := hTP
  have hPreparedPrim : ∀ k, _root_.IsPrimitive (transferMap (prepared k)) := hPrim
  have hPreparedIrr : ∀ k, IsIrreducibleTensor (prepared k) := hIrr
  have hWeightNe : ∀ k, data.activeWeight k ≠ 0 := by
    intro k
    exact (data.activeEquiv k).property
  have hWeightLe : ∀ k, ‖data.activeWeight k‖ ≤ 1 := by
    intro k
    exact hNorm.weight_norm_le_one (data.activeEquiv k)
  have hWeightUnit : ∃ k, ‖data.activeWeight k‖ = 1 := by
    obtain ⟨k, hk⟩ := hNorm.weight_unit_exists hA
    have hkNe : data.weights k ≠ 0 := by
      intro hkZero
      simp [hkZero] at hk
    let ka : data.Active := ⟨k, hkNe⟩
    let l := data.activeEquiv.symm ka
    refine ⟨l, ?_⟩
    change ‖data.weights (data.activeEquiv l)‖ = 1
    rw [show data.activeEquiv l = ka by simp [l]]
    exact hk
  have hDirectGauge :
      GaugeEquiv
        (toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks)
        (toTensorFromBlocks (d := d) data.activeWeight prepared) := by
    apply gaugeEquiv_toTensorFromBlocks_of_blockGauge
    intro k
    simpa only [prepared, activeBlocks, activeDim] using hGauge k
  have hActivePrepared :
      SameMPV₂Pos
        (toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks)
        (toTensorFromBlocks (d := d) data.activeWeight prepared) :=
    fun N _hN w => GaugeEquiv.sameMPV hDirectGauge N w
  obtain ⟨P, hPSame, hBNT, hTotal⟩ :=
    exists_isBNTCanonicalForm_of_tp_primitive_irr_blocks_and_totalDim
      data.activeWeight prepared hDim hPreparedTP hPreparedPrim hPreparedIrr
        hWeightNe hWeightLe hWeightUnit
  refine ⟨P, hBNT, data.sameMPV₂Pos_activeBlocks.trans <|
    hActivePrepared.trans hPSame.symm, ?_⟩
  rw [hTotal]
  exact data.activeEquiv.sum_comp (fun k : data.Active => data.dim k.1)

end CPSVCanonicalFormData

end MPSTensor
