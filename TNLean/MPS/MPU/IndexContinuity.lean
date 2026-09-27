/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Index
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPDO.PhysicalBlocking
import QICLean.Algebra.MatrixRankClosed

/-!
# Constancy of the MPU index along canonical-form-II paths

For a continuous path of fixed physical and bond dimensions whose tensors
each have canonical-form-II data, the common block of length `D ^ 4` is
simple. Its two source ranks are lower semicontinuous and have the same
positive product at every point. Both ranks, and hence the index, are
constant along the path. No continuous choice of canonical data is required.

**Scope restriction (canonical-form-II paths):** Proposition IV.5 of the
source allows the path to leave canonical form and compares ranks of reduced
representatives. The results here apply to the tensors of the path themselves
under a canonical-form-II hypothesis at each point. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## References

Cirac--Pérez-García--Schuch--Verstraete, arXiv:1703.09188,
Proposition `prop:continuity-index`, lines 733--818.
-/

namespace MPOTensor

variable {d D : ℕ}

private theorem continuous_sourceCutM₁ :
    Continuous (sourceCutM₁ : MPOTensor d D →
      Matrix (Fin d × Fin D) (Fin D × Fin d) ℂ) := by
  unfold sourceCutM₁
  fun_prop

private theorem continuous_sourceCutM₂ :
    Continuous (sourceCutM₂ : MPOTensor d D →
      Matrix (Fin D × Fin d) (Fin d × Fin D) ℂ) := by
  unfold sourceCutM₂
  fun_prop

private theorem lowerSemicontinuous_rightRank_blockTensor
    {X : Type*} [TopologicalSpace X] {W : X → MPOTensor d D}
    (hW : Continuous W) (k : ℕ) :
    LowerSemicontinuous (fun x => r[blockTensor (W x) k]) := by
  change LowerSemicontinuous (fun x => (sourceCutM₁ (blockTensor (W x) k)).rank)
  exact ((continuous_sourceCutM₁.comp (hW.blockTensor k))).lowerSemicontinuous_matrix_rank

private theorem lowerSemicontinuous_leftRank_blockTensor
    {X : Type*} [TopologicalSpace X] {W : X → MPOTensor d D}
    (hW : Continuous W) (k : ℕ) :
    LowerSemicontinuous (fun x => ℓ[blockTensor (W x) k]) := by
  change LowerSemicontinuous (fun x => (sourceCutM₂ (blockTensor (W x) k)).rank)
  exact ((continuous_sourceCutM₂.comp (hW.blockTensor k))).lowerSemicontinuous_matrix_rank

/-- A continuous path of blocked tensors has constant source ranks when their
product is a fixed positive number. Source: arXiv:1703.09188,
Proposition `prop:continuity-index`, lines 809--818. -/
theorem sourceRanks_blockTensor_const_of_fixed_product
    {W : unitInterval → MPOTensor d D} (hW : Continuous W)
    (k c : ℕ) (hc : 0 < c)
    (hprod : ∀ x, r[blockTensor (W x) k] * ℓ[blockTensor (W x) k] = c)
    (x y : unitInterval) :
    r[blockTensor (W x) k] = r[blockTensor (W y) k] ∧
      ℓ[blockTensor (W x) k] = ℓ[blockTensor (W y) k] := by
  exact unitInterval_eq_of_lowerSemicontinuous_nat_mul_eq
    (lowerSemicontinuous_rightRank_blockTensor hW k)
    (lowerSemicontinuous_leftRank_blockTensor hW k) hc hprod x y

/-- The source ranks of the common simple block of length `D ^ 4` are
constant along a continuous path of canonical-form-II tensors.
Source: arXiv:1703.09188, Proposition `prop:continuity-index`, lines 739--818.
The source does not require the path itself to remain in canonical form. -/
theorem IsMPUCanonicalFormII.sourceRanks_blockTensor_pow_four_const
    {W : unitInterval → MPOTensor d D} (hW : Continuous W)
    (hCFII : ∀ x, IsMPUCanonicalFormII (W x))
    (x y : unitInterval) :
    r[MPOTensor.blockTensor (W x) (D ^ 4)] =
      r[MPOTensor.blockTensor (W y) (D ^ 4)] ∧
      ℓ[MPOTensor.blockTensor (W x) (D ^ 4)] =
        ℓ[MPOTensor.blockTensor (W y) (D ^ 4)] := by
  let _ : NeZero d := (hCFII 0).neZero_phys
  let _ : NeZero D := (hCFII 0).neZero_bond
  exact sourceRanks_blockTensor_const_of_fixed_product hW (D ^ 4)
    (d ^ (2 * (D ^ 4))) (Nat.pow_pos (NeZero.pos d))
    (fun z => (hCFII z).rightRank_mul_leftRank_blockTensor
      (Nat.pow_pos (NeZero.pos D))
      ((hCFII z).isMPU.blockTensor_pow_four_isMPUSimple)) x y

/-- The MPU index is constant along a continuous path of canonical-form-II
tensors of fixed physical and bond dimensions. Source: arXiv:1703.09188,
Proposition `prop:continuity-index`, lines 739--818, specialized to a path
already in canonical form II. -/
theorem IsMPUCanonicalFormII.index_const_of_continuous
    {W : unitInterval → MPOTensor d D} (hW : Continuous W)
    (hCFII : ∀ x, IsMPUCanonicalFormII (W x))
    (x y : unitInterval) : (hCFII x).index = (hCFII y).index := by
  let _ : NeZero d := (hCFII 0).neZero_phys
  let _ : NeZero D := (hCFII 0).neZero_bond
  have hk : 0 < D ^ 4 := Nat.pow_pos (NeZero.pos D)
  have hSx : IsMPUSimple (MPOTensor.blockTensor (W x) (D ^ 4)) :=
    (hCFII x).isMPU.blockTensor_pow_four_isMPUSimple
  have hSy : IsMPUSimple (MPOTensor.blockTensor (W y) (D ^ 4)) :=
    (hCFII y).isMPU.blockTensor_pow_four_isMPUSimple
  rw [(hCFII x).index_eq_logb_of_isMPUSimple_blockTensor hk hSx,
    (hCFII y).index_eq_logb_of_isMPUSimple_blockTensor hk hSy]
  obtain ⟨hr, hℓ⟩ :=
    IsMPUCanonicalFormII.sourceRanks_blockTensor_pow_four_const hW hCFII x y
  rw [hr, hℓ]

end MPOTensor
