/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.CommonBlockedCyclicSectorFamily

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor
namespace CommonBlockedCyclicSectorFamily

variable {d r : ℕ} {dim : Fin r → ℕ}
variable {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-! ### Representative common sectors -/

/-- Bond dimensions of the representative common-sector family. -/
noncomputable def commonRepresentativeDim (F : CommonBlockedCyclicSectorFamily blocks) :
    Fin r → ℕ :=
  fun k => F.sectorDim k ⟨0, F.period_pos k⟩

/-- One representative common-sector block for each original nonzero-weight block. -/
noncomputable def commonRepresentativeBlocks (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : MPSTensor (blockPhysDim d F.p) (F.commonRepresentativeDim k) :=
  F.commonSectorBlock k ⟨0, F.period_pos k⟩

/-- Representative common-sector blocks expressed at a prescribed common length. -/
noncomputable def commonRepresentativeBlocksAt (F : CommonBlockedCyclicSectorFamily blocks)
    {p' : ℕ} (hp : F.p = p') (k : Fin r) :
    MPSTensor (blockPhysDim d p') (F.commonRepresentativeDim k) :=
  cast (congr_arg (fun q => MPSTensor (blockPhysDim d q) (F.commonRepresentativeDim k)) hp)
    (F.commonRepresentativeBlocks k)

/-- Weights carried by the representative common-sector family. -/
noncomputable def commonRepresentativeWeight (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) : Fin r → ℂ :=
  fun k => (μ k) ^ F.p

/-- Representative weights agree with flattened weights at the chosen representatives. -/
theorem commonRepresentativeWeight_apply (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) (k : Fin r) :
    F.commonRepresentativeWeight μ k =
      F.commonFlatWeight μ (F.flatRepresentativeIndex k) := by
  simp [commonRepresentativeWeight, flatRepresentativeIndex, flatIndexOf,
    commonFlatWeight, flatKey]

/-- Representative weights remain nonzero after common blocking. -/
theorem commonRepresentativeWeight_ne_zero (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0) (k : Fin r) :
    F.commonRepresentativeWeight μ k ≠ 0 :=
  F.commonBlockWeight_ne_zero μ hμ k

/-- Strict ordering by weight norm is preserved when passing to representative
common-sector weights. -/
theorem commonRepresentativeWeight_strictAnti_of_weight_strictAnti
    (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ)
    (hAnti : StrictAnti (fun k : Fin r => ‖μ k‖)) :
    StrictAnti (fun k : Fin r => ‖F.commonRepresentativeWeight μ k‖) := by
  intro k l hkl
  have hpow : ‖μ l‖ ^ F.p < ‖μ k‖ ^ F.p :=
    pow_lt_pow_left₀ (hAnti hkl) (norm_nonneg (μ l)) (Nat.ne_of_gt F.p_pos)
  simpa [commonRepresentativeWeight, norm_pow] using hpow

/-- The representative common-sector family is trace-preserving. -/
theorem commonRepresentativeBlocks_tp (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) :
    ∑ i : Fin (blockPhysDim d F.p),
      (F.commonRepresentativeBlocks k i)ᴴ * F.commonRepresentativeBlocks k i = 1 := by
  simpa [commonRepresentativeBlocks, commonRepresentativeDim] using
    F.commonSectorBlock_tp k ⟨0, F.period_pos k⟩

/-- The representative common-sector family has primitive transfer maps. -/
theorem commonRepresentativeBlocks_primitive (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) :
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d F.p) (D := F.commonRepresentativeDim k)
        (F.commonRepresentativeBlocks k)) := by
  simpa [commonRepresentativeBlocks, commonRepresentativeDim] using
    F.commonSectorBlock_primitive k ⟨0, F.period_pos k⟩

/-- The representative common-sector family is tensor-irreducible. -/
theorem commonRepresentativeBlocks_irreducible (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : IsIrreducibleTensor (F.commonRepresentativeBlocks k) := by
  simpa [commonRepresentativeBlocks, commonRepresentativeDim] using
    F.commonSectorBlock_irreducible k ⟨0, F.period_pos k⟩

/-- The representative common-sector family is trace-preserving at a prescribed
common blocking length. -/
theorem commonRepresentativeBlocksAt_tp (F : CommonBlockedCyclicSectorFamily blocks)
    {p' : ℕ} (hp : F.p = p') (k : Fin r) :
    ∑ i : Fin (blockPhysDim d p'),
      (F.commonRepresentativeBlocksAt hp k i)ᴴ *
        F.commonRepresentativeBlocksAt hp k i = 1 := by
  subst p'
  simpa [commonRepresentativeBlocksAt] using F.commonRepresentativeBlocks_tp k

/-- The representative common-sector family has primitive transfer maps at a
prescribed common blocking length. -/
theorem commonRepresentativeBlocksAt_primitive (F : CommonBlockedCyclicSectorFamily blocks)
    {p' : ℕ} (hp : F.p = p') (k : Fin r) :
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p') (D := F.commonRepresentativeDim k)
        (F.commonRepresentativeBlocksAt hp k)) := by
  subst p'
  simpa [commonRepresentativeBlocksAt] using F.commonRepresentativeBlocks_primitive k

/-- The representative common-sector family is tensor-irreducible at a prescribed
common blocking length. -/
theorem commonRepresentativeBlocksAt_irreducible (F : CommonBlockedCyclicSectorFamily blocks)
    {p' : ℕ} (hp : F.p = p') (k : Fin r) :
    IsIrreducibleTensor (F.commonRepresentativeBlocksAt hp k) := by
  subst p'
  simpa [commonRepresentativeBlocksAt] using F.commonRepresentativeBlocks_irreducible k

/-- The representative common-sector family has positive bond dimensions. -/
theorem commonRepresentativeDim_pos (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : 0 < F.commonRepresentativeDim k := by
  simpa [commonRepresentativeDim] using
    F.commonSectorBlock_dim_pos k ⟨0, F.period_pos k⟩

/-- Each representative common-sector block becomes injective after a further
blocking.  This deliberately does not assert one-site injectivity at the chosen
common blocking length. -/
theorem commonRepresentativeBlocksAt_exists_blockTensor_isInjective
    (F : CommonBlockedCyclicSectorFamily blocks)
    {p' : ℕ} (hp : F.p = p') (k : Fin r) :
    ∃ L : ℕ, IsInjective (blockTensor (F.commonRepresentativeBlocksAt hp k) L) := by
  haveI : NeZero (F.commonRepresentativeDim k) :=
    ⟨Nat.ne_of_gt (F.commonRepresentativeDim_pos k)⟩
  exact exists_blockTensor_isInjective_of_tp_primitive_irreducible
    (F.commonRepresentativeBlocksAt hp k)
    (F.commonRepresentativeBlocksAt_tp hp k)
    (F.commonRepresentativeBlocksAt_primitive hp k)
    (F.commonRepresentativeBlocksAt_irreducible hp k)

/-- A representative common-sector family is a normal canonical form once its transported
representative weights are sorted by strictly decreasing modulus. -/
theorem isNormalCanonicalForm_commonRepresentativeBlocks
    (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ)
    (hμ : ∀ k, μ k ≠ 0)
    (hAnti : StrictAnti (fun k : Fin r => ‖F.commonRepresentativeWeight μ k‖)) :
    IsNormalCanonicalForm (d := blockPhysDim d F.p)
      (F.commonRepresentativeWeight μ) F.commonRepresentativeBlocks :=
  isNormalCanonicalForm_of_tp_primitive_irr_sorted
    (d' := blockPhysDim d F.p)
    (μ := F.commonRepresentativeWeight μ)
    F.commonRepresentativeBlocks
    F.commonRepresentativeBlocks_tp
    F.commonRepresentativeBlocks_primitive
    F.commonRepresentativeDim_pos
    (F.commonRepresentativeWeight_ne_zero μ hμ)
    F.commonRepresentativeBlocks_irreducible
    hAnti

/-- The representative common-sector family is a normal canonical form when expressed at a
prescribed common blocking length. -/
theorem isNormalCanonicalForm_commonRepresentativeBlocksAt
    (F : CommonBlockedCyclicSectorFamily blocks)
    {p' : ℕ} (hp : F.p = p')
    (μ : Fin r → ℂ)
    (hμ : ∀ k, μ k ≠ 0)
    (hAnti : StrictAnti (fun k : Fin r => ‖F.commonRepresentativeWeight μ k‖)) :
    IsNormalCanonicalForm (d := blockPhysDim d p')
      (F.commonRepresentativeWeight μ) (F.commonRepresentativeBlocksAt hp) := by
  subst p'
  simpa [commonRepresentativeBlocksAt] using
    F.isNormalCanonicalForm_commonRepresentativeBlocks μ hμ hAnti

end CommonBlockedCyclicSectorFamily
end MPSTensor
