/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.CommonBlockedCyclicSectorFamily
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Representative common-sector blocks

**Auxiliary construction.**  For each original nonzero-weight block, a
`CommonBlockedCyclicSectorFamily` flattens all its cyclic sectors over
a common alphabet.  This file selects one representative sector per
original block and transports the structural properties
(trace-preservation, primitivity, irreducibility) and weight ordering
to that representative family.

All theorems here are properties of the representative indices derived
from the `CommonBlockedCyclicSectorFamily` record.  They are
consumed by the normal canonical-form existence proof chain, rather than
stating independent theorems of CPSV.
-/

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

/-- Representative weights remain nonzero after common blocking. -/
lemma commonRepresentativeWeight_ne_zero (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0) (k : Fin r) :
    F.commonRepresentativeWeight μ k ≠ 0 :=
  F.commonBlockWeight_ne_zero μ hμ k

/-- The representative common-sector family is trace-preserving. -/
lemma commonRepresentativeBlocks_tp (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) :
    ∑ i : Fin (blockPhysDim d F.p),
      (F.commonRepresentativeBlocks k i)ᴴ * F.commonRepresentativeBlocks k i = 1 := by
  simpa [commonRepresentativeBlocks, commonRepresentativeDim] using
    F.commonSectorBlock_tp k ⟨0, F.period_pos k⟩

/-- The representative common-sector family has primitive transfer maps. -/
lemma commonRepresentativeBlocks_primitive (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) :
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d F.p) (D := F.commonRepresentativeDim k)
        (F.commonRepresentativeBlocks k)) := by
  simpa [commonRepresentativeBlocks, commonRepresentativeDim] using
    F.commonSectorBlock_primitive k ⟨0, F.period_pos k⟩

/-- The representative common-sector family is tensor-irreducible. -/
lemma commonRepresentativeBlocks_irreducible (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : IsIrreducibleTensor (F.commonRepresentativeBlocks k) := by
  simpa [commonRepresentativeBlocks, commonRepresentativeDim] using
    F.commonSectorBlock_irreducible k ⟨0, F.period_pos k⟩

/-- The representative common-sector family has positive bond dimensions. -/
lemma commonRepresentativeDim_pos (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : 0 < F.commonRepresentativeDim k := by
  simpa [commonRepresentativeDim] using
    F.commonSectorBlock_dim_pos k ⟨0, F.period_pos k⟩

/-- A representative common-sector family is a normal canonical form once its transported
representative weights are sorted by non-increasing modulus.

The target normal canonical form permits equal moduli.  Strict ordering is a
separate restricted branch, not part of the general canonical-form reduction. -/
lemma isNormalCanonicalForm_commonRepresentativeBlocks
    (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ)
    (hμ : ∀ k, μ k ≠ 0)
    (hAnti : Antitone (fun k : Fin r => ‖F.commonRepresentativeWeight μ k‖)) :
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
lemma isNormalCanonicalForm_commonRepresentativeBlocksAt
    (F : CommonBlockedCyclicSectorFamily blocks)
    {p' : ℕ} (hp : F.p = p')
    (μ : Fin r → ℂ)
    (hμ : ∀ k, μ k ≠ 0)
    (hAnti : Antitone (fun k : Fin r => ‖F.commonRepresentativeWeight μ k‖)) :
    IsNormalCanonicalForm (d := blockPhysDim d p')
      (F.commonRepresentativeWeight μ) (F.commonRepresentativeBlocksAt hp) := by
  subst p'
  simpa [commonRepresentativeBlocksAt] using
    F.isNormalCanonicalForm_commonRepresentativeBlocks μ hμ hAnti

end CommonBlockedCyclicSectorFamily
end MPSTensor
