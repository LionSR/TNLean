/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.PairAlphabetBridge
import TNLean.MPS.Operator.Product.PhysicalBlocking
import TNLean.MPS.Tensor.Overlap
import TNLean.MPS.Tensor.Reduction.Reduction

/-!
# Physical relabelling and blocking on the pair alphabet

An operator tensor `M : MPOTensor d D` is a tensor on the pair alphabet `Fin d × Fin d`. This file
records how the overlap and rectangular reductions behave under a bijective relabelling of an
arbitrary physical alphabet, and identifies the letters of a blocked operator tensor with the
blocked words over the pair alphabet.

## Main results

* `MPTensor.mpvOverlap_reindexPhysical`: a bijective relabelling of the physical alphabet leaves
  the overlap unchanged.
* `MPTensor.isReduction_reindexPhysical_iff`: a bijective relabelling of the physical alphabet
  preserves rectangular reductions in both directions.
* `MPOTensor.range_blockTensor`, `MPOTensor.isInjective_blockTensor_iff`: the letters of the
  blocked operator tensor are the blocked words over the pair alphabet, so the blocked tensor is
  injective exactly when the tensor on the pair alphabet is block injective.
-/

open scoped Matrix

namespace MPTensor

variable {α α' : Type*}

/-- A bijective relabelling of the physical alphabet leaves the overlap unchanged. -/
theorem mpvOverlap_reindexPhysical [Fintype α] [Fintype α'] {D₁ D₂ : ℕ} (e : α' ≃ α)
    (A : MPTensor α (Fin D₁)) (B : MPTensor α (Fin D₂)) (N : ℕ) :
    mpvOverlap (Kraus.reindexPhysical e A) (Kraus.reindexPhysical e B) N = mpvOverlap A B N := by
  simp only [mpvOverlap, mpv_reindexPhysical]
  exact (Equiv.arrowCongr (Equiv.refl (Fin N)) e).sum_comp
    (fun σ ↦ mpv A σ * star (mpv B σ))

/-- A bijective relabelling of the physical alphabet preserves rectangular reductions, in both
directions.

Source: Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Definition following Proposition 20,
`cornerproblem.tex` lines 3137--3139. -/
theorem isReduction_reindexPhysical_iff {β₁ β₂ : Type*} [Fintype β₁] [DecidableEq β₁]
    [Fintype β₂] [DecidableEq β₂] {B : MPTensor α β₂} {A : MPTensor α β₁}
    {V : Matrix β₁ β₂ ℂ} {W : Matrix β₂ β₁ ℂ} (e : α' ≃ α) :
    IsReduction (Kraus.reindexPhysical e B) (Kraus.reindexPhysical e A) V W ↔
      IsReduction B A V W := by
  simp only [IsReduction, Kraus.evalWord_reindexPhysical]
  refine and_congr_right fun _ ↦ ⟨fun h w ↦ ?_, fun h w ↦ h _⟩
  simpa [List.map_map] using h (w.map e.symm)

end MPTensor

namespace MPOTensor

variable {d D : ℕ}

/-- The letters of a blocked operator tensor are the blocked words over the pair alphabet. -/
theorem range_blockTensor (M : MPOTensor d D) (L : ℕ) :
    Set.range (blockTensor M L) = Set.range (Kraus.block M L) := by
  refine Function.Surjective.range_comp (fun w ↦ ⟨((Kraus.decodeBlockEquiv d L).symm
    fun k ↦ (w k).1, (Kraus.decodeBlockEquiv d L).symm fun k ↦ (w k).2), ?_⟩) _
  funext k
  simp

/-- A blocked operator tensor is injective exactly when the tensor on the pair alphabet is block
injective at the blocking length. -/
theorem isInjective_blockTensor_iff (M : MPOTensor d D) (L : ℕ) :
    Kraus.IsInjective (blockTensor M L) ↔ Kraus.IsNBlkInjective M L := by
  rw [Kraus.isNBlkInjective_iff_isInjective_block, Kraus.IsInjective, Kraus.IsInjective,
    range_blockTensor]

end MPOTensor
