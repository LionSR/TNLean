/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphPhysicalPadding
import TNLean.PEPS.ParentHamiltonian.RegionParentDependentCut
import TNLean.PEPS.DependentOpenCutIntersection

/-!
# No spurious physical vectors in a zero-padded graph parent

Physical zero padding commutes exactly with every actual joint-boundary cut.
Vertex-covering parent constraints force all ambient kernel vectors into the
product of the original independent physical spaces. Explicit restriction and
zero extension therefore recover the entire physical vector, with no assumed
local-image condition and no discarded part of the ambient kernel.
-/

noncomputable section
namespace TNLean.PEPS
open DependentBondNetwork

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (N : Edge Γ → ℕ)
variable {Phys : V → Type*} [∀ v, Fintype (Phys v)]

/-- The actual cut range of a padded tensor is precisely the zero extension
of the cut range on its original independent physical alphabets. -/
theorem cutSpace_graphPhysicalPaddingTensor
    (A : (v : V) → LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ)
    (C : Finset (Edge Γ)) :
    cutSpace graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e))
      (graphDependentTensor (graphPhysicalPaddingTensor N A)) C =
      (cutSpace graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) A C).map
        (dependentPhysicalProductFamilyMap physicalPaddingMatrix) := by
  rw [graphDependentTensor_physicalPadding, map_cutSpace]

/-- The product restriction maps every genuine padded cut back to the original
cut, retaining exactly the same arbitrary joint virtual boundary. -/
theorem restriction_cutMap_graphPhysicalPaddingTensor
    (A : (v : V) → LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ)
    (C : Finset (Edge Γ)) (M : CutConfig C (fun e ↦ Fin (N e)) → ℂ) :
    dependentPhysicalProductFamilyMap physicalRestrictionMatrix
      (cutMap graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e))
        (graphDependentTensor (graphPhysicalPaddingTensor N A)) C M) =
      cutMap graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) A C M := by
  have h := physicalMap_cutMap graphEdgeTail graphEdgeHead
    (graphBondAlphabet (graphPhysicalPaddingTensor N A)) physicalRestrictionMatrix
    (graphDependentTensor (graphPhysicalPaddingTensor N A)) C M
  exact h.trans (congrArg (fun B ↦ cutMap graphEdgeTail graphEdgeHead
    (fun e ↦ Fin (N e)) B C M) (physicalMapSite_restrict_graphPhysicalPaddingTensor N A))

/-- Every vector in a vertex-covering padded parent is recovered by restriction
and zero extension. This is a theorem on the full ambient physical parent space. -/
theorem padding_restriction_eq_self_of_mem_regionParentGroundSpace
    (A : (v : V) → LocalConfig graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e)) v → Phys v → ℂ)
    (hN : ∀ e, N e ≠ 0) {ι : Type*} (i₀ : ι) (R : ι → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ R i)
    {Ψ : (V → Fin (physicalPaddingDimension (Phys := Phys))) → ℂ}
    (hΨ : Ψ ∈ regionParentGroundSpace (graphPhysicalPaddingTensor N A) R) :
    dependentPhysicalProductFamilyMap physicalPaddingMatrix
      (dependentPhysicalProductFamilyMap physicalRestrictionMatrix Ψ) = Ψ := by
  have hcuts := regionParentGroundSpace_le_iInf_cutSpace
    (graphPhysicalPaddingTensor N A) hN R hcover hΨ
  have hcut := (Submodule.mem_iInf _).mp hcuts i₀
  change Ψ ∈ cutSpace graphEdgeTail graphEdgeHead (fun e ↦ Fin (N e))
    (graphDependentTensor (graphPhysicalPaddingTensor N A)) (regionExteriorCut (R i₀)) at hcut
  rw [cutSpace_graphPhysicalPaddingTensor] at hcut
  obtain ⟨ψ, _, rfl⟩ := hcut
  rw [physicalRestrictionProduct_padding]

end TNLean.PEPS
