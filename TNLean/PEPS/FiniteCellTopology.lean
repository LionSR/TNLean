/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Hausdorff

/-!
# Local path connectedness of finite compact cell images

A finite union of continuous images of a compact locally path connected space
in a Hausdorff space is locally path connected. The finite disjoint union maps
onto the union by a closed quotient map. This supplies local path connectedness
for the closed-cell domains in SCP10, §6.3, lines 1935–1957.
-/

namespace TNLean.PEPS

/-- A finite union of compact locally path connected cell images is locally
path connected. This is the quotient argument used for the geometric block
domains of SCP10, §6.3, lines 1935–1957. -/
theorem locallyPathConnectedSpace_iUnion_range
    {ι K X : Type*} [Finite ι] [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] [TopologicalSpace X] [T2Space X]
    (f : ι → C(K, X)) : LocallyPathConnectedSpace (⋃ i, Set.range (f i)) := by
  let q : ((i : ι) × K) → (⋃ i, Set.range (f i)) := fun p =>
    ⟨f p.1 p.2, Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩⟩
  have hq : Continuous q := by
    apply continuous_sigma
    intro i
    exact (f i).continuous.subtype_mk _
  have hsurj : Function.Surjective q := by
    rintro ⟨x, hx⟩
    obtain ⟨i, k, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨i, k⟩, rfl⟩
  exact (hq.isClosedMap.isQuotientMap hq hsurj).locallyPathConnectedSpace

end TNLean.PEPS
