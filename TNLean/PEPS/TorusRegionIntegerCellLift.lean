/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellExteriorCollar
import TNLean.PEPS.TorusRegionExteriorCollar

/-!
# A simply connected planar integer-cell lift with an exterior collar

One covering lift supplies both the genuine simply connected planar square
union and exclusion of the torus region along its exterior collar. The two
properties hold for the same integer coordinates.

Source: SCP10, arXiv:1001.3807, proof of Theorem 6.9, lines 1935–1990;
auxiliary geometric consequence. No exterior connectivity is assumed here.
-/

open Set

namespace TNLean.PEPS

/-- The actual simply connected torus region has integer coordinates whose
closed-cell union is simply connected and whose exterior collar projects
outside the torus region. Source: SCP10, proof of Theorem 6.9,
lines 1935–1990; auxiliary geometry. -/
theorem exists_integerLift_simplyConnected_exteriorCollar_of_isSimplyConnected
    {width height : ℕ} [NeZero width] [NeZero height]
    (R : Finset (TorusVertex width height))
    (hSC : IsSimplyConnected (torusRegionRealization R)) :
    ∃ L : {v // v ∈ R} → ℤ × ℤ, IsTorusRegionIntegerLift R L ∧
      IsSimplyConnected (integerClosedCellUnion (Finset.univ.image L)) ∧
      ∀ x ∈ integerExteriorCollar (Finset.univ.image L),
        torusRealProjection width height x ∉ torusRegionRealization R := by
  obtain ⟨x, hx⟩ := hSC.nonempty
  obtain ⟨v, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hv, _⟩ := mem_iUnion.mp hx
  obtain ⟨F, hF⟩ := exists_continuousLift_torusRegionRealization R hSC ⟨v, hv⟩
  obtain ⟨L, hL, hreal, _⟩ := exists_integerLift_torusRegionPlanarRealization R F hF
  let : SimplyConnectedSpace (torusRegionRealization R) := hSC.simplyConnectedSpace
  have hp : IsSimplyConnected (torusRegionPlanarRealization R L) :=
    (torusRegionLiftHomeomorph R F hF L hreal).symm.toHomotopyEquiv.simplyConnectedSpace
  refine ⟨L, hL, ?_, ?_⟩
  · rwa [integerClosedCellUnion_image_eq_torusRegionPlanarRealization]
  · intro x hx
    rw [integerExteriorCollar, integerClosedCellUnion_image_eq_torusRegionPlanarRealization]
      at hx
    exact torusRealProjection_not_mem_of_mem_planarExteriorCollar R F hF L hreal hx

end TNLean.PEPS
