/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionLiftGauge
import TNLean.PEPS.RegularTwistedRegionProjectorCoordinates

/-!
# Canonical coordinates of integer-lifted torus regions

For commuting closure labels, the actual canonical region tensor is the
untwisted canonical tensor with transported boundary labels. Consequently its
normalized ancillary vector is the same for all commuting closure sectors.
This is derived from the supplied integer lift and the actual twisted finite sum.

**Scope restriction (supplied integer lift):** The arithmetic lift is supplied;
its existence for arbitrary disk regions and the complement-only removal of
the sector-dependent boundary transport are still separate statements. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, regular blocking and
boundary disentangling, local source lines 1840–1920 and 1935–1990.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The original twisted canonical tensor of an integer-lifted region equals
the untwisted tensor at the transported boundary configuration.
Source: SCP10, the regular-coordinate calculation, lines 1935–1990. -/
theorem regularProjectorTwistedRegionMatrix_coordinates_of_torusRegionIntegerLift
    {R : Finset (TorusVertex width height)} {L : {v // v ∈ R} → ℤ × ℤ}
    (hL : IsTorusRegionIntegerLift R L) (T : SimpleGraph {v // v ∈ R})
    [DecidableRel T.Adj]
    (hT : T ≤ (torusGraph width height).induce (R : Set (TorusVertex width height)))
    (htree : T.IsTree) (o : {v // v ∈ R}) (g h : G) (hgh : Commute g h)
    (c : RegularRegionCoordinates (Γ := torusGraph width height) (G := G) R T o)
    (θ : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge R e} → G) :
    regularProjectorTwistedRegionMatrix R (torusClosureEdgeAssignment g h)
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      regularProjectorOpenRegionMatrix R
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c)
        (regularRegionBoundaryTransport R
          (torusRegionLiftRootGauge R L g h o).1 (torusClosureEdgeAssignment g h) θ) := by
  rw [regularProjectorTwistedRegionMatrix_coordinates,
    regularProjectorOpenRegionMatrix_coordinates]
  simp_rw [regularRegionTreeCycleResidual_torusClosure_eq_one hL T hT htree o g h hgh,
    mul_one, mul_inv_cancel]
  rw [regularRegionTreeGauge_eq_torusRegionLiftRootGauge hL T hT htree o g h hgh]
  change _ * (∑ x : G, if c.1 = x • _ ∧ c.2.2.2 = 1 then (1 : ℂ) else 0) = _
  change _ = _ * _ * (if c.2.2.2 = 1 then 1 else 0)
  by_cases hz : c.2.2.2 = 1
  · simp only [hz, and_true, ↓reduceIte, mul_one]
    rw [regularLegProjector_apply, ← mul_assoc]
    have hκ : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [mul_right_comm (Fintype.card G : ℂ), mul_inv_cancel₀ hκ, one_mul]
  · simp only [hz, and_false, ↓reduceIte, Finset.sum_const_zero, mul_zero]

/-- One normalized ancillary vector works for every commuting closure pair on
the supplied lifted region; only the boundary transport depends on the pair.
Source: SCP10, regular blocking and disentangling, lines 1840–1920 and 1935–1990. -/
theorem regularProjectorTwistedRegionMatrix_exists_normalized_ancilla_of_torusRegionIntegerLift
    {R : Finset (TorusVertex width height)} {L : {v // v ∈ R} → ℤ × ℤ}
    (hL : IsTorusRegionIntegerLift R L) (T : SimpleGraph {v // v ∈ R})
    [DecidableRel T.Adj]
    (hT : T ≤ (torusGraph width height).induce (R : Set (TorusVertex width height)))
    (htree : T.IsTree) (o : {v // v ∈ R}) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ φ :
      (({e : Edge (torusGraph width height) // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G) ×
        RootedGroupLabels (G := G) o ×
        ({e : {e : Edge (torusGraph width height) // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
          ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G)) → ℂ,
      ∑ a, ∑ r, ∑ z, star (φ (a, r, z)) * φ (a, r, z) = 1 ∧
        ∀ (g h : G), Commute g h →
        ∀ (c : RegularRegionCoordinates (Γ := torusGraph width height) (G := G) R T o)
        (θ : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge R e} → G),
        regularProjectorTwistedRegionMatrix R (torusClosureEdgeAssignment g h)
            ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
          (γ : ℂ) * regularLegProjector
            {e : Edge (torusGraph width height) // IsRegionBoundaryEdge R e} c.1
            (regularRegionBoundaryTransport R (torusRegionLiftRootGauge R L g h o).1
              (torusClosureEdgeAssignment g h) θ) * φ c.2 := by
  obtain ⟨γ, hγ, φ, hnorm, hfactor⟩ :=
    regularProjectorOpenRegionMatrix_exists_normalized_ancilla (G := G) R T hT htree o
  refine ⟨γ, hγ, φ, hnorm, ?_⟩
  intro g h hgh c θ
  rw [regularProjectorTwistedRegionMatrix_coordinates_of_torusRegionIntegerLift
    hL T hT htree o g h hgh c θ]
  exact hfactor c _

end TNLean.PEPS
