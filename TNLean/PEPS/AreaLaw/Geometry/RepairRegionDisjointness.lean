/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Algebra.ConstMulAction
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInteriors
import TNLean.PEPS.AreaLaw.Geometry.RepairDepth
import TNLean.PEPS.AreaLaw.Geometry.RepairReplacementRegions

/-!
# Disjoint replacement regions at one parent

Distinct connected runs at a parent give disjoint current replacement
regions. This follows from disjointness of the interiors of the normalized
whole runs, transported by the affine homeomorphism of the removal square.
The argument retains inactive seams and applies to reflex runs.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 404–417;
`geometry:repair-induction`, lines 486–514; and closed births and open
current regions, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Distinct runs at one parent have disjoint current replacement regions.
No convexity or difference of colors is required.
Source: area-law Section 11, lines 404–417, 486–514 and 558–561. -/
theorem repairReplacementOpenRegion_pairwise_disjoint {ι : Type*}
    (v : ℝ × ℝ) (S : ℝ) (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) :
    Pairwise (fun R T : RepairFanRun ξ σ ↦
      Disjoint (repairReplacementOpenRegion v S ξ σ R)
        (repairReplacementOpenRegion v S ξ σ T)) := by
  exact fun R T hRT ↦
    let e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
      (Homeomorph.smulOfNeZero (repairHalfSide S) (repairHalfSide_pos S).ne').trans
        (Homeomorph.addLeft v)
    Eq.mp
      (congrArg₂ Disjoint
        (e.image_interior (cellFanRunRegion (-1, -1) 1 (0, 0)
          repairFanSplit (repairExteriorColor ξ σ) R))
        (e.image_interior (cellFanRunRegion (-1, -1) 1 (0, 0)
          repairFanSplit (repairExteriorColor ξ σ) T)))
      (Set.disjoint_image_of_injective e.injective
        (cellFanRunRegions_disjoint_interiors (-1, -1) 1 (0, 0)
          repairFanSplit (repairExteriorColor ξ σ) R T hRT))

end TNLean.PEPS.AreaLaw.Geometry
