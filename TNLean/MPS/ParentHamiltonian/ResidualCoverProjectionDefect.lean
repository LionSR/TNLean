/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ProjectionDefectIsometry
import TNLean.MPS.ParentHamiltonian.ResidualWindowFullSectorSum
import TNLean.MPS.ParentHamiltonian.ResidualWindowLeftGroundSpace
import TNLean.MPS.ParentHamiltonian.ResidualWindowJointProjectionDecay

/-!
# The physical residual cover projection limit

For a normalized periodic tensor, the joint right, left, and full residual
window spaces are the images of the corresponding original-chain boundary
spaces under one physical configuration isometry. The joint-sector defect
therefore has exactly the norm of the original cover defect. Reversal of the
projection order is accounted for by the adjoint, rather than by assuming
that the two projections commute.

**Scope restriction (periodic tensor presentation):** The result concerns
an explicitly supplied normalized periodic tensor. The passage from a
general GVBS presentation to this tensor presentation remains separate;
see `docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531, and Section 6.
-/

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D m : ℕ}

/-- Periodicity derives the vanishing physical cover projection defect,
uniformly along every prefix and tail selection as the overlap tends to
infinity. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531, and Section 6. -/
theorem IsPeriodic.residue_cover_projection_defect_tendsto_zero
    {A : MPSTensor d D} (hA : IsPeriodic m A) (K r : ℕ → ℕ) :
    Filter.Tendsto (fun M =>
      ‖(groundSpaceES A (K M * m + M * m + r M)).starProjection -
        (leftBoundaryMapES A (K M * m + M * m) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * m) (M * m) (r M)).range.starProjection‖)
      Filter.atTop (nhds 0) := by
  obtain ⟨dim, hdim, B, V, hV, hSum, hInt, hCoInt, hJoint⟩ :=
    hA.exists_residualWindow_joint_projection_comp_sub_tendsto_zero
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hNorm (M : ℕ) :
      ‖(⨆ j, (residualWindowRightMapES A (B j) (V j) (K M) M (r M)).range).starProjection.comp
          (⨆ j, (residualWindowLeftMapES (B j) (K M) M (r M)).range).starProjection -
        (⨆ j, (residualWindowMapES A (B j) (V j) (K M) M (r M)).range).starProjection‖ =
      ‖(groundSpaceES A (K M * m + M * m + r M)).starProjection -
        (leftBoundaryMapES A (K M * m + M * m) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * m) (M * m) (r M)).range.starProjection‖ := by
    simp only [iSup_range_residualWindowRightMapES_eq_reindex_reassocTailBoundaryMapES
      A B V hSum hCoInt,
      iSup_range_residualWindowLeftMapES_eq_reindex_cover_leftBoundaryMapES
        A B V hV hSum hInt,
      iSup_range_residualWindowMapES_eq_reindex_groundSpaceES_cover A B V hSum hCoInt]
    exact Submodule.norm_map_starProjection_comp_sub_eq _ _ _ _
  simpa only [hNorm] using hJoint K r

end MPSTensor
