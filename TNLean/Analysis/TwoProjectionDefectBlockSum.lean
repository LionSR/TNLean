/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.TwoProjectionAngleOrthogonality
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Semisimple

/-!
# Orthogonal sum of two-projection defect blocks

The defect blocks indexed by the compression eigenbasis form an orthogonal internal sum. Their
sum and its orthogonal complement are invariant under both projections. The first projection
vanishes on the complement, and therefore the two restricted projections commute there even
though the original projections need not commute.

This is the orthogonal-sum and commuting-remainder part of Jordan's lemma used in
arXiv:1703.09188, Proposition IV.5 (`prop:continuity-index`), lines 759–762.

**Local fix (projector label):** Source line 762 repeats `P` for the second projector, where the
surrounding argument requires `Q`; see `docs/paper-gaps/1703_two_projection_projector_typo.tex`.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private abbrev CompressionIndex {P : E →ₗ[ℂ] E} := Fin (Module.finrank ℂ P.range)

/-- The supremum of the defect blocks indexed by the full compression eigenbasis. -/
noncomputable def angleDefectSum {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) : Submodule ℂ E :=
  ⨆ i, angleDefectBlock hP hQ i

/-- The orthogonal complement of the sum of all compression defect blocks. -/
noncomputable def angleDefectComplement {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) : Submodule ℂ E :=
  (angleDefectSum hP hQ)ᗮ

/-- The compression-indexed defect blocks form an orthogonal family. -/
theorem angleDefectBlock_orthogonalFamily {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    OrthogonalFamily ℂ (fun i : CompressionIndex (P := P) => angleDefectBlock hP hQ i)
      (fun i => (angleDefectBlock hP hQ i).subtypeₗᵢ) :=
  OrthogonalFamily.of_pairwise fun _ _ hij => angleDefectBlock_isOrtho hP hQ hij

/-- After lifting each block to the defect-block sum, the family is an internal direct sum. -/
theorem angleDefectBlock_isInternal {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    DirectSum.IsInternal (fun i : CompressionIndex (P := P) =>
      (angleDefectBlock hP hQ i).comap (angleDefectSum hP hQ).subtype) := by
  classical
  simpa only [angleDefectSum, iSup_true] using
    DirectSum.isInternal_biSup_submodule_of_iSupIndep
      (A := fun i : CompressionIndex (P := P) => angleDefectBlock hP hQ i) Set.univ
      ((angleDefectBlock_orthogonalFamily hP hQ).independent.comp Subtype.coe_injective)

/-- The defect-block sum and its orthogonal complement give the ambient orthogonal
 decomposition. -/
theorem angleDefectSum_isCompl_angleDefectComplement {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    IsCompl (angleDefectSum hP hQ) (angleDefectComplement hP hQ) := by
  exact Submodule.isCompl_orthogonal (K := angleDefectSum hP hQ)

/-- The range of the first projection lies in the sum of the compression defect blocks. -/
theorem range_le_angleDefectSum {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    P.range ≤ angleDefectSum hP hQ := by
  rintro x ⟨y, rfl⟩
  rw [← (rangeCompressionEigenbasis hP hQ).toBasis.span_eq] at y
  refine Submodule.span_induction y ?_ (Submodule.zero_mem _) ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact le_iSup (fun j => angleDefectBlock hP hQ j) i <|
      Submodule.subset_span (by left; rfl)
  · exact fun _ _ => Submodule.add_mem _
  · exact fun c _ => Submodule.smul_mem _ c

/-- The defect-block sum is invariant under the first projection. -/
theorem map_angleDefectSum_le_first_projection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Submodule.map P (angleDefectSum hP hQ) ≤ angleDefectSum hP hQ := by
  rw [angleDefectSum, Submodule.map_iSup]
  exact iSup_le fun i => (map_angleDefectBlock_le_first_projection hP hQ i).trans
    (le_iSup (fun j => angleDefectBlock hP hQ j) i)

/-- The defect-block sum is invariant under the second projection. -/
theorem map_angleDefectSum_le_second_projection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Submodule.map Q (angleDefectSum hP hQ) ≤ angleDefectSum hP hQ := by
  rw [angleDefectSum, Submodule.map_iSup]
  exact iSup_le fun i => (map_angleDefectBlock_le_second_projection hP hQ i).trans
    (le_iSup (fun j => angleDefectBlock hP hQ j) i)

/-- The orthogonal complement of the defect-block sum is invariant under the first projection. -/
theorem map_angleDefectComplement_le_first_projection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Submodule.map P (angleDefectComplement hP hQ) ≤ angleDefectComplement hP hQ := by
  exact Module.End.mem_invtSubmodule_iff_map_le.mp <|
    hP.isSymmetric.orthogonalComplement_mem_invtSubmodule
      (Module.End.mem_invtSubmodule_iff_map_le.mpr
        (map_angleDefectSum_le_first_projection hP hQ))

/-- The orthogonal complement of the defect-block sum is invariant under the second projection. -/
theorem map_angleDefectComplement_le_second_projection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Submodule.map Q (angleDefectComplement hP hQ) ≤ angleDefectComplement hP hQ := by
  exact Module.End.mem_invtSubmodule_iff_map_le.mp <|
    hQ.isSymmetric.orthogonalComplement_mem_invtSubmodule
      (Module.End.mem_invtSubmodule_iff_map_le.mpr
        (map_angleDefectSum_le_second_projection hP hQ))

/-- The first projection vanishes on the complement of the defect-block sum. -/
theorem first_projection_apply_eq_zero_of_mem_angleDefectComplement {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) {z : E}
    (hz : z ∈ angleDefectComplement hP hQ) : P z = 0 := by
  apply LinearMap.mem_ker.mp
  rw [← hP.isSymmetric.orthogonal_range]
  exact Submodule.orthogonal_le (range_le_angleDefectSum hP hQ) hz

/-- Both compositions agree, and vanish, on the complement of the defect-block sum. -/
theorem projections_comp_apply_eq_zero_of_mem_angleDefectComplement {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) {z : E}
    (hz : z ∈ angleDefectComplement hP hQ) : P (Q z) = 0 ∧ Q (P z) = 0 := by
  constructor
  · exact first_projection_apply_eq_zero_of_mem_angleDefectComplement hP hQ <|
      (map_angleDefectComplement_le_second_projection hP hQ) ⟨z, hz, rfl⟩
  · rw [first_projection_apply_eq_zero_of_mem_angleDefectComplement hP hQ hz, map_zero]

/-- The restriction of the first projection to the complementary summand. -/
noncomputable def firstProjectionOnAngleDefectComplement {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    angleDefectComplement hP hQ →ₗ[ℂ] angleDefectComplement hP hQ :=
  P.restrict fun _ hz => (map_angleDefectComplement_le_first_projection hP hQ) ⟨_, hz, rfl⟩

/-- The restriction of the second projection to the complementary summand. -/
noncomputable def secondProjectionOnAngleDefectComplement {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    angleDefectComplement hP hQ →ₗ[ℂ] angleDefectComplement hP hQ :=
  Q.restrict fun _ hz => (map_angleDefectComplement_le_second_projection hP hQ) ⟨_, hz, rfl⟩

/-- The first restricted projection is the zero map. -/
theorem firstProjectionOnAngleDefectComplement_eq_zero {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    firstProjectionOnAngleDefectComplement hP hQ = 0 := by
  ext z
  exact first_projection_apply_eq_zero_of_mem_angleDefectComplement hP hQ z.property

/-- The first restricted projection remains a symmetric projection. -/
theorem firstProjectionOnAngleDefectComplement_isSymmetricProjection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    (firstProjectionOnAngleDefectComplement hP hQ).IsSymmetricProjection := by
  rw [firstProjectionOnAngleDefectComplement_eq_zero hP hQ]
  exact ⟨.zero, LinearMap.IsSymmetric.zero⟩

/-- The second restricted projection remains a symmetric projection. -/
theorem secondProjectionOnAngleDefectComplement_isSymmetricProjection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    (secondProjectionOnAngleDefectComplement hP hQ).IsSymmetricProjection := by
  let hQinv : ∀ z ∈ angleDefectComplement hP hQ, Q z ∈ angleDefectComplement hP hQ :=
    fun z hz => (map_angleDefectComplement_le_second_projection hP hQ) ⟨z, hz, rfl⟩
  constructor
  · apply DFunLike.ext _ _ fun z => Subtype.ext ?_
    exact LinearMap.IsIdempotentElem.apply_apply hQ.isIdempotentElem z
  · exact hQ.isSymmetric.restrict_invariant hQinv

/-- The restricted projections commute on the complementary summand. This conclusion does not
assume that the original projections commute on the ambient space. -/
theorem firstProjectionOnAngleDefectComplement_commute_secondProjection {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Commute (firstProjectionOnAngleDefectComplement hP hQ)
      (secondProjectionOnAngleDefectComplement hP hQ) := by
  rw [firstProjectionOnAngleDefectComplement_eq_zero hP hQ]
  exact Commute.zero_left _

end LinearMap.IsSymmetricProjection
