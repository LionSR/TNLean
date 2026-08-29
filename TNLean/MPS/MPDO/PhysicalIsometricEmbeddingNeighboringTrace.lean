/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalIsometricEmbedding
import TNLean.MPS.MPDO.PhysicalSectorActiveNeighboring
import TNLean.MPS.MPDO.PhysicalSupportRestrictionComparison

/-!
# Neighboring-trace factorization under physical isometric embeddings

A normalized rank-one neighboring-trace factorization of an isometrically
embedded injective MPO tensor descends to the original tensor when the latter
has full one-site physical support. The proof passes through the active
physical support and compares two isometric coordinate descriptions of that
support.

This is a project-derived transport result, not a statement of CPSV16. Its
role is to test the representativewise conclusion of Theorem 4.9(iv), lines
864--889, after the physical-support restriction used in Appendix C.2, lines
1680--1691 and 1733--1770.
-/

open scoped Matrix

noncomputable section

namespace MPOTensor.PhysicalSectorFactorization

variable {d e D : ℕ} {K : MPOTensor d D}

/-- A normalized rank-one neighboring-trace factorization of an isometrically
embedded injective tensor descends to the original tensor when the latter has
full one-site physical support.

The proof first restricts an arbitrary factorization of the embedded tensor to
its active physical support. It then compares those support coordinates with
the coordinates supplied by the embedding isometry; the latter restriction is
the original tensor. Thus the neighboring operators, their positivity, the
factorization \(\operatorname{tr}(\eta_{k,h})=a_kb_h\), and the normalization
\(\sum_k a_kb_k=1\) are all retained by the existing active-support and
unitary-coordinate transports.

This is a project-derived transport theorem, not a statement of CPSV16. Its
role is to test the representativewise conclusion of Theorem 4.9(iv), lines
864--889, after the physical-support restriction used in Appendix C.2, lines
1680--1691 and 1733--1770. -/
theorem exists_neighboringTraceFactorization_of_changePhysicalBasis_of_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (hK : Kraus.IsInjective K.toMPSTensor)
    (hFull : physicalSupportProj K = 1)
    (hEmbedded : ∃ F : PhysicalSectorFactorization (changePhysicalBasis V K),
      Nonempty F.NeighboringTraceFactorization) :
    ∃ F : PhysicalSectorFactorization K,
      Nonempty F.NeighboringTraceFactorization := by
  let M := changePhysicalBasis V K
  have hM : Kraus.IsInjective M.toMPSTensor := by
    exact (isInjective_toMPSTensor_changePhysicalBasis_iff V hV K).2 hK
  have hRestrict : changePhysicalBasis Vᴴ M = K := by
    change changePhysicalBasis Vᴴ (changePhysicalBasis V K) = K
    rw [changePhysicalBasis_changePhysicalBasis, hV]
    ext i j β α
    simp [changePhysicalBasis, physicalSlice]
  let explicitRestriction : PhysicalSupportRestrictionData
      (physicalSupportProj M) M :=
    { supportDim := d
      inclusion := V
      inclusion_isometry := hV
      inclusion_range := by
        simpa [M, hFull] using
          (physicalSupportProj_changePhysicalBasis V hV K).symm
      restricted_injective := by
        rw [hRestrict]
        exact hK
      reembed := by
        rw [hRestrict] }
  obtain ⟨F, ⟨H⟩⟩ := hEmbedded
  let A := F.activeFactorSupportData
  let activeRestriction :=
    F.activePhysicalSupportRestrictionData A hM H.neighboringOperator_pos
  have hActive :
      ∃ G : PhysicalSectorFactorization
          (changePhysicalBasis activeRestriction.inclusionᴴ M),
        Nonempty G.NeighboringTraceFactorization := by
    refine ⟨F.activeRestrictedPhysicalSectorFactorization A, ⟨?_⟩⟩
    exact
      F.activeRestrictedPhysicalSectorFactorization_neighboringTraceFactorization
        A hM H
  have hExplicit :=
    (activeRestriction.exists_neighboringTraceFactorization_restriction_iff
      explicitRestriction).mp hActive
  have hInclusion : explicitRestriction.inclusion = V := rfl
  rw [hInclusion, hRestrict] at hExplicit
  exact hExplicit

end MPOTensor.PhysicalSectorFactorization
