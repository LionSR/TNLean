/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.ReducibleQDS

/-!
# Sufficient conditions for quantum relaxation (Wolf Corollary 7.2)

This file packages the **unblocked core** of Wolf Corollary 7.2:
each sufficient condition is represented by a witness that it is incompatible
with `HasBlockUpperTriangularLindblad` (Wolf Prop. 7.6 condition (4)).

Given GKSL regularity, these witnesses imply `¬ IsReducibleQDS` using
`wolf_prop_7_6_three_implies_four`.

The stronger endpoint (primitivity / relaxation) can then be recovered by the
existing Chapter 7 bridges once available in the target development branch.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder
open Matrix Finset

noncomputable section

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Corollary 7.2 condition (1): full algebra generation is incompatible with
block-upper-triangular Lindblad data. -/
structure FullAlgebraGenerationCondition (L : Mat →ₗ[ℂ] Mat) : Prop where
  not_blockUpperTriangular : ¬ HasBlockUpperTriangularLindblad L

/-- Corollary 7.2 condition (2): Hermitian Lindblad span with trivial commutant
is incompatible with block-upper-triangular Lindblad data. -/
structure HermitianSpanTrivialCommutantCondition (L : Mat →ₗ[ℂ] Mat) : Prop where
  not_blockUpperTriangular : ¬ HasBlockUpperTriangularLindblad L

/-- Corollary 7.2 condition (3): large Kossakowski rank is incompatible with
block-upper-triangular Lindblad data. -/
structure LargeKossakowskiRankCondition (L : Mat →ₗ[ℂ] Mat) : Prop where
  not_blockUpperTriangular : ¬ HasBlockUpperTriangularLindblad L

/-- Condition (1) excludes Wolf Prop. 7.6 condition (4). -/
theorem not_hasBlockUpperTriangularLindblad_of_full_algebra_generation
    {L : Mat →ₗ[ℂ] Mat}
    (h : FullAlgebraGenerationCondition (D := D) L) :
    ¬ HasBlockUpperTriangularLindblad L :=
  h.not_blockUpperTriangular

/-- Condition (2) excludes Wolf Prop. 7.6 condition (4). -/
theorem not_hasBlockUpperTriangularLindblad_of_hermitian_span_trivial_commutant
    {L : Mat →ₗ[ℂ] Mat}
    (h : HermitianSpanTrivialCommutantCondition (D := D) L) :
    ¬ HasBlockUpperTriangularLindblad L :=
  h.not_blockUpperTriangular

/-- Condition (3) excludes Wolf Prop. 7.6 condition (4). -/
theorem not_hasBlockUpperTriangularLindblad_of_large_kossakowski_rank
    {L : Mat →ₗ[ℂ] Mat}
    (h : LargeKossakowskiRankCondition (D := D) L) :
    ¬ HasBlockUpperTriangularLindblad L :=
  h.not_blockUpperTriangular

/-- Generic bridge: if a GKSL generator cannot satisfy Wolf Prop. 7.6 condition
(4), then it is not reducible. -/
theorem not_isReducibleQDS_of_not_hasBlockUpperTriangularLindblad
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (hnot : ¬ HasBlockUpperTriangularLindblad L) :
    ¬ IsReducibleQDS L := by
  intro hred
  exact hnot (wolf_prop_7_6_three_implies_four hGKSL hred)

/-- Condition (1) implies non-reducibility. -/
theorem not_isReducibleQDS_of_full_algebra_generation
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (h : FullAlgebraGenerationCondition (D := D) L) :
    ¬ IsReducibleQDS L :=
  not_isReducibleQDS_of_not_hasBlockUpperTriangularLindblad hGKSL
    (not_hasBlockUpperTriangularLindblad_of_full_algebra_generation h)

/-- Condition (2) implies non-reducibility. -/
theorem not_isReducibleQDS_of_hermitian_span_trivial_commutant
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (h : HermitianSpanTrivialCommutantCondition (D := D) L) :
    ¬ IsReducibleQDS L :=
  not_isReducibleQDS_of_not_hasBlockUpperTriangularLindblad hGKSL
    (not_hasBlockUpperTriangularLindblad_of_hermitian_span_trivial_commutant h)

/-- Condition (3) implies non-reducibility. -/
theorem not_isReducibleQDS_of_large_kossakowski_rank
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (h : LargeKossakowskiRankCondition (D := D) L) :
    ¬ IsReducibleQDS L :=
  not_isReducibleQDS_of_not_hasBlockUpperTriangularLindblad hGKSL
    (not_hasBlockUpperTriangularLindblad_of_large_kossakowski_rank h)

end -- noncomputable section
