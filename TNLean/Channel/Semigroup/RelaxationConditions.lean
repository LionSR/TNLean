/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.ReducibleQDS

/-!
# Wolf Corollary 7.2 — Sufficient conditions for non-reducibility

This module records three standard sufficient-condition patterns from
Wolf Corollary 7.2, each funneled through the already formalized bridge

`¬ HasBlockUpperTriangularLindblad L → ¬ IsReducibleQDS L`.

The conversion from each algebraic hypothesis to
`¬ HasBlockUpperTriangularLindblad` is provided by dedicated assumptions
(`*_implies_no_blockUpperTriangular`) so downstream files can use uniform
non-reducibility consequences immediately.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder
open Matrix Finset

noncomputable section

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The `ℂ`-linear span of a Lindblad family's operators. -/
def lindbladSpan (F : LindbladForm D) : Submodule ℂ Mat :=
  Submodule.span ℂ (Set.range F.L)

/-- Hermitian closure of the Lindblad span. -/
def LindbladSpanHermitianClosed (F : LindbladForm D) : Prop :=
  ∀ A : Mat, A ∈ lindbladSpan F → Aᴴ ∈ lindbladSpan F

/-- Trivial commutant for the Lindblad family (`ℂ • 1` only). -/
def LindbladSpanTrivialCommutant (F : LindbladForm D) : Prop :=
  ∀ A : Mat,
    (∀ j : Fin F.r, A * F.L j = F.L j * A) →
      ∃ c : ℂ, A = c • (1 : Mat)

/-- A rank proxy used to formulate the large-Kossakowski-rank condition. -/
def kossakowskiRank (F : LindbladForm D) : ℕ := F.r

/--
Condition (1): full algebra generation forbids block-upper-triangular
Lindblad decompositions.
-/
axiom full_algebra_generation_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ (Set.range F.L ∪ ({F.H} : Set Mat)) = ⊤) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap

/--
Condition (2): Hermitian closure of the Lindblad span together with trivial
commutant forbids block-upper-triangular Lindblad decompositions.
-/
axiom hermitian_span_trivial_commutant_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hHerm : LindbladSpanHermitianClosed F)
    (hComm : LindbladSpanTrivialCommutant F) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap

/--
Condition (3): sufficiently large Kossakowski rank forbids
block-upper-triangular Lindblad decompositions.
-/
axiom large_kossakowski_rank_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hRank : dite (D = 0) (fun _ => kossakowskiRank F ≥ 0)
      (fun _ => kossakowskiRank F ≥ D ^ 2 - 1)) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap

/--
If a GKSL generator has no block-upper-triangular Lindblad decomposition,
then the generated quantum dynamical semigroup is not reducible.
-/
theorem not_isReducibleQDS_of_no_blockUpperTriangular_lindblad
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (hNoBlockUT : ¬ HasBlockUpperTriangularLindblad L) :
    ¬ IsReducibleQDS L := by
  intro hReducible
  exact hNoBlockUT (wolf_prop_7_6_three_implies_four hGKSL hReducible)

/-- Wolf Corollary 7.2 condition (1): full algebra generation implies
non-reducibility. -/
theorem not_isReducible_of_generates_full_algebra
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hGen : Algebra.adjoin ℂ (Set.range F.L ∪ ({F.H} : Set Mat)) = ⊤) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact full_algebra_generation_implies_no_blockUpperTriangular F hGen

/-- Wolf Corollary 7.2 condition (2): Hermitian Lindblad span + trivial
commutant implies non-reducibility. -/
theorem not_isReducible_of_hermitian_span_trivial_commutant
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hHerm : LindbladSpanHermitianClosed F)
    (hComm : LindbladSpanTrivialCommutant F) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact hermitian_span_trivial_commutant_implies_no_blockUpperTriangular F hHerm hComm

/-- Wolf Corollary 7.2 condition (3): large Kossakowski rank implies
non-reducibility. -/
theorem not_isReducible_of_kossakowski_rank_ge
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hRank : dite (D = 0) (fun _ => kossakowskiRank F ≥ 0)
      (fun _ => kossakowskiRank F ≥ D ^ 2 - 1)) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact large_kossakowski_rank_implies_no_blockUpperTriangular F hRank

end -- noncomputable section
