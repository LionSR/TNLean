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
`¬ HasBlockUpperTriangularLindblad` is recorded as theorem placeholders
(`*_implies_no_blockUpperTriangular`) so downstream files can use uniform
non-reducibility consequences while CI continues to track unfinished proofs.
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

/-- The Lindblad span is closed under Hermitian conjugation, i.e. the `ℂ`-span
of the Lindblad operators `{Lⱼ}` forms a `*`-subspace of `Mₐ(ℂ)`:
for every `X = ∑ xⱼ Lⱼ` there exist `yⱼ` such that `X† = ∑ yⱼ Lⱼ`.
This is the Hermiticity condition appearing in Wolf Corollary 7.2(2). -/
def IsLindbladSpanHermitianClosed (F : LindbladForm D) : Prop :=
  ∀ A : Mat, A ∈ lindbladSpan F → Aᴴ ∈ lindbladSpan F

/-- The commutant of the Lindblad family contains only scalar multiples of the
identity: `{Lⱼ}' = ℂ · 𝟙`.  This means the Lindblad operators act
irreducibly on the matrix algebra `Mₐ(ℂ)`.
This is the trivial-commutant condition appearing in Wolf Corollary 7.2(2). -/
def HasLindbladSpanTrivialCommutant (F : LindbladForm D) : Prop :=
  ∀ A : Mat,
    (∀ j : Fin F.r, A * F.L j = F.L j * A) →
      ∃ c : ℂ, A = c • (1 : Mat)

/-- The minimal number of Lindblad operators across all GKSL representations
of `L`.  This equals the rank of the Kossakowski matrix in the
orthonormal-basis representation (Wolf §7.1). -/
def kossakowskiRank (L : Mat →ₗ[ℂ] Mat) : ℕ :=
  sInf {n : ℕ | ∃ F : LindbladForm D, F.toLinearMap = L ∧ F.r = n}

/--
Condition (1): full algebra generation forbids block-upper-triangular
Lindblad decompositions.
-/
-- TODO: prove that full algebra generation forbids block-upper-triangular
-- decompositions — see Wolf Cor. 7.2(1) and proof sketch via Prop 7.6.
theorem full_algebra_generation_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ (Set.range F.L ∪ ({F.H} : Set Mat)) = ⊤) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  sorry

/--
Condition (2): Hermitian closure of the Lindblad span together with trivial
commutant forbids block-upper-triangular Lindblad decompositions.
-/
-- TODO: prove that Hermitian closure + trivial commutant forbids
-- block-upper-triangular decompositions — see Wolf Cor. 7.2(2).
theorem hermitian_span_trivial_commutant_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hHerm : IsLindbladSpanHermitianClosed F)
    (hComm : HasLindbladSpanTrivialCommutant F) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  sorry

/--
Condition (3): Kossakowski rank `> d² − d` forbids block-upper-triangular
Lindblad decompositions (Wolf Cor. 7.2(3)).

The hypothesis is stated using addition (`rank + D ≥ D² + 1`) to avoid
natural-number subtraction issues; this is equivalent to `rank > D² − D`.
-/
-- TODO: prove that rank(C) > d² − d forbids block-upper-triangular
-- decompositions — see Wolf Cor. 7.2(3) and proof via Prop 7.6.
theorem large_kossakowski_rank_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hRank : kossakowskiRank F.toLinearMap + D ≥ D ^ 2 + 1) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  sorry

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
    (hHerm : IsLindbladSpanHermitianClosed F)
    (hComm : HasLindbladSpanTrivialCommutant F) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact hermitian_span_trivial_commutant_implies_no_blockUpperTriangular F hHerm hComm

/-- Wolf Corollary 7.2 condition (3): large Kossakowski rank implies
non-reducibility. -/
theorem not_isReducible_of_kossakowski_rank_ge
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hRank : kossakowskiRank F.toLinearMap + D ≥ D ^ 2 + 1) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact large_kossakowski_rank_implies_no_blockUpperTriangular F hRank

end -- noncomputable section
