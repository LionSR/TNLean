/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.ReducibleQDS.FixedDensity
import TNLean.Channel.Semigroup.ReducibleQDS.GeneratorCompression
import TNLean.Channel.Semigroup.ReducibleQDS.SubsequenceAnalysis

/-!
# Reducibility Definition and Full Equivalence (Wolf Prop 7.6)

This file defines `IsReducibleQDS` and proves the full four-way equivalence
of Wolf Proposition 7.6.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace
open Matrix Finset

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## Reducibility definition -/

/-- A QDS `T_t = exp(tL)` is **reducible** if there exists a nontrivial
orthogonal projection `P` such that `T_t` preserves the compressed algebra
`P M_d P`. This is the negation of irreducibility for the semigroup.

Note: for a single map, `IsIrreducibleMap` checks that no nontrivial `P`
satisfies `P E(PXP) P = E(PXP)` for all `X`. Here we require this for ALL
`T_t` simultaneously, which by Prop 7.6 is equivalent to requiring it for
the generator `L`. -/
def IsReducibleQDS (L : Mat →ₗ[ℂ] Mat) : Prop :=
  HasInvariantCompression L

/-- A QDS is reducible iff the generator preserves some nontrivial compression. -/
theorem isReducibleQDS_iff_generator_preserves_compression
    (L : Mat →ₗ[ℂ] Mat) :
    IsReducibleQDS L ↔
      ∃ P : Mat, IsNontrivialProjection P ∧
        GeneratorPreservesCompression L P := by
  constructor
  · -- Reducible → nontrivial invariant P at generator level
    intro ⟨P, hP_nt, hT⟩
    exact ⟨P, hP_nt,
      generatorPreservesCompression_of_semigroupPreservesCompression hP_nt.1 hT⟩
  · -- Nontrivial invariant P at generator level → reducible
    intro ⟨P, hP_nt, hgen⟩
    exact ⟨P, hP_nt,
      semigroup_preserves_compression_of_generator hP_nt.1 hgen⟩

/-! ## The full equivalence (Wolf Proposition 7.6) -/

/-- **Wolf Proposition 7.6, (2) → (4)**: A rank-deficient kernel element of a
GKSL generator yields a block-upper-triangular Lindblad form. -/
theorem hasBlockUpperTriangularLindblad_of_hasRankDeficientKernelElement
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (h : HasRankDeficientKernelElement L) :
    HasBlockUpperTriangularLindblad L := by
  apply hasBlockUpperTriangularLindblad_of_hasInvariantCompression hGKSL
  exact wolf_prop_7_6_one_implies_three hGKSL
    (hasRankDeficientFixedDensity_of_hasRankDeficientKernelElement h)

/-- **Wolf Proposition 7.6, (4) → (3)**: Block-upper-triangular Lindblad
operators imply the semigroup preserves the compressed algebra. -/
theorem wolf_prop_7_6_four_implies_three
    {L : Mat →ₗ[ℂ] Mat}
    (h : HasBlockUpperTriangularLindblad L) :
    HasInvariantCompression L :=
  hasInvariantCompression_of_hasBlockUpperTriangularLindblad h

theorem wolf_prop_7_6_three_implies_four
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (h : HasInvariantCompression L) :
    HasBlockUpperTriangularLindblad L :=
  hasBlockUpperTriangularLindblad_of_hasInvariantCompression hGKSL h

/-- **(3) → (2)**: An invariant compression implies a rank-deficient kernel element.
This follows from (3) → (4) → (2). -/
theorem wolf_prop_7_6_three_implies_two
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (h : HasInvariantCompression L) :
    HasRankDeficientKernelElement L :=
  hasRankDeficientKernelElement_of_hasBlockUpperTriangularLindblad hGKSL
    (hasBlockUpperTriangularLindblad_of_hasInvariantCompression hGKSL h)

/-- **Wolf Proposition 7.6 (full equivalence)**: For a GKSL generator `L`, the
four reducibility conditions are equivalent. We state the result by taking
condition (1) as the base condition. -/
theorem wolf_prop_7_6_full_equivalence
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L) :
    HasRankDeficientFixedDensity L ↔
      HasRankDeficientKernelElement L ∧
        HasInvariantCompression L ∧
        HasBlockUpperTriangularLindblad L := by
  constructor
  · intro h1
    refine ⟨?_, ?_, ?_⟩
    · exact hasRankDeficientKernelElement_of_hasRankDeficientFixedDensity h1
    · exact wolf_prop_7_6_one_implies_three hGKSL h1
    · exact hasBlockUpperTriangularLindblad_of_hasRankDeficientKernelElement hGKSL
        (hasRankDeficientKernelElement_of_hasRankDeficientFixedDensity h1)
  · intro h1234
    exact hasRankDeficientFixedDensity_of_hasRankDeficientKernelElement h1234.1

/-! ## Sum-of-squares vanishing lemma -/

/-- If `∑ⱼ Bⱼ Bⱼ† = 0` for square matrices, then each `Bⱼ = 0`.

This is the key algebraic fact needed for the (3) → (4) direction of
Wolf Proposition 7.6. The proof delegates to the existing
`eq_zero_of_sum_mul_conjTranspose_eq_zero` from `Channel.Irreducible.Basic`. -/
theorem sum_conjTranspose_mul_self_eq_zero_imp
    {r : ℕ} (B : Fin r → Mat)
    (h : ∑ j, B j * (B j)ᴴ = 0) :
    ∀ j, B j = 0 :=
  eq_zero_of_sum_mul_conjTranspose_eq_zero B h

end -- noncomputable section
