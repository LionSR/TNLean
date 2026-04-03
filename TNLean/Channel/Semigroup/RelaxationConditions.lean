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

private theorem lower_left_block_vanishes_on_lindbladSpan
    {P : Mat} (F : LindbladForm D)
    (hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0) :
    ∀ A : Mat, A ∈ lindbladSpan F → (1 - P) * A * P = 0 := by
  intro A hA
  induction hA using Submodule.span_induction with
  | mem B hB =>
      rcases hB with ⟨j, rfl⟩
      exact hblock j
  | zero =>
      simp
  | add A B _ _ hA hB =>
      rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
      simp
  | smul c A _ hA =>
      rw [mul_smul_comm, smul_mul_assoc, hA, smul_zero]

private theorem not_isNontrivialProjection_of_eq_smul_one
    {P : Mat} (hP_nt : IsNontrivialProjection P) {c : ℂ}
    (hP : P = c • (1 : Mat)) : False := by
  by_cases hD : D = 0
  · subst hD
    exact hP_nt.2.1 (Subsingleton.elim _ _)
  · haveI : NeZero D := ⟨hD⟩
    have hIdem : (c • (1 : Mat)) * (c • (1 : Mat)) = c • (1 : Mat) := by
      simpa [hP] using hP_nt.1.2
    have hc : c * c = c := by
      have h00 := congrFun (congrFun hIdem 0) 0
      simpa using h00
    have hc01 : c = 0 ∨ c = 1 := by
      have hfac : c * (c - 1) = 0 := by
        calc
          c * (c - 1) = c * c - c := by ring
          _ = 0 := by rw [hc, sub_self]
      rcases mul_eq_zero.mp hfac with hc0 | hc1
      · exact Or.inl hc0
      · exact Or.inr (sub_eq_zero.mp hc1)
    rcases hc01 with hc0 | hc1
    · exact hP_nt.2.1 (by rw [hP, hc0, zero_smul])
    · exact hP_nt.2.2 (by rw [hP, hc1, one_smul])

private theorem lower_left_block_vanishes_on_adjoin
    {P : Mat} (hP : IsOrthogonalProjection P) (S : Set Mat)
    (hS : ∀ A : Mat, A ∈ S → (1 - P) * A * P = 0) :
    ∀ A : Mat, A ∈ Algebra.adjoin ℂ S → (1 - P) * A * P = 0 := by
  have hQP := orthogonalProjection_complement_mul hP
  have hblock_mul :
      ∀ A B : Mat,
        (1 - P) * A * P = 0 →
          (1 - P) * B * P = 0 →
            (1 - P) * (A * B) * P = 0 := by
    intro A B hA hB
    calc
      (1 - P) * (A * B) * P = (1 - P) * A * B * P := by
        simp [Matrix.mul_assoc]
      _ = (1 - P) * A * (P + (1 - P)) * B * P := by
        rw [show (1 : Mat) = P + (1 - P) by abel]
        simp [Matrix.mul_assoc]
      _ = (1 - P) * A * P * B * P + (1 - P) * A * (1 - P) * B * P := by
        noncomm_ring
      _ = (1 - P) * A * (1 - P) * B * P := by
        simp [hA, Matrix.mul_assoc]
      _ = (1 - P) * A * ((1 - P) * B * P) := by
        simp [Matrix.mul_assoc]
      _ = 0 := by simp [hB]
  intro A hA
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
      exact hS A hA
  | algebraMap c =>
      calc
        (1 - P) * algebraMap ℂ Mat c * P = (1 - P) * (c • (1 : Mat)) * P := by
          rw [Algebra.algebraMap_eq_smul_one]
        _ = c • ((1 - P) * (1 : Mat) * P) := by
          simp
        _ = 0 := by simp [hQP]
  | add A B _ _ hA hB =>
      rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
      simp
  | mul A B _ _ hA hB =>
      exact hblock_mul A B hA hB

/--
Condition (1): full algebra generation by the Lindblad operators together with
`κ = F.toGeneratorDecomp.κ` forbids block-upper-triangular Lindblad
decompositions.
-/
theorem full_algebra_generation_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ
      (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) = ⊤) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  intro hBlock
  obtain ⟨P, hP_nt, hT⟩ :=
    hasInvariantCompression_of_hasBlockUpperTriangularLindblad hBlock
  have hgen : GeneratorPreservesCompression F.toLinearMap P :=
    generatorPreservesCompression_of_semigroupPreservesCompression hP_nt.1 hT
  have hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0 :=
    lindblad_block_of_generatorPreservesCompression hP_nt.1 F hgen
  have hκ_block : (1 - P) * F.toGeneratorDecomp.κ * P = 0 :=
    kappa_block_of_generatorPreservesCompression hP_nt.1 F hgen hblock
  have hblock_adjoin :
      ∀ A : Mat, A ∈ Algebra.adjoin ℂ
        (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) →
          (1 - P) * A * P = 0 := by
    apply lower_left_block_vanishes_on_adjoin hP_nt.1
    intro A hA
    rcases hA with hA | hA
    · rcases hA with ⟨j, rfl⟩
      exact hblock j
    · simp only [Set.mem_singleton_iff] at hA
      rw [hA]
      exact hκ_block
  have hall : ∀ A : Mat, (1 - P) * A * P = 0 := by
    intro A
    exact hblock_adjoin A (hGen ▸ Algebra.mem_top)
  rcases proj_zero_or_one_of_sandwich P hall with hP0 | hP1
  · exact hP_nt.2.1 hP0
  · exact hP_nt.2.2 hP1

/--
Condition (2): Hermitian closure of the Lindblad span together with trivial
commutant forbids block-upper-triangular Lindblad decompositions.
-/
theorem hermitian_span_trivial_commutant_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hHerm : IsLindbladSpanHermitianClosed F)
    (hComm : HasLindbladSpanTrivialCommutant F) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  intro hBlock
  obtain ⟨P, hP_nt, hT⟩ :=
    hasInvariantCompression_of_hasBlockUpperTriangularLindblad hBlock
  have hgen : GeneratorPreservesCompression F.toLinearMap P :=
    generatorPreservesCompression_of_semigroupPreservesCompression hP_nt.1 hT
  have hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0 :=
    lindblad_block_of_generatorPreservesCompression hP_nt.1 F hgen
  have hblock_span : ∀ A : Mat, A ∈ lindbladSpan F → (1 - P) * A * P = 0 :=
    lower_left_block_vanishes_on_lindbladSpan F hblock
  have hP_herm : Pᴴ = P := hP_nt.1.1
  have hP_add_compl : P + (1 - P) = (1 : Mat) := by
    abel
  have hcommP : ∀ j : Fin F.r, P * F.L j = F.L j * P := by
    intro j
    have hLj_mem : F.L j ∈ lindbladSpan F := by
      exact Submodule.subset_span ⟨j, rfl⟩
    have hLj_star_mem : (F.L j)ᴴ ∈ lindbladSpan F := hHerm _ hLj_mem
    have hPAQ : P * F.L j * (1 - P) = 0 := by
      have hct := congrArg Matrix.conjTranspose (hblock_span _ hLj_star_mem)
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, Matrix.conjTranspose_zero, hP_herm] at hct
      simpa [Matrix.mul_assoc] using hct
    have hleft : P * F.L j = P * F.L j * P := by
      calc
        P * F.L j = P * F.L j * 1 := by simp
        _ = P * F.L j * (P + (1 - P)) := by
          rw [hP_add_compl]
        _ = P * F.L j * P + P * F.L j * (1 - P) := by rw [Matrix.mul_add]
        _ = P * F.L j * P := by rw [hPAQ, add_zero]
    have hright : F.L j * P = P * F.L j * P := by
      calc
        F.L j * P = 1 * (F.L j * P) := by simp
        _ = (P + (1 - P)) * (F.L j * P) := by
          rw [hP_add_compl]
        _ = P * (F.L j * P) + (1 - P) * (F.L j * P) := by rw [Matrix.add_mul]
        _ = P * F.L j * P + (1 - P) * F.L j * P := by simp [Matrix.mul_assoc]
        _ = P * F.L j * P := by rw [hblock j, add_zero]
    exact hleft.trans hright.symm
  obtain ⟨c, hP_scalar⟩ := hComm P hcommP
  exact not_isNontrivialProjection_of_eq_smul_one hP_nt hP_scalar

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
    (hGen : Algebra.adjoin ℂ
      (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) = ⊤) :
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
