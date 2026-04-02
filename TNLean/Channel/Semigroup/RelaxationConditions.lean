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

private theorem lindblad_block_of_generatorPreservesCompression
    {P : Mat} (hP : IsOrthogonalProjection P) (F : LindbladForm D)
    (hgen : GeneratorPreservesCompression F.toLinearMap P) :
    ∀ j : Fin F.r, (1 - P) * F.L j * P = 0 := by
  have hPP : P * P = P := hP.2
  have hP_herm : Pᴴ = P := hP.1
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hLP_compress : P * F.toLinearMap P * P = F.toLinearMap P := by
    have h1 := hgen 1
    simp only [mul_one] at h1
    rwa [hPP] at h1
  have hQ_LP : (1 - P) * F.toLinearMap P = 0 := by
    calc
      (1 - P) * F.toLinearMap P = (1 - P) * (P * F.toLinearMap P * P) := by
        rw [hLP_compress]
      _ = ((1 - P) * P) * (F.toLinearMap P * P) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQP, Matrix.zero_mul]
  set κ : Mat := F.toGeneratorDecomp.κ
  have hQ_phi_eq_Q_kappa :
      (1 - P) * (∑ j : Fin F.r, F.L j * P * (F.L j)ᴴ) = (1 - P) * (κ * P) := by
    rw [F.toLinearMap_eq_generatorDecomp] at hQ_LP
    simp only [GeneratorDecomp.toLinearMap_apply] at hQ_LP
    rw [Matrix.mul_sub, Matrix.mul_sub] at hQ_LP
    have hQPκ : (1 - P) * (P * F.toGeneratorDecomp.κᴴ) = 0 := by
      rw [← Matrix.mul_assoc, hQP, Matrix.zero_mul]
    rw [hQPκ, sub_zero] at hQ_LP
    change (1 - P) * (∑ j : Fin F.r, F.L j * P * (F.L j)ᴴ) = (1 - P) * (κ * P)
    exact sub_eq_zero.mp hQ_LP
  have hsum_zero :
      ∑ j : Fin F.r, ((1 - P) * F.L j * P) * ((1 - P) * F.L j * P)ᴴ = 0 := by
    have hPP' : P * (1 - P) = 0 := by
      rw [mul_sub, mul_one, hPP, sub_self]
    suffices hLHS :
        ∑ j : Fin F.r, ((1 - P) * F.L j * P) * ((1 - P) * F.L j * P)ᴴ =
        (1 - P) * (∑ j : Fin F.r, F.L j * P * (F.L j)ᴴ) * (1 - P) by
      rw [hLHS, hQ_phi_eq_Q_kappa]
      simp [Matrix.mul_assoc, hPP']
    rw [mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    calc
      ((1 - P) * F.L j * P) * ((1 - P) * F.L j * P)ᴴ
          = (1 - P) * (F.L j * (P * (P * ((F.L j)ᴴ * (1 - P))))) := by
              simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
                Matrix.conjTranspose_one, hP_herm, Matrix.mul_assoc]
      _ = (1 - P) * (F.L j * (P * ((F.L j)ᴴ * (1 - P)))) := by
              congr 2
              rw [← Matrix.mul_assoc, hPP]
      _ = (1 - P) * (F.L j * P * (F.L j)ᴴ) * (1 - P) := by
              simp [Matrix.mul_assoc]
  exact eq_zero_of_sum_mul_conjTranspose_eq_zero _ hsum_zero

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
