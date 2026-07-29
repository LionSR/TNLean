/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PosSemidefSupport

/-!
# Joint column supports of finite matrix families

A finite family of rectangular complex matrices has a canonical joint column
support: the orthogonal projection onto the span of all columns in the family.
It is realized as the support projection of the Gram matrix obtained by
stacking those columns.

The projection absorbs every member of the family on the left. If the linear
span of the family is closed under conjugate transpose, it also absorbs every
member on the right. A nonzero family on a finite coordinate space has a
positive-dimensional isometric parametrization of its joint column support.

## Main definitions

* `Matrix.familyColumns`: all columns of a finite matrix family in one matrix.
* `Matrix.familyColumnGram`: the positive-semidefinite joint column Gram matrix.
* `Matrix.familySupportProj`: the orthogonal projection onto the joint column span.

## Main results

* `Matrix.familySupportProj_mul`: left absorption of every family member.
* `Matrix.mul_familySupportProj_of_conjTranspose_mem_span`: right absorption
  under closure of the family span under conjugate transpose.
* `Matrix.familySupportProj_mul_eq_self_of_forall_mul_eq`: minimality of the
  joint column support.
* `Matrix.exists_familySupport_isometry_of_exists_ne_zero`: a
  positive-dimensional isometric parametrization for a nonzero `Fin`-indexed
  family.
-/

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

variable {ι m n : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Stack all columns of a finite rectangular matrix family into one matrix. -/
noncomputable def familyColumns (A : ι → Matrix m n ℂ) :
    Matrix m (ι × n) ℂ :=
  fun i q ↦ A q.1 i q.2

/-- The positive-semidefinite Gram matrix of all columns in a finite matrix family. -/
noncomputable def familyColumnGram (A : ι → Matrix m n ℂ) : Matrix m m ℂ :=
  familyColumns A * (familyColumns A)ᴴ

omit [DecidableEq ι] [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The family column Gram matrix is the sum of the individual column Gram matrices. -/
theorem familyColumnGram_eq_sum (A : ι → Matrix m n ℂ) :
    familyColumnGram A = ∑ a, A a * (A a)ᴴ := by
  ext i j
  simp [familyColumnGram, familyColumns, Matrix.mul_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]

omit [DecidableEq ι] [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The joint column Gram matrix of a finite family is positive semidefinite. -/
theorem familyColumnGram_posSemidef [Finite m] (A : ι → Matrix m n ℂ) :
    (familyColumnGram A).PosSemidef :=
  posSemidef_self_mul_conjTranspose (familyColumns A)

/-- The orthogonal projection onto the joint column span of a finite matrix family. -/
noncomputable def familySupportProj (A : ι → Matrix m n ℂ) : Matrix m m ℂ :=
  (familyColumnGram_posSemidef A).supportProj

omit [DecidableEq ι] [DecidableEq n] in
/-- The joint column support of a finite matrix family is an orthogonal projection. -/
theorem isOrthogonalProjection_familySupportProj
    {p : ℕ} (A : ι → Matrix (Fin p) n ℂ) :
    IsOrthogonalProjection (familySupportProj A) :=
  (familyColumnGram_posSemidef A).isOrthogonalProjection_supportProj

omit [DecidableEq ι] [DecidableEq n] in
/-- The joint column support absorbs every member of the family on the left. -/
theorem familySupportProj_mul (A : ι → Matrix m n ℂ) (a : ι) :
    familySupportProj A * A a = A a := by
  have hColumns :
      familySupportProj A * familyColumns A = familyColumns A := by
    change (familyColumnGram_posSemidef A).supportProj * familyColumns A =
      familyColumns A
    have hProof :
        familyColumnGram_posSemidef A =
          posSemidef_self_mul_conjTranspose (familyColumns A) :=
      Subsingleton.elim _ _
    rw [hProof]
    exact Matrix.supportProj_mul_conjTranspose_mul_self (familyColumns A)
  ext i j
  simpa [familyColumns, Matrix.mul_apply] using
    congrFun (congrFun hColumns i) (a, j)

omit [DecidableEq ι] in
/-- If the family span is closed under conjugate transpose, its joint column
support absorbs every member on the right. -/
theorem mul_familySupportProj_of_conjTranspose_mem_span
    (A : ι → Matrix m m ℂ)
    (hstar : ∀ a, ∃ c : ι → ℂ, (A a)ᴴ = ∑ b, c b • A b) (a : ι) :
    A a * familySupportProj A = A a := by
  obtain ⟨c, hc⟩ := hstar a
  have hleft : familySupportProj A * (A a)ᴴ = (A a)ᴴ := by
    rw [hc, Matrix.mul_sum]
    simp_rw [Matrix.mul_smul, familySupportProj_mul]
  have hAdjoint := congrArg Matrix.conjTranspose hleft
  have hHermitian :
      (familySupportProj A)ᴴ = familySupportProj A :=
    (familyColumnGram_posSemidef A).supportProj_isHermitian.eq
  simpa [Matrix.conjTranspose_mul, hHermitian] using hAdjoint

omit [DecidableEq ι] [DecidableEq n] in
/-- Every matrix that fixes all family members on the left also fixes their
joint column support on the left. -/
theorem familySupportProj_mul_eq_self_of_forall_mul_eq
    (A : ι → Matrix m n ℂ) (P : Matrix m m ℂ)
    (hP : ∀ a, P * A a = A a) :
    P * familySupportProj A = familySupportProj A := by
  have hGram : P * familyColumnGram A = familyColumnGram A := by
    rw [familyColumnGram_eq_sum, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Matrix.mul_assoc, hP]
  obtain ⟨W, hW⟩ :=
    (familyColumnGram_posSemidef A).exists_supportProj_eq_mul
  change P * (familyColumnGram_posSemidef A).supportProj =
    (familyColumnGram_posSemidef A).supportProj
  rw [hW, ← Matrix.mul_assoc, hGram]

omit [DecidableEq ι] [DecidableEq n] in
/-- A finite matrix family with a nonzero member has nonzero joint column support. -/
theorem familySupportProj_ne_zero_of_exists_ne_zero
    (A : ι → Matrix m n ℂ) (hA : ∃ a, A a ≠ 0) :
    familySupportProj A ≠ 0 := by
  obtain ⟨a, ha⟩ := hA
  intro hzero
  apply ha
  have hAbsorb := familySupportProj_mul A a
  rw [hzero, Matrix.zero_mul] at hAbsorb
  exact hAbsorb.symm

/-- A nonzero `Fin`-indexed matrix family has a positive-dimensional isometric
parametrization of its joint column support. -/
theorem exists_familySupport_isometry_of_exists_ne_zero
    {r p q : ℕ} (A : Fin r → Matrix (Fin p) (Fin q) ℂ)
    (hA : ∃ a, A a ≠ 0) :
    ∃ (s : ℕ) (V : Matrix (Fin p) (Fin s) ℂ),
      0 < s ∧ Vᴴ * V = 1 ∧ V * Vᴴ = familySupportProj A := by
  obtain ⟨s, V, hIsometry, hRange⟩ :=
    (isOrthogonalProjection_familySupportProj A).exists_range_isometry
  have hs : 0 < s := by
    apply Nat.pos_of_ne_zero
    intro hs
    subst s
    have hVzero : V = 0 := Subsingleton.elim _ _
    apply familySupportProj_ne_zero_of_exists_ne_zero A hA
    rw [← hRange, hVzero, Matrix.zero_mul]
  exact ⟨s, V, hs, hIsometry, hRange⟩

end Matrix
