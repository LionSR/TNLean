/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Scalar commutant lemma: center of M_n(R) = R·1

If a matrix `Z` commutes with every element of a spanning set of `M_n(R)`,
then `Z` is a scalar matrix. This is the algebraic fact that the center
of the full matrix algebra over a commutative ring is trivial.

## Main results

* `Matrix.isScalar_of_commute_span_eq_top`: if `Z` commutes with a spanning set,
  then `Z = scalar n c` for some `c`.
* `Matrix.exists_eq_kronecker_one_of_intertwines_span_eq_top`: an intertwiner
  between two multiplicity amplifications has the form `F ⊗ 1`.
-/

open scoped Matrix Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommSemiring R]

/-- A matrix that commutes with a spanning set of `M_n(R)` lies in the center,
hence is a scalar matrix. -/
theorem isScalar_of_commute_span_eq_top
    (Z : Matrix n n R)
    {S : Set (Matrix n n R)}
    (hS : Submodule.span R S = ⊤)
    (hZ : ∀ M ∈ S, Z * M = M * Z) :
    ∃ c : R, Z = Matrix.scalar n c := by
  have hcomm_all : ∀ M : Matrix n n R, Z * M = M * Z := by
    intro M
    have hM : M ∈ Submodule.span R S := hS ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx => exact hZ x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
    | smul r x _ hx =>
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hx]
  have hcenter : Z ∈ Set.center (Matrix n n R) := by
    rw [Set.mem_center_iff]
    exact {
      comm := fun a => hcomm_all a
      left_assoc := fun b c => (mul_assoc Z b c).symm
      right_assoc := fun a b => mul_assoc a b Z
    }
  rw [center_eq_scalar_image] at hcenter
  obtain ⟨c, _, rfl⟩ := hcenter
  exact ⟨c, rfl⟩

/-- An intertwiner between two multiplicity amplifications of a spanning
family of square matrices acts trivially on the matrix factor.

Thus, if the matrices `A i` span the full matrix algebra and `C` intertwines
`1 ⊗ A i` on two possibly different multiplicity spaces, then
`C = F ⊗ 1` for a rectangular multiplicity matrix `F`.

This is the amplified commutant step used in arXiv:1511.08090,
Section ``Fusion tensors'', in the uniqueness paragraph preceding equation
`zippercondition2`, and Section ``Associativity and the pentagon equation'',
in the injectivity argument following equation `pentagon3`. -/
lemma exists_eq_kronecker_one_of_intertwines_span_eq_top
    {m₁ m₂ d ι : Type*}
    [Fintype m₁] [Fintype m₂] [Fintype d]
    [DecidableEq m₁] [DecidableEq m₂] [DecidableEq d]
    (A : ι → Matrix d d R)
    (C : Matrix (m₁ × d) (m₂ × d) R)
    (hA : Submodule.span R (Set.range A) = ⊤)
    (hC : ∀ i,
      ((1 : Matrix m₁ m₁ R) ⊗ₖ A i) * C =
        C * ((1 : Matrix m₂ m₂ R) ⊗ₖ A i)) :
    ∃ F : Matrix m₁ m₂ R, C = F ⊗ₖ (1 : Matrix d d R) := by
  classical
  let Z : m₁ → m₂ → Matrix d d R := fun a b x y => C (a, x) (b, y)
  have hZ (a : m₁) (b : m₂) (i : ι) : Z a b * A i = A i * Z a b := by
    ext x y
    have h := congrFun (congrFun (hC i) (a, x)) (b, y)
    simpa [Z, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type] using h.symm
  have hscalar (a : m₁) (b : m₂) : ∃ c : R, Z a b = Matrix.scalar d c := by
    apply Matrix.isScalar_of_commute_span_eq_top (Z a b) hA
    rintro M ⟨i, rfl⟩
    exact hZ a b i
  let F : Matrix m₁ m₂ R := fun a b => Classical.choose (hscalar a b)
  refine ⟨F, ?_⟩
  ext ⟨a, x⟩ ⟨b, y⟩
  have h := congrFun (congrFun (Classical.choose_spec (hscalar a b)) x) y
  simpa [Z, F, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply] using h

/-! ## Block-diagonal commutants -/

section BlockDiagonal

variable {ι : Type*} {n : ι → Type*}
variable [DecidableEq ι]

/-- The block-diagonal projection onto the block indexed by `k` in a dependent
block decomposition. -/
def blockProjection {R : Type*} [Zero R] [One R] [(i : ι) → DecidableEq (n i)]
    (k : ι) : Matrix ((i : ι) × n i) ((i : ι) × n i) R :=
  Matrix.blockDiagonal' fun i => if i = k then (1 : Matrix (n i) (n i) R) else 0

/-- A matrix on a dependent direct sum is block diagonal when it is a dependent
`Matrix.blockDiagonal'` of its diagonal blocks. -/
def IsBlockDiagonal' {R : Type*} [Zero R]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R) : Prop :=
  ∃ Xb : (i : ι) → Matrix (n i) (n i) R, X = Matrix.blockDiagonal' Xb

/-- A dependent block matrix is block diagonal iff all off-diagonal block entries vanish. -/
theorem isBlockDiagonal'_iff_offBlock_zero {R : Type*} [Zero R]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R) :
    IsBlockDiagonal' X ↔
      ∀ {i j : ι}, i ≠ j → ∀ (a : n i) (b : n j), X ⟨i, a⟩ ⟨j, b⟩ = 0 := by
  classical
  constructor
  · rintro ⟨Xb, rfl⟩ i j hij a b
    exact Matrix.blockDiagonal'_apply_ne Xb a b hij
  · intro hzero
    refine ⟨fun i a b => X ⟨i, a⟩ ⟨i, b⟩, ?_⟩
    ext x y
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
    · rw [Matrix.blockDiagonal'_apply_ne _ a b hij, hzero hij a b]

section Semiring

variable {R : Type*} [Semiring R]

/-- A block projection is idempotent. -/
theorem blockProjection_isIdempotentElem
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    (k : ι) : IsIdempotentElem (blockProjection (n := n) (R := R) k) := by
  rw [IsIdempotentElem, blockProjection, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  by_cases hik : i = k
  · simp [hik]
  · simp [hik]

/-- A complex block projection is Hermitian. -/
theorem blockProjection_isHermitian
    [(i : ι) → DecidableEq (n i)]
    (k : ι) :
    (blockProjection (n := n) (R := ℂ) k).IsHermitian := by
  simp only [Matrix.IsHermitian, blockProjection,
    Matrix.blockDiagonal'_conjTranspose]
  congr 1
  funext i
  by_cases hik : i = k
  · simp [hik]
  · simp [hik]

/-- Left multiplication by a block projection fixes entries whose row belongs
to the selected block. -/
@[simp] theorem blockProjection_mul_apply_same
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R)
    (k : ι) (a : n k) (j : (i : ι) × n i) :
    (blockProjection (n := n) (R := R) k * X) ⟨k, a⟩ j = X ⟨k, a⟩ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨k, a⟩]
  · simp [blockProjection]
  · rintro ⟨i, b⟩ _ hib
    by_cases hik : i = k
    · subst i
      have hba : b ≠ a := by
        intro hba
        apply hib
        subst b
        rfl
      simp [blockProjection, Ne.symm hba]
    · rw [show blockProjection (n := n) (R := R) k ⟨k, a⟩ ⟨i, b⟩ = 0 by
        exact Matrix.blockDiagonal'_apply_ne _ a b (Ne.symm hik)]
      simp
  · simp

/-- Left multiplication by a block projection kills entries whose row lies
outside the selected block. -/
theorem blockProjection_mul_apply_ne
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R)
    (k : ι) {i : ι} (hik : i ≠ k) (a : n i) (j : (i : ι) × n i) :
    (blockProjection (n := n) (R := R) k * X) ⟨i, a⟩ j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  rintro ⟨q, b⟩ _
  by_cases hiq : i = q
  · subst q
    simp [blockProjection, hik]
  · rw [show blockProjection (n := n) (R := R) k ⟨i, a⟩ ⟨q, b⟩ = 0 by
      exact Matrix.blockDiagonal'_apply_ne _ a b hiq]
    simp

/-- Right multiplication by a block projection fixes entries whose column
belongs to the selected block. -/
@[simp] theorem mul_blockProjection_apply_same
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R)
    (k : ι) (i : (i : ι) × n i) (b : n k) :
    (X * blockProjection (n := n) (R := R) k) i ⟨k, b⟩ = X i ⟨k, b⟩ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨k, b⟩]
  · simp [blockProjection]
  · rintro ⟨j, a⟩ _ haj
    by_cases hjk : j = k
    · subst j
      have hab : a ≠ b := by
        intro hab
        apply haj
        subst a
        rfl
      simp [blockProjection, hab]
    · rw [show blockProjection (n := n) (R := R) k ⟨j, a⟩ ⟨k, b⟩ = 0 by
        exact Matrix.blockDiagonal'_apply_ne _ a b hjk]
      simp
  · simp

/-- Right multiplication by a block projection kills entries whose column
lies outside the selected block. -/
theorem mul_blockProjection_apply_ne
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R)
    (k : ι) {j : ι} (hjk : j ≠ k) (i : (i : ι) × n i) (b : n j) :
    (X * blockProjection (n := n) (R := R) k) i ⟨j, b⟩ = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  rintro ⟨q, a⟩ _
  by_cases hqj : q = j
  · subst q
    simp [blockProjection, hjk]
  · rw [show blockProjection (n := n) (R := R) k ⟨q, a⟩ ⟨j, b⟩ = 0 by
      exact Matrix.blockDiagonal'_apply_ne _ a b hqj]
    simp

/-- A left-right block compression vanishes when all entries in the selected
block vanish. -/
theorem blockProjection_mul_mul_blockProjection_eq_zero
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R)
    (k l : ι) (hblock : ∀ (a : n k) (b : n l), X ⟨k, a⟩ ⟨l, b⟩ = 0) :
    blockProjection (n := n) (R := R) k * X *
        blockProjection (n := n) (R := R) l = 0 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hik : i = k
  · subst i
    by_cases hjl : j = l
    · subst j
      rw [mul_blockProjection_apply_same,
        blockProjection_mul_apply_same, hblock]
      rfl
    · exact mul_blockProjection_apply_ne _ _ hjl _ _
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [blockProjection_mul_apply_ne _ _ hik, zero_mul]

/-- If a matrix commutes with every block projection, then it is block diagonal.

This is the algebraic off-block-zero step needed in block-decomposition
arguments: after one proves that the relevant projections onto BNT sectors lie
in the commutant generated by the tensor words, commutation with those
projections forces the boundary matrix to have no off-diagonal block entries. -/
theorem isBlockDiagonal'_of_commutes_blockProjection
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    {X : Matrix ((i : ι) × n i) ((i : ι) × n i) R}
    (hComm : ∀ k : ι, X * blockProjection (n := n) (R := R) k =
      blockProjection (n := n) (R := R) k * X) :
    IsBlockDiagonal' X := by
  rw [isBlockDiagonal'_iff_offBlock_zero]
  intro i j hij a b
  have hentry := congrFun (congrFun (hComm j) ⟨i, a⟩) ⟨j, b⟩
  have hleft := mul_blockProjection_apply_same X j ⟨i, a⟩ b
  have hright := blockProjection_mul_apply_ne X j hij a ⟨j, b⟩
  simpa [hleft, hright] using hentry

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The commutant of a dependent direct sum of full right matrix factors
consists exactly of block-diagonal left-factor matrices. -/
theorem commutes_blockDiagonal'_one_kronecker_iff
    {m d : ι → Type*}
    [Fintype ι] [(j : ι) → Fintype (m j)] [(j : ι) → DecidableEq (m j)]
    [(j : ι) → Fintype (d j)] [(j : ι) → DecidableEq (d j)]
    (X : Matrix ((j : ι) × (m j × d j)) ((j : ι) × (m j × d j)) R) :
    (∀ B : (j : ι) → Matrix (d j) (d j) R,
      X * Matrix.blockDiagonal' (fun j =>
          (1 : Matrix (m j) (m j) R) ⊗ₖ B j) =
        Matrix.blockDiagonal' (fun j =>
          (1 : Matrix (m j) (m j) R) ⊗ₖ B j) * X) ↔
    ∃ C : (j : ι) → Matrix (m j) (m j) R,
      X = Matrix.blockDiagonal' (fun j =>
        C j ⊗ₖ (1 : Matrix (d j) (d j) R)) := by
  classical
  constructor
  · intro hComm
    have hProjection (k : ι) :
        Matrix.blockDiagonal' (fun j =>
            (1 : Matrix (m j) (m j) R) ⊗ₖ
              (Pi.single k (1 : Matrix (d k) (d k) R) :
                (i : ι) → Matrix (d i) (d i) R) j) =
          Matrix.blockProjection (n := fun j => m j × d j) (R := R) k := by
      change Matrix.blockDiagonal' _ =
        Matrix.blockDiagonal' (fun j =>
          if j = k then (1 : Matrix (m j × d j) (m j × d j) R) else 0)
      congr 1
      funext j
      by_cases hjk : j = k
      · subst j
        simp
      · simp [hjk]
    have hProjComm (k : ι) :
        X * Matrix.blockProjection (n := fun j => m j × d j) (R := R) k =
          Matrix.blockProjection (n := fun j => m j × d j) (R := R) k * X := by
      rw [← hProjection k]
      exact hComm (Pi.single k (1 : Matrix (d k) (d k) R))
    obtain ⟨Xb, hX⟩ :=
      Matrix.isBlockDiagonal'_of_commutes_blockProjection hProjComm
    have hLocalComm (k : ι) (B : Matrix (d k) (d k) R) :
        Xb k * ((1 : Matrix (m k) (m k) R) ⊗ₖ B) =
          ((1 : Matrix (m k) (m k) R) ⊗ₖ B) * Xb k := by
      have h := hComm
        (Pi.single k B : (j : ι) → Matrix (d j) (d j) R)
      rw [hX, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul] at h
      have hFamilies := Matrix.blockDiagonal'_injective h
      have hk := congrFun hFamilies k
      simpa using hk
    have hLocal (k : ι) :
        ∃ Ck : Matrix (m k) (m k) R,
          Xb k = Ck ⊗ₖ (1 : Matrix (d k) (d k) R) := by
      apply Matrix.exists_eq_kronecker_one_of_intertwines_span_eq_top
        (A := fun B : Matrix (d k) (d k) R => B)
        (C := Xb k)
      · rw [show Set.range (fun B : Matrix (d k) (d k) R => B) = Set.univ by
              ext B
              simp,
          Submodule.span_univ]
      · intro B
        exact (hLocalComm k B).symm
    choose C hC using hLocal
    refine ⟨C, ?_⟩
    rw [hX]
    congr 1
    funext k
    exact hC k
  · rintro ⟨C, rfl⟩ B
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext k
    simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

end CommSemiring

end BlockDiagonal

end Matrix
