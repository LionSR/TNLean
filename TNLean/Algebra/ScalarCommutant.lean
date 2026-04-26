/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block

/-!
# Scalar commutant lemma: center of M_n(R) = R·1

If a matrix `Z` commutes with every element of a spanning set of `M_n(R)`,
then `Z` is a scalar matrix. This is the algebraic fact that the center
of the full matrix algebra over a commutative ring is trivial.

## Main results

* `Matrix.isScalar_of_commute_span_eq_top`: if `Z` commutes with a spanning set,
  then `Z = scalar n c` for some `c`.
-/

open scoped Matrix

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

/-- Right multiplication by a block projection keeps the corresponding column block. -/
@[simp] private theorem mul_blockProjection_apply_col
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R)
    (j i : ι) (a : n i) (b : n j) :
    (X * blockProjection (n := n) (R := R) j) ⟨i, a⟩ ⟨j, b⟩ = X ⟨i, a⟩ ⟨j, b⟩ := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨j, b⟩]
  · simp [blockProjection]
  · rintro ⟨k, c⟩ _ hkc
    by_cases hkj : k = j
    · subst k
      have hcb : c ≠ b := by
        intro hcb
        apply hkc
        subst hcb
        rfl
      simp [blockProjection, hcb]
    · rw [show blockProjection (n := n) (R := R) j ⟨k, c⟩ ⟨j, b⟩ = 0 from by
        exact Matrix.blockDiagonal'_apply_ne _ c b hkj]
      simp
  · intro hmem
    simp at hmem

/-- Left multiplication by a block projection kills rows in all other blocks. -/
@[simp] private theorem blockProjection_mul_apply_of_ne
    [Fintype ι] [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    (X : Matrix ((i : ι) × n i) ((i : ι) × n i) R)
    {i j : ι} (hij : i ≠ j) (a : n i) (b : n j) :
    (blockProjection (n := n) (R := R) j * X) ⟨i, a⟩ ⟨j, b⟩ = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  rintro ⟨k, c⟩ _
  by_cases hik : i = k
  · subst k
    simp [blockProjection, hij]
  · rw [show blockProjection (n := n) (R := R) j ⟨i, a⟩ ⟨k, c⟩ = 0 from by
      exact Matrix.blockDiagonal'_apply_ne _ a c hik]
    simp

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
  simpa [hij] using hentry

end Semiring

end BlockDiagonal

end Matrix
