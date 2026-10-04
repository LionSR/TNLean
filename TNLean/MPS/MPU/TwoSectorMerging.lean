/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Module
import TNLean.Algebra.ComplexSqrt

/-!
# Coherent merging of two orthogonal sectors

For an orthogonal projection `P`, the block matrix
`E = [[P, 1 - P], [1 - P, P]]` records the two sectors in a qubit and erases
that record after sector-preserving operations. The central identity is
`twoSectorEncoder_merge_kronecker`: starting in the zero-flag sector, the
encoder, two controlled local operations, and encoder again implement
`X₀ ⊗ P + X₁ ⊗ (1 - P)`, with the flag returned to zero.

For a Hermitian involution `R`, the projection is `(1 + R) / 2` and the
encoder is a Hadamard, controlled `R`, and another Hadamard. The final
factor can be combined with sector erasure by
`diagonal_mul_twoSectorEncoder_of_mem_unitaryGroup`.

These are the algebraic identities in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The module does not assert
the structural decomposition of every Schmidt-rank-two unitary or a circuit
complexity bound. Self-adjointness and involutivity of `R` are explicit
hypotheses; unitarity of two factors alone would not imply them.
-/

open scoped Matrix Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The block operator that records the complementary sectors `P` and `1 - P`
in a flag. Source: the sector encoder in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def twoSectorEncoder (P : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks P (1 - P) (1 - P) P

/-- The sector encoder is an involution whenever its sector matrix is idempotent. -/
theorem twoSectorEncoder_mul_self (P : Matrix n n ℂ) (hP : IsIdempotentElem P) :
    twoSectorEncoder P * twoSectorEncoder P = 1 := by
  unfold twoSectorEncoder
  rw [fromBlocks_multiply]
  simp [hP.eq, hP.one_sub.eq, hP.mul_one_sub_self, hP.one_sub_mul_self]

omit [Fintype n] in
/-- Self-adjoint sector matrices give self-adjoint encoders. -/
theorem twoSectorEncoder_conjTranspose (P : Matrix n n ℂ) (hP : IsSelfAdjoint P) :
    (twoSectorEncoder P)ᴴ = twoSectorEncoder P := by
  simpa only [twoSectorEncoder, fromBlocks_conjTranspose, conjTranspose_sub,
    conjTranspose_one, star_eq_conjTranspose] using
    congrArg (fun Q : Matrix n n ℂ => fromBlocks Q (1 - Q) (1 - Q) Q) hP.star_eq

/-- Recording the sectors of an orthogonal projection is unitary. -/
theorem twoSectorEncoder_mem_unitaryGroup (P : Matrix n n ℂ) (hP : IsStarProjection P) :
    twoSectorEncoder P ∈ unitaryGroup (n ⊕ n) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose,
    twoSectorEncoder_conjTranspose P hP.isSelfAdjoint,
    twoSectorEncoder_mul_self P hP.isIdempotentElem]

/-- The projection onto data with its flag in the zero state. -/
def zeroFlagProjection : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 1 0 0 0

/-- Operations preserving both sectors can be applied under the recorded flag,
after which the record is erased. The zero lower-left block states that the
final flag is zero for every input in the zero-flag sector.
Source: the coherent merging identity in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem twoSectorEncoder_merge (P X₀ X₁ : Matrix n n ℂ) (hP : IsIdempotentElem P)
    (h₀ : Commute P X₀) (h₁ : Commute P X₁) :
    twoSectorEncoder P * fromBlocks X₀ 0 0 X₁ * twoSectorEncoder P * zeroFlagProjection =
      fromBlocks (X₀ * P + X₁ * (1 - P)) 0 0 0 := by
  simp only [twoSectorEncoder, zeroFlagProjection, fromBlocks_multiply,
    mul_zero, add_zero, zero_add, mul_one]
  rw [h₀.eq, ((Commute.one_left X₁).sub_left h₁).eq,
    ((Commute.one_left X₀).sub_left h₀).eq, h₁.eq]
  simp only [mul_assoc, hP.eq, hP.one_sub.eq, hP.one_sub_mul_self,
    hP.mul_one_sub_self, mul_zero, add_zero]

/-- A Hermitian involution defines its positive eigenspace projection as
`(1 + R) / 2`. The complementary projection is provided by
`IsStarProjection.one_sub`. -/
theorem isStarProjection_half_one_add (R : Matrix n n ℂ)
    (hR : IsSelfAdjoint R) (hRR : R * R = 1) :
    IsStarProjection ((1 / 2 : ℂ) • (1 + R)) := by
  rw [isStarProjection_iff']
  constructor
  · simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
      one_mul, mul_one, hRR]
    module
  · simp [star_smul, hR.star_eq]

/-- A Hadamard on the flag, with identity action on the data. -/
noncomputable def flagHadamard : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Complex.invSqrtTwo • fromBlocks 1 1 1 (-1)

/-- Conjugation of a two-block diagonal operator by the flag Hadamard. -/
theorem flagHadamard_mul_diagonal_mul (A B : Matrix n n ℂ) :
    flagHadamard * fromBlocks A 0 0 B * flagHadamard =
      (1 / 2 : ℂ) • fromBlocks (A + B) (A - B) (A - B) (A + B) := by
  simp only [flagHadamard, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.invSqrtTwo_mul_self, fromBlocks_multiply, one_mul, mul_one,
    mul_zero, add_zero, zero_add, neg_mul, mul_neg, smul_neg, neg_neg,
    fromBlocks_smul, sub_eq_add_neg, one_div]
  simp only [smul_add, smul_neg]

/-- Hadamard, controlled `R`, and Hadamard again give the sector encoder.
For a Hermitian involution, `isStarProjection_half_one_add` makes this a
unitary recording of its positive and negative eigenspaces.
Source: `E_c` in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem flagHadamard_mul_controlled_mul (R : Matrix n n ℂ) :
    flagHadamard * fromBlocks 1 0 0 R * flagHadamard =
      twoSectorEncoder ((1 / 2 : ℂ) • (1 + R)) := by
  rw [flagHadamard_mul_diagonal_mul]
  simp only [twoSectorEncoder, fromBlocks_smul]
  congr 1 <;> module

/-- A common final factor combines with the sector encoder into two controlled
factors between Hadamards. -/
theorem diagonal_mul_twoSectorEncoder (B R : Matrix n n ℂ) :
    fromBlocks B 0 0 B * twoSectorEncoder ((1 / 2 : ℂ) • (1 + R)) =
      flagHadamard * fromBlocks B 0 0 (B * R) * flagHadamard := by
  rw [flagHadamard_mul_diagonal_mul]
  simp only [twoSectorEncoder, fromBlocks_multiply, zero_mul,
    add_zero, mul_smul_comm, mul_add, mul_sub, mul_one, fromBlocks_smul]
  congr 1 <;> module

/-- For a unitary common factor `B` and relative operator `Bᴴ * C`, sector
erasure and the final factor use the two blocks `B` and `C`.
This is the cancellation that reduces the seven-call construction to six
child calls in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The equality itself does
not require the relative operator to be a Hermitian involution. -/
theorem diagonal_mul_twoSectorEncoder_of_mem_unitaryGroup (B C : Matrix n n ℂ)
    (hB : B ∈ unitaryGroup n ℂ) :
    fromBlocks B 0 0 B * twoSectorEncoder ((1 / 2 : ℂ) • (1 + Bᴴ * C)) =
      flagHadamard * fromBlocks B 0 0 C * flagHadamard := by
  have hBC : B * (Bᴴ * C) = C := by
    simp only [← mul_assoc, ← star_eq_conjTranspose, hB.2, one_mul]
  simpa only [hBC] using diagonal_mul_twoSectorEncoder B (Bᴴ * C)

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Operators on the two distinct tensor factors commute. -/
theorem one_kronecker_commute_kronecker_one (P : Matrix n n ℂ) (X : Matrix m m ℂ) :
    Commute ((1 : Matrix m m ℂ) ⊗ₖ P) (X ⊗ₖ (1 : Matrix n n ℂ)) := by
  change (1 ⊗ₖ P) * (X ⊗ₖ 1) = (X ⊗ₖ 1) * (1 ⊗ₖ P)
  simp only [← mul_kronecker_mul, one_mul, mul_one]

/-- Coherently record a sector on the second factor, apply the two corresponding
operations on the first factor, and erase the flag. The resulting physical
operator is `X₀ ⊗ P + X₁ ⊗ (1 - P)` and the auxiliary flag is zero.
Source: the two-sector merging step in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem twoSectorEncoder_merge_kronecker (P : Matrix n n ℂ) (X₀ X₁ : Matrix m m ℂ)
    (hP : IsIdempotentElem P) :
    twoSectorEncoder ((1 : Matrix m m ℂ) ⊗ₖ P) *
      fromBlocks (X₀ ⊗ₖ (1 : Matrix n n ℂ)) 0 0 (X₁ ⊗ₖ (1 : Matrix n n ℂ)) *
      twoSectorEncoder ((1 : Matrix m m ℂ) ⊗ₖ P) * zeroFlagProjection =
        fromBlocks (X₀ ⊗ₖ P + X₁ ⊗ₖ (1 - P)) 0 0 0 := by
  have hIP : IsIdempotentElem ((1 : Matrix m m ℂ) ⊗ₖ P) := by
    change (1 ⊗ₖ P) * (1 ⊗ₖ P) = 1 ⊗ₖ P
    simp only [← mul_kronecker_mul, hP.eq, one_mul]
  have hcompl : (1 : Matrix m m ℂ) ⊗ₖ (1 - P) = 1 - (1 : Matrix m m ℂ) ⊗ₖ P := by
    rw [← one_kronecker_one (m := m) (n := n)]
    ext i j; simp only [kroneckerMap_apply, sub_apply, mul_sub]
  have h := twoSectorEncoder_merge ((1 : Matrix m m ℂ) ⊗ₖ P)
    (X₀ ⊗ₖ (1 : Matrix n n ℂ)) (X₁ ⊗ₖ (1 : Matrix n n ℂ)) hIP
    (one_kronecker_commute_kronecker_one P X₀)
    (one_kronecker_commute_kronecker_one P X₁)
  simpa only [← hcompl, ← mul_kronecker_mul, mul_one, one_mul] using h

end Matrix
