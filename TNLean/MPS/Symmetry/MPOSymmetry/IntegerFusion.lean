/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.BigOperators

/-!
# Integer combinations of fusion labels

Project construction of the additive group of integer combinations
and the bilinear product specified by natural structure constants. Evaluation
preserves this product whenever the images satisfy the basis multiplication
identities. The Ring instance is constructed in `BasedRing.lean`.
-/

@[expose] public section

noncomputable section

namespace MPOTensor

variable {ι : Type*} [Fintype ι]

/-- Convolution of integer combinations with natural structure constants.
Project construction for the based-ring formulation of fusion rules. -/
def integerFusionMul (N : ι → ι → ι → ℕ) (u v : ι →₀ ℤ) : ι →₀ ℤ :=
  Finsupp.onFinset Finset.univ
    (fun c ↦ ∑ a, ∑ b, u a * v b * (N a b c : ℤ)) (by simp)

/-- The coefficient formula defining integer fusion convolution. -/
@[simp]
theorem integerFusionMul_apply (N : ι → ι → ι → ℕ) (u v : ι →₀ ℤ) (c : ι) :
    integerFusionMul N u v c = ∑ a, ∑ b, u a * v b * (N a b c : ℤ) :=
  rfl

/-- Convolution is additive in its left argument. -/
theorem integerFusionMul_add_left (N : ι → ι → ι → ℕ) (u v w : ι →₀ ℤ) :
    integerFusionMul N (u + v) w = integerFusionMul N u w + integerFusionMul N v w := by
  ext c
  simp [integerFusionMul_apply, add_mul, Finset.sum_add_distrib]

/-- Convolution is additive in its right argument. -/
theorem integerFusionMul_add_right (N : ι → ι → ι → ℕ) (u v w : ι →₀ ℤ) :
    integerFusionMul N u (v + w) = integerFusionMul N u v + integerFusionMul N u w := by
  ext c
  simp [integerFusionMul_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- Zero on the left gives zero. -/
@[simp]
theorem integerFusionMul_zero_left (N : ι → ι → ι → ℕ) (u : ι →₀ ℤ) :
    integerFusionMul N 0 u = 0 := by
  ext c
  simp

/-- Zero on the right gives zero. -/
@[simp]
theorem integerFusionMul_zero_right (N : ι → ι → ι → ℕ) (u : ι →₀ ℤ) :
    integerFusionMul N u 0 = 0 := by
  ext c
  simp

/-- Multiplication of singleton terms recovers the prescribed constants. -/
@[simp]
theorem integerFusionMul_single_apply (N : ι → ι → ι → ℕ)
    (a b c : ι) (m n : ℤ) :
    integerFusionMul N (Finsupp.single a m) (Finsupp.single b n) c =
      m * n * (N a b c : ℤ) := by
  classical
  simp [Finsupp.single_apply, ite_mul, mul_ite]

/-- Evaluate an integer combination in an additive commutative group.
This is the additive part of the proposed universal RingHom extension. -/
def integerFusionEval {A : Type*} [AddCommGroup A] (f : ι → A) : (ι →₀ ℤ) →+ A where
  toFun u := ∑ a, u a • f a
  map_zero' := by simp
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]

/-- Evaluation of a singleton is integer scalar multiplication. -/
@[simp]
theorem integerFusionEval_single {A : Type*} [AddCommGroup A]
    (f : ι → A) (a : ι) (m : ℤ) :
    integerFusionEval f (Finsupp.single a m) = m • f a := by
  classical
  simp [integerFusionEval, Finsupp.single_apply, ite_smul]

/-- Evaluation preserves convolution when the label images satisfy the fusion
product identities. The target ring may be noncommutative. Project result. -/
theorem integerFusionEval_mul {R : Type*} [Ring R]
    (N : ι → ι → ι → ℕ) (f : ι → R)
    (hf : ∀ a b, f a * f b = ∑ c, (N a b c : ℤ) • f c)
    (u v : ι →₀ ℤ) :
    integerFusionEval f (integerFusionMul N u v) =
      integerFusionEval f u * integerFusionEval f v := by
  change (∑ c, integerFusionMul N u v c • f c) =
    (∑ a, u a • f a) * (∑ b, v b • f b)
  simp_rw [integerFusionMul_apply, Finset.sum_smul]
  calc
    (∑ c, ∑ a, ∑ b, (u a * v b * (N a b c : ℤ)) • f c) =
        ∑ a, ∑ b, ∑ c, (u a * v b * (N a b c : ℤ)) • f c := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ b, (u a * v b) • (f a * f b) := by
      simp_rw [hf, Finset.smul_sum, smul_smul]
    _ = (∑ a, u a • f a) * (∑ b, v b • f b) := by
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
        smul_smul]

end MPOTensor
