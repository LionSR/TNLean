/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Module.Defs

/-!
# Integer combinations of fusion labels

Project construction for issue #8322: the additive group of integer combinations
and the bilinear product specified by natural structure constants. No Ring
instance is installed here. Associativity, duality and the universal extension
to ring homomorphisms are separate obligations.
-/

noncomputable section

namespace MPOTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
  simp [integerFusionEval, Finsupp.single_apply, ite_smul]

end MPOTensor
