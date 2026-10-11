/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorComap
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorToolkit

/-!
# Order-two families with a bond-two generator

A representation of `ℤ₂` by matrix product operators whose identity is represented by a
bond-one tensor `E` and whose generator is represented by a bond-two tensor `A`. When stacking
`E` with `E` gives `E`, stacking `E` with `A` on either side gives `A`, and `(V, W)` reduces the
stacked square of `A` onto `E`, the fusion tensors are the identity whenever a factor is the
identity and `(V, W)` for two generators. With these fusion tensors `ω(g,1,g) = 1`, so the
gauge-invariant product `ω(g,1,g) ω(g,g,g)` is the single value `ω(g,g,g)`, and the two fusion
trees of three generators are `V ⊗ 1` and `1 ⊗ V`.

## Main definitions

* `MPOTensor.GroupFamily.orderTwoFamily`: the `ℤ₂`-indexed family `1 ↦ E`, `g ↦ A`.
* `MPOTensor.GroupFamily.FusionData.orderTwo`: its fusion tensors.

## Main results

* `MPOTensor.GroupFamily.FusionData.orderTwo_leftV_gen_gen_gen`,
  `MPOTensor.GroupFamily.FusionData.orderTwo_rightV_gen_gen_gen`: the two fusion trees.
* `MPOTensor.GroupFamily.FusionData.cyclicInvariant_orderTwo`: the cyclic invariant at the
  generator is `ω(g,g,g)`.
* `MPOTensor.GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq_orderTwo`: for a
  family whose restriction along `f : ℤ₂ →* G` is `1 ↦ E`, `g ↦ A`, the cyclic invariant at
  `f g` is the associator scalar of the fusion tensors `FusionData.orderTwo`.

Source: arXiv:2502.20257, equations `eq:fusion_1` and `eq:fusion_2`, `main.tex`
lines 1403--1497, for the fusion tensors, and the display preceding `eq:3-cocycle`,
lines 1506--1535, for the anomaly three-cochain.
-/

noncomputable section

open scoped Matrix Kronecker

namespace MPOTensor.GroupFamily

variable {d : ℕ}

/-- The generator of `ℤ₂`, written multiplicatively. Naming it keeps rewriting by the lemmas
below independent of the instance path through which a numeral of `ZMod 2` is elaborated. -/
def orderTwoGen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

/-- The generator of `ℤ₂` has order two. -/
theorem orderTwoGen_pow_two : orderTwoGen ^ 2 = 1 := by decide

/-- The bond dimension attached to a label of `ℤ₂`: one for the identity and two for the
generator. -/
def orderTwoBondDim (a : Fin 2) : ℕ := if a = 0 then 1 else 2

/-- The tensor attached to a label of `ℤ₂`: `E` for the identity and `A` for the generator. -/
def orderTwoLabelTensor (E : MPOTensor d 1) (A : MPOTensor d 2) :
    (a : Fin 2) → MPOTensor d (orderTwoBondDim a)
  | ⟨0, _⟩ => E
  | ⟨1, _⟩ => A
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- The `ℤ₂`-indexed family `1 ↦ E`, `g ↦ A`, with a bond-one tensor for the identity and a
bond-two tensor for the generator. -/
def orderTwoFamily (E : MPOTensor d 1) (A : MPOTensor d 2) :
    GroupFamily (Multiplicative (ZMod 2)) d where
  bondDim x := orderTwoBondDim x.toAdd
  bondDim_pos x := by unfold orderTwoBondDim; split <;> norm_num
  tensor x := orderTwoLabelTensor E A x.toAdd

/-- The left fusion tensors attached to a pair of labels: the identity when a label is the
identity, and `V` for two generators. -/
def orderTwoLabelV (V : Matrix (Fin 1) (Fin (2 * 2)) ℂ) : (a b : Fin 2) →
    Matrix (Fin (orderTwoBondDim (a + b))) (Fin (orderTwoBondDim a * orderTwoBondDim b)) ℂ
  | ⟨0, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨1, _⟩ => V
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 2, h⟩ => absurd h (by omega)

/-- The right fusion tensors attached to a pair of labels: the identity when a label is the
identity, and `W` for two generators. -/
def orderTwoLabelW (W : Matrix (Fin (2 * 2)) (Fin 1) ℂ) : (a b : Fin 2) →
    Matrix (Fin (orderTwoBondDim a * orderTwoBondDim b)) (Fin (orderTwoBondDim (a + b))) ℂ
  | ⟨0, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨1, _⟩ => W
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 2, h⟩ => absurd h (by omega)

/-- **Fusion tensors of a `ℤ₂`-indexed family with a bond-two generator**: the identity
whenever a factor is the identity, which requires that stacking `E` with `E` gives `E` and that
stacking `E` with `A` on either side gives `A`, and a reduction `(V, W)` of the stacked square
of `A` onto `E` for two generators.

Source: arXiv:2502.20257, equations `eq:fusion_1` and `eq:fusion_2`, `main.tex`
lines 1403--1497. -/
def FusionData.orderTwo (E : MPOTensor d 1) (A : MPOTensor d 2)
    (V : Matrix (Fin 1) (Fin (2 * 2)) ℂ) (W : Matrix (Fin (2 * 2)) (Fin 1) ℂ)
    (hEE : (mulTensor E E).toMPSTensor = E.toMPSTensor)
    (hEA : (mulTensor E A).toMPSTensor = A.toMPSTensor)
    (hAE : (mulTensor A E).toMPSTensor = A.toMPSTensor)
    (hAA : MPSTensor.IsReduction (mulTensor A A).toMPSTensor E.toMPSTensor V W) :
    (orderTwoFamily E A).FusionData where
  V x y := orderTwoLabelV V x.toAdd y.toAdd
  W x y := orderTwoLabelW W x.toAdd y.toAdd
  isReduction := by
    refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_)
    · exact MPSTensor.isReduction_one_one_of_eq hEE
    · exact MPSTensor.isReduction_one_one_of_eq hEA
    · exact MPSTensor.isReduction_one_one_of_eq hAE
    · exact hAA

namespace FusionData

variable {E : MPOTensor d 1} {A : MPOTensor d 2} {V : Matrix (Fin 1) (Fin (2 * 2)) ℂ}
  {W : Matrix (Fin (2 * 2)) (Fin 1) ℂ}
  {hEE : (mulTensor E E).toMPSTensor = E.toMPSTensor}
  {hEA : (mulTensor E A).toMPSTensor = A.toMPSTensor}
  {hAE : (mulTensor A E).toMPSTensor = A.toMPSTensor}
  {hAA : MPSTensor.IsReduction (mulTensor A A).toMPSTensor E.toMPSTensor V W}

private theorem assocInv_two_two_two :
    mulTensorAssocInvMatrix 2 2 2 = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  rw [mulTensorAssocInvMatrix_eq_finCongr]
  exact finCongr_toMatrix_eq_one _

private theorem assocInv_two_one_two :
    mulTensorAssocInvMatrix 2 1 2 = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [mulTensorAssocInvMatrix_eq_finCongr]
  exact finCongr_toMatrix_eq_one _

private theorem castMat_gen_gen_gen (E : MPOTensor d 1) (A : MPOTensor d 2) :
    (orderTwoFamily E A).castMat
        (mul_assoc orderTwoGen orderTwoGen orderTwoGen).symm =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [GroupFamily.castMat_eq_finCongr]
  exact finCongr_toMatrix_eq_one _

private theorem castMat_gen_one_gen (E : MPOTensor d 1) (A : MPOTensor d 2) :
    (orderTwoFamily E A).castMat
        (mul_assoc orderTwoGen 1 orderTwoGen).symm =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [GroupFamily.castMat_eq_finCongr]
  exact finCongr_toMatrix_eq_one _

/-- The tree fusing the first two of three generators first is `V ⊗ 1`. -/
theorem orderTwo_leftV_gen_gen_gen :
    (orderTwo E A V W hEE hEA hAE hAA).leftV orderTwoGen orderTwoGen orderTwoGen =
      kronId V 2 := by
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) * kronId V 2 = _
  rw [Matrix.one_mul]

/-- The tree fusing the last two of three generators first is `1 ⊗ V`. -/
theorem orderTwo_rightV_gen_gen_gen :
    (orderTwo E A V W hEE hEA hAE hAA).rightV orderTwoGen orderTwoGen orderTwoGen =
      idKron 2 V := by
  rw [GroupFamily.FusionData.rightV, castMat_gen_gen_gen]
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) *
      idKron 2 V * mulTensorAssocInvMatrix 2 2 2) = _
  rw [assocInv_two_two_two, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

/-- `ω(g,1,g) = 1` for the fusion tensors of `FusionData.orderTwo`, which are trivial whenever
a factor is the identity: both fusion trees are `V`. -/
theorem orderTwo_omega_gen_one_gen (hF : (orderTwoFamily E A).IsNormalRepresentation) :
    (orderTwo E A V W hEE hEA hAE hAA).omega orderTwoGen 1 orderTwoGen = 1 := by
  refine GroupFamily.FusionData.omega_eq_one_of_leftV_eq_rightV hF ?_
  rw [GroupFamily.FusionData.rightV, castMat_gen_one_gen]
  change V * kronId (1 : Matrix (Fin 2) (Fin 2) ℂ) 2 = (1 : Matrix (Fin 1) (Fin 1) ℂ) *
    (V * idKron 2 (1 : Matrix (Fin 2) (Fin 2) ℂ) * mulTensorAssocInvMatrix 2 1 2)
  rw [kronId_one, idKron_one, assocInv_two_one_two, Matrix.mul_one, Matrix.mul_one,
    Matrix.one_mul]

/-- The cyclic invariant of `FusionData.orderTwo` at the generator is `ω(g,g,g)`. -/
theorem cyclicInvariant_orderTwo (hF : (orderTwoFamily E A).IsNormalRepresentation) :
    TNLean.Algebra.ScalarThreeCochain.cyclicInvariant (orderTwo E A V W hEE hEA hAE hAA).omega
        orderTwoGen 2 =
      (orderTwo E A V W hEE hEA hAE hAA).omega orderTwoGen orderTwoGen orderTwoGen := by
  simp only [TNLean.Algebra.ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul, pow_zero, pow_one, orderTwo_omega_gen_one_gen hF]

/-- The cyclic invariant of `FusionData.orderTwo` at the generator is `z` when the two fusion
trees of three generators are dressed proportional with scalar `z`. -/
theorem cyclicInvariant_orderTwo_of_isAssociator
    (hF : (orderTwoFamily E A).IsNormalRepresentation) {z : ℂ}
    (h : (orderTwo E A V W hEE hEA hAE hAA).IsAssociator orderTwoGen orderTwoGen orderTwoGen
      z) :
    ((TNLean.Algebra.ScalarThreeCochain.cyclicInvariant
      (orderTwo E A V W hEE hEA hAE hAA).omega orderTwoGen 2 : ℂˣ) : ℂ) = z := by
  rw [cyclicInvariant_orderTwo hF]
  exact (GroupFamily.FusionData.eq_omega_of_isAssociator hF h).symm

/-- **Cyclic invariants from an order-two restriction**: if the restriction of a normal
representation `F` along `f : ℤ₂ →* G` is the family `1 ↦ E`, `g ↦ A`, then for every choice of
fusion tensors of `F` the cyclic invariant `ω(f g, e, f g) ω(f g, f g, f g)` is the scalar by
which the two fusion trees of three generators of `FusionData.orderTwo` differ.

Source: arXiv:2502.20257, `eq:omegagauge` and the sentence following it, `main.tex`
lines 1541--1546, with the display preceding `eq:3-cocycle`, lines 1506--1535. -/
theorem cyclicInvariant_omega_map_of_comap_eq_orderTwo {G : Type} [Group G]
    {F : GroupFamily G d} (fd : F.FusionData) (hF : F.IsNormalRepresentation)
    (f : Multiplicative (ZMod 2) →* G) (hc : F.comap f = orderTwoFamily E A) {z : ℂ}
    (h : (orderTwo E A V W hEE hEA hAE hAA).IsAssociator orderTwoGen orderTwoGen orderTwoGen
      z) :
    ((TNLean.Algebra.ScalarThreeCochain.cyclicInvariant fd.omega (f orderTwoGen) 2 : ℂˣ) :
      ℂ) = z := by
  rw [GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq fd f hF hc
    (orderTwo E A V W hEE hEA hAE hAA) orderTwoGen_pow_two]
  exact cyclicInvariant_orderTwo_of_isAssociator (hc ▸ hF.comap f) h

end FusionData

end MPOTensor.GroupFamily
