/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.CZXDecoratedFusion
import TNLean.MPS.MPDO.StackedLayers
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# The anomaly class of the decorated CZX representation

The decorated CZX matrix product unitary `U` of Garre-Rubio and Schuch
(arXiv:2405.00439, Section III.D) squares to the identity, so together with the
bond-one identity tensor it represents the group `ℤ₂`.  This file computes the
anomaly three-cochain `ω` of this representation, in the sense of
arXiv:2502.20257 (display preceding `eq:3-cocycle`), and shows that its
cohomology class is nontrivial for every choice of fusion tensors.

For the fusion tensors that are trivial whenever a factor is the identity and are
the printed pair `(V̂, V)` of arXiv:2405.00439, lines 1225--1244, for `(g, g)`,
the two fusion trees of the triple product of `g` agree up to the sign `-1`
against every nonempty word, so `ω(g,g,g) = -1`, while `ω(g,1,g) = 1`.  The
gauge-invariant product `ω(g,1,g) ω(g,g,g)` is therefore `-1`, for every choice
of fusion tensors.

## Main definitions

* `CZXCompression.czxFamily`: the `ℤ₂`-indexed family `1 ↦ δ`, `g ↦ U`.
* `CZXCompression.czxFusionData`: the fusion tensors described above.

## Main results

* `CZXCompression.czxFamily_isNormalRepresentation`
* `CZXCompression.czxFusionData_omega_gen_gen_gen`: `ω(g,g,g) = -1`.
* `CZXCompression.cyclicInvariant_omega_czx`: `ω(g,1,g) ω(g,g,g) = -1` for every
  choice of fusion tensors.
* `CZXCompression.not_isTrivialGaugeClass_omega_czx`: the anomaly class is
  nontrivial for every choice of fusion tensors.
-/

noncomputable section

open scoped Matrix Kronecker
open TNLean.Algebra MPOTensor MPSTensor

namespace CZXCompression

/-! ### The family -/

/-- The bond dimension attached to a label of `ℤ₂`: one for the identity and two
for the generator. -/
def czxLabelBondDim (a : Fin 2) : ℕ := if a = 0 then 1 else 2

/-- The tensor attached to a label of `ℤ₂`: the bond-one identity tensor for the
identity and the decorated CZX tensor for the generator. -/
def czxLabelTensor : (a : Fin 2) → MPOTensor 2 (czxLabelBondDim a)
  | ⟨0, _⟩ => MPOTensor.idTensor 2
  | ⟨1, _⟩ => czxDecoratedTensor
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- **The decorated CZX representation of `ℤ₂`**: the identity is represented by
the bond-one identity tensor and the generator by the decorated CZX tensor.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 412--428 (an MPU
of order two) and lines 1128--1180 (the decorated CZX tensor). -/
def czxFamily : GroupFamily (Multiplicative (Fin 2)) 2 where
  bondDim x := czxLabelBondDim x.toAdd
  bondDim_pos x := by unfold czxLabelBondDim; split <;> norm_num
  tensor x := czxLabelTensor x.toAdd

/-- The generator of `ℤ₂`, written multiplicatively. -/
def czxGen : Multiplicative (Fin 2) := Multiplicative.ofAdd 1

theorem czxGen_pow_two : czxGen ^ 2 = 1 := by decide

private theorem forall_z2 {P : Multiplicative (Fin 2) → Prop}
    (h0 : P (Multiplicative.ofAdd 0)) (h1 : P (Multiplicative.ofAdd 1)) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1]

/-! ### The bond-one identity tensor -/

theorem idTensor_toMPSTensor (a : Fin 4) :
    (MPOTensor.idTensor 2).toMPSTensor a = pairDelta a • 1 := by
  fin_cases a <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [MPOTensor.idTensor, MPOTensor.toMPSTensor, pairDelta, pairDeltaInt] <;> rfl

theorem evalWord_idTensor_toMPSTensor (w : List (Fin 4)) :
    Kraus.evalWord (MPOTensor.idTensor 2).toMPSTensor w = (w.map pairDelta).prod • 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [Kraus.evalWord_cons, ih, idTensor_toMPSTensor, smul_mul_smul_comm, Matrix.one_mul]
      simp

theorem idTensor_isNormal : Kraus.IsNormal (MPOTensor.idTensor 2).toMPSTensor := by
  refine ⟨1, one_pos, Submodule.eq_top_of_forall_single_mem _ fun i j ↦ ?_⟩
  have hij : Matrix.single i j (1 : ℂ) = 1 := by
    ext r c
    fin_cases i; fin_cases j; fin_cases r; fin_cases c
    simp
  rw [hij]
  refine Submodule.subset_span ⟨fun _ ↦ 0, ?_⟩
  simp [idTensor_toMPSTensor, pairDelta, pairDeltaInt]

/-- The product of the identity tensor with a bond-two tensor is that tensor. -/
theorem mulTensor_idTensor_left (M : MPOTensor 2 2) :
    mulTensor (MPOTensor.idTensor 2) M = (M : MPOTensor 2 (1 * 2)) := by
  have h : ∀ r : Fin (1 * 2), finProdFinEquiv.symm r = ((0 : Fin 1), (r : Fin 2)) := by
    decide
  funext i j
  ext r c
  simp [mulTensor_apply, MPOTensor.idTensor, Fin.sum_univ_two, Matrix.kroneckerMap_apply, h]
  fin_cases i <;> fin_cases j <;> simp

/-- The product of a bond-two tensor with the identity tensor is that tensor. -/
theorem mulTensor_idTensor_right (M : MPOTensor 2 2) :
    mulTensor M (MPOTensor.idTensor 2) = (M : MPOTensor 2 (2 * 1)) := by
  have h : ∀ r : Fin (2 * 1), finProdFinEquiv.symm r = ((r : Fin 2), (0 : Fin 1)) := by
    decide
  funext i j
  ext r c
  simp [mulTensor_apply, MPOTensor.idTensor, Fin.sum_univ_two, Matrix.kroneckerMap_apply, h]
  fin_cases i <;> fin_cases j <;> simp

/-- The product of two identity tensors is the identity tensor. -/
theorem mulTensor_idTensor_idTensor :
    mulTensor (MPOTensor.idTensor 2) (MPOTensor.idTensor 2) =
      (MPOTensor.idTensor 2 : MPOTensor 2 (1 * 1)) := by
  funext i j
  ext r c
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases c <;>
    simp [mulTensor_apply, MPOTensor.idTensor, Fin.sum_univ_two]

end CZXCompression
