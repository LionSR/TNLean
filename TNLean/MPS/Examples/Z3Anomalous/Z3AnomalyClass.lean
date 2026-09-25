/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousInverseFusion
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalyTreeUDU
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalyTreeUUU
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousRepresentation
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# The anomaly class of the `ℤ₃` representation `{1, U, U†}`

The family `Z3Anomalous.family` represents `ℤ₃` exactly, with normal tensors, on
every nonempty chain.  This file computes its anomaly three-cochain `ω` in the
sense of arXiv:2502.20257 (display preceding `eq:3-cocycle`) and shows that its
cohomology class is nontrivial for every choice of fusion tensors.

For the fusion tensors that are trivial whenever a factor is the identity and are
the recorded compressions `U ⊗ U → U†`, `U ⊗ U† → 1`, `U† ⊗ U → 1`,
`U† ⊗ U† → U` otherwise, the gauge-invariant product
`ω(g,1,g) ω(g,g,g) ω(g,g²,g)` for the generator `g ↦ U` is `ω₃²`, where `ω₃` is
the primitive cube root of unity `eisensteinOmega`: the two fusion trees of
`(g,g,g)` differ by `ω₃²` and those of `(g,g²,g)` agree, against every nonempty
word.  The product is invariant under a change of fusion tensors because
`g³ = 1`, so the class is nontrivial for every choice.  This is the class `j = 2`
of the cocycles `ω_j` of arXiv:2405.00439, line 2040, in the orientation of the
three-cochain of arXiv:2502.20257 used here.

## Main results

* `Z3Anomalous.family_isNormalRepresentation`
* `Z3Anomalous.z3FusionData`: the fusion tensors described above.
* `Z3Anomalous.z3FusionData_omega_gen_gen_gen`,
  `Z3Anomalous.z3FusionData_omega_gen_sq_gen`,
  `Z3Anomalous.z3FusionData_omega_gen_one_gen`
* `Z3Anomalous.cyclicInvariant_omega_z3`: for every choice of fusion tensors,
  the gauge-invariant product is `ω₃²`.
* `Z3Anomalous.not_isTrivialGaugeClass_omega_z3`.
-/

noncomputable section

open scoped Matrix Kronecker
open TNLean.Algebra MPOTensor MPSTensor EisensteinInt

namespace Z3Anomalous

/-- The generator of `ℤ₃`, written multiplicatively; it carries the tensor `U`. -/
def z3Gen : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1

theorem z3Gen_pow_three : z3Gen ^ 3 = 1 := by decide

private theorem forall_z3 {P : Multiplicative (ZMod 3) → Prop}
    (h0 : P (Multiplicative.ofAdd 0)) (h1 : P (Multiplicative.ofAdd 1))
    (h2 : P (Multiplicative.ofAdd 2)) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1, h2]

/-! ### The identity tensor -/

theorem identityTensor_apply (i j : Fin 3) :
    identityTensor i j = if i = j then 1 else 0 := by
  unfold identityTensor identityEis
  split_ifs <;> simp [complexOfEisenstein_one, complexOfEisenstein_zero]

theorem mulTensor_identityTensor_left (M : MPOTensor 3 2) :
    mulTensor identityTensor M = (M : MPOTensor 3 (1 * 2)) := by
  have h : ∀ r : Fin (1 * 2), finProdFinEquiv.symm r = ((0 : Fin 1), (r : Fin 2)) := by
    decide
  funext i j
  ext r c
  fin_cases i <;> fin_cases j <;>
    simp [mulTensor_apply, identityTensor_apply, Fin.sum_univ_three, Matrix.kroneckerMap_apply,
      h]

theorem mulTensor_identityTensor_right (M : MPOTensor 3 2) :
    mulTensor M identityTensor = (M : MPOTensor 3 (2 * 1)) := by
  have h : ∀ r : Fin (2 * 1), finProdFinEquiv.symm r = ((r : Fin 2), (0 : Fin 1)) := by
    decide
  funext i j
  ext r c
  fin_cases i <;> fin_cases j <;>
    simp [mulTensor_apply, identityTensor_apply, Fin.sum_univ_three, Matrix.kroneckerMap_apply,
      h]

theorem mulTensor_identityTensor_identityTensor :
    mulTensor identityTensor identityTensor = (identityTensor : MPOTensor 3 (1 * 1)) := by
  funext i j
  ext r c
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases c <;>
    simp [mulTensor_apply, identityTensor_apply, Fin.sum_univ_three]

/-! ### The representation -/

/-- **`{1, U, U†}` represents `ℤ₃` with normal tensors**: the three tensors are
normal and the periodic operators multiply exactly as the group on every nonempty
chain (`family_operator_laws`).

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 1684 (the
representation law); the tensors are those of `Z3AnomalousTensor`. -/
theorem family_isNormalRepresentation : family.IsNormalRepresentation where
  isNormal := forall_z3 identityMPS_isNormal uMPS_isNormal uDagMPS_isNormal
  operator_mul g h N hN := family_operator_laws.2.2.1 g h N hN

/-! ### The fusion tensors -/

/-- The left fusion tensors attached to a pair of residues: the identity when a
residue is zero, and the recorded compressions otherwise. -/
def z3LabelV : (a b : Fin 3) →
    Matrix (Fin (repBondDim (a + b))) (Fin (repBondDim a * repBondDim b)) ℂ
  | 0, 0 => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | 0, 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 0, 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 1, 0 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 2, 0 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 1, 1 => uu_compression.left theSlot
  | 1, 2 => ud_compression.left theSlot
  | 2, 1 => du_compression.left theSlot
  | 2, 2 => dd_compression.left theSlot

/-- The right fusion tensors attached to a pair of residues. -/
def z3LabelW : (a b : Fin 3) →
    Matrix (Fin (repBondDim a * repBondDim b)) (Fin (repBondDim (a + b))) ℂ
  | 0, 0 => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | 0, 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 0, 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 1, 0 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 2, 0 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 1, 1 => uu_compression.right theSlot
  | 1, 2 => ud_compression.right theSlot
  | 2, 1 => du_compression.right theSlot
  | 2, 2 => dd_compression.right theSlot

private theorem isReduction_one_one_of_eq {D : ℕ} {B A : MPSTensor 9 D} (h : B = A) :
    MPSTensor.IsReduction B A 1 1 := by
  subst h
  exact ⟨Matrix.one_mul 1, fun w ↦ by rw [Matrix.one_mul, Matrix.mul_one]⟩

/-- **Fusion tensors of `{1, U, U†}`**: trivial whenever a factor is the identity,
and the recorded compressions `U ⊗ U → U†`, `U ⊗ U† → 1`, `U† ⊗ U → 1`,
`U† ⊗ U† → U` otherwise.

Source: the compression data of `Z3AnomalousFusion` and `Z3AnomalousInverseFusion`;
arXiv:2502.20257, equations `eq:fusion_1`, `eq:fusion_2`. -/
def z3FusionData : family.FusionData where
  V x y := z3LabelV x.toAdd y.toAdd
  W x y := z3LabelW x.toAdd y.toAdd
  isReduction := by
    refine forall_z3 (forall_z3 ?_ ?_ ?_) (forall_z3 ?_ ?_ ?_) (forall_z3 ?_ ?_ ?_)
    · change MPSTensor.IsReduction (mulTensor identityTensor identityTensor).toMPSTensor
        ((identityTensor : MPOTensor 3 (1 * 1))).toMPSTensor 1 1
      exact isReduction_one_one_of_eq (by rw [mulTensor_identityTensor_identityTensor])
    · change MPSTensor.IsReduction (mulTensor identityTensor uTensor).toMPSTensor
        ((uTensor : MPOTensor 3 (1 * 2))).toMPSTensor 1 1
      exact isReduction_one_one_of_eq (by rw [mulTensor_identityTensor_left])
    · change MPSTensor.IsReduction (mulTensor identityTensor uDagTensor).toMPSTensor
        ((uDagTensor : MPOTensor 3 (1 * 2))).toMPSTensor 1 1
      exact isReduction_one_one_of_eq (by rw [mulTensor_identityTensor_left])
    · change MPSTensor.IsReduction (mulTensor uTensor identityTensor).toMPSTensor
        ((uTensor : MPOTensor 3 (2 * 1))).toMPSTensor 1 1
      exact isReduction_one_one_of_eq (by rw [mulTensor_identityTensor_right])
    · exact uu_isReduction
    · exact ud_isReduction
    · change MPSTensor.IsReduction (mulTensor uDagTensor identityTensor).toMPSTensor
        ((uDagTensor : MPOTensor 3 (2 * 1))).toMPSTensor 1 1
      exact isReduction_one_one_of_eq (by rw [mulTensor_identityTensor_right])
    · exact du_isReduction
    · exact dd_isReduction

/-! ### Trees from local identities -/

/-- Two left boundaries of a triple product that both intertwine two letters with
the target, `X T^a T^b = A^a X T^b`, and agree up to `z` on single letters, agree up
to `z` against every nonempty word. -/
private theorem tree_evalWord {m : ℕ} {T : MPSTensor 9 8} {A : MPSTensor 9 m}
    {L R : Matrix (Fin m) (Fin 8) ℂ} {z : ℂ}
    (hL : ∀ a b, L * T a * T b = A a * L * T b) (hR : ∀ a b, R * T a * T b = A a * R * T b)
    (h1 : ∀ a, L * T a = z • (R * T a)) (w : List (Fin 9)) (hw : w ≠ []) :
    L * Kraus.evalWord T w = z • (R * Kraus.evalWord T w) := by
  induction w with
  | nil => exact absurd rfl hw
  | cons a w ih =>
      cases w with
      | nil => simpa using h1 a
      | cons b w =>
          have ih' := ih (List.cons_ne_nil _ _)
          rw [Kraus.evalWord_cons] at ih'
          calc
            L * Kraus.evalWord T (a :: b :: w) = L * T a * T b * Kraus.evalWord T w := by
              simp only [Kraus.evalWord_cons, Matrix.mul_assoc]
            _ = A a * (L * (T b * Kraus.evalWord T w)) := by
              rw [hL]; simp only [Matrix.mul_assoc]
            _ = z • (R * T a * T b * Kraus.evalWord T w) := by
              rw [ih', hR, Matrix.mul_smul]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Kraus.evalWord_cons, Matrix.mul_assoc]

private theorem kronId_complexOfEisenstein {m n : ℕ} (X : Matrix (Fin m) (Fin n) EisensteinInt)
    (D : ℕ) :
    kronId (complexOfEisenstein X) D =
      complexOfEisenstein ((X ⊗ₖ (1 : Matrix (Fin D) (Fin D) EisensteinInt)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  ext r c
  simp only [kronId, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    complexOfEisenstein_apply, Matrix.one_apply, map_mul]
  split_ifs <;> simp

private theorem idKron_complexOfEisenstein {m n : ℕ} (D : ℕ)
    (X : Matrix (Fin m) (Fin n) EisensteinInt) :
    idKron D (complexOfEisenstein X) =
      complexOfEisenstein (((1 : Matrix (Fin D) (Fin D) EisensteinInt) ⊗ₖ X).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  ext r c
  simp only [idKron, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    complexOfEisenstein_apply, Matrix.one_apply, map_mul]
  split_ifs <;> simp

private theorem assocInv_two_two_two :
    mulTensorAssocInvMatrix 2 2 2 = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  have he : (mulTensorAssocEquiv 2 2 2).symm = Equiv.refl (Fin 8) := Equiv.ext (by decide)
  rw [mulTensorAssocInvMatrix, he, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

private theorem assocInv_two_one_two :
    mulTensorAssocInvMatrix 2 1 2 = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have he : (mulTensorAssocEquiv 2 1 2).symm = Equiv.refl (Fin 4) := Equiv.ext (by decide)
  rw [mulTensorAssocInvMatrix, he, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

private theorem castMat_apply {a b : Multiplicative (ZMod 3)} (e : a = b)
    (i : Fin (family.bondDim b)) (j : Fin (family.bondDim a)) :
    family.castMat e i j = if (i : ℕ) = j then 1 else 0 := by
  subst e
  simp [Matrix.one_apply, Fin.ext_iff]

private theorem mulTensor_uTensor_uTensor :
    mulTensor uTensor uTensor = fun i j ↦ complexOfEisenstein (mulTensorR uEis uEis i j) :=
  funext₂ fun i j ↦ mulTensor_complexOfRing _ uEis uEis i j

private theorem mulTensor_uTensor_uDagTensor :
    mulTensor uTensor uDagTensor =
      fun i j ↦ complexOfEisenstein (mulTensorR uEis uDagEis i j) :=
  funext₂ fun i j ↦ mulTensor_complexOfRing _ uEis uDagEis i j

private theorem tripleUUU_eq (a : Fin 9) :
    (family.tripleTensor z3Gen z3Gen z3Gen).toMPSTensor a =
      complexOfEisenstein (tripleUUUTable a) := by
  change (mulTensor (mulTensor uTensor uTensor) uTensor).toMPSTensor a = _
  rw [mulTensor_uTensor_uTensor, ← tripleUUUEis_eq_table]
  exact mulTensor_complexOfRing _ _ uEis _ _

private theorem tripleUDU_eq (a : Fin 9) :
    (family.tripleTensor z3Gen (z3Gen * z3Gen) z3Gen).toMPSTensor a =
      complexOfEisenstein (tripleUDUTable a) := by
  change (mulTensor (mulTensor uTensor uDagTensor) uTensor).toMPSTensor a = _
  rw [mulTensor_uTensor_uDagTensor, ← tripleUDUEis_eq_table]
  exact mulTensor_complexOfRing _ _ uEis _ _

theorem z3FusionData_leftV_gen_gen_gen :
    z3FusionData.leftV z3Gen z3Gen z3Gen = complexOfEisenstein leftUUUEis := by
  change du_compression.left theSlot * kronId (uu_compression.left theSlot) 2 = _
  rw [du_left_eq, uu_left_eq, kronId_complexOfEisenstein, ← complexOfEisenstein_mul]
  rfl

theorem z3FusionData_rightV_gen_gen_gen :
    z3FusionData.rightV z3Gen z3Gen z3Gen = complexOfEisenstein rightUUUEis := by
  have hc : family.castMat (mul_assoc z3Gen z3Gen z3Gen).symm =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    rw [castMat_apply]
    fin_cases i; fin_cases j
    rfl
  rw [GroupFamily.FusionData.rightV, hc]
  change (1 : Matrix (Fin 1) (Fin 1) ℂ) * (ud_compression.left theSlot *
    idKron 2 (uu_compression.left theSlot) * mulTensorAssocInvMatrix 2 2 2) = _
  rw [ud_left_eq, uu_left_eq, assocInv_two_two_two, idKron_complexOfEisenstein, Matrix.one_mul,
    Matrix.mul_one, ← complexOfEisenstein_mul]
  rfl

theorem z3FusionData_leftV_gen_sq_gen :
    z3FusionData.leftV z3Gen (z3Gen * z3Gen) z3Gen = complexOfEisenstein leftUDUEis := by
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) * kronId (ud_compression.left theSlot) 2 = _
  rw [ud_left_eq, kronId_complexOfEisenstein, Matrix.one_mul]
  rfl

theorem z3FusionData_rightV_gen_sq_gen :
    z3FusionData.rightV z3Gen (z3Gen * z3Gen) z3Gen = complexOfEisenstein rightUDUEis := by
  have hc : family.castMat (mul_assoc z3Gen (z3Gen * z3Gen) z3Gen).symm =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    rw [castMat_apply]
    fin_cases i <;> fin_cases j <;> rfl
  rw [GroupFamily.FusionData.rightV, hc]
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) *
    idKron 2 (du_compression.left theSlot) * mulTensorAssocInvMatrix 2 2 2) = _
  rw [du_left_eq, assocInv_two_two_two, idKron_complexOfEisenstein, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one]
  rfl

/-- The two trees of `(g,g,g)` differ by `ω₃² = -1 - ω₃` against every nonempty
word. -/
theorem z3FusionData_isAssociator_gen_gen_gen :
    z3FusionData.IsAssociator z3Gen z3Gen z3Gen (eisensteinToComplex ⟨-1, -1⟩) := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [z3FusionData_leftV_gen_gen_gen, z3FusionData_rightV_gen_gen_gen]
  refine ⟨1, fun w hw ↦ tree_evalWord (A := identityMPS) (fun a b ↦ ?_) (fun a b ↦ ?_)
    (fun a ↦ ?_) w (List.ne_nil_of_length_pos hw)⟩
  · rw [tripleUUU_eq, tripleUUU_eq, identityMPS_eq, ← complexOfEisenstein_mul,
      ← complexOfEisenstein_mul, ← complexOfEisenstein_mul, ← complexOfEisenstein_mul,
      leftUUU_pair]
  · rw [tripleUUU_eq, tripleUUU_eq, identityMPS_eq, ← complexOfEisenstein_mul,
      ← complexOfEisenstein_mul, ← complexOfEisenstein_mul, ← complexOfEisenstein_mul,
      rightUUU_pair]
  · rw [tripleUUU_eq, ← complexOfEisenstein_mul, ← complexOfEisenstein_mul, UUU_letter,
      complexOfEisenstein_smul]

/-- The two trees of `(g,g²,g)` agree against every nonempty word. -/
theorem z3FusionData_isAssociator_gen_sq_gen :
    z3FusionData.IsAssociator z3Gen (z3Gen * z3Gen) z3Gen 1 := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [z3FusionData_leftV_gen_sq_gen, z3FusionData_rightV_gen_sq_gen]
  refine ⟨1, fun w hw ↦ tree_evalWord (A := uMPS) (fun a b ↦ ?_) (fun a b ↦ ?_)
    (fun a ↦ ?_) w (List.ne_nil_of_length_pos hw)⟩
  · rw [tripleUDU_eq, tripleUDU_eq, uMPS_eq, ← complexOfEisenstein_mul,
      ← complexOfEisenstein_mul, ← complexOfEisenstein_mul, ← complexOfEisenstein_mul,
      leftUDU_pair]
  · rw [tripleUDU_eq, tripleUDU_eq, uMPS_eq, ← complexOfEisenstein_mul,
      ← complexOfEisenstein_mul, ← complexOfEisenstein_mul, ← complexOfEisenstein_mul,
      rightUDU_pair]
  · rw [tripleUDU_eq, ← complexOfEisenstein_mul, ← complexOfEisenstein_mul, UDU_letter,
      one_smul]

/-- For the fusion tensors of `z3FusionData`, `ω(g,1,g) = 1`: both trees are the
recorded fusion tensor of `U ⊗ U`. -/
theorem z3FusionData_omega_gen_one_gen : z3FusionData.omega z3Gen 1 z3Gen = 1 := by
  have hL : z3FusionData.leftV z3Gen 1 z3Gen = uu_compression.left theSlot := by
    change uu_compression.left theSlot * kronId (1 : Matrix (Fin 2) (Fin 2) ℂ) 2 = _
    rw [kronId_one, Matrix.mul_one]
  have hc : family.castMat (mul_assoc z3Gen 1 z3Gen).symm =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    rw [castMat_apply]
    fin_cases i <;> fin_cases j <;> rfl
  have hR : z3FusionData.rightV z3Gen 1 z3Gen = uu_compression.left theSlot := by
    rw [GroupFamily.FusionData.rightV, hc]
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) * (uu_compression.left theSlot *
      idKron 2 (1 : Matrix (Fin 2) (Fin 2) ℂ) * mulTensorAssocInvMatrix 2 1 2) = _
    rw [idKron_one, Matrix.mul_one, assocInv_two_one_two, Matrix.mul_one, Matrix.one_mul]
  have h : z3FusionData.IsAssociator z3Gen 1 z3Gen 1 := by
    unfold GroupFamily.FusionData.IsAssociator
    rw [hR, ← hL]
    exact MPSTensor.IsDressedProportional.refl _ _
  apply Units.ext
  rw [← GroupFamily.FusionData.eq_omega_of_isAssociator family_isNormalRepresentation h]
  simp

/-- `ω(g,g,g) = ω₃²` for the fusion tensors of `z3FusionData`. -/
theorem z3FusionData_omega_gen_gen_gen :
    (z3FusionData.omega z3Gen z3Gen z3Gen : ℂ) = eisensteinOmega ^ 2 := by
  rw [← GroupFamily.FusionData.eq_omega_of_isAssociator family_isNormalRepresentation
    z3FusionData_isAssociator_gen_gen_gen, eisensteinToComplex_apply]
  linear_combination -eisensteinOmega_quadratic

/-- `ω(g,g²,g) = 1` for the fusion tensors of `z3FusionData`. -/
theorem z3FusionData_omega_gen_sq_gen :
    z3FusionData.omega z3Gen (z3Gen * z3Gen) z3Gen = 1 := by
  apply Units.ext
  rw [← GroupFamily.FusionData.eq_omega_of_isAssociator family_isNormalRepresentation
    z3FusionData_isAssociator_gen_sq_gen]
  simp

/-! ### The anomaly class -/

theorem cyclicInvariant_z3FusionData :
    (ScalarThreeCochain.cyclicInvariant z3FusionData.omega z3Gen 3 : ℂ) =
      eisensteinOmega ^ 2 := by
  have h2 : z3Gen ^ 2 = z3Gen * z3Gen := sq z3Gen
  simp only [ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ, Finset.prod_range_zero,
    one_mul, pow_zero, pow_one, h2, z3FusionData_omega_gen_one_gen,
    z3FusionData_omega_gen_sq_gen, mul_one]
  exact z3FusionData_omega_gen_gen_gen

/-- **For every choice of fusion tensors of `{1, U, U†}`**, the gauge-invariant
product `ω(g,1,g) ω(g,g,g) ω(g,g²,g)` is the primitive cube root of unity `ω₃²`.

Source: arXiv:2502.20257, `eq:omegagauge`; arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` line 2040 (the classes `ω_j` of `ℤ_n`). -/
theorem cyclicInvariant_omega_z3 (fd : family.FusionData) :
    (ScalarThreeCochain.cyclicInvariant fd.omega z3Gen 3 : ℂ) = eisensteinOmega ^ 2 := by
  rw [(GroupFamily.FusionData.omega_cohomologousTo family_isNormalRepresentation
    z3FusionData fd).cyclicInvariant_eq z3Gen_pow_three, cyclicInvariant_z3FusionData]

theorem eisensteinOmega_sq_ne_one : eisensteinOmega ^ 2 ≠ 1 := by
  intro h
  have h1 : eisensteinToComplex (omega ^ 2) = eisensteinToComplex 1 := by
    rw [map_pow, eisensteinToComplex_omega, h, map_one]
  exact absurd (eisensteinToComplex_injective h1) (by decide)

/-- **The `ℤ₃` representation `{1, U, U†}` is anomalous**: for every choice of
fusion tensors, the anomaly three-cocycle is not cohomologous to the trivial one.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040; arXiv:2502.20257,
`eq:omegagauge` and the sentence following it. -/
theorem not_isTrivialGaugeClass_omega_z3 (fd : family.FusionData) :
    ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  refine ScalarThreeCochain.not_isTrivialGaugeClass_of_cyclicInvariant_ne_one z3Gen_pow_three ?_
  intro h
  have := cyclicInvariant_omega_z3 fd
  rw [h, Units.val_one] at this
  exact eisensteinOmega_sq_ne_one this.symm

end Z3Anomalous
