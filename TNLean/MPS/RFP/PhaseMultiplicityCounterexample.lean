/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.StructuralFull

/-!
# Literal repeated-phase formula and the physical-isometry obstruction

The displayed formula `III_CFI_RFP` in arXiv:1606.00608 (lines 543--550) permits
repeated virtual blocks indexed by `q`, with independent unit-modulus phases.
Read literally as a virtual block diagonal, its smallest repeated-phase example
is the one-letter tensor `diag(1, -1)`, made from two scalar blocks with phases
`1` and `-1`.

The prose immediately following the display says that `j,q` also give a direct
sum in the physical space after applying the isometry (lines 559--563).  The
one-letter virtual-block reading does not realize that additional physical
direct sum: its blocked matrix is the identity and is not a scalar multiple of
`diag(1, -1)`.  It therefore fails the defining physical-isometry relation
`AA=A` (lines 396--425), and its transfer map is not idempotent.  The example
records an ambiguity between the literal displayed matrix formula and its
accompanying physical-space interpretation; it is not asserted to be a source
renormalization fixed point.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The one-dimensional representative normal tensor in the counterexample. -/
def scalarUnitTensor : MPSTensor 1 1 := fun _ => 1

/-- The two unit-modulus phases `1` and `-1`. -/
def signPhase : Fin 2 → ℂ
  | 0 => 1
  | 1 => -1

/-- Two phase copies of `scalarUnitTensor`, assembled on the bond direct sum. -/
def phaseFlipTensor : MPSTensor 1 2 := fun _ => !![1, 0; 0, -1]

/-- Both copy coefficients have unit modulus. -/
lemma norm_signPhase (q : Fin 2) : ‖signPhase q‖ = 1 := by
  fin_cases q <;> simp [signPhase]

/-- `phaseFlipTensor` is the literal virtual block-diagonal reading of two
copies of the same scalar tensor with phases `1` and `-1` in equation
`III_CFI_RFP` of arXiv:1606.00608, lines 543--550.  This assertion does not
include the physical direct-sum interpretation described at lines 559--563. -/
lemma phaseFlipTensor_is_two_phase_copies :
    (∀ q : Fin 2, ‖signPhase q‖ = 1) ∧
    (∀ (i : Fin 1) (q : Fin 2),
      phaseFlipTensor i q q = signPhase q * scalarUnitTensor i 0 0) ∧
    (∀ (i : Fin 1) (q r : Fin 2), q ≠ r → phaseFlipTensor i q r = 0) := by
  refine ⟨norm_signPhase, ?_, ?_⟩
  · intro i q
    fin_cases i
    fin_cases q <;> simp [phaseFlipTensor, signPhase, scalarUnitTensor]
  · intro i q r hqr
    fin_cases i
    fin_cases q <;> fin_cases r <;> simp_all [phaseFlipTensor]

/-- The scalar representative is in the trace-normalized unit-isometry form of
arXiv:1606.00608, Lemma `charact-NT-pure-RFP`, lines 1271--1301. -/
lemma scalarUnitTensor_isIsometryCanonicalForm :
    IsIsometryCanonicalForm scalarUnitTensor := by
  refine ⟨1, fun _ => 1, scalarUnitTensor, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro k
    simp
  · simp
  · intro p q
    fin_cases p
    fin_cases q
    simp [scalarUnitTensor]
  · intro i
    fin_cases i
    ext a b
    fin_cases a
    fin_cases b
    simp [scalarUnitTensor]

/-- The one-letter virtual-block tensor does not satisfy even the scalar form
of the defining physical-isometry relation `AA=A` from arXiv:1606.00608,
lines 396--425.  Its blocked matrix is the identity, which is not a scalar
multiple of `diag(1, -1)`. -/
lemma phaseFlipTensor_no_blocking_coefficient :
    ¬ ∃ v : ℂ,
      phaseFlipTensor 0 * phaseFlipTensor 0 = v • phaseFlipTensor 0 := by
  rintro ⟨v, hv⟩
  have h00 := congrFun (congrFun hv 0) 0
  have h11 := congrFun (congrFun hv 1) 1
  norm_num [phaseFlipTensor, Matrix.mul_apply] at h00 h11
  subst v
  norm_num at h11

/-- The two-phase assembly is not a renormalization fixed point under the
present whole-tensor definition.  Evaluation on the off-diagonal matrix unit
`E₀₁` gives `E²(E₀₁) = E₀₁` but `E(E₀₁) = -E₀₁` after one application.

Together with `phaseFlipTensor_no_blocking_coefficient`, this distinguishes the
literal virtual-block reading of `III_CFI_RFP` from the physical-isometry
interpretation in arXiv:1606.00608, lines 559--563. -/
theorem phaseFlipTensor_not_isRFP : ¬ IsRFP phaseFlipTensor := by
  intro hRFP
  have h := LinearMap.congr_fun hRFP (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
  have h01 := congrFun (congrFun h 0) 1
  norm_num [IsRFP, LinearMap.comp_apply, transferMap_apply, phaseFlipTensor,
    Matrix.mul_apply, Matrix.conjTranspose_apply] at h01
  norm_num [Matrix.vecMul, dotProduct] at h01
  norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply] at h01

/-- The scalar representative and two unit phases satisfy the literal virtual
block-diagonal reading of `III_CFI_RFP`, but the resulting one-letter tensor
fails both `AA=A` and whole-tensor transfer-map idempotence.  Hence the example
exhibits an ambiguity between the display at arXiv:1606.00608, lines 543--554,
and its physical direct-sum interpretation at lines 559--563; it is not a
source renormalization fixed point. -/
theorem phaseFlipTensor_literal_display_ambiguity :
    ((∀ q : Fin 2, ‖signPhase q‖ = 1) ∧
      (∀ (i : Fin 1) (q : Fin 2),
        phaseFlipTensor i q q = signPhase q * scalarUnitTensor i 0 0) ∧
      (∀ (i : Fin 1) (q r : Fin 2), q ≠ r → phaseFlipTensor i q r = 0)) ∧
    IsIsometryCanonicalForm scalarUnitTensor ∧
    (¬ ∃ v : ℂ,
      phaseFlipTensor 0 * phaseFlipTensor 0 = v • phaseFlipTensor 0) ∧
    ¬ IsRFP phaseFlipTensor := by
  exact ⟨phaseFlipTensor_is_two_phase_copies,
    scalarUnitTensor_isIsometryCanonicalForm, phaseFlipTensor_no_blocking_coefficient,
    phaseFlipTensor_not_isRFP⟩

end MPSTensor
