import TNLean.MPS.Examples.PeriodicStringExamples

/-!
Exact periodic examples for arXiv:0802.0447, lines 380–411.
These regressions include the empty-ring convention, the zero one-site AKLT
vector, and positive even and odd rings. The norm checks distinguish the
unnormalized periodic vectors from normalized physical expectations.
-/

open scoped Matrix BigOperators InnerProductSpace
open MPSTensor

-- The imported Pauli matrix is definitionally the exact old σy matrix.
example : SpinCover.pauli 1 =
    (!![0, -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) := rfl

example : mpvState akltPGWSVC08Tensor 1 = 0 := akltPGWSVC08_mpvState_one

example : mpvState akltPGWSVC08Tensor 0 ≠ 0 :=
  (akltPGWSVC08_mpvState_ne_zero_iff 0).mpr (by decide)

example : mpvState akltPGWSVC08Tensor 2 ≠ 0 :=
  (akltPGWSVC08_mpvState_ne_zero_iff 2).mpr (by decide)

example : mpvState akltPGWSVC08Tensor 3 ≠ 0 :=
  (akltPGWSVC08_mpvState_ne_zero_iff 3).mpr (by decide)

example : ⟪mpvState akltPGWSVC08Tensor 0, mpvState akltPGWSVC08Tensor 0⟫_ℂ = 4 := by
  rw [akltPGWSVC08_mpvState_inner_self]
  norm_num

example : ⟪mpvState akltPGWSVC08Tensor 2, mpvState akltPGWSVC08Tensor 2⟫_ℂ = 4 / 3 := by
  rw [akltPGWSVC08_mpvState_inner_self]
  norm_num

example : ⟪mpvState akltPGWSVC08Tensor 3, mpvState akltPGWSVC08Tensor 3⟫_ℂ = 8 / 9 := by
  rw [akltPGWSVC08_mpvState_inner_self]
  norm_num

example : mpvExpectation akltPGWSVC08Tensor 0
    (Matrix.finKronecker fun _ : Fin 0 => akltSpinRotationZ) = 1 := by
  simp [akltPGWSVC08_fullRing]

example : mpvExpectation akltPGWSVC08Tensor 1
    (Matrix.finKronecker fun _ : Fin 1 => akltSpinRotationZ) = 0 := by
  simp [akltPGWSVC08_fullRing]

example : mpvExpectation akltPGWSVC08Tensor 2
    (Matrix.finKronecker fun _ : Fin 2 => akltSpinRotationZ) = 1 := by
  simp [akltPGWSVC08_fullRing]

example : mpvExpectation akltPGWSVC08Tensor 3
    (Matrix.finKronecker fun _ : Fin 3 => akltSpinRotationZ) = 1 := by
  simp [akltPGWSVC08_fullRing]

example : mpv clusterTensorRMP (Fin.elim0 : Fin 0 → Fin 2) = 2 := by simp

example : ‖mpvState clusterTensorRMP 0‖ ^ 2 = 4 := by
  rw [EuclideanSpace.norm_sq_eq]
  norm_num [mpvState_apply]

example : ‖mpvState clusterTensorRMP 1‖ ^ 2 = 1 :=
  clusterTensorRMP_mpvState_norm_sq (by decide)

example : ‖mpvState clusterTensorRMP 2‖ ^ 2 = 1 :=
  clusterTensorRMP_mpvState_norm_sq (by decide)

example : mpvExpectation clusterTensorRMP 0
    (Matrix.finKronecker fun _ : Fin 0 => -pauliX) = 1 := clusterTensorRMP_fullRing 0

example : mpvExpectation clusterTensorRMP 1
    (Matrix.finKronecker fun _ : Fin 1 => -pauliX) = 1 := clusterTensorRMP_fullRing 1

example : mpvExpectation clusterTensorRMP 2
    (Matrix.finKronecker fun _ : Fin 2 => -pauliX) = 1 := clusterTensorRMP_fullRing 2

example : mpvExpectation clusterTensorRMP 3
    (Matrix.finKronecker fun _ : Fin 3 => -pauliX) = 1 := clusterTensorRMP_fullRing 3

section AxiomChecks
set_option linter.hashCommand false

/--
info: 'MPSTensor.akltPGWSVC08_fullRing'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.akltPGWSVC08_fullRing

/--
info: 'MPSTensor.clusterTensorRMP_fullRing'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.clusterTensorRMP_fullRing

end AxiomChecks
