/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.Zsqrt2Ring

/-!
# The three topological-symmetry tensors of the Ising anyon chain

The tensors `A_1`, `A_ψ`, `A_σ` of the Ising anyon chain are matrix product operators on the ten
fusion-tree labels `(x', ρ, x)` with `x ∈ x' ⊗ ρ`; their letters are the F-symbols
`[F^{a x' ρ}_y]_{y' x}` of the Ising category, and a letter vanishes unless its two labels carry
the same `ρ` (`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, "Conventions and the
dictionary" and §1.1, verified by `checks/asym_ising_action_verify.py`). This file records the
three tensors over `ℤ[√2]`, the `σ` strand scaled by `√2` so that every entry lies in the ring,
the vanishing of the letters across sectors, and the normality of each tensor at blocking length
one. The weighted bond object built from them and its compression are in `IsingGauge` and
`IsingWeightedTwist`.

## Main definitions

* `IsingTwist.isingRho`: the middle label `ρ` of each fusion-tree label.
* `IsingTwist.isingOne`, `IsingTwist.isingPsi`, `IsingTwist.isingSigma`: the three
  topological-symmetry tensors, the last one scaled by `√2`.

## Main results

* `IsingTwist.isingOneZ_eq_zero_of_rho_ne`, `IsingTwist.isingPsiZ_eq_zero_of_rho_ne`,
  `IsingTwist.isingSigmaZ_eq_zero_of_rho_ne`: the letters vanish across sectors.
* `IsingTwist.isingSigma_isNormal`, `IsingTwist.isingOne_isNormal`,
  `IsingTwist.isingPsi_isNormal`: the three tensors are normal at blocking length one.
-/

namespace IsingTwist

open MPSTensor Zsqrtd

/-! ### The three topological-symmetry tensors -/

/-- The label `ρ` of a fusion-tree label `(x', ρ, x)`, in the order `1, ψ, σ`; the ten labels
are `(1,1,1), (1,ψ,ψ), (1,σ,σ), (ψ,1,ψ), (ψ,ψ,1), (ψ,σ,σ), (σ,1,σ), (σ,ψ,σ), (σ,σ,1), (σ,σ,ψ)`
(data file, "Conventions and the dictionary"). -/
def isingRho : Fin 10 → Fin 3 := ![0, 1, 2, 0, 1, 2, 0, 1, 2, 2]

/-- The tensor `A_1` over `ℤ√2`, on the site space `P_1 = [(1,1), (ψ,ψ), (σ,σ)]`: every letter
is a matrix unit (data file §1.1). -/
def isingOneZ : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) (ℤ√2)
  | 0, 0 => Matrix.single 0 0 1
  | 1, 1 => Matrix.single 0 1 1
  | 2, 2 => Matrix.single 0 2 1
  | 3, 3 => Matrix.single 1 1 1
  | 4, 4 => Matrix.single 1 0 1
  | 5, 5 => Matrix.single 1 2 1
  | 6, 6 => Matrix.single 2 2 1
  | 7, 7 => Matrix.single 2 2 1
  | 8, 8 => Matrix.single 2 0 1
  | 9, 9 => Matrix.single 2 1 1
  | _, _ => 0

/-- The tensor `A_ψ` over `ℤ√2`, on the site space `P_ψ = [(1,ψ), (ψ,1), (σ,σ)]`: every letter
is a signed matrix unit, the sign at the letter `((σ,ψ,σ), (σ,ψ,σ))` being the F-symbol
`[F^{ψσψ}_σ] = -1` (data file §1.1). -/
def isingPsiZ : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) (ℤ√2)
  | 0, 3 => Matrix.single 1 1 1
  | 1, 4 => Matrix.single 1 0 1
  | 2, 5 => Matrix.single 1 2 1
  | 3, 0 => Matrix.single 0 0 1
  | 4, 1 => Matrix.single 0 1 1
  | 5, 2 => Matrix.single 0 2 1
  | 6, 6 => Matrix.single 2 2 1
  | 7, 7 => Matrix.single 2 2 (-1)
  | 8, 9 => Matrix.single 2 1 1
  | 9, 8 => Matrix.single 2 0 1
  | _, _ => 0

/-- The tensor `√2 A_σ` over `ℤ√2`, on the site space
`P_σ = [(1,σ), (ψ,σ), (σ,1), (σ,ψ)]`: every letter is a matrix unit scaled by `±1` or `±√2`,
the entries `±1` being the rescaled F-symbols `±1/√2` of the `σσσ` fusion (data file §1.1). -/
def isingSigmaZ : Fin 10 → Fin 10 → Matrix (Fin 4) (Fin 4) (ℤ√2)
  | 0, 6 => Matrix.single 2 2 sqrtd
  | 1, 7 => Matrix.single 2 3 sqrtd
  | 2, 8 => Matrix.single 2 0 1
  | 2, 9 => Matrix.single 2 1 1
  | 3, 6 => Matrix.single 3 3 sqrtd
  | 4, 7 => Matrix.single 3 2 sqrtd
  | 5, 8 => Matrix.single 3 0 1
  | 5, 9 => Matrix.single 3 1 (-1)
  | 6, 0 => Matrix.single 0 0 sqrtd
  | 6, 3 => Matrix.single 1 1 sqrtd
  | 7, 1 => Matrix.single 0 1 sqrtd
  | 7, 4 => Matrix.single 1 0 sqrtd
  | 8, 2 => Matrix.single 0 2 sqrtd
  | 8, 5 => Matrix.single 1 2 sqrtd
  | 9, 2 => Matrix.single 0 3 sqrtd
  | 9, 5 => Matrix.single 1 3 (-sqrtd)
  | _, _ => 0

/-- The tensor `A_1` as a matrix product operator tensor. -/
noncomputable def isingOne : MPOTensor 10 3 := fun h h' => complexOfZsqrt2 (isingOneZ h h')

/-- The tensor `A_ψ` as a matrix product operator tensor. -/
noncomputable def isingPsi : MPOTensor 10 3 := fun h h' => complexOfZsqrt2 (isingPsiZ h h')

/-- The tensor `√2 A_σ` as a matrix product operator tensor. -/
noncomputable def isingSigma : MPOTensor 10 4 :=
  fun h h' => complexOfZsqrt2 (isingSigmaZ h h')

/-- The letter `((1,1,1), (σ,1,σ))` of `√2 A_σ` is `√2` times the matrix unit at
`((σ,1), (σ,1))` (data file §1.1). -/
theorem isingSigma_apply_zero_six :
    isingSigma 0 6 = (Real.sqrt 2 : ℂ) • Matrix.single 2 2 1 := by
  ext p q
  simp only [isingSigma, isingSigmaZ, complexOfZsqrt2_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp

theorem isingOneZ_eq_zero_of_rho_ne :
    ∀ h h' : Fin 10, isingRho h ≠ isingRho h' → isingOneZ h h' = 0 := by
  decide +kernel

theorem isingPsiZ_eq_zero_of_rho_ne :
    ∀ h h' : Fin 10, isingRho h ≠ isingRho h' → isingPsiZ h h' = 0 := by
  decide +kernel

theorem isingSigmaZ_eq_zero_of_rho_ne :
    ∀ h h' : Fin 10, isingRho h ≠ isingRho h' → isingSigmaZ h h' = 0 := by
  decide +kernel

/-! ### Normality of the three tensors

Each tensor realises every matrix unit of its bond algebra as a nonzero multiple of one of its
letters (data file §1.1, check 1b), so it is normal at blocking length one. The pair-alphabet
letter of the pair `(h, h')` is `10 h + h'`.
-/

/-- The letter of `A_1` realising each matrix unit of the three-by-three bond algebra. -/
def isingOneUnitLetter : Fin 3 → Fin 3 → Fin 100 :=
  ![![0, 11, 22], ![44, 33, 55], ![88, 99, 66]]

/-- The letter of `A_ψ` realising each matrix unit of the three-by-three bond algebra. -/
def isingPsiUnitLetter : Fin 3 → Fin 3 → Fin 100 :=
  ![![30, 41, 52], ![14, 3, 25], ![98, 89, 66]]

/-- The letter of `√2 A_σ` realising each matrix unit of the four-by-four bond algebra. -/
def isingSigmaUnitLetter : Fin 4 → Fin 4 → Fin 100 :=
  ![![60, 71, 82, 92], ![74, 63, 85, 95], ![28, 29, 6, 17], ![58, 59, 47, 36]]

/-- The nonzero factor relating that letter of `√2 A_σ` to its matrix unit. -/
def isingSigmaUnitCoef : Fin 4 → Fin 4 → ℤ√2 :=
  ![![sqrtd, sqrtd, sqrtd, sqrtd], ![sqrtd, sqrtd, sqrtd, -sqrtd], ![1, 1, sqrtd, sqrtd],
    ![1, -1, sqrtd, sqrtd]]

private theorem isingOneZ_unit (x y : Fin 3) :
    isingOneZ (Fin.divNat (m := 10) (n := 10) (isingOneUnitLetter x y))
      (Fin.modNat (m := 10) (n := 10) (isingOneUnitLetter x y)) =
      (1 : ℤ√2) • Matrix.single x y 1 := by
  revert x y
  decide +kernel

private theorem isingPsiZ_unit (x y : Fin 3) :
    isingPsiZ (Fin.divNat (m := 10) (n := 10) (isingPsiUnitLetter x y))
      (Fin.modNat (m := 10) (n := 10) (isingPsiUnitLetter x y)) =
      (1 : ℤ√2) • Matrix.single x y 1 := by
  revert x y
  decide +kernel

private theorem isingSigmaZ_unit (x y : Fin 4) :
    isingSigmaZ (Fin.divNat (m := 10) (n := 10) (isingSigmaUnitLetter x y))
      (Fin.modNat (m := 10) (n := 10) (isingSigmaUnitLetter x y)) =
      isingSigmaUnitCoef x y • Matrix.single x y 1 := by
  revert x y
  decide +kernel

/-- **`A_1` is normal at blocking length one** (data file §1.1, check 1b). -/
theorem isingOne_isNormal : Kraus.IsNormal isingOne.toMPSTensor :=
  isNormal_of_single_eq_smul_zsqrt2 (fun a => isingOneZ (Fin.divNat (m := 10) (n := 10) a)
      (Fin.modNat (m := 10) (n := 10) a)) (fun _ => rfl)
    isingOneUnitLetter (fun _ _ => 1) (fun _ _ => one_ne_zero) isingOneZ_unit

/-- **`A_ψ` is normal at blocking length one** (data file §1.1, check 1b). -/
theorem isingPsi_isNormal : Kraus.IsNormal isingPsi.toMPSTensor :=
  isNormal_of_single_eq_smul_zsqrt2 (fun a => isingPsiZ (Fin.divNat (m := 10) (n := 10) a)
      (Fin.modNat (m := 10) (n := 10) a)) (fun _ => rfl)
    isingPsiUnitLetter (fun _ _ => 1) (fun _ _ => one_ne_zero) isingPsiZ_unit

/-- **`√2 A_σ` is normal at blocking length one**: its sixteen nonzero letters are scaled
matrix units covering every position of the four-by-four matrix algebra (data file §1.1,
check 1b). -/
theorem isingSigma_isNormal : Kraus.IsNormal isingSigma.toMPSTensor :=
  isNormal_of_single_eq_smul_zsqrt2 (fun a => isingSigmaZ (Fin.divNat (m := 10) (n := 10) a)
      (Fin.modNat (m := 10) (n := 10) a)) (fun _ => rfl)
    isingSigmaUnitLetter isingSigmaUnitCoef (by decide) isingSigmaZ_unit

end IsingTwist
