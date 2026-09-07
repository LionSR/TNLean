/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.SpinCover.Basic
import TNLean.MPS.MPDO.CZXTensor
import TNLean.MPS.MPDO.PhysicalAdjoint

/-!
# The explicit CZX dagger gauge

For the exact shared tensor of arXiv:2502.20257, `eq:MPU_CZX`, the adjoint
calculation in lines 4547–4559 gives the virtual gauge `T_g = Y` and sign
`σ_g = -1`. Here `Y` is the existing Pauli matrix `SpinCover.pauli 1`.
The physical adjoint swaps physical indices and conjugates entries; it does
not transpose virtual indices. No scalar prefactor is needed.

We exhibit an admissible unitary gauge, not an equality with the generic
choice-selected dagger-inverse gauge. The subsequent decompositions in
lines 4560–4659, local action, fusion, and anomaly symbols are not treated.
-/

noncomputable section

open scoped Matrix

namespace MPOTensor.CZX

/-- The explicit virtual gauge `T_g = Y` in arXiv:2502.20257, lines 4547–4559. -/
def daggerGauge : Matrix (Fin 2) (Fin 2) ℂ := SpinCover.pauli 1

/-- The CZX dagger gauge is Hermitian, as used in the adjoint diagram of
arXiv:2502.20257, lines 4547–4559. -/
@[simp] theorem daggerGauge_conjTranspose : daggerGaugeᴴ = daggerGauge := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [daggerGauge, SpinCover.pauli_one, Matrix.conjTranspose_apply]

/-- The Pauli gauge squares to the identity (arXiv:2502.20257, lines 4547–4559). -/
@[simp] theorem daggerGauge_mul_self : daggerGauge * daggerGauge = 1 :=
  SpinCover.pauli_mul_eq 1 1

/-- The displayed gauge is unitary, hence admissible for the dagger-inverse
convention of `eq:defT` (arXiv:2502.20257, lines 1552–1557 and 4547–4559). -/
theorem daggerGauge_mem_unitaryGroup :
    daggerGauge ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    daggerGauge_conjTranspose, daggerGauge_mul_self]

/-- The exact adjoint diagram of arXiv:2502.20257, lines 4547–4559:
physical adjunction is conjugation by `Y`, with no extra scalar. -/
theorem physicalAdjointTensor_tensor (u v : Fin 4) :
    physicalAdjointTensor tensor u v = daggerGauge * tensor u v * daggerGauge := by
  have hc : ∀ j : Fin 4, complementSite j = j.rev := by decide
  have hb : ∀ i : Fin 4, siteBits i =
      (show ZMod 2 from Fin.divNat (m := 2) (n := 2) i,
        show ZMod 2 from Fin.modNat (m := 2) (n := 2) i) := by decide
  ext l r
  simp only [physicalAdjointTensor_apply, Matrix.mul_apply, Fin.sum_univ_two,
    tensor_apply, hc, edgeExponent, hb]
  fin_cases u <;> fin_cases v <;> fin_cases l <;> fin_cases r <;>
    norm_num [daggerGauge, SpinCover.pauli_one, Fin.divNat, Fin.modNat, Fin.rev,
      ZMod.val]

/-- An explicit unitary witness for the dagger-inverse equation `eq:defT`,
specialized to CZX (`g = g⁻¹`), arXiv:2502.20257, lines 4547–4559. -/
def daggerGaugeUnitary : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨daggerGauge, daggerGauge_mem_unitaryGroup⟩

/-- The CZX witness satisfies the generic convention `Tᴴ B T`, without
identifying it with any choice-selected gauge (arXiv:2502.20257, `eq:defT`
and lines 4547–4559). -/
theorem physicalAdjointTensor_tensor_eq_unitaryGauge (u v : Fin 4) :
    physicalAdjointTensor tensor u v =
      (daggerGaugeUnitary : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * tensor u v *
        (daggerGaugeUnitary : Matrix (Fin 2) (Fin 2) ℂ) := by
  change physicalAdjointTensor tensor u v = daggerGaugeᴴ * tensor u v * daggerGauge
  rw [daggerGauge_conjTranspose, physicalAdjointTensor_tensor]

/-- Entrywise conjugation negates `Y` (arXiv:2502.20257, lines 4547–4559). -/
theorem daggerGauge_map_star : daggerGauge.map (starRingEnd ℂ) = -daggerGauge := by
  rw [daggerGauge, SpinCover.pauli_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

/-- The explicit CZX sign is `σ_g = -1`, in the entrywise-conjugation
convention of `eq:intro_sigma` (arXiv:2502.20257, lines 4547–4559). -/
theorem daggerGauge_mul_map_star :
    daggerGauge * daggerGauge.map (starRingEnd ℂ) = (-1 : ℂ) • 1 := by
  rw [daggerGauge_map_star, Matrix.mul_neg, daggerGauge_mul_self, neg_one_smul]

end MPOTensor.CZX
