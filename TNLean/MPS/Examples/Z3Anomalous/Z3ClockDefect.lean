/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Z3Anomalous.Z3ClockTensor
import TNLean.MPS.MPDO.DirectSum
import TNLean.MPS.MPDO.IdentityTensor
import TNLean.MPS.MPU.GroupCocycleMPO.FusionAlgebra

/-!
# Non-anomalous `ℤ₃` clock symmetry: the condensation defect and its length-dependent fusion

**Source.** Construction of this development; no source prints the `ℤ₃` clock tensors or the
defect below. Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), lines 361–362 of
`Papers/2203.12563/REsubmission.tex`: the periodic operators of a matrix product operator
algebra satisfy `O_a O_b = ∑_c N_{ab}^c O_c` with nonnegative integers `N_{ab}^c` independent of
the system size; lines 2202–2224: the periodic representation of a finite group built from a
three-cocycle. Garre-Rubio, Schuch 2024 (arXiv:2405.00439), `Papers/2405.00439/MPU-DW.tex`
line 2040: the three-cocycles `ω_j` of `ℤ_n`, `j = 0` being the trivial class.

**Formalized here.** The condensation defect `A = 1 ⊕ U ⊕ V` of the clock symmetry of
`Z3ClockTensor` is the block-diagonal tensor of bond dimension seven; its periodic operator is
`1 + U + V`. On every periodic chain of length `L ≥ 1`,
`A² = (1 + 2ω^L) 1 + 3 U + (2 + ω^L) V`,
with `ω = exp(2πi/3)`: the coefficients are the power sums of the weight multisets
`{1, ω, ω}`, `{1, 1, 1}` and `{1, 1, ω}`. Since `1`, `U` and `V` are linearly independent, the
coefficients are determined by `L`, and they genuinely depend on it: `A² = 3A` holds exactly
when `3 ∣ L`, and no length-independent coefficients exist. Equivalently, the family
`{1, U, V}` is not a matrix product operator fusion algebra in the sense of arXiv:2203.12563,
lines 361–362, for any structure constants.

This contrasts with the anomalous `ℤ₃` symmetry, whose defect satisfies `A² = 3A` at every
length (`Z3Anomalous.mpo_defect_mul_defect`), and with the exact representation of the
trivial-cocycle construction, whose defect `A₀ = ∑_g U_g` satisfies `A₀² = 3A₀` at every length
(`Z3Clock.cocycleDefect_mul_self`, an instance of
`MPOTensor.GroupCocycle.sum_mpo_mul_sum_mpo`). The clock symmetry is not anomalous, so the
length dependence is not an anomaly signature: it comes from the per-site phases of the chosen
representatives, `U² = ω^L V`, `U V = V U = ω^L`.

The multi-block compression of the stacked square `A ⊗ A` (bond dimension forty-nine) recorded
in the data file is not formalized here; the fusion identity is proved at the level of periodic
operators from the multiplication table of `Z3ClockTensor`.

## Main definitions

* `Z3Clock.defectTensor`: the condensation defect `1 ⊕ U ⊕ V`.
* `Z3Clock.repBondDim`, `Z3Clock.repTensor`: the family `{1, U, V}` indexed by residues.
* `Z3Clock.cocycleDefect`: the defect `∑_g U_g` of the trivial-cocycle construction.

## Main results

* `Z3Clock.mpo_defectTensor`: `A = 1 + U + V`.
* `Z3Clock.mpo_defect_mul_defect`: `A² = (1 + 2ω^L) 1 + 3 U + (2 + ω^L) V`.
* `Z3Clock.eq_of_smul_add_smul_add_smul_eq`: the coefficients on `1, U, V` are unique.
* `Z3Clock.mpo_defect_mul_defect_eq_three_smul_iff`: `A² = 3A` if and only if `3 ∣ L`.
* `Z3Clock.not_exists_const_defect_coeff`: no length-independent structure constants.
* `Z3Clock.not_isMPOFusionAlgebra`: `{1, U, V}` is not a fusion algebra.
* `Z3Clock.cocycleDefect_mul_self`: `A₀² = 3A₀` for the trivial-cocycle construction.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*

## Provenance
The defect, the identity `A² = (1 + 2ω^L) 1 + 3 U + (2 + ω^L) V` and the compression data of its
stacked square were first recorded in `Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`,
§0 and §3.5, and checked over `ℤ[ω]` by `Notes/OpenProblemsTN/checks/asym_z3_anomalous_verify.py`;
they are verification records, not the source.
-/

noncomputable section

open scoped BigOperators Matrix

namespace Z3Clock

open MPOTensor TNLean.Algebra TNLean.Algebra.ScalarThreeCochain

/-! ### The defect -/

/-- **The condensation defect `A = 1 ⊕ U ⊕ V`**: the block-diagonal tensor of bond dimension
`1 + 3 + 3` (data file §3.5). -/
def defectTensor : MPOTensor 3 (1 + 3 + 3) :=
  directSum (directSum (idTensor 3) uTensor) vTensor

/-- **The defect is the sum of the three operators**, `A = 1 + U + V`, at every length. -/
theorem mpo_defectTensor (L : ℕ) : mpo defectTensor L = 1 + mpo uTensor L + mpo vTensor L := by
  rw [defectTensor, mpo_directSum, mpo_directSum, mpo_idTensor]

/-- **The fusion of the condensation defect of the clock symmetry**: on every periodic chain of
length `L ≥ 1`, `A² = (1 + 2ω^L) 1 + 3 U + (2 + ω^L) V` (data file §0 and §3.5). -/
theorem mpo_defect_mul_defect (L : ℕ) (hL : 0 < L) :
    mpo defectTensor L * mpo defectTensor L =
      (1 + 2 * omega ^ L) • (1 : Matrix _ _ ℂ) + (3 : ℂ) • mpo uTensor L +
        (2 + omega ^ L) • mpo vTensor L := by
  have : NeZero L := ⟨by omega⟩
  rw [mpo_defectTensor]
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, mpo_u_mul_u, mpo_u_mul_v,
    mpo_v_mul_u, mpo_v_mul_v]
  module

/-! ### Uniqueness of the coefficients -/

section Coefficients

variable {L : ℕ} [NeZero L]

/-- The entry of a clock operator in the column of the constant configuration `0` and the row
of the constant configuration `a`: it is one if `a` is the shift and zero otherwise. -/
theorem mpo_clockTensor_apply_const (g a : Fin 3) {f : Fin 3 → Fin 3 → Fin 3} (hf : f 0 0 = 0) :
    mpo (clockTensor g f) L (fun _ ↦ a) (fun _ ↦ 0) = if a = g then 1 else 0 := by
  have hiff : ((fun _ ↦ a : Fin L → Fin 3) = clockShift g L fun _ ↦ 0) ↔ a = g := by
    simp only [funext_iff, clockShift_apply, zero_add]
    exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩
  rw [mpo_clockTensor, Matrix.monomial_apply]
  simp only [hiff, clockPhase, hf, Finset.sum_const_zero, AddChar.map_zero_eq_one]

/-- The combination `a 1 + b U + c V` read at the constant configurations: the coefficient of
the operator that shifts `0` to `x`. -/
theorem smul_add_smul_add_smul_apply_const (a b c : ℂ) (x : Fin 3) :
    (a • (1 : Matrix (Fin L → Fin 3) (Fin L → Fin 3) ℂ) + b • mpo uTensor L + c • mpo vTensor L)
      (fun _ ↦ x) (fun _ ↦ 0) = ![a, b, c] x := by
  have h1 : ((1 : Matrix (Fin L → Fin 3) (Fin L → Fin 3) ℂ) (fun _ ↦ x) fun _ ↦ 0) =
      if x = 0 then 1 else 0 := by
    simp only [Matrix.one_apply, funext_iff]
    exact if_congr ⟨fun h ↦ h 0, fun h _ ↦ h⟩ rfl rfl
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h1, uTensor, vTensor,
    mpo_clockTensor_apply_const _ _ (show uWeight 0 0 = 0 by decide),
    mpo_clockTensor_apply_const _ _ (show vWeight 0 0 = 0 by decide)]
  fin_cases x <;> simp

/-- **The operators `1`, `U`, `V` are linearly independent** on every nonempty chain: the
coefficients of a combination of them are unique. -/
theorem eq_of_smul_add_smul_add_smul_eq {a b c a' b' c' : ℂ}
    (h : a • (1 : Matrix _ _ ℂ) + b • mpo uTensor L + c • mpo vTensor L =
      a' • 1 + b' • mpo uTensor L + c' • mpo vTensor L) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hx := fun x : Fin 3 ↦ congrFun (congrFun h fun _ ↦ x) fun _ ↦ 0
  simp only [smul_add_smul_add_smul_apply_const] at hx
  exact ⟨hx 0, hx 1, hx 2⟩

end Coefficients

/-- **The structure constants of the defect are determined by the length**: if
`A² = a 1 + b U + c V` on a chain of length `L ≥ 1`, then `a = 1 + 2ω^L`, `b = 3` and
`c = 2 + ω^L`. -/
theorem defect_coeff_eq {L : ℕ} (hL : 0 < L) {a b c : ℂ}
    (h : mpo defectTensor L * mpo defectTensor L =
      a • (1 : Matrix _ _ ℂ) + b • mpo uTensor L + c • mpo vTensor L) :
    a = 1 + 2 * omega ^ L ∧ b = 3 ∧ c = 2 + omega ^ L := by
  have : NeZero L := ⟨by omega⟩
  obtain ⟨ha, hb, hc⟩ := eq_of_smul_add_smul_add_smul_eq (h.symm.trans (mpo_defect_mul_defect L hL))
  exact ⟨ha, hb, hc⟩

/-- **`A² = 3A` exactly when `3 ∣ L`**: the defect of the clock symmetry has the fusion of an
exact representation only on chains whose length is a multiple of three. -/
theorem mpo_defect_mul_defect_eq_three_smul_iff {L : ℕ} (hL : 0 < L) :
    mpo defectTensor L * mpo defectTensor L = (3 : ℂ) • mpo defectTensor L ↔ 3 ∣ L := by
  have h3 : (3 : ℂ) • mpo defectTensor L =
      (3 : ℂ) • (1 : Matrix _ _ ℂ) + (3 : ℂ) • mpo uTensor L + (3 : ℂ) • mpo vTensor L := by
    rw [mpo_defectTensor, smul_add, smul_add]
  rw [h3, ← isPrimitiveRoot_omega.pow_eq_one_iff_dvd]
  constructor
  · intro h
    have := (defect_coeff_eq hL h).2.2
    linear_combination -this
  · intro h
    rw [mpo_defect_mul_defect L hL, h]
    norm_num

/-- **The structure constants of the defect genuinely depend on the length**: there are no
coefficients `a, b, c` with `A² = a 1 + b U + c V` at every length `L ≥ 1`. This contrasts with
`A² = 3A` for the anomalous symmetry (`Z3Anomalous.mpo_defect_mul_defect`). -/
theorem not_exists_const_defect_coeff :
    ¬ ∃ a b c : ℂ, ∀ L : ℕ, 0 < L →
      mpo defectTensor L * mpo defectTensor L =
        a • (1 : Matrix _ _ ℂ) + b • mpo uTensor L + c • mpo vTensor L := by
  rintro ⟨a, b, c, h⟩
  have h1 := (defect_coeff_eq one_pos (h 1 one_pos)).2.2
  have h3 := (defect_coeff_eq three_pos (h 3 three_pos)).2.2
  rw [omega_pow_three, pow_one] at *
  exact omega_ne_one (by linear_combination h3 - h1)

/-! ### The family `{1, U, V}` is not a fusion algebra -/

/-- The bond dimensions of `1`, `U` and `V`, indexed by the residues `0, 1, 2`. -/
def repBondDim : Fin 3 → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 3

/-- The tensors of `1`, `U` and `V`, indexed by the residues `0, 1, 2`. -/
def repTensor : (a : Fin 3) → MPOTensor 3 (repBondDim a)
  | 0 => idTensor 3
  | 1 => uTensor
  | 2 => vTensor

/-- **`{1, U, V}` is not a matrix product operator fusion algebra**: no nonnegative integer
structure constants, independent of the length as required by arXiv:2203.12563, lines 361–362,
describe its products, because `U² = ω^L V` (`mpo_u_mul_u`). -/
theorem not_isMPOFusionAlgebra (Nc : Fin 3 → Fin 3 → Fin 3 → ℕ) :
    ¬ IsMPOFusionAlgebra repTensor Nc := by
  intro h
  have key : ∀ L : ℕ, 0 < L → omega ^ L = Nc 1 1 2 := by
    intro L hL
    have : NeZero L := ⟨by omega⟩
    have hL' := h 1 1 L hL
    simp only [Fin.sum_univ_three] at hL'
    change mpo uTensor L * mpo uTensor L =
      (Nc 1 1 0 : ℂ) • mpo (idTensor 3) L + (Nc 1 1 1 : ℂ) • mpo uTensor L +
        (Nc 1 1 2 : ℂ) • mpo vTensor L at hL'
    rw [mpo_idTensor, mpo_u_mul_u] at hL'
    have hc := eq_of_smul_add_smul_add_smul_eq
      ((show omega ^ L • mpo vTensor L =
        (0 : ℂ) • (1 : Matrix _ _ ℂ) + (0 : ℂ) • mpo uTensor L + omega ^ L • mpo vTensor L by
          simp).symm.trans hL')
    exact hc.2.2
  have h1 := key 1 one_pos
  have h3 := key 3 three_pos
  rw [omega_pow_three, pow_one] at *
  exact omega_ne_one (h1.trans h3.symm)

/-! ### Contrast: the defect of the trivial-cocycle construction -/

/-- The condensation defect `A₀ = ∑_g U_g` of the construction of arXiv:2203.12563, lines
2204–2222, for the trivial cocycle `ω_0` of `ℤ₃` (arXiv:2405.00439, line 2040), whose group
operators are the plain shifts. -/
def cocycleDefect (L : ℕ) : Matrix (Fin L → Fin 3) (Fin L → Fin 3) ℂ :=
  ∑ g, mpo (GroupCocycle.tensor (GroupCocycle.residueEquiv 2) (cyclicCocycle 3 0) g) L

/-- **The defect of the trivial-cocycle representation has constant structure constants**:
`A₀² = 3A₀` at every length `L ≥ 1`, an instance of `GroupCocycle.sum_mpo_mul_sum_mpo`. The
clock operators `U` and `V` are the nontrivial group operators of this construction dressed by
diagonal circuits (`mpo_uTensor_eq_cocycle`, `mpo_vTensor_eq_cocycle`), and the circuits make
the structure constants of `A = 1 + U + V` depend on the length. -/
theorem cocycleDefect_mul_self {L : ℕ} (hL : 0 < L) :
    cocycleDefect L * cocycleDefect L = (3 : ℂ) • cocycleDefect L := by
  have : NeZero L := ⟨by omega⟩
  rw [cocycleDefect, GroupCocycle.sum_mpo_mul_sum_mpo _ (cyclicCocycle_isCocycle 3 0)]
  congr 1

end Z3Clock
