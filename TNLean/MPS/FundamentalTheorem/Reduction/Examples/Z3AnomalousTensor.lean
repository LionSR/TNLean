/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.EisensteinCertificates
import TNLean.MPS.MPDO.OperatorFromWordTrace

/-!
# The anomalous `ℤ/3` matrix product operator symmetry

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section IV.D,
`Papers/2405.00439/MPU-DW.tex` lines 2038–2068: the three-cocycles
`ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}` label the classes of matrix product unitary
representations of `ℤ_n` (line 2040), with the `n = 3` interchange table (lines 2046–2054).
The paper prints no `ℤ₃` tensor. The tensors below are representatives constructed in this
development of the class `j = 1` of that formula; the group family and its operator laws are in
`Z3AnomalousRepresentation`.

This file sets up the tensors of the anomalous `ℤ/3` example of the multi-block asymmetric
compression theorem (P5 note, `Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`,
§7.5, Theorem 7.7; planning note `Notes/OpenProblemsTN/checks/p5_examples_plan_2026-09-17.md`).
The exact data and its verification in exact arithmetic over `ℤ[ω]` are recorded in
`Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`, §1–§2, and
`Notes/OpenProblemsTN/checks/asym_z3_anomalous_verify.py`.

On a periodic chain of `L` qutrits the symmetry is the phase-decorated shift
`U = X^{⊗ L} ∏_k ω^{[s_k ≠ 0] s_{k+1}}`, where `X|s⟩ = |s + 1⟩` and `ω = e^{2πi/3}`: a matrix
product operator of bond dimension two with tensor `M^{s+1, s} = c_s e_{[s ≠ 0]}ᵀ`,
`c_s = (1, ω^s)ᵀ`, that satisfies `U³ = 1` exactly at every length. Together with the identity
and the inverse `U† = U² = U⁻¹` it is an exact representation of `ℤ/3`. In this file `U†`
is defined as the group inverse, and the statements proved about it are `U U† = U† U = 1` and
`U³ = 1` at every positive length. Unitarity of `U`, which identifies `U†` with the adjoint of
`U`, is proved in `Z3AnomalousUnitary.lean` (`mpo_uTensor_mem_unitaryGroup`,
`mpo_uDagTensor_mem_unitaryGroup`, `mpo_uDagTensor_eq_conjTranspose`). The representation is
anomalous: the
class of its restricted operators in `H³(ℤ/3, U(1)) = ℤ/3` is the generator `j = 1`, certified
in the verification script in two independent exact ways (the Else–Nayak cocycle of the
restricted operators, and the associator of the fusion tensors of the compression data), against
the `ℤ/n` cocycle formula `ω_j(a, b, c) = exp(2πi j a (b + c - [b + c]) / n²)` of arXiv:2405.00439
(the paper prints no `ℤ/3` tensor; the tensor here is the phase-decorated shift built from that
formula). The Lean development does not formalize the anomaly itself; it formalizes the
compression data of the four stacked products `U_g ⊗ U_h`, the absence of sitewise
intertwiners, and the condensation defect `1 ⊕ U ⊕ U†` whose square is `3` times itself.

Every entry of every tensor, gauge and inverse gauge lies in the Eisenstein integers `ℤ[ω]`,
so the tensors are defined as entrywise images of matrices over `ℤ[ω]` and all later
verifications are decided over that ring. An Eisenstein integer is written in the coordinates
`⟨c₀, c₁⟩` of `c₀ + c₁ ω`, so `ω² = ⟨-1, -1⟩`.

## Main definitions

* `Z3Anomalous.uEis`, `Z3Anomalous.uDagEis`, `Z3Anomalous.identityEis`: the tensors of `U`,
  `U†` and the identity over `ℤ[ω]`, of bond dimensions two, two and one.
* `Z3Anomalous.uTensor`, `Z3Anomalous.uDagTensor`, `Z3Anomalous.identityTensor`: the same as
  matrix product operator tensors; `Z3Anomalous.uMPS`, `Z3Anomalous.uDagMPS`,
  `Z3Anomalous.identityMPS`: the pair-alphabet views over `Fin 9`.
* `Z3Anomalous.uuStack`, `Z3Anomalous.udStack`, `Z3Anomalous.duStack`,
  `Z3Anomalous.ddStack`: the stacked product tensors of `U ⊗ U`, `U ⊗ U†`, `U† ⊗ U`, `U† ⊗ U†`,
  of bond dimension four.

## Main results

* `Z3Anomalous.uMPS_isNBlkInjective_two`, `Z3Anomalous.uDagMPS_isNBlkInjective_two`,
  `Z3Anomalous.identityMPS_isNBlkInjective_one`: the three blocks are injective after blocking
  two, two and one sites.
* `Z3Anomalous.uMPS_isNormal`, `Z3Anomalous.uDagMPS_isNormal`,
  `Z3Anomalous.identityMPS_isNormal`: hence they are normal.
* `Z3Anomalous.mpo_identityTensor`: the periodic operator of the identity tensor is the
  identity operator at every length.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*

## Provenance
The tensors and the exact-arithmetic certificates were first recorded in
`Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`, §1–§2; they are verification records,
not the source.
-/

noncomputable section

open scoped Matrix

namespace Z3Anomalous

open EisensteinInt MPSTensor

/-! ### The three blocks -/

/-- The tensor of the anomalous `ℤ/3` symmetry `U` over `ℤ[ω]` (data file §2.0): the letter
`(s + 1, s)` carries the column `(1, ω^s)ᵀ` in position `[s ≠ 0]`, all other letters vanish. -/
def uEis : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 2) EisensteinInt
  | 1, 0 => !![1, 0; 1, 0]
  | 2, 1 => !![0, 1; 0, omega]
  | 0, 2 => !![0, 1; 0, omega ^ 2]
  | _, _ => 0

/-- The tensor of `U† = U²` over `ℤ[ω]` (data file §2.0): the letter `(s, s + 1)` carries the
column `(1, ω^{-s})ᵀ` in position `[s ≠ 0]`. -/
def uDagEis : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 2) EisensteinInt
  | 0, 1 => !![1, 0; 1, 0]
  | 1, 2 => !![0, 1; 0, omega ^ 2]
  | 2, 0 => !![0, 1; 0, omega]
  | _, _ => 0

/-- The tensor of the identity operator over `ℤ[ω]`, of bond dimension one. -/
def identityEis : Fin 3 → Fin 3 → Matrix (Fin 1) (Fin 1) EisensteinInt :=
  fun i j => if i = j then 1 else 0

/-- The symmetry `U` as a matrix product operator tensor. -/
def uTensor : MPOTensor 3 2 := fun i j => complexOfEisenstein (uEis i j)

/-- The inverse symmetry `U†` as a matrix product operator tensor. -/
def uDagTensor : MPOTensor 3 2 := fun i j => complexOfEisenstein (uDagEis i j)

/-- The identity operator as a matrix product operator tensor of bond dimension one. -/
def identityTensor : MPOTensor 3 1 := fun i j => complexOfEisenstein (identityEis i j)

/-- The symmetry `U` read as a tensor over the pair alphabet `Fin 9`, letter `a = 3 i + j` with
`i` the output and `j` the input label. -/
def uMPS : MPSTensor 9 2 := uTensor.toMPSTensor

/-- The inverse symmetry `U†` read as a tensor over the pair alphabet `Fin 9`. -/
def uDagMPS : MPSTensor 9 2 := uDagTensor.toMPSTensor

/-- The identity tensor `δ` read as a tensor over the pair alphabet `Fin 9`. -/
def identityMPS : MPSTensor 9 1 := identityTensor.toMPSTensor

/-- The Eisenstein matrices of the pair-alphabet symmetry `U`. -/
def uEisMPS : Fin 9 → Matrix (Fin 2) (Fin 2) EisensteinInt :=
  fun a => uEis (Fin.divNat (m := 3) (n := 3) a) (Fin.modNat (m := 3) (n := 3) a)

/-- The Eisenstein matrices of the pair-alphabet inverse symmetry `U†`. -/
def uDagEisMPS : Fin 9 → Matrix (Fin 2) (Fin 2) EisensteinInt :=
  fun a => uDagEis (Fin.divNat (m := 3) (n := 3) a) (Fin.modNat (m := 3) (n := 3) a)

/-- The Eisenstein matrices of the pair-alphabet identity tensor. -/
def identityEisMPS : Fin 9 → Matrix (Fin 1) (Fin 1) EisensteinInt :=
  fun a => identityEis (Fin.divNat (m := 3) (n := 3) a) (Fin.modNat (m := 3) (n := 3) a)

theorem uMPS_eq (a : Fin 9) : uMPS a = complexOfEisenstein (uEisMPS a) := rfl

theorem uDagMPS_eq (a : Fin 9) : uDagMPS a = complexOfEisenstein (uDagEisMPS a) := rfl

theorem identityMPS_eq (a : Fin 9) : identityMPS a = complexOfEisenstein (identityEisMPS a) :=
  rfl

/-- The letter `(1, 0)` of `U` carries the column `(1, 1)ᵀ` in position zero (data file
§2.0). -/
theorem uMPS_apply_three : uMPS 3 = !![1, 0; 1, 0] := by
  rw [show uMPS 3 = complexOfEisenstein !![1, 0; 1, 0] from rfl]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [complexOfEisenstein]

/-- The letter `(2, 1)` of `U` carries the column `(1, ω)ᵀ` in position one (data file §2.0). -/
theorem uMPS_apply_seven : uMPS 7 = !![0, 1; 0, eisensteinOmega] := by
  rw [show uMPS 7 = complexOfEisenstein !![0, 1; 0, omega] from rfl]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [complexOfEisenstein]

/-- The letter `(0, 2)` of `U` carries the column `(1, ω²)ᵀ` in position one (data file
§2.0). -/
theorem uMPS_apply_two : uMPS 2 = !![0, 1; 0, eisensteinOmega ^ 2] := by
  rw [show uMPS 2 = complexOfEisenstein !![0, 1; 0, omega ^ 2] from rfl]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [complexOfEisenstein]

/-! ### Normality of the three blocks

`U` and `U†` are normal at word length two (data file §2.0): four length-two words combine,
with coefficients in `ℤ[ω]`, to `(ω - 1)` times each matrix unit, and `ω - 1 ≠ 0`. The scaling
is unavoidable over `ℤ[ω]`, since the columns `(1, 1)ᵀ` and `(1, ω)ᵀ` of the letters span the
matrix units only after division by `ω - 1`, which is not a unit. The identity tensor is normal
at length one.
-/

/-- The four length-two words of `U` used to span the two-by-two matrix algebra: the letters
`2 = (0, 2)` and `3 = (1, 0)` in every order. -/
def uUnitWord : Fin 4 → Fin 2 → Fin 9 := ![![2, 2], ![2, 3], ![3, 2], ![3, 3]]

/-- The coefficients expressing `(ω - 1) E_{ij}` as a combination of the words `uUnitWord`. -/
def uUnitCoeff : Fin 2 → Fin 2 → Fin 4 → EisensteinInt
  | 0, 0 => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]
  | 0, 1 => ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]
  | 1, 0 => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩]
  | 1, 1 => ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]

/-- The four length-two words of `U†` used to span the two-by-two matrix algebra: the letters
`1 = (0, 1)` and `5 = (1, 2)` in every order. -/
def uDagUnitWord : Fin 4 → Fin 2 → Fin 9 := ![![1, 1], ![1, 5], ![5, 1], ![5, 5]]

/-- The coefficients expressing `(ω - 1) E_{ij}` as a combination of the words `uDagUnitWord`. -/
def uDagUnitCoeff : Fin 2 → Fin 2 → Fin 4 → EisensteinInt
  | 0, 0 => ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]
  | 0, 1 => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]
  | 1, 0 => ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]
  | 1, 1 => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]

private theorem uUnit_single (i j : Fin 2) :
    ∑ k, uUnitCoeff i j k • evalWordEisenstein uEisMPS (List.ofFn (uUnitWord k)) =
      (omega - 1) • Matrix.single i j 1 := by
  revert i j
  decide +kernel

private theorem uDagUnit_single (i j : Fin 2) :
    ∑ k, uDagUnitCoeff i j k • evalWordEisenstein uDagEisMPS (List.ofFn (uDagUnitWord k)) =
      (omega - 1) • Matrix.single i j 1 := by
  revert i j
  decide +kernel

private theorem identityUnit_single (i j : Fin 1) :
    ∑ k : Fin 1, (1 : EisensteinInt) •
        evalWordEisenstein identityEisMPS (List.ofFn (![![0]] k)) =
      (1 : EisensteinInt) • Matrix.single i j 1 := by
  revert i j
  decide +kernel

/-- **The symmetry `U` is injective after blocking two sites.** Its length-two words span the
full two-by-two matrix algebra (data file §2.0). -/
theorem uMPS_isNBlkInjective_two : Kraus.IsNBlkInjective uMPS 2 :=
  isNBlkInjective_of_scaled_single uEisMPS uMPS_eq (fun _ _ => uUnitWord) uUnitCoeff
    omega_sub_one_ne_zero uUnit_single

/-- **The inverse symmetry `U†` is injective after blocking two sites.** Its length-two words
span the full two-by-two matrix algebra (data file §2.0). -/
theorem uDagMPS_isNBlkInjective_two : Kraus.IsNBlkInjective uDagMPS 2 :=
  isNBlkInjective_of_scaled_single uDagEisMPS uDagMPS_eq (fun _ _ => uDagUnitWord)
    uDagUnitCoeff omega_sub_one_ne_zero uDagUnit_single

/-- **The identity tensor is injective** at word length one. -/
theorem identityMPS_isNBlkInjective_one : Kraus.IsNBlkInjective identityMPS 1 :=
  isNBlkInjective_of_scaled_single identityEisMPS identityMPS_eq (fun _ _ => ![![0]])
    (fun _ _ _ => 1) (by decide) identityUnit_single

/-- **The symmetry `U` is normal**, at word length two. -/
theorem uMPS_isNormal : Kraus.IsNormal uMPS := ⟨2, two_pos, uMPS_isNBlkInjective_two⟩

/-- **The inverse symmetry `U†` is normal**, at word length two. -/
theorem uDagMPS_isNormal : Kraus.IsNormal uDagMPS := ⟨2, two_pos, uDagMPS_isNBlkInjective_two⟩

/-- **The identity tensor is normal** at word length one. -/
theorem identityMPS_isNormal : Kraus.IsNormal identityMPS :=
  ⟨1, one_pos, identityMPS_isNBlkInjective_one⟩

/-! ### The stacked product tensors -/

/-- The stacked product tensor of `U ⊗ U`, of bond dimension four (data file §2.1). -/
def uuStack : MPSTensor 9 4 := (MPOTensor.mulTensor uTensor uTensor).toMPSTensor

/-- The stacked product tensor of `U ⊗ U†`, of bond dimension four (data file §2.2). -/
def udStack : MPSTensor 9 4 := (MPOTensor.mulTensor uTensor uDagTensor).toMPSTensor

/-- The stacked product tensor of `U† ⊗ U`, of bond dimension four (data file §2.3). -/
def duStack : MPSTensor 9 4 := (MPOTensor.mulTensor uDagTensor uTensor).toMPSTensor

/-- The stacked product tensor of `U† ⊗ U†`, of bond dimension four (data file §2.4). -/
def ddStack : MPSTensor 9 4 := (MPOTensor.mulTensor uDagTensor uDagTensor).toMPSTensor

/-- The Eisenstein matrices of the stacked product tensor of `U ⊗ U`, in the bond order
`2 p₁ + p₂`. -/
def uuStackEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt :=
  fun a => mulEisensteinTensor uEis uEis (Fin.divNat (m := 3) (n := 3) a)
    (Fin.modNat (m := 3) (n := 3) a)

/-- The Eisenstein matrices of the stacked product tensor of `U ⊗ U†`. -/
def udStackEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt :=
  fun a => mulEisensteinTensor uEis uDagEis (Fin.divNat (m := 3) (n := 3) a)
    (Fin.modNat (m := 3) (n := 3) a)

/-- The Eisenstein matrices of the stacked product tensor of `U† ⊗ U`. -/
def duStackEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt :=
  fun a => mulEisensteinTensor uDagEis uEis (Fin.divNat (m := 3) (n := 3) a)
    (Fin.modNat (m := 3) (n := 3) a)

/-- The Eisenstein matrices of the stacked product tensor of `U† ⊗ U†`. -/
def ddStackEis : Fin 9 → Matrix (Fin 4) (Fin 4) EisensteinInt :=
  fun a => mulEisensteinTensor uDagEis uDagEis (Fin.divNat (m := 3) (n := 3) a)
    (Fin.modNat (m := 3) (n := 3) a)

theorem uuStack_eq (a : Fin 9) : uuStack a = complexOfEisenstein (uuStackEis a) :=
  mulTensor_complexOfEisenstein uEis uEis _ _

theorem udStack_eq (a : Fin 9) : udStack a = complexOfEisenstein (udStackEis a) :=
  mulTensor_complexOfEisenstein uEis uDagEis _ _

theorem duStack_eq (a : Fin 9) : duStack a = complexOfEisenstein (duStackEis a) :=
  mulTensor_complexOfEisenstein uDagEis uEis _ _

theorem ddStack_eq (a : Fin 9) : ddStack a = complexOfEisenstein (ddStackEis a) :=
  mulTensor_complexOfEisenstein uDagEis uDagEis _ _

/-! ### The identity operator -/

/-- The two-word evaluation of the identity tensor is the one-by-one identity when the two
configurations agree and zero otherwise. -/
theorem evalWord_identityTensor {L : ℕ} (σ τ : Fin L → Fin 3) :
    MPOTensor.evalWord identityTensor (List.ofFn σ) (List.ofFn τ) = if σ = τ then 1 else 0 := by
  induction L with
  | zero => simp [Subsingleton.elim σ τ]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, MPOTensor.evalWord_cons, ih]
    have h1 : identityTensor (σ 0) (τ 0) = if σ 0 = τ 0 then 1 else 0 := by
      simp only [identityTensor, identityEis]
      split_ifs <;> simp [complexOfEisenstein_one, complexOfEisenstein_zero]
    rw [h1]
    by_cases h0 : σ 0 = τ 0
    · by_cases hs : (fun i : Fin n => σ i.succ) = fun i : Fin n => τ i.succ
      · have hστ : σ = τ := by
          funext i
          exact Fin.cases h0 (fun i => congrFun hs i) i
        simp [hστ]
      · have hστ : σ ≠ τ := fun h => hs (by rw [h])
        simp [h0, hs, hστ]
    · have hστ : σ ≠ τ := fun h => h0 (by rw [h])
      simp [h0, hστ]

/-- **The periodic operator of the identity tensor is the identity** at every length. -/
theorem mpo_identityTensor (L : ℕ) : MPOTensor.mpo identityTensor L = 1 := by
  ext σ τ
  rw [MPOTensor.mpo_apply, MPOTensor.mpoMatrixEntry, evalWord_identityTensor, Matrix.one_apply]
  split_ifs <;> simp

end Z3Anomalous
