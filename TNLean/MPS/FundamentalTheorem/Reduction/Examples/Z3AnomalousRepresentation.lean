/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.Z3AnomalousUnitary
import TNLean.MPS.MPU.GroupCocycleMPO.Instances

/-!
# Anomalous `ℤ₃` symmetry: the representation `{1, U, U†}` as a group family

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section IV.A,
`Papers/2405.00439/MPU-DW.tex` line 1684: a matrix product unitary representation of a finite
group is a family of operators with `U_g U_h = U_{gh}` and `U_e = 1`; Section IV.C, line 2040:
the three-cocycles `ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}` label the `n` classes of
such representations of `ℤ_n`. The paper prints no `ℤ₃` tensor.
Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), `Papers/2203.12563/REsubmission.tex`
lines 2200–2224: a periodic representation built from any three-cocycle.

**Formalized here.** The bond-two tensors `U`, `U†` and the bond-one identity tensor of
`Z3AnomalousTensor` form a group family over `ℤ₃` (written `Multiplicative (ZMod 3)`), and it
satisfies the operator laws of line 1684 at every positive chain length: every member is a
matrix product unitary, `U_e = 1`, `U_g U_h = U_{gh}` and `U_g† = U_{g⁻¹}`. The bond-two
tensors are not injective as single-site tensors, so the packaged predicate
`MPOTensor.GroupFamily.IsRawRepresentation`, which demands one-site injectivity, does not hold
(`uMPS_not_isInjective`); the laws are stated directly.

Beside it stands the representation `cocycleFamily` produced by the general construction of
arXiv:2203.12563 from the cocycle `ω_1` of line 2040, of bond dimension three. Both are exact
representations of `ℤ₃`, and the verification record below certifies the class `j = 1` for
`{1, U, U†}`; no class is computed in Lean, and no on-site gauge or other relation between the
two families is claimed.

## Main definitions

* `Z3Anomalous.repBondDim`, `Z3Anomalous.repTensor`: the three tensors indexed by residues.
* `Z3Anomalous.family`: the group family `{1, U, U†}` over `ℤ₃`.
* `Z3Anomalous.cocycleFamily`: the construction of arXiv:2203.12563 for `ω_1`.

## Main results

* `Z3Anomalous.family_operator_laws`: the operator laws of a matrix product unitary
  representation for `{1, U, U†}`.
* `Z3Anomalous.uMPS_not_isInjective`: `U` is not injective as a single-site tensor.
* `Z3Anomalous.cocycleFamily_operator_laws`: the same laws for the cocycle construction.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*

## Provenance
The tensors `U` and `U†` are representatives constructed in this development, recorded with
their exact-arithmetic checks in `Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`,
§1–§2, where the class `j = 1` of `ω_j` is certified in two independent ways; these are
verification records, not the source.
-/

noncomputable section

open scoped Matrix

namespace Z3Anomalous

open MPOTensor TNLean.Algebra

/-! ### The group family -/

/-- The bond dimensions of the identity, `U` and `U†`, indexed by the residues `0, 1, 2`. -/
def repBondDim : Fin 3 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 2

/-- The tensors of the identity, `U` and `U†`, indexed by the residues `0, 1, 2`. -/
def repTensor : (a : Fin 3) → MPOTensor 3 (repBondDim a)
  | 0 => identityTensor
  | 1 => uTensor
  | 2 => uDagTensor

/-- The group family `{1, U, U†}` over `ℤ₃`: the residue `a` carries the tensor of `U^a`.

Source: arXiv:2405.00439, line 1684 (a group-indexed family of matrix product operators). -/
def family : GroupFamily (Multiplicative (ZMod 3)) 3 where
  bondDim g := repBondDim (Multiplicative.toAdd g)
  bondDim_pos g := by
    generalize (Multiplicative.toAdd g : Fin 3) = a
    fin_cases a <;> decide
  tensor g := repTensor (Multiplicative.toAdd g)

section Laws

variable {N : ℕ}

private theorem mpo_repTensor_mul (hN : 0 < N) (a b : Fin 3) :
    mpo (repTensor a) N * mpo (repTensor b) N = mpo (repTensor (a + b)) N := by
  fin_cases a <;> fin_cases b
  · exact (mpo_identityTensor N).symm ▸ Matrix.one_mul _
  · exact (mpo_identityTensor N).symm ▸ Matrix.one_mul _
  · exact (mpo_identityTensor N).symm ▸ Matrix.one_mul _
  · exact (mpo_identityTensor N).symm ▸ Matrix.mul_one _
  · exact mpo_uu N hN
  · exact (mpo_u_mul_uDag N hN).trans (mpo_identityTensor N).symm
  · exact (mpo_identityTensor N).symm ▸ Matrix.mul_one _
  · exact (mpo_uDag_mul_u N hN).trans (mpo_identityTensor N).symm
  · exact mpo_dd N hN

private theorem mpo_repTensor_conjTranspose (hN : 0 < N) (a : Fin 3) :
    (mpo (repTensor a) N)ᴴ = mpo (repTensor (-a)) N := by
  have : NeZero N := ⟨by omega⟩
  fin_cases a
  · exact (mpo_identityTensor N).symm ▸ Matrix.conjTranspose_one
  · exact mpo_uDagTensor_eq_conjTranspose.symm
  · exact (congrArg Matrix.conjTranspose mpo_uDagTensor_eq_conjTranspose).trans
      (Matrix.conjTranspose_conjTranspose _)

private theorem repTensor_isMPUPos (a : Fin 3) : IsMPUPos (repTensor a) := by
  fin_cases a
  · intro N _
    change mpo identityTensor N ∈ _
    rw [mpo_identityTensor]
    exact one_mem _
  · exact uTensor_isMPUPos
  · exact uDagTensor_isMPUPos

/-- **`{1, U, U†}` satisfies the operator laws of a matrix product unitary representation of
`ℤ₃`** at every positive chain length: every member is a matrix product unitary, `U_e = 1`,
`U_g U_h = U_{gh}` and `U_g† = U_{g⁻¹}`. One-site injectivity, the remaining clause of
`GroupFamily.IsRawRepresentation`, fails (`uMPS_not_isInjective`).

Source: arXiv:2405.00439, line 1684 (`U_g U_h = U_{gh}`, `U_e = 1`); the adjoint law is the
consequence of unitarity and the group laws. -/
theorem family_operator_laws :
    (∀ g, IsMPUPos (family.tensor g)) ∧
      (∀ N, 0 < N → mpo (family.tensor 1) N = 1) ∧
      (∀ g h N, 0 < N →
        mpo (family.tensor g) N * mpo (family.tensor h) N = mpo (family.tensor (g * h)) N) ∧
      (∀ g N, 0 < N → (mpo (family.tensor g) N)ᴴ = mpo (family.tensor g⁻¹) N) :=
  ⟨fun g ↦ repTensor_isMPUPos (Multiplicative.toAdd g),
    fun N _ ↦ mpo_identityTensor N,
    fun g h _ hN ↦ mpo_repTensor_mul hN (Multiplicative.toAdd g) (Multiplicative.toAdd h),
    fun g _ hN ↦ mpo_repTensor_conjTranspose hN (Multiplicative.toAdd g)⟩

end Laws

/-! ### Failure of one-site injectivity -/

/-- The functional `X ↦ X₀₀ − X₁₀`, which annihilates every letter of `U`. -/
private def rowDifference : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  Matrix.entryLinearMap ℂ ℂ 0 0 - Matrix.entryLinearMap ℂ ℂ 1 0

private theorem rowDifference_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    rowDifference X = X 0 0 - X 1 0 := rfl

/-- **`U` is not injective as a single-site tensor**: every letter has equal entries in the
first column, so the nine letters span a proper subspace of the two-by-two matrices. Hence
`family` does not satisfy `GroupFamily.IsRawRepresentation`. -/
theorem uMPS_not_isInjective : ¬ Kraus.IsInjective uMPS := by
  intro h
  have hle : Submodule.span ℂ (Set.range uMPS) ≤ LinearMap.ker rowDifference := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, rowDifference_apply]
    fin_cases a <;>
      simp [uMPS, MPOTensor.toMPSTensor, uTensor_apply, occupied, Fin.divNat, Fin.modNat]
  have h1 := hle (h ▸ Submodule.mem_top (x := Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)))
  simp [rowDifference_apply] at h1

/-! ### The cocycle construction for `ω_1` -/

/-- The periodic representation of `ℤ₃` constructed in arXiv:2203.12563 from the three-cocycle
`ω_1` of arXiv:2405.00439, line 2040, of bond dimension three. It is an exact representation
in the class `j = 1`, as is `family`; no on-site gauge between the two is claimed.

Source: arXiv:2203.12563, lines 2204–2222; arXiv:2405.00439, line 2040. -/
abbrev cocycleFamily : GroupFamily (Multiplicative (ZMod 3)) 3 :=
  GroupCocycle.family (GroupCocycle.residueEquiv 2) (ScalarThreeCochain.cyclicCocycle 3 1)

/-- The operator laws for the cocycle construction with `ω_1` on `ℤ₃`.

Source: arXiv:2203.12563, lines 2204–2222; arXiv:2405.00439, lines 1684 and 2040. -/
theorem cocycleFamily_operator_laws :
    (∀ g, IsMPUPos (cocycleFamily.tensor g)) ∧
      (∀ N, 0 < N → mpo (cocycleFamily.tensor 1) N = 1) ∧
      (∀ g h N, 0 < N →
        mpo (cocycleFamily.tensor g) N * mpo (cocycleFamily.tensor h) N =
          mpo (cocycleFamily.tensor (g * h)) N) ∧
      (∀ g N, 0 < N →
        (mpo (cocycleFamily.tensor g) N)ᴴ = mpo (cocycleFamily.tensor g⁻¹) N) :=
  GroupCocycle.cyclic_operator_laws 2 1

end Z3Anomalous
