/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking

/-!
# Matching blocked contractions and output-tail coisometry

These results supply the two contraction ingredients for the later source-u
Gram calculation. They do not identify that Gram matrix; the finite-sum
reduction to the source factors is treated separately.

These are the blocked matching and global coisometry contractions used in
arXiv:1703.09188, Figure `II_uUnitary.png` and Lemma `lemuisometry` (lines
536--556). In the present open-leg conventions, the output-tail proof keeps the
first two sites and traces the remaining tail using the global unitary equation
`U Uᴴ = 1`; the figure instead traces the first tail and keeps the final two
sites in the `Uᴴ U = 1` orientation.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- Output-first MPU coisometry, with a common output tail of length \(K\)
traced out and normalized by \(d^{-K}\), leaves the identity on the first two output sites.
The retained arguments occur in reversed matrix order because this convention
keeps the first two sites and uses the output-first equation `U Uᴴ = 1`.

Source: arXiv:1703.09188, equation `UisUnitary` and Figure
`II_uUnitary.png`, lines 327--335 and 536--556. -/
theorem IsMPU.normalized_mpo_tail_coisometry [NeZero d]
    {U : MPOTensor d D} (hU : IsMPU U) (K : ℕ)
    (p q : Fin d × Fin d) :
    ((d : ℂ)⁻¹) ^ K *
        ∑ τ : Fin K → Fin d, ∑ η : Fin (K + 2) → Fin d,
          mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) η *
            star (mpo U (K + 2)
              ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ)) η) =
      if p = q then 1 else 0 := by
  classical
  have hco := hU.mpo_mul_conjTranspose_mpo (N := K + 2) (by omega)
  have hentry (τ : Fin K → Fin d) :
      (∑ η : Fin (K + 2) → Fin d,
        mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) η *
          star (mpo U (K + 2)
            ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ)) η)) =
        if q = p then 1 else 0 := by
    have := congrArg (fun M ↦ M
      ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))
      ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))) hco
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      (finAddTwoArrowEquiv (Fin d) K).symm.injective.eq_iff, Prod.mk.injEq,
      and_true] using this
  simp_rw [hentry]
  by_cases hpq : p = q
  · subst q
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow, if_pos]
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero K hd), one_mul]
  · rw [if_neg hpq, if_neg (Ne.symm hpq)]
    simp

/-- The stabilized first block followed by the corrected \(D^2\) block has the
exact simple contractions obtained from the supplied fixed matrix and the
identity left vector.

Source: arXiv:1703.09188, equations `Erightleft`, `simple1`, and `simple2`,
lines 397--427.

**Local fix (nil-matrix length):** the second blocking uses \(D^2\); see
`docs/paper-gaps/mpu_nil_matrix_bound.tex`. -/
theorem IsMPU.blockTensor_mul_sq_simple_contractions_of_transfer_power
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρtrace : Matrix.trace ρ = 1)
    (J : ℕ) (hJ : 0 < J)
    (hpower : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    let ρ' : Fin (D * D) → ℂ := fun i ↦ ρ.vec (finProdFinEquiv.symm i)
    let Φ' : Fin (D * D) → ℂ := fun i ↦
      (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm i)
    (∀ i j : Fin (MPSTensor.blockPhysDim d (J * (D * D))),
      Φ' ⬝ᵥ (doubleLayerTensor (MPOTensor.blockTensor U (J * (D * D))) i j *ᵥ ρ') =
        if i = j then 1 else 0) ∧
    (∀ i j k l : Fin (MPSTensor.blockPhysDim d (J * (D * D))),
      doubleLayerTensor (MPOTensor.blockTensor U (J * (D * D))) i j *
          doubleLayerTensor (MPOTensor.blockTensor U (J * (D * D))) k l =
        doubleLayerTensor (MPOTensor.blockTensor U (J * (D * D))) i j *
          Matrix.vecMulVec ρ' Φ' *
            doubleLayerTensor (MPOTensor.blockTensor U (J * (D * D))) k l) := by
  classical
  let V := MPOTensor.blockTensor U J
  let ρ' : Fin (D * D) → ℂ := fun i ↦ ρ.vec (finProdFinEquiv.symm i)
  let Φ' : Fin (D * D) → ℂ := fun i ↦
    (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm i)
  have hpair : Φ' ⬝ᵥ ρ' = 1 := by
    change (∑ i : Fin (D * D),
      (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm i) *
        ρ.vec (finProdFinEquiv.symm i)) = 1
    calc
      _ = (1 : Matrix (Fin D) (Fin D) ℂ).vec ⬝ᵥ ρ.vec := by
        exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ ↦ rfl)
      _ = Matrix.trace ρ := Matrix.vec_one_dotProduct_vec_eq_trace ρ
      _ = 1 := hρtrace
  have hVmpu : IsMPU V := hU.blockTensor J hJ
  have hVE : normalizedDiagonal (doubleLayerTensor V) = Matrix.vecMulVec ρ' Φ' := by
    change normalizedDiagonal (doubleLayerTensor (MPOTensor.blockTensor U J)) = _
    rw [normalizedDiagonal_doubleLayerTensor_blockTensor, hpower]
    rfl
  letI : NeZero (MPSTensor.blockPhysDim d J) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero J (NeZero.ne d)⟩
  have hs := hVmpu.blockTensor_sq_simple_contractions_of_normalizedDiagonal_eq_vecMulVec
    ρ' Φ' hpair hVE
  let e := MPSTensor.directIteratedBlockEquiv d J (D * D)
  have htensor := reindexPhysical_blockTensor_blockTensor U J (D * D)
  constructor
  · intro i j
    have hij := hs.1 (e i) (e j)
    simpa only [e, ← htensor, doubleLayerTensor_reindexPhysical,
      (MPSTensor.directIteratedBlockEquiv d J (D * D)).injective.eq_iff] using hij
  · intro i j k l
    have hijkl := hs.2 (e i) (e j) (e k) (e l)
    simpa only [e, ← htensor, doubleLayerTensor_reindexPhysical] using hijkl

end MPOTensor
