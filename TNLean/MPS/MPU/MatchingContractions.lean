/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryEntries
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPU.TransferStabilization

/-!
# Matching blocked contractions and output-tail coisometry

These checked results supply blocked matching and global coisometry identities
used by the auxiliary $Y_1$--$X_2$ mixed-kernel calculations. They do not
identify a Gram matrix for the paper gate $u=Y_2\mathbin{-}Y_1$.

The source proof in arXiv:1703.09188, Figure `II_uUnitary.png` and Lemma
`lemuisometry` (lines 536--556), instead contracts the staggered paper-$u$
network. That route remains unformalized. Similar blocked and output-tail
shapes in this file must not be read as a formalization of the figure or as
support for the paper source-$u$ isometry.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ}

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
    simpa only [(finAddTwoArrowEquiv (Fin d) K).symm.injective.eq_iff,
      Prod.mk.injEq, and_true] using
      Matrix.sum_mul_star_eq_ite_of_mul_conjTranspose_eq_one
        (mpo U (K + 2)) hco
        ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))
        ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))
  simp_rw [hentry]
  by_cases hpq : p = q
  · subst q
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow, ite_eq_left]
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero K hd), one_mul]
  · rw [ite_eq_right hpq, ite_eq_right (Ne.symm hpq)]
    simp

/-- Input-first MPU isometry, with a common input tail of length \(K\)
traced out and normalized by \(d^{-K}\), leaves the identity on the first two
input sites.

This is the input-first counterpart of `IsMPU.normalized_mpo_tail_coisometry`.
It follows directly from the global equation `Uᴴ U = 1`, without an ambient
source-factor coisometry.

Source: arXiv:1703.09188, Theorem III.8, equations (31)--(32), Section III.B
(lines 563--600). -/
theorem IsMPU.normalized_mpo_tail_isometry [NeZero d]
    {U : MPOTensor d D} (hU : IsMPU U) (K : ℕ)
    (p q : Fin d × Fin d) :
    ((d : ℂ)⁻¹) ^ K *
        ∑ τ : Fin K → Fin d, ∑ η : Fin (K + 2) → Fin d,
          star (mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))) *
          mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) =
      if p = q then 1 else 0 := by
  classical
  have hiso := hU.conjTranspose_mpo_mul_mpo (N := K + 2) (by omega)
  have hentry (τ : Fin K → Fin d) :
      (∑ η : Fin (K + 2) → Fin d,
        star (mpo U (K + 2) η
          ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))) *
        mpo U (K + 2) η
          ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))) =
        if p = q then 1 else 0 := by
    simpa only [(finAddTwoArrowEquiv (Fin d) K).symm.injective.eq_iff,
      Prod.mk.injEq, and_true] using
      Matrix.sum_star_mul_eq_ite_of_conjTranspose_mul_eq_one
        (mpo U (K + 2)) hiso
          ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))
          ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))
  simp_rw [hentry]
  by_cases hpq : p = q
  · subst q
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow, ite_eq_left]
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero K hd), one_mul]
  · rw [ite_eq_right hpq]
    simp

/-- The stabilized first block followed by the corrected \(D^2\) block has the
exact simple contractions obtained from the supplied fixed matrix and the
identity left vector.

Source: arXiv:1703.09188, equations `Erightleft`, `simple1`, and `simple2`,
lines 397--427.

**Local fix (nil-matrix length):** the second blocking uses \(D^2\); see
<https://sirui-lu.com/QICLean/paper-gaps/mpu_nil_matrix_bound.pdf>. -/
theorem IsMPU.blockTensor_mul_sq_simple_contractions_of_transfer_power
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρtrace : Matrix.trace ρ = 1)
    (J : ℕ) (hJ : 0 < J)
    (hpower : transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ J =
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
  let : NeZero (MPSTensor.blockPhysDim d J) := ⟨by
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

/-- A reduced full-support canonical-form-II representative supplies the
normalized positive fixed pair and the exact aligned simple contractions on
the forced block of length \(J D^2\), where \(J = D^2 - 1\).

All fixed-point data and both contractions refer to the same original tensor
and its direct block; no source-cut factorization or source-v isometry is
asserted.

Source: arXiv:1703.09188, Section III.A, lines 397--427. The forced simple
block is subsequently used in Lemma III.7, lines 550--556; Theorem III.8 uses
that lemma at lines 589 and 592.

**Scope restriction (full support):** This uses the chosen reduced
representative supplied by
`IsMPU.normalized_transfer_power_eq_vecMulVec_of_reduced_cfii`. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

**Local fix (nil-matrix length):** the second blocking uses \(D^2\); see
<https://sirui-lu.com/QICLean/paper-gaps/mpu_nil_matrix_bound.pdf>. -/
theorem IsMPU.exists_reduced_cfii_forced_block_simple_contractions
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D)
    (cfii : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (hfull : cfii.toCPSVCanonicalFormData.HasFullSupport) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosDef ∧ Matrix.trace ρ = 1 ∧
      Kraus.transferMap U.normalizedFlattening ρ = ρ ∧
      Matrix.vecMul (1 : Matrix (Fin D) (Fin D) ℂ).vec
          (transferMatrix (Kraus.transferMap U.normalizedFlattening)) =
        (1 : Matrix (Fin D) (Fin D) ℂ).vec ∧
      transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ (D * D - 1) =
        Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec ∧
      let J := D * D - 1
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
  obtain ⟨_, _, ρ, _, _, _, _, _, _, hρpd, hρtrace, hρfix, hΦfix, hpower⟩ :=
    hU.normalized_transfer_power_eq_vecMulVec_of_reduced_cfii hD cfii hfull
  have hJ : 0 < D * D - 1 := Nat.sub_pos_of_lt (by nlinarith)
  have hs := hU.blockTensor_mul_sq_simple_contractions_of_transfer_power
    ρ hρtrace (D * D - 1) hJ hpower
  exact ⟨ρ, hρpd, hρtrace, hρfix, hΦfix, hpower, hs⟩

end MPOTensor
