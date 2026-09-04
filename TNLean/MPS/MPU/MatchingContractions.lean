/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryEntries
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPU.TransferStabilization

/-!
# Matching blocked contractions and the input-tail isometry

This module records the blocked simple contractions with the named witnesses
$a=\Phi$ and $b=\rho$ of arXiv:1703.09188, line 427, together with the
normalized input-tail identity
$d^{-K}\tr_{1,\ldots,K}[U^{(K+2)\dagger}U^{(K+2)}]=\Id$ used at the last step of
Lemma `lemuisometry` (lines 553--556).

The staggered paper-$u$ network of Figure `II_uUnitary.png` (lines 536--556) is
contracted in `SourceUCompleteNetwork`; the blocked shapes below are its
inputs, not that identity itself.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Input-first MPU isometry, with a common input tail of length \(K\)
traced out and normalized by \(d^{-K}\), leaves the identity on the first two
input sites.

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

/-- An MPU in canonical form II has the exact aligned simple contractions on
the forced block of length \(JD^2\), with \(J=\max(D^2-1,1)\) and the named
witnesses \(a=\Phi\), \(b=\rho\) of the convention.

Both contractions refer to the same original tensor and its direct block; no
source-cut factorization or source-v isometry is asserted. The ambient fixed
matrix, its positivity and normalization, and the two fixed-vector equations
are the fields of the convention, so they are no longer restated here.

Source: arXiv:1703.09188, Section III.A, lines 397--427. The forced simple
block is subsequently used in Lemma III.7, lines 550--556; Theorem III.8 uses
that lemma at lines 589 and 592.

**Local fix (nil-matrix length):** the second blocking uses \(D^2\); see
<https://sirui-lu.com/QICLean/paper-gaps/mpu_nil_matrix_bound.pdf>. -/
theorem IsMPUCanonicalFormII.forced_block_simple_contractions
    [NeZero d] {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) :
    let J := max (D * D - 1) 1
    let ρ' : Fin (D * D) → ℂ := fun i ↦ hU.ρ.vec (finProdFinEquiv.symm i)
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
  have := hU.neZero_bond
  exact hU.isMPU.blockTensor_mul_sq_simple_contractions_of_transfer_power
    hU.ρ hU.ρ_trace (max (D * D - 1) 1) (by omega)
    hU.normalized_transfer_power_eq_vecMulVec

end MPOTensor
