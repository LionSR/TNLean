/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.SupportCompletion
import TNLean.MPS.Core.TransferMatrix
import TNLean.MPS.MPDO.PureAreaLaw
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.MPS.RFP.Defs

/-!
# Pure-state equivalence for the MPDO renormalization fixed-point condition

This file identifies Definition 4.1 of arXiv:1606.00608 on the doubled tensor
of a pure MPS with the pure-state physical blocking condition. The refinement
map is conjugation by the blocking isometry. When the physical dimension is
positive, the coarse-graining map is compression by its adjoint, completed on
the orthogonal physical complement by a trace-and-prepare channel. In physical
dimension zero, the unique zero maps give both channels.

## Main results

* `MPSTensor.doubledTensor_isRFPViaTS_iff_isTransferIdempotent`
* `MPSTensor.doubledTensor_isRFPViaTS_iff_hasPhysicalBlockingIsometry`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, labels
  *Def-equiv-pure* and *T-and-S-mixed-equiv-pure*, lines 675--687.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix MPOTensor

namespace MPSTensor

variable {d D : ℕ}

private theorem physTraceTransfer_doubledTensor (A : MPSTensor d D) :
    Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (physTraceTransfer (doubledTensor A)) =
      Matrix.reindex (Equiv.prodComm (Fin D) (Fin D))
        (Equiv.prodComm (Fin D) (Fin D)) (transferMatrix (transferMap A)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [physTraceTransfer, doubledTensor, transferMatrix_apply, transferMap_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, Equiv.apply_symm_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, RCLike.star_def, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hbk
      simp [hbk.symm]
    · simp
  · intro b _ hbl
    have hsum : (∑ c, if k = c ∧ l = b then A x i c else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      simp [hbl.symm]
    rw [hsum, zero_mul]
  · simp

private theorem doubledTensor_mul_eq_of_blocking_isometry
    (A : MPSTensor d D) (V : Matrix (Fin d × Fin d) (Fin d) ℂ)
    (hprod : ∀ i₁ i₂ : Fin d,
      A i₁ * A i₂ = ∑ j : Fin d, V (i₁, i₂) j • A j)
    (i₁ i₂ j₁ j₂ : Fin d) :
    doubledTensor A i₁ j₁ * doubledTensor A i₂ j₂ =
      ∑ a : Fin d, ∑ b : Fin d,
        (V (i₁, i₂) a * star (V (j₁, j₂) b)) • doubledTensor A a b := by
  rw [doubledTensor, doubledTensor,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm,
    ← Matrix.mul_kronecker_mul]
  rw [hprod i₁ i₂]
  have hstar :
      (A j₁).map (starRingEnd ℂ) * (A j₂).map (starRingEnd ℂ) =
        (∑ b : Fin d, V (j₁, j₂) b • A b).map (starRingEnd ℂ) := by
    calc
      (A j₁).map (starRingEnd ℂ) * (A j₂).map (starRingEnd ℂ) =
          (A j₁ * A j₂).map (starRingEnd ℂ) :=
        ((starRingEnd ℂ).mapMatrix.map_mul _ _).symm
      _ = _ := congrArg (Matrix.map · (starRingEnd ℂ)) (hprod j₁ j₂)
  rw [hstar]
  have hmapEntry (r c : Fin D) :
      (starRingEnd ℂ) (∑ b : Fin d, V (j₁, j₂) b • A b r c) =
        ∑ b : Fin d, star (V (j₁, j₂) b) * star (A b r c) := by
    simp [map_sum, map_mul, RCLike.star_def]
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, doubledTensor]
  rw [hmapEntry, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp [mul_comm, mul_left_comm, mul_assoc]

private theorem singleKrausMap_physClose1_doubledTensor
    (A : MPSTensor d D) (V : Matrix (Fin d × Fin d) (Fin d) ℂ)
    (hprod : ∀ i₁ i₂ : Fin d,
      A i₁ * A i₂ = ∑ j : Fin d, V (i₁, i₂) j • A j)
    (X : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) :
    singleKrausMap V (physClose1 (doubledTensor A) X) =
      physClose2 (doubledTensor A) X := by
  ext p q
  rw [singleKrausMap_apply, physClose2_apply,
    doubledTensor_mul_eq_of_blocking_isometry A V hprod]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, physClose1_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem doubledTensor_isRFPViaTS_of_hasPhysicalBlockingIsometry
    (A : MPSTensor d D) (h : HasPhysicalBlockingIsometry A) :
    IsRFPViaTS (doubledTensor A) := by
  obtain ⟨V, hV, hprod⟩ := h
  by_cases hd : d = 0
  · subst d
    let S : Matrix (Fin 0 × Fin 0) (Fin 0 × Fin 0) ℂ →ₗ[ℂ]
        Matrix (Fin 0) (Fin 0) ℂ := 0
    let T : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ]
        Matrix (Fin 0 × Fin 0) (Fin 0 × Fin 0) ℂ := 0
    have hS : IsKrausCPTP S := by
      refine ⟨0, fun _ ↦ 0, ?_, ?_⟩
      · intro X
        exact Subsingleton.elim _ _
      · exact Subsingleton.elim _ _
    have hT : IsKrausCPTP T := by
      refine ⟨0, fun _ ↦ 0, ?_, ?_⟩
      · intro X
        exact Subsingleton.elim _ _
      · exact Subsingleton.elim _ _
    exact ⟨S, T, hS, hT, fun _ ↦ Subsingleton.elim _ _,
      fun _ ↦ Subsingleton.elim _ _⟩
  · letI : NeZero d := ⟨hd⟩
    let P : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := V * Vᴴ
    let S := Matrix.supportCompletion (singleKrausMap Vᴴ) P
      (Matrix.faithfulDensity (Fin d))
    let T := singleKrausMap V
    have hPherm : P.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self V
    have hPidem : P * P = P := by
      change (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ
      calc
        (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
        _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
    have hEtrace : ∀ X, Matrix.trace (singleKrausMap Vᴴ X) =
        Matrix.trace (P * X) := by
      intro X
      simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose, P]
      exact Matrix.trace_mul_cycle Vᴴ X V
    have hS : IsKrausCPTP S := by
      exact Matrix.supportCompletion_isKrausCPTP
        (singleKrausMap Vᴴ) P (Matrix.faithfulDensity (Fin d))
        (singleKrausMap_isKrausCP Vᴴ) hPherm hPidem hEtrace
        (Matrix.faithfulDensity_posDef (Fin d)).posSemidef
        (Matrix.faithfulDensity_trace (Fin d))
    have hT : IsKrausCPTP T := singleKrausMap_isKrausCPTP V hV
    refine ⟨S, T, hS, hT, ?_, ?_⟩
    · intro X
      rw [← singleKrausMap_physClose1_doubledTensor A V hprod X]
      let Y := physClose1 (doubledTensor A) X
      have hsupported : P * T Y * P = T Y := by
        change (V * Vᴴ) * (V * Y * Vᴴ) * (V * Vᴴ) = V * Y * Vᴴ
        calc
          (V * Vᴴ) * (V * Y * Vᴴ) * (V * Vᴴ) =
              V * (Vᴴ * V) * Y * (Vᴴ * V) * Vᴴ := by
            simp only [Matrix.mul_assoc]
          _ = V * Y * Vᴴ := by rw [hV]; simp
      change Matrix.supportCompletion (singleKrausMap Vᴴ) P
          (Matrix.faithfulDensity (Fin d)) (T Y) = Y
      rw [Matrix.supportCompletion_apply_of_supported
        (singleKrausMap Vᴴ) P (Matrix.faithfulDensity (Fin d)) _
        hPherm hPidem hsupported]
      dsimp only [T]
      simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
      calc
        Vᴴ * (V * Y * Vᴴ) * V = (Vᴴ * V) * Y * (Vᴴ * V) := by
          simp only [Matrix.mul_assoc]
        _ = Y := by rw [hV]; simp
    · exact singleKrausMap_physClose1_doubledTensor A V hprod

private theorem isTransferIdempotent_of_doubledTensor_isRFPViaTS
    (A : MPSTensor d D) (h : IsRFPViaTS (doubledTensor A)) :
    IsTransferIdempotent A := by
  have hphys := physTraceTransfer_sq_of_isRFPViaTS (doubledTensor A) h
  have hreindex := congrArg
    (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv.symm) hphys
  rw [map_mul] at hreindex
  change
    Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (physTraceTransfer (doubledTensor A)) *
        Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (physTraceTransfer (doubledTensor A)) =
      Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (physTraceTransfer (doubledTensor A)) at hreindex
  rw [physTraceTransfer_doubledTensor] at hreindex
  have htransfer : transferMatrix (transferMap A) * transferMatrix (transferMap A) =
      transferMatrix (transferMap A) := by
    apply (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodComm (Fin D) (Fin D))).injective
    rw [map_mul]
    exact hreindex
  apply transferMatrix_injective
  rw [transferMatrix_comp]
  exact htransfer

/-- On a doubled pure-state tensor, the physical-channel renormalization
fixed-point condition of Definition 4.1 is equivalent to idempotence of the
pure MPS transfer map.

Let \(V : \mathbb C^d \to \mathbb C^{d^2}\) be the physical blocking
isometry. The refinement channel has the source orientation
\(\mathcal T(X) = V X V^\dagger\). When \(d > 0\), the coarse-graining
channel is \(Y \mapsto V^\dagger Y V\) on the active projection
\(P = V V^\dagger\); outside this projection, the complementary trace is
mapped to a fixed density matrix. On tensor-generated closures this channel
agrees with the source formula
\(\mathcal S(Y) = \operatorname{tr}_2(U^\dagger Y U)\), where the isometry is
extended to a unitary and a pure ancilla is adjoined. When \(d = 0\), both
matrix spaces are trivial and the unique zero maps give the two channels.

For the converse, trace preservation of \(\mathcal T\) makes the
physical-trace transfer of the tensor `doubledTensor` associated with \(A\)
idempotent. After simultaneous reindexing, this matrix is the transfer matrix
of the map `transferMap` associated with \(A\). This
argument does not concern `MPOTensor.IsZCL` or `MPOTensor.IsSourceZCL`.

Source: arXiv:1606.00608, pure-state specialization at line 668, labels
*Def-equiv-pure* and *T-and-S-mixed-equiv-pure*, lines 675--687, and the
trace-preservation argument in Appendix C, lines 1333--1340. -/
theorem doubledTensor_isRFPViaTS_iff_isTransferIdempotent (A : MPSTensor d D) :
    IsRFPViaTS (doubledTensor A) ↔ IsTransferIdempotent A := by
  constructor
  · exact isTransferIdempotent_of_doubledTensor_isRFPViaTS A
  · intro h
    apply doubledTensor_isRFPViaTS_of_hasPhysicalBlockingIsometry A
    exact (isTransferIdempotent_iff_hasPhysicalBlockingIsometry A).mp h

/-- The doubled pure-state tensor satisfies the physical tpCP-map condition of
Definition 4.1 exactly when the original MPS tensor has a physical blocking
isometry.

The isometry is oriented from one physical site to two and defines
\(\mathcal T(X) = V X V^\dagger\). When \(d > 0\), compression by
\(V^\dagger\), followed by trace-preserving completion on the orthogonal
complement, defines \(\mathcal S\). When \(d = 0\), the unique zero maps define
both channels.

Source: arXiv:1606.00608, pure-state specialization at line 668, labels
*Def-equiv-pure* and *T-and-S-mixed-equiv-pure*, lines 675--687, and the
trace-preservation argument in Appendix C, lines 1333--1340. -/
theorem doubledTensor_isRFPViaTS_iff_hasPhysicalBlockingIsometry
    (A : MPSTensor d D) :
    IsRFPViaTS (doubledTensor A) ↔ HasPhysicalBlockingIsometry A := by
  rw [doubledTensor_isRFPViaTS_iff_isTransferIdempotent,
    isTransferIdempotent_iff_hasPhysicalBlockingIsometry]

end MPSTensor
