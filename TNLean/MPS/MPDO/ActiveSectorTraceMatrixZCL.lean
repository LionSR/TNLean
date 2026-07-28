/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorTraceMatrix
import TNLean.MPS.MPDO.SectorPairingTransfer
import TNLean.Channel.MaximalOverlap

/-!
# Zero correlation length on an active-sector trace matrix

This file gives the source-zero-correlation-length relations for an arbitrary
active restriction of a positive physical-sector trace matrix.  It has no
area-law or inverse-map hypothesis.

## Main result

* `PhysicalSectorFactorization.activeSectorTraceMatrix_normalized_relations_of_isSourceZCL`:
  one positive normalization of the active trace matrix satisfies the
  square--cube and positive-power trace relations.

## Reference

* arXiv:1606.00608, Appendix C.2, equations `Tkn` and `SALZCL`, lines
  1473--1497.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Suppose that the left tensor vanishes in every sector of zero weight and
that all neighboring operators are positive semidefinite.  If the original
tensor has source zero correlation length, then one positive normalization of
the active trace matrix satisfies
\[
  \widehat T^2=\widehat T^3,
  \qquad
  \operatorname{tr}(\widehat T^N)=\operatorname{tr}(\widehat T)
  \quad (N\geq1).
\]

The proof restricts the rectangular decomposition of the physical-trace
transfer to the nonzero-weight sectors.  Positivity identifies the opposite
rectangular product with the complexification of the real active trace matrix.

Source: arXiv:1606.00608, Appendix C.2, equations `Tkn` and `SALZCL`, lines
1473--1497.  The conclusion does not assert idempotence, rank one, or
semisimplicity of the trace matrix. -/
theorem activeSectorTraceMatrix_normalized_relations_of_isSourceZCL
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hZCL : K.IsSourceZCL) :
    ∃ lam : ℝ, 0 < lam ∧
      let T := F.activeSectorTraceMatrix p
      ((lam⁻¹ • T) ^ 2 = (lam⁻¹ • T) ^ 3) ∧
        ∀ N : ℕ, 0 < N →
          Matrix.trace ((lam⁻¹ • T) ^ N) = Matrix.trace (lam⁻¹ • T) := by
  classical
  obtain ⟨lam, hlam, hidem⟩ := hZCL.normalized_idempotent
  let L : Matrix (Fin D) (F.ActiveSector p) ℂ :=
    fun beta h ↦ (F.leftTensor h beta).trace
  let Q : Matrix (F.ActiveSector p) (Fin D) ℂ :=
    fun k alpha ↦ (F.rightTensor k alpha).trace
  have hphys : MPOTensor.physTraceTransfer K = L * Q := by
    let U : Matrix.unitaryGroup (Fin d) ℂ := ⟨F.physicalIsometry, by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact F.physicalIsometry_isometry⟩
    have hfactor : ∀ beta alpha,
        Matrix.reindex F.sectorEquiv F.sectorEquiv
            ((U : Matrix (Fin d) (Fin d) ℂ) * MPOTensor.physicalSlice K beta alpha *
              (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
          Matrix.blockDiagonal' fun q ↦
            Matrix.kroneckerMap (· * ·) (F.leftTensor q beta) (F.rightTensor q alpha) := by
      simpa [U] using F.factorization
    rw [MPOTensor.physTraceTransfer_eq_sum_closedSector K F.sectorEquiv U
      F.leftTensor F.rightTensor hfactor]
    ext beta alpha
    simp only [MPOTensor.closedSectorPairingOperator, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Matrix.mul_apply, L, Q]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun k ↦ p k ≠ 0)) (by simp)
      (fun k ↦ (F.leftTensor k beta).trace * (F.rightTensor k alpha).trace)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : p k ≠ 0
    · simp [hk]
    · rw [if_neg hk, hinactive k (not_ne_iff.mp hk) beta, Matrix.trace_zero, zero_mul]
  have hrect : IsIdempotentElem (((lam : ℂ)⁻¹ • L) * Q) := by
    simpa only [Matrix.smul_mul, ← hphys] using hidem
  let TC : Matrix (F.ActiveSector p) (F.ActiveSector p) ℂ := Q * L
  have hTC : TC = Matrix.map (F.activeSectorTraceMatrix p) Complex.ofReal := by
    ext k h
    simp only [TC, Matrix.mul_apply, Q, L, Matrix.map_apply]
    change (∑ j, (F.rightTensor (k : Fin F.sectorCount) j).trace *
      (F.leftTensor (h : Fin F.sectorCount) j).trace) =
        ((F.neighboringOperator k h).trace.re : ℂ)
    rw [← (hpos k h).isHermitian.trace_eq_ofReal_re]
    simp only [neighboringOperator, Matrix.trace, Matrix.diag, Matrix.of_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  refine ⟨lam, hlam, ?_⟩
  dsimp only
  have hmap : Matrix.map (lam⁻¹ • F.activeSectorTraceMatrix p) Complex.ofReal =
      (lam : ℂ)⁻¹ • TC := by
    rw [hTC]
    ext k h
    simp [Matrix.smul_apply, Matrix.map_apply]
  have hmapHom :
      Matrix.map (lam⁻¹ • F.activeSectorTraceMatrix p) (⇑Complex.ofRealHom) =
        (lam : ℂ)⁻¹ • TC := hmap
  constructor
  · apply Matrix.map_injective Complex.ofReal_injective
    change Matrix.map ((lam⁻¹ • F.activeSectorTraceMatrix p) ^ 2) (⇑Complex.ofRealHom) =
      Matrix.map ((lam⁻¹ • F.activeSectorTraceMatrix p) ^ 3) (⇑Complex.ofRealHom)
    rw [Matrix.map_pow, Matrix.map_pow, hmapHom]
    simpa only [Matrix.mul_smul, TC] using
      (Matrix.pow_two_eq_pow_three_of_rectangular_idempotent
        ((lam : ℂ)⁻¹ • L) Q hrect)
  · intro N hN
    apply Complex.ofReal_injective
    change Complex.ofRealHom (Matrix.trace ((lam⁻¹ • F.activeSectorTraceMatrix p) ^ N)) =
      Complex.ofRealHom (Matrix.trace (lam⁻¹ • F.activeSectorTraceMatrix p))
    rw [AddMonoidHom.map_trace Complex.ofRealHom,
      AddMonoidHom.map_trace Complex.ofRealHom, Matrix.map_pow, hmapHom]
    simpa only [Matrix.mul_smul, TC] using
      (Matrix.trace_pow_eq_trace_of_rectangular_idempotent
        ((lam : ℂ)⁻¹ • L) Q hrect N hN)

end MPOTensor.PhysicalSectorFactorization
