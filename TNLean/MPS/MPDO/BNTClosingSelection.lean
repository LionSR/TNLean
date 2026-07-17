/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.MPS.MPDO.CommonWeightAbsorption

/-!
# Nonzero physical-trace closing matrices

For a simple tensor, the physical-trace transfer of each basis-of-normal-
tensors representative is not nilpotent.  Hence a common positive power has
a nonzero matrix entry in every representative.  When the canonical-form
weights are independent of the copy index, multiplying this power by the
coefficient at the corresponding total chain length gives the nonzero closing
matrix selected before the principal BNT--Markov identity in
arXiv:1606.00608, Appendix C.2.

The physical legs of the tail in the source diagram are traced.  Thus the
tail is a power of the physical-trace transfer, not an arbitrary physical-word
matrix.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  simplicity at lines 815--822 and Appendix C.2, lines 1714--1718.
-/

open scoped Matrix BigOperators

namespace MPSTensor

namespace SectorDecomposition

variable {d : ℕ}

/-- For a simple sector decomposition, one common positive power of the
physical-trace transfers has a nonzero entry in every representative.

The source tail diagram traces the two physical legs at each tail site, so its
matrix is
\[
  \mathcal B_j^L,
  \qquad \mathcal B_j=\sum_i A_j^{ii}.
\]
Simplicity says that no \(\mathcal B_j\) is nilpotent.

Source: arXiv:1606.00608, simplicity at lines 815--822 and Appendix C.2,
lines 1714--1718. -/
theorem exists_common_nonzero_physicalTraceTail_entry
    (S : SectorDecomposition (d * d))
    (hnonNil : ∀ j,
      ¬ IsNilpotent (MPOTensor.doubledPhysTraceTransfer d (S.basis j))) :
    ∃ L : ℕ, 0 < L ∧ ∀ j : Fin S.basisCount,
      ∃ α β : Fin (S.basisDim j),
        ((MPOTensor.doubledPhysTraceTransfer d (S.basis j)) ^ L) α β ≠ 0 := by
  refine ⟨1, by omega, ?_⟩
  intro j
  have hTail : (MPOTensor.doubledPhysTraceTransfer d (S.basis j)) ^ 1 ≠ 0 := by
    intro hzero
    exact hnonNil j ⟨1, hzero⟩
  obtain ⟨α, β, hαβ⟩ := Matrix.exists_entry_ne_zero_of_ne_zero _ hTail
  exact ⟨α, β, hαβ⟩

/-- The closing matrix of representative \(j\) after retaining three physical
sites and tracing a tail of length \(L\):
\[
  R_j=q_j\mathcal B_j^L,
  \qquad q_j=\sum_q\mu_{j,q}^{L+3}.
\]

Source: arXiv:1606.00608, Appendix C.2, lines 1714--1718 and 1726--1732. -/
noncomputable def threeSiteClosingMatrix
    (S : SectorDecomposition (d * d)) (L : ℕ) (j : Fin S.basisCount) :
    Matrix (Fin (S.basisDim j)) (Fin (S.basisDim j)) ℂ :=
  S.coeff (L + 3) j •
    (MPOTensor.doubledPhysTraceTransfer d (S.basis j)) ^ L

/-- At one common positive tail length, every three-site closing matrix has a
nonzero entry:
\[
  (R_j)_{\alpha,\beta}
  =q_j(\mathcal B_j^L)_{\alpha,\beta}\ne0.
\]

This is the scalar \(m_j=q_j\widetilde m_j\) in the source, now identified
with an entry of the physical-trace closing matrix \(R_j\).

Source: arXiv:1606.00608, Appendix C.2, lines 1714--1718. -/
theorem exists_common_nonzero_threeSiteClosingMatrix_entry
    (S : SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (MPOTensor.doubledPhysTraceTransfer d (S.basis j))) :
    ∃ L : ℕ, 0 < L ∧ ∀ j : Fin S.basisCount,
      ∃ α β : Fin (S.basisDim j),
        S.threeSiteClosingMatrix L j α β ≠ 0 := by
  obtain ⟨L, hL, hEntry⟩ :=
    S.exists_common_nonzero_physicalTraceTail_entry hnonNil
  refine ⟨L, hL, ?_⟩
  intro j
  obtain ⟨α, β, hαβ⟩ := hEntry j
  refine ⟨α, β, ?_⟩
  simpa [threeSiteClosingMatrix, Matrix.smul_apply, smul_eq_mul] using
    mul_ne_zero
      (S.coeff_ne_zero_of_weight_copy_independent hWeight (L + 3) j)
      hαβ

/-- For one common positive tail length, every physical-trace closing matrix
is nonzero.

Source: arXiv:1606.00608, Appendix C.2, lines 1714--1718. -/
theorem exists_common_threeSiteClosingMatrix_ne_zero
    (S : SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (MPOTensor.doubledPhysTraceTransfer d (S.basis j))) :
    ∃ L : ℕ, 0 < L ∧ ∀ j : Fin S.basisCount,
      S.threeSiteClosingMatrix L j ≠ 0 := by
  obtain ⟨L, hL, hEntry⟩ :=
    S.exists_common_nonzero_threeSiteClosingMatrix_entry hWeight hnonNil
  refine ⟨L, hL, ?_⟩
  intro j hzero
  obtain ⟨α, β, hαβ⟩ := hEntry j
  exact hαβ (by rw [hzero]; rfl)

end SectorDecomposition

end MPSTensor
