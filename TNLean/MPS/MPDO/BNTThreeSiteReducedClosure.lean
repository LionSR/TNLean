/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.MPDO.BNTClosingSelection
import TNLean.MPS.MPDO.BNTThreeSiteCollapse
import TNLean.MPS.MPDO.MutualInfoMonotone
import TNLean.MPS.MPDO.SectorTrace
import TNLean.MPS.MPDO.VerticalCF

/-!
# Three-site reduced states from BNT closing matrices

Tracing all but three consecutive physical sites closes the three exposed
tensors against a power of the physical-trace transfer.  For a horizontal
basis-of-normal-tensors representation, the reduced state is therefore a
finite family closure.  Its closing matrix in sector (j) is the product of
the normalization scalar, the canonical-form coefficient, and the traced
virtual tail.

This is the reduced-state expansion used in the Case II calculation of
arXiv:1606.00608, Appendix C.2.  The result below includes the normalization
of the density operator and transports the formula through equality of the
positive-length matrix-product-vector families.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, lines 1660--1665 and 1714--1732.
-/

open scoped Matrix BigOperators

namespace MPSTensor.SectorDecomposition

variable {d : ℕ}

/-- Read a doubled-index BNT representative as an MPO tensor:

\[
  (\mathcal A_j)^{ab}=A_j^{(a,b)}.
\]

Source: arXiv:1606.00608, Appendix C.2, the BNT convention at lines
1628--1632 and the canonical-form display at lines 1660--1665. -/
def basisMPOTensor (S : SectorDecomposition (d * d))
    (j : Fin S.basisCount) : MPOTensor d (S.basisDim j) :=
  fun a b ↦ S.basis j (finProdFinEquiv (a, b))

/-- Converting the representative MPO back to a doubled-index MPS tensor
recovers the original BNT representative.

Source: arXiv:1606.00608, Appendix C.2, the doubled-index convention at lines
1628--1632. -/
@[simp] theorem basisMPOTensor_toMPSTensor
    (S : SectorDecomposition (d * d)) (j : Fin S.basisCount) :
    (S.basisMPOTensor j).toMPSTensor = S.basis j := by
  funext ab
  change S.basis j (finProdFinEquiv (ab.divNat, ab.modNat)) = S.basis j ab
  exact congrArg (S.basis j) (finProdFinEquiv.apply_symm_apply ab)

/-- The physical trace transfer of a representative MPO is its doubled-index
physical trace transfer.

Source: arXiv:1606.00608, Appendix C.2, the traced physical legs in the
closing construction at lines 1714--1718. -/
@[simp] theorem basisMPOTensor_verticalLoop
    (S : SectorDecomposition (d * d)) (j : Fin S.basisCount) :
    MPOTensor.verticalLoop (S.basisMPOTensor j) =
    MPOTensor.doubledPhysTraceTransfer d (S.basis j) := by
  simp [MPOTensor.verticalLoop, MPOTensor.physTraceTransfer,
    MPOTensor.doubledPhysTraceTransfer, basisMPOTensor]

/-- Equality of the positive-length doubled-index matrix-product-vector
families gives the representative expansion of every physical MPO matrix entry.

Source: arXiv:1606.00608, equations `decBSV` and `CFK`, lines 298--301 and
1660--1665. -/
theorem mpo_eq_sum_coeff_basisMPOTensor
    {D : ℕ} (M : MPOTensor d D) (S : SectorDecomposition (d * d))
    (hM : SameMPV₂Pos M.toMPSTensor S.toTensor) {N : ℕ} (hN : 0 < N)
    (u v : Fin N → Fin d) :
    MPOTensor.mpo M N u v =
      ∑ j : Fin S.basisCount,
        S.coeff N j * MPOTensor.mpo (S.basisMPOTensor j) N u v := by
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig, hM N hN,
    S.mpv_toTensor_eq_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
    S.basisMPOTensor_toMPSTensor]

/-- The normalized closing matrix of sector (j) after tracing a tail of
length (L):

\[
  \widehat R_j=
  \operatorname{tr}(\rho^{(L+3)})^{-1}
  q_j\mathcal B_j^L.
\]

The unnormalized factor (q_j\mathcal B_j^L) is
`threeSiteClosingMatrix`.  The additional scalar is exactly the normalization
in the density operator (sigma^{(L+3)}).

Source: arXiv:1606.00608, lines 792--793 and Appendix C.2, lines
1714--1732. -/
noncomputable def normalizedThreeSiteClosingMatrix
    {D : ℕ} (M : MPOTensor d D) (S : SectorDecomposition (d * d))
    (L : ℕ) (j : Fin S.basisCount) :
    Matrix (Fin (S.basisDim j)) (Fin (S.basisDim j)) ℂ :=
  (Matrix.trace (MPOTensor.mpo M (L + 3)))⁻¹ •
    S.threeSiteClosingMatrix L j

/-- A nonzero unnormalized closing matrix remains nonzero after density-operator
normalization, provided the total state has nonzero trace.

Source: arXiv:1606.00608, lines 792--793 and Appendix C.2, lines
1714--1718. -/
theorem normalizedThreeSiteClosingMatrix_ne_zero
    {D : ℕ} (M : MPOTensor d D) (S : SectorDecomposition (d * d))
    (L : ℕ) (j : Fin S.basisCount)
    (htrace : Matrix.trace (MPOTensor.mpo M (L + 3)) ≠ 0)
    (hR : S.threeSiteClosingMatrix L j ≠ 0) :
    S.normalizedThreeSiteClosingMatrix M L j ≠ 0 := by
  exact smul_ne_zero (inv_ne_zero htrace) hR

/-- Under copy independence and simplicity, the one-site-tail closing matrix
is nonzero in every sector.  Thus the common choice may be made at total
chain length four, the length used by the formal SAL-to-Markov theorem.

Source: arXiv:1606.00608, simplicity at lines 815--822 and Appendix C.2,
lines 1646--1665 and 1714--1718. -/
theorem threeSiteClosingMatrix_one_ne_zero
    (S : SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (MPOTensor.doubledPhysTraceTransfer d (S.basis j)))
    (j : Fin S.basisCount) :
    S.threeSiteClosingMatrix 1 j ≠ 0 := by
  have hTail :
      (MPOTensor.doubledPhysTraceTransfer d (S.basis j)) ^ 1 ≠ 0 := by
    intro hzero
    exact hnonNil j ⟨1, hzero⟩
  exact smul_ne_zero
    (S.coeff_ne_zero_of_weight_copy_independent hWeight 4 j) hTail

end MPSTensor.SectorDecomposition

namespace MPOTensor

variable {d D : ℕ}

/-- Tracing a tail of length (L) after three exposed sites closes the
three-site word against the (L)-th power of the physical-trace transfer.

Source: arXiv:1606.00608, Appendix C.2, lines 1343--1348 and its Case II use
at lines 1714--1732. -/
theorem sum_mpo_threeSite_prefix_diagonal_tail
    (K : MPOTensor d D) (L : ℕ) (u v : Fin 3 → Fin d) :
    (∑ w : Fin L → Fin d,
      mpo K (3 + L) (Fin.append u w) (Fin.append v w)) =
      Matrix.trace
        (K.evalWord (List.ofFn u) (List.ofFn v) * K.verticalLoop ^ L) := by
  simp only [mpo_apply, mpoMatrixEntry]
  have hwords (a : Fin 3 → Fin d) (w : Fin L → Fin d) :
      List.ofFn (Fin.append a w) = List.ofFn a ++ List.ofFn w := by
    exact List.ofFn_fin_append a w
  simp_rw [hwords]
  have heval (w : Fin L → Fin d) :
      K.evalWord (List.ofFn u ++ List.ofFn w) (List.ofFn v ++ List.ofFn w) =
        K.evalWord (List.ofFn u) (List.ofFn v) *
          K.evalWord (List.ofFn w) (List.ofFn w) := by
    exact K.evalWord_append _ _ _ _ (by simp)
  simp_rw [heval]
  rw [← Matrix.trace_sum]
  congr 1
  rw [← Finset.mul_sum, K.sum_evalWord_diag_eq_verticalLoop_pow]

/-- The normalized three-site reduced state of an MPO with a horizontal BNT
representation is the family closure whose virtual boundaries are the
normalized physical-trace closing matrices.

The matrix is reindexed from length-three configurations to ordered triples
only to match `IsThreeSiteFamilyClosure`.

Source: arXiv:1606.00608, lines 792--793 and Appendix C.2, equations `CFK`,
`sigma3bka`, and `keyformula`, lines 1660--1665 and 1714--1732. -/
theorem reducedBlockState_reindex_isThreeSiteFamilyClosure_of_sameMPV₂Pos
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor) (L : ℕ) :
    IsThreeSiteFamilyClosure
      (fun j ↦ S.basisMPOTensor j)
      (S.normalizedThreeSiteClosingMatrix M L)
      (Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
        (_root_.finThreeArrowEquiv (Fin d))
        (M.reducedBlockState (L + 3) 3 (by omega))) := by
  classical
  unfold IsThreeSiteFamilyClosure
  intro i₁ i₂ i₃ j₁ j₂ j₃
  let u : Fin 3 → Fin d := ![i₁, i₂, i₃]
  let v : Fin 3 → Fin d := ![j₁, j₂, j₃]
  have hReduced :
      M.reducedBlockState (L + 3) 3 (by omega) u v =
        (Matrix.trace (M.mpo (L + 3)))⁻¹ *
          ∑ w : Fin L → Fin d,
            M.mpo (3 + L) (Fin.append u w) (Fin.append v w) := by
    rw [reducedBlockState_eq_sum]
    simp only [normalizedMPO, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [mpo_apply, mpoMatrixEntry]
    have hwords (a : Fin 3 → Fin d) :
        List.ofFn
            (Fin.append a w ∘ Fin.cast (show L + 3 = 3 + L by omega)) =
          List.ofFn a ++ List.ofFn w := by
      rw [← List.ofFn_fin_append]
      apply List.ext_getElem
      · simp
        omega
      · intro n hn₁ hn₂
        simp only [List.getElem_ofFn, Function.comp_apply]
        congr 1
    rw [hwords u, hwords v, List.ofFn_fin_append, List.ofFn_fin_append]
    rfl
  rw [Matrix.reindex_apply]
  change M.reducedBlockState (L + 3) 3 (by omega) u v = _
  rw [hReduced]
  have hMpoExpand (u' v' : Fin (3 + L) → Fin d) :
      mpo M (3 + L) u' v' = ∑ j : Fin S.basisCount,
        S.coeff (3 + L) j * mpo (S.basisMPOTensor j) (3 + L) u' v' :=
    S.mpo_eq_sum_coeff_basisMPOTensor M hM (by omega) u' v'
  simp_rw [hMpoExpand]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ w, (Matrix.trace (M.mpo (L + 3)))⁻¹ *
          (S.coeff (3 + L) j *
            mpo (S.basisMPOTensor j) (3 + L) (Fin.append u w) (Fin.append v w))) =
        ((Matrix.trace (M.mpo (L + 3)))⁻¹ * S.coeff (3 + L) j) *
          ∑ w, mpo (S.basisMPOTensor j) (3 + L)
            (Fin.append u w) (Fin.append v w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = ((Matrix.trace (M.mpo (L + 3)))⁻¹ * S.coeff (3 + L) j) *
          Matrix.trace
            ((S.basisMPOTensor j).evalWord (List.ofFn u) (List.ofFn v) *
              (S.basisMPOTensor j).verticalLoop ^ L) := by
      rw [sum_mpo_threeSite_prefix_diagonal_tail]
    _ = Matrix.trace
          (S.basisMPOTensor j i₁ j₁ * S.basisMPOTensor j i₂ j₂ *
            S.basisMPOTensor j i₃ j₃ *
              S.normalizedThreeSiteClosingMatrix M L j) := by
      simp only [MPSTensor.SectorDecomposition.normalizedThreeSiteClosingMatrix,
        MPSTensor.SectorDecomposition.threeSiteClosingMatrix,
        MPSTensor.SectorDecomposition.basisMPOTensor_verticalLoop,
        Matrix.mul_smul, Matrix.trace_smul,
        smul_smul, smul_eq_mul]
      have hcoeff : S.coeff (L + 3) j = S.coeff (3 + L) j := by
        congr 1
        omega
      rw [hcoeff]
      simp [MPSTensor.SectorDecomposition.basisMPOTensor, u, v,
        evalWord, Matrix.mul_assoc]

/-- At chain length four, the normalized three-site reduced state is a BNT
family closure with every closing matrix nonzero.

This is the form directly compatible with the four-site SAL-to-Markov
decomposition.  No independent closing-matrix hypothesis remains: SAL gives
the nonzero normalization, copy independence gives the nonzero coefficient,
and simplicity gives the nonzero physical-trace tail.

Source: arXiv:1606.00608, simplicity and SAL at lines 815--822, and Appendix
C.2, lines 1646--1665 and 1714--1732. -/
theorem reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (hSAL : IsSAL M) :
    IsThreeSiteFamilyClosure
        (fun j ↦ S.basisMPOTensor j)
        (S.normalizedThreeSiteClosingMatrix M 1)
        (Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
          (_root_.finThreeArrowEquiv (Fin d))
          (M.reducedBlockState 4 3 (by omega))) ∧
      ∀ j : Fin S.basisCount,
        S.normalizedThreeSiteClosingMatrix M 1 j ≠ 0 := by
  obtain ⟨_hMPDO, htrace, _hSAL⟩ := hSAL
  constructor
  · simpa using
      reducedBlockState_reindex_isThreeSiteFamilyClosure_of_sameMPV₂Pos M S hM 1
  · intro j
    exact S.normalizedThreeSiteClosingMatrix_ne_zero M 1 j
      (htrace 4 (by omega))
      (S.threeSiteClosingMatrix_one_ne_zero hWeight hnonNil j)

end MPOTensor
