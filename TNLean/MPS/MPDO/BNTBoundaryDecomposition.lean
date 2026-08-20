/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTProjectorSelection
import TNLean.MPS.MPDO.PhysicalClosure
import TNLean.MPS.MPDO.SourceSimpleScaling
import TNLean.MPS.SharedInfra.BoundaryDecomposition

/-!
# Virtual boundaries of canonical BNT sums

An exact canonical BNT reconstruction determines every open virtual-boundary
closure of the original MPO tensor. After transporting the boundary through
the canonical gauge, only its diagonal copy blocks remain. The same boundary
transformation applies at every chain length.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  bicanonical-form gauge convention at lines 1666--1674, and Appendix C.2,
  lines 1646--1665 and 1810--1825.
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor

variable {d : ℕ}

/-- The MPO representative carried by one flattened copy of a canonical BNT
sum. Copies with the same outer label give the same tensor after the canonical
bond-dimension identification. -/
def flatBasisMPOTensor (S : MPSTensor.SectorDecomposition (d * d))
    (s : Fin S.totalCopies) : MPOTensor d (S.flatDim s) :=
  fun a b ↦ S.flatBasis s (finProdFinEquiv (a, b))

@[simp]
theorem flatBasisMPOTensor_toMPSTensor
    (S : MPSTensor.SectorDecomposition (d * d)) (s : Fin S.totalCopies) :
    (flatBasisMPOTensor S s).toMPSTensor = S.flatBasis s := by
  funext ab
  change S.flatBasis s (finProdFinEquiv (ab.divNat, ab.modNat)) =
    S.flatBasis s ab
  exact congrArg (S.flatBasis s) (finProdFinEquiv.apply_symm_apply ab)

@[simp]
theorem evalWord_flatBasisMPOTensor_pairConfig
    (S : MPSTensor.SectorDecomposition (d * d)) (s : Fin S.totalCopies)
    {N : ℕ} (σ τ : Fin N → Fin d) :
    MPSTensor.evalWord (S.flatBasis s)
        (List.ofFn fun k ↦ finProdFinEquiv (σ k, τ k)) =
      evalWord (flatBasisMPOTensor S s) (List.ofFn σ) (List.ofFn τ) := by
  rw [← flatBasisMPOTensor_toMPSTensor]
  exact evalWord_toMPSTensor_pairConfig (flatBasisMPOTensor S s) σ τ

/-- Sum the diagonal virtual-boundary blocks over all repeated copies of one
BNT representative. -/
def representativeBoundary (S : MPSTensor.SectorDecomposition (d * d))
    (Y : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)
    (j : Fin S.basisCount) :
    Matrix (Fin (S.basisDim j)) (Fin (S.basisDim j)) ℂ :=
  ∑ q : Fin (S.copies j),
    cast (by rw [S.flatDim_flatIndexEquiv ⟨j, q⟩] :
      Matrix
          (Fin (S.flatDim (S.flatIndexEquiv ⟨j, q⟩)))
          (Fin (S.flatDim (S.flatIndexEquiv ⟨j, q⟩))) ℂ =
        Matrix (Fin (S.basisDim j)) (Fin (S.basisDim j)) ℂ)
      (Matrix.finSigmaDiagonalBlock Y (S.flatIndexEquiv ⟨j, q⟩))

/-- The physical closure of an exact gauge-transformed canonical BNT sum is
the sum of the representative closures with the transported diagonal copy
boundaries.

The formula holds at every length with one boundary transformation
\(G^{-1}XG\). In particular, its specializations at the two closure lengths
in Definition 4.1 use the same representative boundary matrices.

Source: arXiv:1606.00608, canonical form at lines 237--246, bicanonical-form
gauge convention at lines 1666--1674, and Appendix C.2, lines 1646--1665 and
1810--1825. -/
theorem physCloseN_eq_sum_flatBasis_of_gauge_toTensor
    (S : MPSTensor.SectorDecomposition (d * d))
    (M : MPOTensor d S.totalDim)
    (G : GL (Fin S.totalDim) ℂ)
    (hG : ∀ i, M.toMPSTensor i =
      (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))
    (N : ℕ) (X : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) :
    physCloseN M N X =
      ∑ s : Fin S.totalCopies,
        physCloseN (flatBasisMPOTensor S s) N
          ((S.flatWeight s) ^ N •
            Matrix.finSigmaDiagonalBlock
              ((↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * X *
                (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) s) := by
  classical
  ext σ τ
  let w : Fin N → Fin (d * d) := fun k ↦ finProdFinEquiv (σ k, τ k)
  have h := MPSTensor.trace_evalWord_gauge_toTensorFromBlocks_mul
    S.flatWeight S.flatBasis M.toMPSTensor G hG (List.ofFn w) X
  simpa only [physCloseN_apply, Matrix.sum_apply,
    flatBasisMPOTensor_toMPSTensor, evalWord_toMPSTensor_pairConfig,
    evalWord_flatBasisMPOTensor_pairConfig,
    List.length_ofFn, Matrix.smul_mul, Matrix.mul_smul, w,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat] using h

/-- If the repeated-copy weights agree within each BNT representative, the
copy sum is absorbed into the representative and the virtual boundary becomes
the sum of its diagonal copy blocks.

Source: arXiv:1606.00608, Appendix C.2, lines 1646--1665 and 1810--1825. -/
theorem physCloseN_eq_sum_commonWeightAbsorbedBasis_of_gauge_toTensor
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (M : MPOTensor d S.totalDim)
    (G : GL (Fin S.totalDim) ℂ)
    (hG : ∀ i, M.toMPSTensor i =
      (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))
    (N : ℕ) (X : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) :
    physCloseN M N X =
      ∑ j : Fin S.basisCount,
        physCloseN (commonWeightAbsorbedBasisMPOTensor S hWeight j) N
          (representativeBoundary S
            ((↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * X *
              (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) j) := by
  rw [physCloseN_eq_sum_flatBasis_of_gauge_toTensor S M G hG N X]
  ext σ τ
  simp only [Matrix.sum_apply, representativeBoundary, map_sum]
  let Y := (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * X *
    (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)
  let f : ((j : Fin S.basisCount) × Fin (S.copies j)) → ℂ := fun jq ↦
    physCloseN (commonWeightAbsorbedBasisMPOTensor S hWeight jq.1) N
      (cast (by rw [S.flatDim_flatIndexEquiv jq] :
        Matrix
            (Fin (S.flatDim (S.flatIndexEquiv jq)))
            (Fin (S.flatDim (S.flatIndexEquiv jq))) ℂ =
          Matrix (Fin (S.basisDim jq.1)) (Fin (S.basisDim jq.1)) ℂ)
        (Matrix.finSigmaDiagonalBlock Y (S.flatIndexEquiv jq))) σ τ
  let g : Fin S.totalCopies → ℂ := fun s ↦
    physCloseN (flatBasisMPOTensor S s) N
      ((S.flatWeight s) ^ N • Matrix.finSigmaDiagonalBlock Y s) σ τ
  change ∑ s, g s = ∑ j, ∑ q, f ⟨j, q⟩
  calc
    ∑ s, g s = ∑ jq, f jq :=
      (Fintype.sum_equiv S.flatIndexEquiv f g (fun jq ↦ by
        rcases jq with ⟨j, q⟩
        simp only [f, g,
          MPSTensor.SectorDecomposition.flatWeight_flatIndexEquiv]
        rw [hWeight j q ⟨0, S.copies_pos j⟩]
        simp only [physCloseN_apply]
        change Matrix.trace
            (evalWord
                (S.commonWeight hWeight j • S.basisMPOTensor j)
                (List.ofFn σ) (List.ofFn τ) *
              cast _ (Matrix.finSigmaDiagonalBlock Y
                (S.flatIndexEquiv ⟨j, q⟩))) = _
        rw [evalWord_smul _ _ _ _ (by simp)]
        simp only [List.length_ofFn, smul_eq_mul, Algebra.mul_smul_comm,
          Matrix.trace_smul]
        unfold MPSTensor.SectorDecomposition.commonWeight
        rw [Algebra.smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
        apply congrArg (fun z : ℂ ↦ S.weight j ⟨0, S.copies_pos j⟩ ^ N * z)
        rw [← evalWord_toMPSTensor_pairConfig
          (S.basisMPOTensor j) σ τ]
        rw [← evalWord_toMPSTensor_pairConfig
          (flatBasisMPOTensor S (S.flatIndexEquiv ⟨j, q⟩)) σ τ]
        simp only [MPSTensor.SectorDecomposition.basisMPOTensor_toMPSTensor,
          flatBasisMPOTensor_toMPSTensor]
        exact (MPSTensor.trace_evalWord_mul_cast_of_heq
          (S.flatDim_flatIndexEquiv ⟨j, q⟩)
          (S.flatBasis (S.flatIndexEquiv ⟨j, q⟩)) (S.basis j)
          (S.flatBasis_flatIndexEquiv_heq ⟨j, q⟩)
          (List.ofFn fun k ↦ finProdFinEquiv (σ k, τ k))
          (Matrix.finSigmaDiagonalBlock Y
            (S.flatIndexEquiv ⟨j, q⟩))).symm)).symm
    _ = ∑ j, ∑ q, f ⟨j, q⟩ := by
      simpa using Fintype.sum_sigma' (fun j q ↦ f ⟨j, q⟩)

end MPOTensor
