/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondRegroupingLocality
import TNLean.Algebra.MatrixProjectionReindex
import TNLean.MPS.Symmetry.BondProductPhysicalParentHamiltonian
import TNLean.MPS.Symmetry.GappedInteractionPath
import TNLean.MPS.MPDO.CommutingBondEtaCyclicCore
import TNLean.MPS.MPDO.EmbedLocalOperatorMonomial
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Two-site interaction of an independent virtual bond

A bond operator acts on the right register of the first physical site and
the left register of the second, with identities on the two exterior
registers. This is the local interaction of Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.D.2, `eq:phase-nosym:iso-hamiltonian`.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator

namespace MPSTensor

/-- Enumerate the four registers of two physical sites in the order
`(L₀, (R₀, L₁), R₁)`. Source: arXiv:1010.3732, Section II.D.2,
`fig:iso-injective`. -/
def twoSiteBondEquiv (D : ℕ) :
    (Fin 2 → Fin (D * D)) ≃ (Fin D × (Fin D × Fin D)) × Fin D where
  toFun s := (((finProdFinEquiv.symm (s 0)).1,
    ((finProdFinEquiv.symm (s 0)).2, (finProdFinEquiv.symm (s 1)).1)),
    (finProdFinEquiv.symm (s 1)).2)
  invFun x := ![finProdFinEquiv (x.1.1, x.1.2.1),
    finProdFinEquiv (x.1.2.2, x.2)]
  left_inv s := by
    funext i
    fin_cases i
    · exact finProdFinEquiv.apply_symm_apply (s 0)
    · exact finProdFinEquiv.apply_symm_apply (s 1)
  right_inv x := by simp

/-- Place a bond matrix on the middle two registers of two physical sites.
Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
noncomputable def twoSiteBondInteraction {D : ℕ}
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    MPOTensor.ChainOperator (D * D) 2 :=
  Matrix.reindex (twoSiteBondEquiv D).symm (twoSiteBondEquiv D).symm
    (((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ K) ⊗ₖ
      (1 : Matrix (Fin D) (Fin D) ℂ))

/-- The exterior registers carry identity factors in the two-site bond
interaction. Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondInteraction_apply {D : ℕ}
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (s t : Fin 2 → Fin (D * D)) :
    twoSiteBondInteraction K s t =
      (if (finProdFinEquiv.symm (s 0)).1 = (finProdFinEquiv.symm (t 0)).1 then 1 else 0) *
      K ((finProdFinEquiv.symm (s 0)).2, (finProdFinEquiv.symm (s 1)).1)
        ((finProdFinEquiv.symm (t 0)).2, (finProdFinEquiv.symm (t 1)).1) *
      (if (finProdFinEquiv.symm (s 1)).2 = (finProdFinEquiv.symm (t 1)).2 then 1 else 0) := by
  simp [twoSiteBondInteraction, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    twoSiteBondEquiv, Matrix.one_apply]

/-- A bond projection gives an orthogonal projection on the two physical
sites. Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondInteraction_isStarProjection {D : ℕ}
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (hK : IsStarProjection K) :
    IsStarProjection (twoSiteBondInteraction K) := by
  let B := ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ K) ⊗ₖ
    (1 : Matrix (Fin D) (Fin D) ℂ)
  have hBB : B * B = B := by
    dsimp only [B]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hK.isIdempotentElem.eq]
    simp
  apply Matrix.isStarProjection_reindex
  refine ⟨hBB, ?_⟩
  simp only [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    hK.isSelfAdjoint.isHermitian.eq]

/-- A projection-valued bond interaction has operator norm at most one,
as required in arXiv:1010.3732, `sec:phases-definition-no-sym`, line 422. -/
theorem twoSiteBondInteraction_norm_le_one {D : ℕ}
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (hK : IsStarProjection K) :
    ‖twoSiteBondInteraction K‖ ≤ 1 :=
  IsStarProjection.norm_le _ (twoSiteBondInteraction_isStarProjection K hK)

private def singleSectorRegisterEquiv (D : ℕ) :
    Matrix.EtaSiteIndex 1 (fun _ => D) (fun _ => D) ≃ Fin (D * D) where
  toFun x := finProdFinEquiv (x.2.2, x.2.1)
  invFun x := ⟨0, ((finProdFinEquiv.symm x).2, (finProdFinEquiv.symm x).1)⟩
  left_inv x := by
    obtain ⟨q, a, b⟩ := x
    have hq : q = 0 := Subsingleton.elim _ _
    subst q
    simp only [Equiv.symm_apply_apply]
  right_inv x := finProdFinEquiv.apply_symm_apply x

private theorem twoSiteBondInteraction_etaPair {D : ℕ}
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    Matrix.reindex (Matrix.etaPairSpatialBlockEquiv (singleSectorRegisterEquiv D)).symm
      (Matrix.etaPairSpatialBlockEquiv (singleSectorRegisterEquiv D)).symm
      (Matrix.reindex (finTwoArrowEquiv (Fin (D * D)))
        (finTwoArrowEquiv (Fin (D * D))) (twoSiteBondInteraction K)) =
      Matrix.blockDiagonal' (fun _ : Fin 1 × Fin 1 =>
        ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ K) ⊗ₖ
          (1 : Matrix (Fin D) (Fin D) ℂ)) := by
  ext x y
  obtain ⟨q, x⟩ := x
  obtain ⟨r, y⟩ := y
  have hr : r = q := Subsingleton.elim _ _
  subst r
  rw [Matrix.blockDiagonal'_apply_eq]
  simp [Matrix.reindex_apply, Matrix.etaPairSpatialBlockEquiv, singleSectorRegisterEquiv,
    twoSiteBondInteraction_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Embedding the two-site interaction acts on the outgoing bond and is
identity on every other bond. Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
theorem embed_twoSiteBondInteraction_apply {D N : ℕ} [NeZero N]
    (hN : 2 ≤ N) (i : Fin N)
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (s t : Fin N → Fin (D * D)) :
    MPOTensor.embedLocalOperator 2 N hN i (twoSiteBondInteraction K) s t =
      ∏ n, if n = i then
        K ((finProdFinEquiv.symm (s n)).2, (finProdFinEquiv.symm (s (n + 1))).1)
          ((finProdFinEquiv.symm (t n)).2, (finProdFinEquiv.symm (t (n + 1))).1)
      else if ((finProdFinEquiv.symm (s n)).2,
          (finProdFinEquiv.symm (s (n + 1))).1) =
        ((finProdFinEquiv.symm (t n)).2,
          (finProdFinEquiv.symm (t (n + 1))).1) then 1 else 0 := by
  let e := singleSectorRegisterEquiv D
  let k : Fin N → Fin 1 := fun _ => 0
  let sx : (n : Fin N) → Fin D × Fin D :=
    fun n => ((finProdFinEquiv.symm (s n)).2, (finProdFinEquiv.symm (s n)).1)
  let tx : (n : Fin N) → Fin D × Fin D :=
    fun n => ((finProdFinEquiv.symm (t n)).2, (finProdFinEquiv.symm (t n)).1)
  let x := Matrix.etaFixedSectorCyclicEdgeEquiv (fun _ : Fin 1 => D) (fun _ => D) k sx
  let y := Matrix.etaFixedSectorCyclicEdgeEquiv (fun _ : Fin 1 => D) (fun _ => D) k tx
  have hs : (Matrix.etaCyclicEdgeEquiv (fun _ : Fin 1 => D) (fun _ => D) e).symm
      ⟨k, x⟩ = s := by
    funext n
    rw [Matrix.etaCyclicEdgeEquiv_symm_apply]
    simp only [x, Equiv.symm_apply_apply]
    exact finProdFinEquiv.apply_symm_apply (s n)
  have ht : (Matrix.etaCyclicEdgeEquiv (fun _ : Fin 1 => D) (fun _ => D) e).symm
      ⟨k, y⟩ = t := by
    funext n
    rw [Matrix.etaCyclicEdgeEquiv_symm_apply]
    simp only [y, Equiv.symm_apply_apply]
    exact finProdFinEquiv.apply_symm_apply (t n)
  have h := MPOTensor.reindex_embedLocalOperator_etaPairBond hN
    (fun _ : Fin 1 => D) (fun _ => D) e (fun _ _ => K)
    (Matrix.reindex (finTwoArrowEquiv (Fin (D * D)))
      (finTwoArrowEquiv (Fin (D * D))) (twoSiteBondInteraction K))
    (twoSiteBondInteraction_etaPair K) i
  have hentry := congrArg (fun M => M ⟨k, x⟩ ⟨k, y⟩) h
  have hcancel : Matrix.reindex (finTwoArrowEquiv (Fin (D * D))).symm
      (finTwoArrowEquiv (Fin (D * D))).symm
      (Matrix.reindex (finTwoArrowEquiv (Fin (D * D)))
        (finTwoArrowEquiv (Fin (D * D))) (twoSiteBondInteraction K)) =
      twoSiteBondInteraction K :=
    (Matrix.reindex (finTwoArrowEquiv (Fin (D * D)))
      (finTwoArrowEquiv (Fin (D * D)))).symm_apply_apply _
  rw [hcancel] at hentry
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hs, ht,
    Matrix.blockDiagonal'_apply_eq] at hentry
  change MPOTensor.embedLocalOperator 2 N hN i (twoSiteBondInteraction K) s t =
    ∏ n, if n ∈ ({i} : Finset (Fin N)) then K (x n) (y n)
      else if x n = y n then 1 else 0 at hentry
  simpa only [Finset.mem_singleton, x, y, Matrix.etaFixedSectorCyclicEdgeEquiv_apply,
    sx, tx] using hentry

/-- The two-site interaction beginning at `i` is the incoming bond term at
its successor, transported to physical coordinates. Source:
arXiv:1010.3732, Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem embed_twoSiteBondInteraction_eq_conj {D N : ℕ} [NeZero N]
    (hN : 2 ≤ N) (i : Fin N)
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    MPOTensor.embedLocalOperator 2 N hN i (twoSiteBondInteraction K) =
      (incomingBondPerm D N).permMatrix ℂ *
        MPOTensor.embedLocalOperator 1 N (by omega) (finRotate N i)
          (MPOTensor.oneSiteOperator (Matrix.reindex finProdFinEquiv finProdFinEquiv K)) *
        ((incomingBondPerm D N).permMatrix ℂ).conjTranspose := by
  classical
  ext s t
  rw [embed_twoSiteBondInteraction_apply, incomingBondPerm_conj_local_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← Equiv.prod_comp (finRotate N) (fun j =>
    if j = finRotate N i then K (incomingBondEquiv D N s j) (incomingBondEquiv D N t j)
    else if incomingBondEquiv D N s j = incomingBondEquiv D N t j then 1 else 0)]
  apply Finset.prod_congr rfl
  intro n _
  simp [incomingBondEquiv, finRotate_apply, finRotate_symm_apply]

/-- The transported independent-bond parent Hamiltonian is the sum of one
translation-invariant two-site interaction. Source: arXiv:1010.3732,
Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem interactionHamiltonian_twoSiteBondPenalty {D N : ℕ} [NeZero N]
    (hN : 2 ≤ N) (η : Fin (D * D) → ℂ) :
    interactionHamiltonian
      (twoSiteBondInteraction (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty η))) hN =
      physicalBondProductParentHamiltonian η (by omega) := by
  unfold interactionHamiltonian physicalBondProductParentHamiltonian bondProductParentHamiltonian
  simp_rw [embed_twoSiteBondInteraction_eq_conj]
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
    Matrix.submatrix_id_id]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Equiv.sum_comp (finRotate N) (fun i =>
    (incomingBondPerm D N).permMatrix ℂ * bondPenaltyAt η (by omega) i *
      ((incomingBondPerm D N).permMatrix ℂ)ᴴ)

end MPSTensor
