/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TwistedDimerFactorStates
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.Algebra.MatrixCyclicPathSum

/-!
# The mixed-Bell bond dimer

The matrix-unit construction in `Notes/OpenProblemsTN/strategies/
p6_round44_graded_dimer_twist.tex`, Proposition `prop:p6-r44-dimer`, specialized
to the Bell weights seven eighths and one eighth. This is a project example
motivated by arXiv:1606.00608, lines 995--1010, not a tensor printed there.
Only the bond state and its renormalization channels are considered here;
no assertion about canonical coefficients or simplicity is made.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder

noncomputable section

namespace MPOTensor.TwistedDimer

/-- The left and right qubits of a four-dimensional physical site. -/
def bondSiteEquiv : Bond ≃ Fin 4 := finProdFinEquiv

/-- The matrix-unit tensor of the mixed-Bell dimer. -/
def sigmaDimer : MPOTensor 4 4 := fun i j =>
  let a := bondSiteEquiv.symm i
  let b := bondSiteEquiv.symm j
  Matrix.single (bondSiteEquiv (a.1, b.1)) (bondSiteEquiv (a.2, b.2))
    (Cmat 0 a.1 b.1 : ℂ)

/-- The one-site closure retains the two exterior qubits. -/
lemma sigmaDimer_physClose1 (X : Matrix (Fin 4) (Fin 4) ℂ) (a b : Bond) :
    physClose1 sigmaDimer X (bondSiteEquiv a) (bondSiteEquiv b) =
      (Cmat 0 a.1 b.1 : ℂ) * X (bondSiteEquiv (a.2, b.2))
        (bondSiteEquiv (a.1, b.1)) := by
  simp [physClose1_apply, sigmaDimer, Matrix.trace_single_mul]

/-- Two letters contract precisely when both intermediate qubits agree. -/
lemma sigmaDimer_mul (a b c d : Bond) :
    sigmaDimer (bondSiteEquiv a) (bondSiteEquiv b) *
      sigmaDimer (bondSiteEquiv c) (bondSiteEquiv d) =
      if a.2 = c.1 ∧ b.2 = d.1 then
        Matrix.single (bondSiteEquiv (a.1, b.1)) (bondSiteEquiv (c.2, d.2))
          ((Cmat 0 a.1 b.1 : ℂ) * (Cmat 0 c.1 d.1 : ℂ)) else 0 := by
  simp only [sigmaDimer, Equiv.symm_apply_apply]
  split_ifs with h
  · rw [h.1, h.2, Matrix.single_mul_single_same]
  · apply Matrix.single_mul_single_of_ne
    intro he
    exact h (Prod.mk.inj (bondSiteEquiv.injective he))

/-- Regroup an exterior site and an inserted bond into two physical sites:
$((l,r),(u,v))\mapsto((l,u),(v,r))$. -/
def bondInsertionEquiv : (Fin 4 × Bond) ≃ (Fin 4 × Fin 4) where
  toFun a := (bondSiteEquiv ((bondSiteEquiv.symm a.1).1, a.2.1),
    bondSiteEquiv (a.2.2, (bondSiteEquiv.symm a.1).2))
  invFun a := (bondSiteEquiv ((bondSiteEquiv.symm a.1).1,
    (bondSiteEquiv.symm a.2).2),
    ((bondSiteEquiv.symm a.1).2, (bondSiteEquiv.symm a.2).1))
  left_inv a := by simp
  right_inv a := by simp

/-- Refinement adjoins the exact normalized Bell mixture and regroups the qubits. -/
def sigmaDimerRefine : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ]
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  Matrix.equivReindexMap bondInsertionEquiv ∘ₗ Matrix.preparationMap sigma

/-- Coarse-graining undoes the regrouping and traces out the inserted bond. -/
def sigmaDimerCoarse : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ →ₗ[ℂ]
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.partialTraceRightLM ∘ₗ Matrix.equivReindexMap bondInsertionEquiv.symm

/-- The source two-letter identity, valid for every virtual boundary matrix. -/
theorem sigmaDimerRefine_physClose1 (X : Matrix (Fin 4) (Fin 4) ℂ) :
    sigmaDimerRefine (physClose1 sigmaDimer X) = physClose2 sigmaDimer X := by
  ext i j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  obtain ⟨a, rfl⟩ := bondSiteEquiv.surjective i₁
  obtain ⟨b, rfl⟩ := bondSiteEquiv.surjective j₁
  obtain ⟨c, rfl⟩ := bondSiteEquiv.surjective i₂
  obtain ⟨d, rfl⟩ := bondSiteEquiv.surjective j₂
  have hr (Y : Matrix (Fin 4) (Fin 4) ℂ) :
      sigmaDimerRefine Y (bondSiteEquiv a, bondSiteEquiv c)
        (bondSiteEquiv b, bondSiteEquiv d) =
      Y (bondSiteEquiv (a.1, c.2)) (bondSiteEquiv (b.1, d.2)) *
        sigma (a.2, c.1) (b.2, d.1) := by
    change Y _ _ * sigma _ _ = _
    simp [bondInsertionEquiv]
  rw [hr]
  rw [sigmaDimer_physClose1, sigma, bondState_apply, physClose2_apply, sigmaDimer_mul]
  split_ifs <;> simp_all [Matrix.trace_single_mul, mul_assoc, mul_comm, mul_left_comm]

/-- Regroup physical sites into incoming bonds, with the predecessor taken cyclically. -/
def incomingBondEquiv (N : ℕ) : (Fin N → Fin 4) ≃ (Fin N → Bond) where
  toFun s m := ((bondSiteEquiv.symm (s ((finRotate N).symm m))).2,
    (bondSiteEquiv.symm (s m)).1)
  invFun a m := bondSiteEquiv ((a m).2, (a (finRotate N m)).1)
  left_inv s := by
    funext m
    simp only [Equiv.symm_apply_apply, Prod.eta, Equiv.apply_symm_apply]
  right_inv a := by
    funext m
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.eta]

/-- Contracting the matrix units fixes a unique cyclic virtual path. -/
private lemma sigmaDimer_mpo_entry (N : ℕ) (s t : Fin (N + 1) → Fin 4) :
    mpo sigmaDimer (N + 1) s t = ∏ m,
      if (bondSiteEquiv.symm (s m)).2 =
          (bondSiteEquiv.symm (s (finRotate (N + 1) m))).1 ∧
        (bondSiteEquiv.symm (t m)).2 =
          (bondSiteEquiv.symm (t (finRotate (N + 1) m))).1 then
        (Cmat 0 (bondSiteEquiv.symm (s m)).1 (bondSiteEquiv.symm (t m)).1 : ℂ)
      else 0 := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn, Matrix.trace_ofFn_prod_eq_sum_cyclic]
  let p : Fin (N + 1) → Fin 4 := fun m => bondSiteEquiv
    ((bondSiteEquiv.symm (s m)).1, (bondSiteEquiv.symm (t m)).1)
  rw [Finset.sum_eq_single p]
  · apply Finset.prod_congr rfl
    intro m _
    simp [sigmaDimer, p, Matrix.single_apply, Prod.mk.injEq]
  · intro q _ hq
    obtain ⟨m, hm⟩ := Function.ne_iff.mp hq
    apply Finset.prod_eq_zero (Finset.mem_univ m)
    exact Matrix.single_apply_of_row_ne (Ne.symm hm) _ _ _
  · simp

/-- At positive length the closed dimer is the product of the exact mixed-Bell
bond states in incoming-bond coordinates. The empty MPO has trace four and is excluded. -/
theorem mpo_sigmaDimer_eq_bondProduct {N : ℕ} (hN : 0 < N) :
    mpo sigmaDimer N = (powN sigma N).submatrix (incomingBondEquiv N)
      (incomingBondEquiv N) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  ext s t
  rw [sigmaDimer_mpo_entry]
  change _ = ∏ m, sigma (incomingBondEquiv (N + 1) s m)
    (incomingBondEquiv (N + 1) t m)
  simp only [sigma, bondState_apply, incomingBondEquiv, Equiv.coe_fn_mk]
  by_cases hs : ∀ m, (bondSiteEquiv.symm (s m)).2 =
      (bondSiteEquiv.symm (s (finRotate (N + 1) m))).1 ∧
      (bondSiteEquiv.symm (t m)).2 =
      (bondSiteEquiv.symm (t (finRotate (N + 1) m))).1
  · apply Finset.prod_congr rfl
    intro m _
    have hp := hs ((finRotate (N + 1)).symm m)
    simp only [Equiv.apply_symm_apply] at hp
    simp only [hs m, hp]
  · push Not at hs
    obtain ⟨m, hm⟩ := hs
    have hleft : (∏ n : Fin (N + 1), if
        (bondSiteEquiv.symm (s n)).2 = (bondSiteEquiv.symm
          (s (finRotate (N + 1) n))).1 ∧
        (bondSiteEquiv.symm (t n)).2 = (bondSiteEquiv.symm
          (t (finRotate (N + 1) n))).1 then
        (Cmat 0 (bondSiteEquiv.symm (s n)).1 (bondSiteEquiv.symm (t n)).1 : ℂ)
        else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ m)
      simp only [ite_eq_right (not_and.mpr hm)]
    rw [hleft]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ (finRotate (N + 1) m))
    simp only [Equiv.symm_apply_apply, ite_eq_right (not_and.mpr hm)]

/-- The exact bond dimer is positive at every positive chain length. -/
theorem sigmaDimer_isMPDO : IsMPDO sigmaDimer := by
  intro N hN
  rw [mpo_sigmaDimer_eq_bondProduct hN]
  exact (Matrix.finKronecker_posSemidef (fun _ : Fin N => sigma)
    (fun _ => sigma_posSemidef)).submatrix (incomingBondEquiv N)

/-- Every positive-length bond dimer has trace one. -/
theorem trace_mpo_sigmaDimer {N : ℕ} (hN : 0 < N) :
    (mpo sigmaDimer N).trace = 1 := by
  rw [mpo_sigmaDimer_eq_bondProduct hN]
  exact ((incomingBondEquiv N).sum_comp (fun a => powN sigma N a a)).trans
    (trace_powN_sigma N)

/-- Inserting the normalized positive bond state is a quantum channel. -/
theorem sigmaDimerRefine_isKrausCPTP : IsKrausCPTP sigmaDimerRefine :=
  isKrausCPTP_comp
    (Matrix.preparationMap_isKrausCPTP sigma sigma_posSemidef trace_sigma)
    (Matrix.equivReindexMap_isKrausCPTP bondInsertionEquiv)

/-- Undoing the permutation and tracing the inserted bond is a quantum channel. -/
theorem sigmaDimerCoarse_isKrausCPTP : IsKrausCPTP sigmaDimerCoarse :=
  isKrausCPTP_comp (Matrix.equivReindexMap_isKrausCPTP bondInsertionEquiv.symm)
    Matrix.partialTraceRightLM_isKrausCPTP

/-- Coarse-graining reverses refinement on every input operator. -/
lemma sigmaDimerCoarse_refine (Y : Matrix (Fin 4) (Fin 4) ℂ) :
    sigmaDimerCoarse (sigmaDimerRefine Y) = Y := by
  have h : Matrix.equivReindexMap bondInsertionEquiv.symm
      (Matrix.equivReindexMap bondInsertionEquiv (Matrix.preparationMap sigma Y)) =
      Matrix.preparationMap sigma Y := by
    ext i j
    change (Matrix.preparationMap sigma Y)
      (bondInsertionEquiv.symm (bondInsertionEquiv i))
      (bondInsertionEquiv.symm (bondInsertionEquiv j)) = _
    simp only [Equiv.symm_apply_apply]
  change Matrix.partialTraceRightLM
    (Matrix.equivReindexMap bondInsertionEquiv.symm
      (Matrix.equivReindexMap bondInsertionEquiv (Matrix.preparationMap sigma Y))) = Y
  rw [h]
  change Matrix.partialTraceRight (Y ⊗ₖ sigma) = Y
  rw [Matrix.partialTraceRight_kronecker, trace_sigma, one_smul]

/-- The coarse-graining closure equation holds for arbitrary virtual boundaries. -/
theorem sigmaDimerCoarse_physClose2 (X : Matrix (Fin 4) (Fin 4) ℂ) :
    sigmaDimerCoarse (physClose2 sigmaDimer X) = physClose1 sigmaDimer X := by
  rw [← sigmaDimerRefine_physClose1, sigmaDimerCoarse_refine]

/-- The mixed-Bell bond dimer satisfies the two quantum-channel equations of
CPSV16 Definition 4.1, by the insertion and partial-trace construction of
Proposition `prop:p6-r44-dimer` in the graded dimer twist note. -/
theorem sigmaDimer_isRFPViaTS : IsRFPViaTS sigmaDimer :=
  ⟨sigmaDimerCoarse, sigmaDimerRefine, sigmaDimerCoarse_isKrausCPTP,
    sigmaDimerRefine_isKrausCPTP, sigmaDimerCoarse_physClose2,
    sigmaDimerRefine_physClose1⟩

/-- Split each physical site into its left/right qubits and its flag, without
moving any qubit between sites. This is distinct from the incoming-bond regrouping. -/
def onsiteBondFlagEquiv (N : ℕ) :
    (Fin N → Fin 8) ≃ (Fin N → Fin 4) × (Fin N → Fin 2) where
  toFun s := (fun m => bondSiteEquiv (bitL (s m), bitR (s m)), fun m => bitF (s m))
  invFun a m := physIdx (bondSiteEquiv.symm (a.1 m)).1
    (bondSiteEquiv.symm (a.1 m)).2 (a.2 m)
  left_inv s := by funext m; simp only [Equiv.symm_apply_apply, physIdx_bits]
  right_inv a := by
    apply Prod.ext <;> funext m
    · simp only [bitL_physIdx, bitR_physIdx, Prod.eta, Equiv.apply_symm_apply]
    · exact bitF_physIdx _ _ _

/-- The on-site split followed by incoming-bond regrouping agrees with the
bond/flag coordinates of the explicit unitary factorization. -/
lemma onsiteBondFlagEquiv_incoming (N : ℕ) :
    (onsiteBondFlagEquiv N).trans
      (Equiv.prodCongr (incomingBondEquiv N) (Equiv.refl _)) =
      (incomingCellEquiv N).trans (bondFlagEquiv N) := by
  apply Equiv.ext
  intro s
  apply Prod.ext
  · funext m
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, onsiteBondFlagEquiv,
      incomingBondEquiv, incomingCellEquiv, bondFlagEquiv, Equiv.coe_fn_mk,
      Equiv.arrowProdEquivProdArrow_apply, Prod.map_fst, Equiv.symm_apply_apply]
  · rfl

/-- At positive length the decorated state is the on-site reindexing of the
Kronecker product of the exact bond-dimer MPO and normalized Example 4.12 MPO.
At length zero these expressions instead have entries two and eight. -/
theorem decoratedState_eq_mpo_factors {N : ℕ} (hN : 0 < N) :
    decoratedState N =
      (mpo sigmaDimer N ⊗ₖ mpo CPSVExample412NormalizedRFP.Mhat N).submatrix
        (onsiteBondFlagEquiv N) (onsiteBondFlagEquiv N) := by
  rw [mpo_sigmaDimer_eq_bondProduct hN, ← evenFlagState_eq_mpo_Mhat]
  ext s t
  have hs := Equiv.congr_fun (onsiteBondFlagEquiv_incoming N) s
  have ht := Equiv.congr_fun (onsiteBondFlagEquiv_incoming N) t
  change _ = powN sigma N _ _ * evenFlagState N _ _
  change (powN sigma N ⊗ₖ evenFlagState N) _ _ = _
  rw [← hs, ← ht]
  rfl

/-- The twisted-dimer MPO is unitarily conjugate to the on-site product of
the two explicit RFP tensor families. The conjugating unitary acts across site
boundaries; this does not assert strict on-site or virtual-gauge tensor equivalence. -/
theorem mpo_eq_unitary_mpo_factors {N : ℕ} (hN : 0 < N) :
    mpo T N = chainUnitary N *
      (mpo sigmaDimer N ⊗ₖ mpo CPSVExample412NormalizedRFP.Mhat N).submatrix
        (onsiteBondFlagEquiv N) (onsiteBondFlagEquiv N) * (chainUnitary N)ᴴ := by
  rw [mpo_eq_unitary_factorization hN, decoratedState_eq_mpo_factors hN]

end MPOTensor.TwistedDimer
