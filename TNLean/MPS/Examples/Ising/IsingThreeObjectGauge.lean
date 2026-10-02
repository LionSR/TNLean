/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Ising.IsingThreeObjectTwist
import TNLean.MPS.Examples.Ising.IsingWeightedTwist
import TNLean.MPS.Examples.Ising.IsingFusionAlgebraSigma

/-!
# An explicit split compression of the three-object Ising product

The four-channel product of the full weighted bond object has a change of
auxiliary coordinates obtained by adjoining the two-object signed-permutation
gauge to the sigma-sigma fusion gauge. The latter has inverse equal to half
its transpose. The resulting four-target compression has zero remainder.

The construction is recorded in
`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1.4. Its fusion data
come from arXiv:1511.08090, Appendix D.2, lines 1305–1323 in the local source.
**Scope restriction (round-45B boundary tensors):** The larger boundary tensors
remain distinct, as documented in
`docs/paper-gaps/tnlean_ising_three_object_twist_scope.tex`.

## References

* Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete,
  *Anyons and matrix product operator algebras*, arXiv:1511.08090, Appendix D.2.
* Project construction record:
  `Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1.4.
-/
open scoped Matrix Kronecker
open MPSTensor Zsqrtd
namespace IsingTwist

private def sumStackEquiv (m n k : ℕ) : Fin (m * k) ⊕ Fin (n * k) ≃ Fin ((m + n) * k) :=
  (Equiv.sumCongr (finProdFinEquiv (m := m) (n := k)).symm
    (finProdFinEquiv (m := n) (n := k)).symm).trans
    ((Equiv.sumProdDistrib (Fin m) (Fin n) (Fin k)).symm.trans
      ((Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin k))).trans finProdFinEquiv))

private theorem mulTensorR_fromBlocks {R : Type*} [CommRing R] {d m n k : ℕ}
    (M : Fin d → Fin d → Matrix (Fin m) (Fin m) R)
    (M' : Fin d → Fin d → Matrix (Fin n) (Fin n) R)
    (N : Fin d → Fin d → Matrix (Fin k) (Fin k) R) (i j : Fin d) :
    mulTensorR (fun i j => (Matrix.fromBlocks (M i j) 0 0 (M' i j)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm) N i j =
      (Matrix.fromBlocks (mulTensorR M N i j) 0 0 (mulTensorR M' N i j)).submatrix
        (sumStackEquiv m n k).symm (sumStackEquiv m n k).symm := by
  ext x y
  obtain ⟨x, rfl⟩ := (sumStackEquiv m n k).surjective x
  obtain ⟨y, rfl⟩ := (sumStackEquiv m n k).surjective y
  rcases x with x | x <;> rcases y with y | y
  all_goals simp [mulTensorR, sumStackEquiv]
  all_goals simp [Matrix.sum_apply, Matrix.kroneckerMap_apply]

private theorem thetaThreeZ_eq_fromBlocks (h h' : Fin 10) : thetaThreeZ h h' =
    (Matrix.fromBlocks (thetaTwoZ h h') 0 0 ((sqrtd : ℤ√2) • isingSigmaZ h h')).submatrix
      (finSumFinEquiv (m := 6) (n := 4)).symm (finSumFinEquiv (m := 6) (n := 4)).symm := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaThreeZ, thetaTwoZ, Matrix.fromBlocks, finSumFinEquiv, Fin.addCases,
      Fin.castLT, Fin.subNat, Fin.castAdd ]

private theorem mulTensorR_smul_left {R : Type*} [CommRing R] {d m n : ℕ} (c : R)
    (M : Fin d → Fin d → Matrix (Fin m) (Fin m) R)
    (N : Fin d → Fin d → Matrix (Fin n) (Fin n) R) (i j : Fin d) :
    mulTensorR (fun i j => c • M i j) N i j = c • mulTensorR M N i j := by
  apply Matrix.ext
  intro x y
  simp [mulTensorR, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    Finset.mul_sum, mul_assoc]

private noncomputable def threeGaugeMatrix : Matrix (Fin 40) (Fin 40) ℂ :=
  (Matrix.fromBlocks (complexOfZsqrt2 isingGaugeZ) 0 0
    (complexOfZsqrt2 isingGaugeSigmaSigmaZ)).submatrix
      (sumStackEquiv 6 4 4).symm (sumStackEquiv 6 4 4).symm

private noncomputable def threeGaugeMatrixInv : Matrix (Fin 40) (Fin 40) ℂ :=
  (Matrix.fromBlocks (complexOfZsqrt2 isingGaugeZᵀ) 0 0
    ((1 / 2 : ℂ) • complexOfZsqrt2 isingGaugeSigmaSigmaZᵀ)).submatrix
      (sumStackEquiv 6 4 4).symm (sumStackEquiv 6 4 4).symm

private theorem threeSigmaGauge_mul_transpose :
    complexOfZsqrt2 isingGaugeSigmaSigmaZ * complexOfZsqrt2 isingGaugeSigmaSigmaZᵀ =
      (2 : ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  rw [← complexOfZsqrt2_mul, isingGaugeSigmaSigmaZ_mul_transpose,
    complexOfZsqrt2_smul, complexOfZsqrt2_one]
  norm_num [zsqrt2ToComplex]

private theorem threeSigmaGauge_transpose_mul :
    complexOfZsqrt2 isingGaugeSigmaSigmaZᵀ * complexOfZsqrt2 isingGaugeSigmaSigmaZ =
      (2 : ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  rw [← complexOfZsqrt2_mul, isingGaugeSigmaSigmaZ_transpose_mul,
    complexOfZsqrt2_smul, complexOfZsqrt2_one]
  norm_num [zsqrt2ToComplex]

private theorem threeGaugeMatrix_mul_inv : threeGaugeMatrix * threeGaugeMatrixInv = 1 := by
  simp only [threeGaugeMatrix, threeGaugeMatrixInv, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    Matrix.mul_smul, threeSigmaGauge_mul_transpose, isingGaugeComplex_mul_transpose,
    smul_smul]
  norm_num [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private theorem threeGaugeMatrix_inv_mul : threeGaugeMatrixInv * threeGaugeMatrix = 1 := by
  simp only [threeGaugeMatrix, threeGaugeMatrixInv, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    Matrix.smul_mul, threeSigmaGauge_transpose_mul, isingGaugeComplex_transpose_mul,
    smul_smul]
  norm_num [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private theorem threeStack_eq_fromBlocks (h h' : Fin 10) :
    mulTensorR thetaThreeZ isingSigmaZ h h' =
      (Matrix.fromBlocks (mulTensorR thetaTwoZ isingSigmaZ h h') 0 0
        ((sqrtd : ℤ√2) • mulTensorR isingSigmaZ isingSigmaZ h h')).submatrix
        (sumStackEquiv 6 4 4).symm (sumStackEquiv 6 4 4).symm := by
  rw [show thetaThreeZ = (fun h h' =>
    (Matrix.fromBlocks (thetaTwoZ h h') 0 0 ((sqrtd : ℤ√2) • isingSigmaZ h h')).submatrix
      (finSumFinEquiv (m := 6) (n := 4)).symm (finSumFinEquiv (m := 6) (n := 4)).symm)
    from funext fun h => funext fun h' => thetaThreeZ_eq_fromBlocks h h']
  rw [mulTensorR_fromBlocks, mulTensorR_smul_left]

private theorem complexOfZsqrt2_fromBlocks {m n : Type*}
    (A : Matrix m m (ℤ√2)) (D : Matrix n n (ℤ√2)) :
    complexOfZsqrt2 (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (complexOfZsqrt2 A) 0 0 (complexOfZsqrt2 D) := by
  ext (i | i) (j | j) <;> simp

private noncomputable def threeConjugatedLetterZ (h h' : Fin 10) : Matrix (Fin 40) (Fin 40) (ℤ√2) :=
  (Matrix.fromBlocks
    (isingGaugeZ * mulTensorR thetaTwoZ isingSigmaZ h h' * isingGaugeZᵀ) 0 0
    ((sqrtd : ℤ√2) • padZsqrt2 10 (isingOnePsiZ h h'))).submatrix
      (sumStackEquiv 6 4 4).symm (sumStackEquiv 6 4 4).symm

private theorem threeGaugeMatrix_conj (h h' : Fin 10) :
    threeGaugeMatrix * complexOfZsqrt2 (mulTensorR thetaThreeZ isingSigmaZ h h') *
      threeGaugeMatrixInv = complexOfZsqrt2 (threeConjugatedLetterZ h h') := by
  rw [threeStack_eq_fromBlocks]
  simp only [threeGaugeMatrix, threeGaugeMatrixInv, threeConjugatedLetterZ,
    complexOfZsqrt2_submatrix, complexOfZsqrt2_fromBlocks,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  simp only [complexOfZsqrt2_mul, complexOfZsqrt2_smul, zsqrt2ToComplex_sqrtd,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 2
  rw [← complexOfZsqrt2_mul, ← complexOfZsqrt2_mul, isingSigmaSigma_conj,
    complexOfZsqrt2_smul, smul_smul]
  congr 1
  norm_num only [map_ofNat]
  ring


private def threeBlockCoord : BlockSpace isingThreeBlockDim (Finset.univ : Finset (Fin 4)) 26 →
    Fin 24 ⊕ Fin 16
  | ⟨Sum.inl ⟨0, _⟩, p⟩ => Sum.inl ⟨p.val, by have := p.isLt; change p.val < 4 at this; omega⟩
  | ⟨Sum.inl ⟨1, _⟩, p⟩ => Sum.inl ⟨4 + p.val, by have := p.isLt; change p.val < 4 at this; omega⟩
  | ⟨Sum.inl ⟨2, _⟩, p⟩ => Sum.inr ⟨p.val, by have := p.isLt; change p.val < 3 at this; omega⟩
  | ⟨Sum.inl ⟨3, _⟩, p⟩ => Sum.inr ⟨3 + p.val, by have := p.isLt; change p.val < 3 at this; omega⟩
  | ⟨Sum.inr t, _⟩ => if ht : t.val < 16 then Sum.inl ⟨8 + t.val, by omega⟩
    else Sum.inr ⟨6 + (t.val - 16), by omega⟩

private theorem threeBlockCoord_bijective : Function.Bijective threeBlockCoord := by
  decide +kernel

private noncomputable def threeBlockEquiv :
    BlockSpace isingThreeBlockDim (Finset.univ : Finset (Fin 4)) 26 ≃ Fin 40 :=
  (Equiv.ofBijective threeBlockCoord threeBlockCoord_bijective).trans (sumStackEquiv 6 4 4)


private theorem threeOldConjugatedLetter (h h' : Fin 10) :
    isingGaugeZ * mulTensorR thetaTwoZ isingSigmaZ h h' * isingGaugeZᵀ =
      (Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h'))).submatrix
        isingTau.symm isingTau.symm := by
  apply Matrix.ext
  intro i j
  have hi := congrFun (congrFun (isingGaugeZ_conj h h') (isingTau.symm i)) (isingTau.symm j)
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using hi

private def threeBlockZ (h h' : Fin 10) :
    ∀ b : BlockIndex (Finset.univ : Finset (Fin 4)) 26,
      Matrix (Fin (slotSize isingThreeBlockDim b)) (Fin (slotSize isingThreeBlockDim b)) (ℤ√2)
  | Sum.inl ⟨0, _⟩ => (5 : ℤ√2) • isingSigmaZ h h'
  | Sum.inl ⟨1, _⟩ => (3 : ℤ√2) • isingSigmaZ h h'
  | Sum.inl ⟨2, _⟩ => (2 * sqrtd : ℤ√2) • isingOneZ h h'
  | Sum.inl ⟨3, _⟩ => (2 * sqrtd : ℤ√2) • isingPsiZ h h'
  | Sum.inr _ => 0

private theorem threeBlockIdentity (h h' : Fin 10) :
    (threeConjugatedLetterZ h h').submatrix threeBlockEquiv threeBlockEquiv =
      Matrix.blockDiagonal' (threeBlockZ h h') := by
  rw [threeConjugatedLetterZ, threeOldConjugatedLetter]
  apply Matrix.ext
  intro x y
  simp only [Matrix.submatrix_apply, threeBlockEquiv, Equiv.trans_apply,
    Equiv.ofBijective_apply, Equiv.symm_apply_apply]
  obtain ⟨s | t, p⟩ := x
  all_goals obtain ⟨s' | t', q⟩ := y
  · obtain ⟨s, hs⟩ := s
    obtain ⟨s', hs'⟩ := s'
    fin_cases s <;> fin_cases s'
    all_goals dsimp +instances [slotSize, isingThreeBlockDim] at p q ⊢
    all_goals have hp := p.isLt
    all_goals have hq := q.isLt
    all_goals have hp4 : p.val < 4 := by omega
    all_goals have hq4 : q.val < 4 := by omega
    all_goals have hp8 : 4 + p.val < 8 := by omega
    all_goals have hq8 : 4 + q.val < 8 := by omega
    all_goals have hp6 : p.val < 6 := by omega
    all_goals have hq6 : q.val < 6 := by omega
    all_goals try have hp36 : 3 + p.val < 6 := by omega
    all_goals try have hq36 : 3 + q.val < 6 := by omega
    all_goals simp (disch := omega) [threeBlockCoord, threeBlockZ, isingTau, isingBlockZ,
      padZsqrt2, isingOnePsiZ, Matrix.blockDiagonal', isingWeightsZ, Matrix.smul_apply, slotSize,
      isingThreeBlockDim,
      smul_eq_mul, finSumFinEquiv, Fin.addCases, hp4, hp8, hp6, hq4, hq8, hq6]
    all_goals simp_all [smul_eq_mul]
    all_goals ring_nf
    all_goals first
      | change isingSigmaZ h h' p q * 5 = isingSigmaZ h h' p q * 5
      | change isingSigmaZ h h' p q * 3 = isingSigmaZ h h' p q * 3
      | change sqrtd * isingOneZ h h' p q * 2 = sqrtd * isingOneZ h h' p q * 2
      | change sqrtd * isingPsiZ h h' p q * 2 = sqrtd * isingPsiZ h h' p q * 2
    all_goals rfl
  · obtain ⟨s, hs⟩ := s
    fin_cases s
    all_goals by_cases ht : t'.val < 16
    all_goals dsimp +instances [slotSize, isingThreeBlockDim] at p q ⊢
    all_goals have hp := p.isLt
    all_goals have hp4 : p.val < 4 := by omega
    all_goals have hp8 : 4 + p.val < 8 := by omega
    all_goals have hp6 : p.val < 6 := by omega
    all_goals try have hp36 : 3 + p.val < 6 := by omega
    all_goals have ht4 : ¬ 8 + t'.val < 4 := by omega
    all_goals have ht8 : ¬ 8 + t'.val < 8 := by omega
    all_goals have ht6 : ¬ 6 + (t'.val - 16) < 6 := by omega
    all_goals simp (disch := omega) [threeBlockCoord, threeBlockZ, isingTau, isingBlockZ,
      padZsqrt2, isingOnePsiZ, Matrix.blockDiagonal', isingWeightsZ, Matrix.smul_apply,
      smul_eq_mul, finSumFinEquiv, Fin.addCases, hp4, hp8, hp6, ht, ht4, ht8, ht6]
    all_goals simp_all
  · obtain ⟨s', hs'⟩ := s'
    fin_cases s'
    all_goals by_cases ht : t.val < 16
    all_goals dsimp +instances [slotSize, isingThreeBlockDim] at p q ⊢
    all_goals have hq4 : q.val < 4 := by omega
    all_goals have hq8 : 4 + q.val < 8 := by omega
    all_goals have hq6 : q.val < 6 := by omega
    all_goals try have hq36 : 3 + q.val < 6 := by omega
    all_goals have ht4 : ¬ 8 + t.val < 4 := by omega
    all_goals have ht8 : ¬ 8 + t.val < 8 := by omega
    all_goals have ht6 : ¬ 6 + (t.val - 16) < 6 := by omega
    all_goals simp (disch := omega) [threeBlockCoord, threeBlockZ, isingTau, isingBlockZ,
      padZsqrt2, isingOnePsiZ, Matrix.blockDiagonal', isingWeightsZ, Matrix.smul_apply,
      smul_eq_mul, finSumFinEquiv, Fin.addCases, hq4, hq8, hq6, ht, ht4, ht8, ht6]
    all_goals simp_all
  · by_cases ht : t.val < 16 <;> by_cases ht' : t'.val < 16
    all_goals have ht4 : ¬ 8 + t.val < 4 := by omega
    all_goals have ht8 : ¬ 8 + t.val < 8 := by omega
    all_goals have ht6 : ¬ 6 + (t.val - 16) < 6 := by omega
    all_goals have ht'4 : ¬ 8 + t'.val < 4 := by omega
    all_goals have ht'8 : ¬ 8 + t'.val < 8 := by omega
    all_goals have ht'6 : ¬ 6 + (t'.val - 16) < 6 := by omega
    all_goals simp (disch := omega) [threeBlockCoord, threeBlockZ, isingTau, isingBlockZ,
      padZsqrt2, isingOnePsiZ, Matrix.blockDiagonal', isingWeightsZ, Matrix.smul_apply,
      smul_eq_mul, finSumFinEquiv, Fin.addCases, ht, ht', ht4, ht8, ht6, ht'4, ht'8, ht'6]

private def threeOrd : BlockIndex (Finset.univ : Finset (Fin 4)) 26 ≃ Fin 30 where
  toFun := Sum.elim (fun s => Fin.castLE (by norm_num) s.1) fun t => ⟨t.val + 4, by omega⟩
  invFun i := if h : i.val < 4 then Sum.inl ⟨⟨i.val, h⟩, Finset.mem_univ _⟩
    else Sum.inr ⟨i.val - 4, by omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private noncomputable def threeGauge : (Fin 40 → ℂ) ≃ₗ[ℂ]
    (BlockSpace isingThreeBlockDim (Finset.univ : Finset (Fin 4)) 26 → ℂ) :=
  gaugeOfMatrix threeBlockEquiv threeGaugeMatrix threeGaugeMatrixInv
    threeGaugeMatrix_mul_inv threeGaugeMatrix_inv_mul

private def threeTargetZ : (s : Fin 4) → Fin 100 →
    Matrix (Fin (isingThreeBlockDim s)) (Fin (isingThreeBlockDim s)) (ℤ√2)
  | 0, a => (5 : ℤ√2) • isingSigmaZ
      (Fin.divNat (m := 10) (n := 10) a) (Fin.modNat (m := 10) (n := 10) a)
  | 1, a => (3 : ℤ√2) • isingSigmaZ
      (Fin.divNat (m := 10) (n := 10) a) (Fin.modNat (m := 10) (n := 10) a)
  | 2, a => (2 * sqrtd : ℤ√2) • isingOneZ
      (Fin.divNat (m := 10) (n := 10) a) (Fin.modNat (m := 10) (n := 10) a)
  | 3, a => (2 * sqrtd : ℤ√2) • isingPsiZ
      (Fin.divNat (m := 10) (n := 10) a) (Fin.modNat (m := 10) (n := 10) a)

private theorem threeTargetZ_complex (s : Fin 4) (a : Fin 100) :
    isingThreeTargets s a = complexOfZsqrt2 (threeTargetZ s a) := by
  fin_cases s <;>
    dsimp [isingThreeTargets, threeTargetZ, isingThreeBlockDim, MPOTensor.toMPSTensor]
  all_goals rw [complexOfZsqrt2_smul]
  all_goals simp [isingSigma, isingOne, isingPsi, map_ofNat, map_mul, zsqrt2ToComplex_sqrtd]


private theorem isingBondObjectThree_conjMatrix (a : Fin 100) :
    conjMatrix threeGauge (isingBondObjectThree a) =
      complexOfZsqrt2 (Matrix.blockDiagonal' (threeBlockZ
        (Fin.divNat (m := 10) (n := 10) a) (Fin.modNat (m := 10) (n := 10) a))) := by
  have hA : isingBondObjectThree a = complexOfZsqrt2 (mulTensorR thetaThreeZ isingSigmaZ
      (Fin.divNat (m := 10) (n := 10) a) (Fin.modNat (m := 10) (n := 10) a)) :=
    mulTensor_complexOfRing _ thetaThreeZ isingSigmaZ _ _
  rw [threeGauge, conjMatrix_gaugeOfMatrix, hA, threeGaugeMatrix_conj,
    ← complexOfZsqrt2_submatrix, threeBlockIdentity]

/-- The explicit four-channel compression of data file §1.4, obtained from the direct sum
of the two-object gauge and the sigma-square gauge (arXiv:1511.08090, Appendix D.2). -/
noncomputable def isingThreeSplitCompression :
    MultiBlockCompression isingBondObjectThree Finset.univ isingThreeTargets :=
  MultiBlockCompression.ofRingBlockDiagonal zsqrt2ToComplex threeOrd threeBlockEquiv threeGauge
    (fun a => threeBlockZ (Fin.divNat (m := 10) (n := 10) a)
      (Fin.modNat (m := 10) (n := 10) a))
    isingBondObjectThree_conjMatrix threeTargetZ threeTargetZ_complex
    (fun _ s => by obtain ⟨s, hs⟩ := s; fin_cases s <;> rfl) (fun _ _ => rfl)

/-- The explicit four-channel compression has zero remainder (data file §1.4;
arXiv:1511.08090, Appendix D.2). -/
theorem isingBondObjectThree_split_remainder : isingThreeSplitCompression.remainder = 0 := by
  unfold isingThreeSplitCompression
  exact funext MultiBlockCompression.remainder_ofRingBlockDiagonal

/-- The right inclusion intertwines every letter with its weighted target
(data file §1.4; arXiv:1511.08090, Appendix D.2). -/
theorem isingBondObjectThree_mul_right_eq_right_mul (a : Fin 100)
    (s : {s : Fin 4 // s ∈ (Finset.univ : Finset (Fin 4))}) :
    isingBondObjectThree a * isingThreeSplitCompression.right s =
      isingThreeSplitCompression.right s * isingThreeTargets s.1 a :=
  isingThreeSplitCompression.mul_right_eq_right_mul isingBondObjectThree_split_remainder a s

/-- The left projection intertwines every letter with its weighted target
(data file §1.4; arXiv:1511.08090, Appendix D.2). -/
theorem isingBondObjectThree_left_mul_eq_mul_left (a : Fin 100)
    (s : {s : Fin 4 // s ∈ (Finset.univ : Finset (Fin 4))}) :
    isingThreeSplitCompression.left s * isingBondObjectThree a =
      isingThreeTargets s.1 a * isingThreeSplitCompression.left s :=
  isingThreeSplitCompression.left_mul_eq_mul_left isingBondObjectThree_split_remainder a s

end IsingTwist
