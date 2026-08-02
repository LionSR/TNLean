/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ActiveSectorInverseMapProvenance
import TNLean.MPS.MPDO.SALArbitraryCut
import TNLean.MPS.MPDO.SectorTrace

/-!
# Saturated area law for the four-sector classical tensor

This file proves the strong area law for the explicit four-sector tensor in
`ActiveSectorSpanningCounterexample`.  Its finite-chain operators are the
classical cyclic law determined by the neighboring transition matrix
\[
  T_{ij}=(r_i\mid l_j).
\]
The marginal obtained by removing one site is therefore an ordinary Markov
path.  Conditioning on the physical label at the middle site gives an
explicit Hayashi quantum-Markov decomposition at every admissible cut.

## Main result

* `tensor_isSAL`: the four-sector tensor satisfies the strong area law.

## Reference

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.6 and Appendix C.2, lines 1351--1369.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.ActiveSectorSpanningCounterexample

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The real transition matrix of the classical four-sector chain. -/
private noncomputable def transition : Matrix (Fin 4) (Fin 4) ℝ :=
  !![3 / 8, 1 / 8, 3 / 8, 1 / 8;
     3 / 8, 1 / 8, 3 / 8, 1 / 8;
     1 / 8, 3 / 8, 1 / 8, 3 / 8;
     1 / 8, 3 / 8, 1 / 8, 3 / 8]

private lemma transition_nonneg (i j : Fin 4) : 0 ≤ transition i j := by
  fin_cases i <;> fin_cases j <;> norm_num [transition]

private lemma transition_row_sum (i : Fin 4) : ∑ j, transition i j = 1 := by
  fin_cases i <;>
    simp [transition, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num

private lemma transition_column_sum (j : Fin 4) : ∑ i, transition i j = 1 := by
  fin_cases j <;>
    simp [transition, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num

private lemma pairing_eq_transition (i j : Fin 4) :
    (rightPairing * leftPairing) i j = transition i j := by
  rw [rightPairing_mul_leftPairing]
  fin_cases i <;> fin_cases j <;> norm_num [transition]

/-- Product of the neighboring transition weights along a finite path.
The empty path and a one-vertex path have weight one. -/
private noncomputable def pathWeight : List (Fin 4) → ℝ
  | [] => 1
  | [_] => 1
  | i :: j :: w => transition i j * pathWeight (j :: w)

@[simp] private lemma pathWeight_nil : pathWeight [] = 1 := rfl

@[simp] private lemma pathWeight_singleton (i : Fin 4) : pathWeight [i] = 1 := rfl

@[simp] private lemma pathWeight_cons_cons (i j : Fin 4) (w : List (Fin 4)) :
    pathWeight (i :: j :: w) = transition i j * pathWeight (j :: w) := rfl

private lemma pathWeight_nonneg (w : List (Fin 4)) : 0 ≤ pathWeight w := by
  induction w with
  | nil => norm_num
  | cons i w ih =>
      cases w with
      | nil => norm_num
      | cons j w =>
          rw [pathWeight_cons_cons]
          exact mul_nonneg (transition_nonneg i j) ih

private lemma pathWeight_append_middle (u v : List (Fin 4)) (k : Fin 4) :
    pathWeight (u ++ k :: v) = pathWeight (u ++ [k]) * pathWeight (k :: v) := by
  induction u with
  | nil => simp
  | cons i u ih =>
      cases u with
      | nil =>
          cases v with
          | nil => simp
          | cons j v => simp
      | cons j u =>
          simp only [List.cons_append, pathWeight_cons_cons]
          rw [show j :: (u ++ k :: v) = (j :: u) ++ k :: v by rfl,
            show j :: (u ++ [k]) = (j :: u) ++ [k] by rfl, ih]
          ring

private lemma sum_pathWeight_from (n : ℕ) (k : Fin 4) :
    ∑ w : Fin n → Fin 4, pathWeight (k :: List.ofFn w) = 1 := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 4)).sum_comp,
        Fintype.sum_prod_type]
      have hof (a : Fin 4) (w : Fin n → Fin 4) :
          List.ofFn (Fin.cons a w) = a :: List.ofFn w := by
        simp [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
      calc
        (∑ a : Fin 4, ∑ w : Fin n → Fin 4,
            pathWeight (k :: List.ofFn (Fin.cons a w))) =
            ∑ a : Fin 4, transition k a *
              ∑ w : Fin n → Fin 4, pathWeight (a :: List.ofFn w) := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro w _
                rw [hof, pathWeight_cons_cons]
        _ = ∑ a : Fin 4, transition k a := by
              apply Finset.sum_congr rfl
              intro a _
              rw [ih a, mul_one]
        _ = 1 := transition_row_sum k

private lemma sum_pathWeight_to (n : ℕ) (k : Fin 4) :
    ∑ w : Fin n → Fin 4, pathWeight (List.ofFn w ++ [k]) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 4)).sum_comp,
        Fintype.sum_prod_type]
      have hof (a : Fin 4) (w : Fin n → Fin 4) :
          List.ofFn (Fin.cons a w) = a :: List.ofFn w := by
        simp [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
      cases n with
      | zero =>
          simp only [Fintype.sum_unique]
          simpa [hof] using transition_column_sum k
      | succ n =>
          have htail (w : Fin (n + 1) → Fin 4) :
              List.ofFn w = w 0 :: List.ofFn (w ∘ Fin.succ) := by
            rw [List.ofFn_succ]
            congr 1
          calc
            (∑ a : Fin 4, ∑ w : Fin (n + 1) → Fin 4,
                pathWeight (List.ofFn (Fin.cons a w) ++ [k])) =
                ∑ w : Fin (n + 1) → Fin 4,
                  (∑ a : Fin 4, transition a (w 0)) *
                    pathWeight (List.ofFn w ++ [k]) := by
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro w _
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [hof, List.cons_append, htail]
                      change pathWeight
                          (a :: w 0 :: (List.ofFn (w ∘ Fin.succ) ++ [k])) = _
                      rfl
            _ = ∑ w : Fin (n + 1) → Fin 4,
                  pathWeight (List.ofFn w ++ [k]) := by
                    apply Finset.sum_congr rfl
                    intro w _
                    rw [transition_column_sum, one_mul]
            _ = 1 := ih

private lemma trace_crossSectorMatrix_mul_loop (i k : Fin 4) :
    Matrix.trace (crossSectorMatrix i k * physTraceTransfer tensor) = 1 / 4 := by
  rw [physTraceTransfer_tensor]
  exact trace_crossSectorMatrix_mul_transfer i k

private lemma trace_crossSectorMatrix (i k : Fin 4) :
    Matrix.trace (crossSectorMatrix i k) = transition k i := by
  rw [← pairing_eq_transition]
  fin_cases i <;> fin_cases k <;>
    norm_num [crossSectorMatrix, leftPairing, rightPairing, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two]

private def lastFrom (i : Fin 4) : List (Fin 4) → Fin 4
  | [] => i
  | j :: w => lastFrom j w

private lemma evalWord_same_eq (i : Fin 4) (w : List (Fin 4)) :
    evalWord tensor (i :: w) (i :: w) =
      (pathWeight (i :: w) : ℂ) • crossSectorMatrix i (lastFrom i w) := by
  induction w generalizing i with
  | nil =>
      simp [evalWord, tensor, sectorMatrix_eq_crossSectorMatrix, lastFrom]
  | cons j w ih =>
      rw [evalWord_cons, tensor, if_pos rfl, sectorMatrix_eq_crossSectorMatrix,
        ih j, Matrix.mul_smul, crossSectorMatrix_mul, pairing_eq_transition]
      simp only [pathWeight_cons_cons, lastFrom, smul_smul]
      push_cast
      ring_nf

private noncomputable def cycleWeight : List (Fin 4) → ℝ
  | [] => 0
  | i :: w => pathWeight (i :: w) * transition (lastFrom i w) i

private lemma cycleWeight_nonneg (w : List (Fin 4)) : 0 ≤ cycleWeight w := by
  cases w with
  | nil => simp [cycleWeight]
  | cons i w =>
      exact mul_nonneg (pathWeight_nonneg _) (transition_nonneg _ _)

private lemma trace_evalWord_same (i : Fin 4) (w : List (Fin 4)) :
    Matrix.trace (evalWord tensor (i :: w) (i :: w)) = cycleWeight (i :: w) := by
  rw [evalWord_same_eq, Matrix.trace_smul, trace_crossSectorMatrix]
  simp [cycleWeight]

private lemma evalWord_eq_zero_of_ne :
    ∀ (u v : List (Fin 4)), u.length = v.length → u ≠ v →
      evalWord tensor u v = 0 := by
  intro u
  induction u with
  | nil =>
      intro v hlen
      have hv : v = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst v
      simp
  | cons i u ih =>
      intro v hlen hne
      cases v with
      | nil => simp at hlen
      | cons j v =>
          have hlen' : u.length = v.length := by simpa using hlen
          by_cases hij : i = j
          · subst j
            rw [evalWord_cons, tensor, if_pos rfl]
            have huv : u ≠ v := by
              intro huv
              exact hne (huv ▸ rfl)
            rw [ih v hlen' huv, Matrix.mul_zero]
          · rw [evalWord_cons, tensor, if_neg hij, Matrix.zero_mul]

private lemma trace_evalWord_same_mul_loop (i : Fin 4) (w : List (Fin 4)) :
    Matrix.trace
        (evalWord tensor (i :: w) (i :: w) * physTraceTransfer tensor) =
      (1 / 4 : ℂ) * pathWeight (i :: w) := by
  rw [evalWord_same_eq, Matrix.smul_mul, Matrix.trace_smul,
    trace_crossSectorMatrix_mul_loop]
  ring

private lemma trace_mpo_tensor (N : ℕ) (hN : 0 < N) :
    (mpo tensor N).trace = 1 := by
  rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer]
  have hIdem : IsIdempotentElem (physTraceTransfer tensor) :=
    physTraceTransfer_tensor_idempotent
  rw [hIdem.pow_eq hN.ne']
  rw [physTraceTransfer_tensor, leftPairing_mul_rightPairing]
  norm_num [Matrix.trace, Fin.sum_univ_two]

private lemma mpo_tensor_eq_diagonal (N : ℕ) (hN : 0 < N) :
    mpo tensor N = Matrix.diagonal fun sigma => (cycleWeight (List.ofFn sigma) : ℂ) := by
  ext sigma tau
  by_cases hst : sigma = tau
  · subst tau
    rw [Matrix.diagonal_apply_eq, mpo_apply, mpoMatrixEntry]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [List.ofFn_succ]
    exact trace_evalWord_same _ _
  · rw [Matrix.diagonal_apply_ne _ hst, mpo_apply, mpoMatrixEntry,
      evalWord_eq_zero_of_ne (List.ofFn sigma) (List.ofFn tau) (by simp)]
    · simp
    · exact fun h => hst (List.ofFn_injective h)

private lemma tensor_isMPDO : IsMPDO tensor := by
  intro N hN
  rw [mpo_tensor_eq_diagonal N hN]
  apply Matrix.PosSemidef.diagonal
  intro sigma
  change 0 ≤ (cycleWeight (List.ofFn sigma) : ℂ)
  rw [Complex.nonneg_iff]
  exact ⟨cycleWeight_nonneg _, by simp⟩

private lemma reducedBlockState_apply_of_trace_one
    (M : MPOTensor d D) {N m : ℕ} (hm : m ≤ N)
    (htrace : (mpo M N).trace = 1) (u v : Fin m → Fin d) :
    M.reducedBlockState N m hm u v =
      Matrix.trace
        (M.evalWord (List.ofFn u) (List.ofFn v) * M.verticalLoop ^ (N - m)) := by
  rw [reducedBlockState_eq_sum]
  simp only [normalizedMPO, htrace, inv_one, one_smul, mpo_apply, mpoMatrixEntry]
  have hwords (a : Fin m → Fin d) (w : Fin (N - m) → Fin d) :
      List.ofFn
          (Fin.append a w ∘ Fin.cast (show N = m + (N - m) by omega)) =
        List.ofFn a ++ List.ofFn w := by
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr (Nat.add_sub_of_le hm) (Fin.append a w)).symm
  simp_rw [hwords]
  have heval (w : Fin (N - m) → Fin d) :
      M.evalWord (List.ofFn u ++ List.ofFn w) (List.ofFn v ++ List.ofFn w) =
        M.evalWord (List.ofFn u) (List.ofFn v) *
          M.evalWord (List.ofFn w) (List.ofFn w) := by
    exact M.evalWord_append _ _ _ _ (by simp)
  simp_rw [heval]
  rw [← Matrix.trace_sum]
  congr 1
  rw [← Finset.mul_sum, M.sum_evalWord_diag_eq_verticalLoop_pow]

private lemma reducedBlockState_pred_eq_diagonal
    {N m : ℕ} (hN : 2 ≤ N) (hm : m = N - 1) (hle : m ≤ N) :
    tensor.reducedBlockState N m hle =
      Matrix.diagonal fun u => ((1 / 4 : ℂ) * pathWeight (List.ofFn u)) := by
  ext u v
  rw [reducedBlockState_apply_of_trace_one tensor hle (trace_mpo_tensor N (by omega))]
  rw [verticalLoop_eq_physTraceTransfer, show N - m = 1 by omega, pow_one]
  by_cases huv : u = v
  · subst v
    rw [Matrix.diagonal_apply_eq]
    have hmpos : 0 < m := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [List.ofFn_succ]
    exact trace_evalWord_same_mul_loop _ _
  · rw [Matrix.diagonal_apply_ne _ huv,
      evalWord_eq_zero_of_ne (List.ofFn u) (List.ofFn v) (by simp)]
    · simp
    · exact fun h => huv (List.ofFn_injective h)

private noncomputable def oneSiteEquiv : Fin 4 ≃ Fin (4 ^ 1) :=
  (Equiv.funUnique (Fin 1) (Fin 4)).symm.trans finFunctionFinEquiv

private noncomputable def markovMiddleEquiv :
    Fin (4 ^ 1) ≃ Σ _k : Fin 4, Fin 1 × Fin 1 :=
  oneSiteEquiv.symm.trans sectorEquiv

private lemma ofFn_tripartite_middle
    {a c : ℕ} (i : Fin (4 ^ a)) (k : Fin 4) (j : Fin (4 ^ c)) :
    List.ofFn ((tripartiteSplitEquiv 4 a 1 c).symm (i, oneSiteEquiv k, j)) =
      List.ofFn (finFunctionFinEquiv.symm i) ++
        [k] ++ List.ofFn (finFunctionFinEquiv.symm j) := by
  simp only [tripartiteSplitEquiv, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.refl_symm, Equiv.prodAssoc_symm_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id_eq, blockSplitEquiv_symm_apply]
  rw [List.ofFn_fin_append, List.ofFn_fin_append]
  congr 1
  simp [oneSiteEquiv]

private noncomputable def leftConditionalDensity (a : ℕ) (k : Fin 4) :
    Matrix (Fin (4 ^ a) × Fin 1) (Fin (4 ^ a) × Fin 1) ℂ :=
  Matrix.diagonal fun x =>
    (pathWeight (List.ofFn (finFunctionFinEquiv.symm x.1) ++ [k]) : ℂ)

private noncomputable def rightConditionalDensity (c : ℕ) (k : Fin 4) :
    Matrix (Fin 1 × Fin (4 ^ c)) (Fin 1 × Fin (4 ^ c)) ℂ :=
  Matrix.diagonal fun x =>
    (pathWeight (k :: List.ofFn (finFunctionFinEquiv.symm x.2)) : ℂ)

private lemma leftConditionalDensity_posSemidef (a : ℕ) (k : Fin 4) :
    (leftConditionalDensity a k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  rintro ⟨i, u⟩
  change 0 ≤ (pathWeight (List.ofFn (finFunctionFinEquiv.symm i) ++ [k]) : ℂ)
  rw [Complex.nonneg_iff]
  exact ⟨pathWeight_nonneg _, by simp⟩

private lemma rightConditionalDensity_posSemidef (c : ℕ) (k : Fin 4) :
    (rightConditionalDensity c k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  rintro ⟨u, i⟩
  change 0 ≤ (pathWeight (k :: List.ofFn (finFunctionFinEquiv.symm i)) : ℂ)
  rw [Complex.nonneg_iff]
  exact ⟨pathWeight_nonneg _, by simp⟩

private lemma trace_leftConditionalDensity (a : ℕ) (k : Fin 4) :
    (leftConditionalDensity a k).trace = 1 := by
  rw [leftConditionalDensity, Matrix.trace_diagonal]
  change (∑ x : Fin (4 ^ a) × Fin 1,
    (pathWeight (List.ofFn (finFunctionFinEquiv.symm x.1) ++ [k]) : ℂ)) = 1
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  have hsum :
      (∑ i : Fin (4 ^ a),
          (pathWeight (List.ofFn (finFunctionFinEquiv.symm i) ++ [k]) : ℂ)) =
        ∑ w : Fin a → Fin 4, (pathWeight (List.ofFn w ++ [k]) : ℂ) := by
    exact Fintype.sum_equiv finFunctionFinEquiv.symm _ _ (fun _ => rfl)
  rw [hsum]
  exact_mod_cast sum_pathWeight_to a k

private lemma trace_rightConditionalDensity (c : ℕ) (k : Fin 4) :
    (rightConditionalDensity c k).trace = 1 := by
  rw [rightConditionalDensity, Matrix.trace_diagonal]
  change (∑ x : Fin 1 × Fin (4 ^ c),
    (pathWeight (k :: List.ofFn (finFunctionFinEquiv.symm x.2)) : ℂ)) = 1
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  have hsum :
      (∑ i : Fin (4 ^ c),
          (pathWeight (k :: List.ofFn (finFunctionFinEquiv.symm i)) : ℂ)) =
        ∑ w : Fin c → Fin 4, (pathWeight (k :: List.ofFn w) : ℂ) := by
    exact Fintype.sum_equiv finFunctionFinEquiv.symm _ _ (fun _ => rfl)
  rw [hsum]
  exact_mod_cast sum_pathWeight_from c k

/-- Every admissible three-region marginal of the classical four-sector
tensor has the quantum-Markov decomposition obtained by conditioning on its
middle physical label.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.3, lines 1351--1369. -/
private theorem nonempty_markovDecomposition_tripartite
    (N m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N / 2) :
    let h3 : (m - 1) + 1 + (N - m - 1) ≤ N := by omega
    let rho :=
      (tensor.reducedBlockState N ((m - 1) + 1 + (N - m - 1)) h3).submatrix
        (tripartiteSplitEquiv 4 (m - 1) 1 (N - m - 1)).symm
        (tripartiteSplitEquiv 4 (m - 1) 1 (N - m - 1)).symm
    Nonempty (Entropy.QuantumMarkovDecomposition rho) := by
  dsimp only
  have hN : 2 ≤ N := by omega
  refine ⟨{
    m := 4
    dL := fun _ => 1
    dR := fun _ => 1
    decompB := markovMiddleEquiv
    U_B := ⟨1, by simp⟩
    p := p
    hp_nonneg := p_nonneg
    hp_sum := sum_p
    ρ_left := leftConditionalDensity (m - 1)
    ρ_right := rightConditionalDensity (N - m - 1)
    hρ_left_dm := fun k => ⟨leftConditionalDensity_posSemidef _ k,
      trace_leftConditionalDensity _ k⟩
    hρ_right_dm := fun k => ⟨rightConditionalDensity_posSemidef _ k,
      trace_rightConditionalDensity _ k⟩
    h_state := ?_ }⟩
  rw [reducedBlockState_pred_eq_diagonal hN (by omega) (by omega)]
  ext x y
  obtain ⟨i, ⟨⟨k, ⟨l, r⟩⟩, j⟩⟩ := x
  obtain ⟨i', ⟨⟨k', ⟨l', r'⟩⟩, j'⟩⟩ := y
  fin_cases l
  fin_cases r
  fin_cases l'
  fin_cases r'
  rw [HayashiMarkov.blockState_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Nat.reducePow, HayashiMarkov.liftB, zero_mul, implies_true, mul_zero,
    mul_one, Matrix.kroneckerMap_one_one, one_div, Matrix.submatrix_diagonal_equiv,
    one_mul, Matrix.conjTranspose_one, HayashiMarkov.abcEquiv, markovMiddleEquiv,
    oneSiteEquiv, Equiv.symm_trans, Equiv.symm_symm, sectorEquiv, Fin.isValue,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.symm_mk,
    Fin.zero_eta, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_trans,
    Equiv.funUnique_symm_apply, Equiv.coe_fn_mk, Prod.map_apply, id_eq,
    Function.comp_apply, Matrix.diagonal_mul, p, Complex.ofReal_inv,
    Complex.ofReal_ofNat, leftConditionalDensity, eq_rec_constant,
    rightConditionalDensity, dite_eq_ite]
  rw [show finFunctionFinEquiv (uniqueElim k) = oneSiteEquiv k by rfl,
    show finFunctionFinEquiv (uniqueElim k') = oneSiteEquiv k' by rfl]
  by_cases hii : i = i'
  · subst i'
    by_cases hkk : k = k'
    · subst k'
      by_cases hjj : j = j'
      · subst j'
        rw [Matrix.one_apply_eq, ofFn_tripartite_middle,
          List.append_assoc]
        simp only [List.singleton_append]
        rw [pathWeight_append_middle]
        simp [Matrix.diagonal_apply_eq]
        ring
      · have htuple : (i, oneSiteEquiv k, j) ≠ (i, oneSiteEquiv k, j') := by
          intro h
          exact hjj (congrArg (fun x => x.2.2) h)
        rw [Matrix.one_apply_ne htuple]
        simp [hjj]
    · have htuple : (i, oneSiteEquiv k, j) ≠ (i, oneSiteEquiv k', j') := by
        intro h
        exact hkk (oneSiteEquiv.injective (congrArg (fun x => x.2.1) h))
      rw [Matrix.one_apply_ne htuple]
      simp [hkk]
  · have htuple : (i, oneSiteEquiv k, j) ≠ (i', oneSiteEquiv k', j') := by
      intro h
      exact hii (congrArg Prod.fst h)
    rw [Matrix.one_apply_ne htuple]
    simp [hii]

/-- The four-sector classical tensor satisfies the strong area law.  The
proof uses its exact cyclic transition law and the resulting quantum-Markov
decomposition at every admissible cut; it does not assume that the transition
matrix has rank one.

Source: arXiv:1606.00608, Definition 4.6 and Appendix C.2, Lemma C.3,
lines 1351--1369. -/
theorem tensor_isSAL : IsSAL tensor := by
  apply isSAL_of_quantumMarkovDecomposition_tripartite_m tensor tensor_isMPDO
  · intro N hN
    rw [trace_mpo_tensor N hN]
    exact one_ne_zero
  · intro N m hm1 hmN
    exact nonempty_markovDecomposition_tripartite N m hm1 hmN

/-- The source-selected active trace matrix of the four-sector tensor has no
outer-product factorization.  This is the precise conclusion asserted in
equation `Apptralktrrk` of the printed Lemma C.5.

Source: arXiv:1606.00608, Appendix C.2, Lemma `SALZCL`, lines 1484--1499. -/
lemma activeSectorTraceMatrix_not_rankOne :
    ¬ ∃ a b : factorization.ActiveSector p → ℝ,
      factorization.activeSectorTraceMatrix p = Matrix.vecMulVec a b := by
  rintro ⟨a, b, hT⟩
  apply activeSectorTraceMatrix_ne_idempotent
  have hdot : a ⬝ᵥ b = 1 := by
    rw [← Matrix.trace_vecMulVec, ← hT, trace_activeSectorTraceMatrix]
  have hdot' : b ⬝ᵥ a = 1 := by simpa [dotProduct_comm] using hdot
  rw [hT, Matrix.vecMulVec_mul_vecMulVec, hdot']
  simp

/-- The raw four-sector tensor is injective, satisfies SAL and `IsSourceZCL`,
and its source-selected inverse-map factorization has positive neighboring
operators and a primitive trace-one active trace matrix. Yet that matrix has
no factorization `T_{k,h} = a_k b_h`; equivalently, the rectangular remainder
`Q(1-LQ)L` is nonzero.

**Scope restriction (non-normal representative):** Lemma C.5 is proved inside
the source's Case I, where the tensor is assumed to be an injective normal
tensor. The raw tensor here has doubled-transfer spectral radius `5 / 16` and
does not meet that normalization. Its normalized representative loses the
paper's literal zero-correlation-length identity. Thus this theorem records the
normalization obstruction but does not refute Lemma C.5 under its complete
standing hypotheses. Documented in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Appendix C.2, Case I at lines 1374--1381 and Lemma
`SALZCL` at lines 1473--1499. -/
theorem tensor_has_sal_sourceZCL_and_non_rankOne_activeTraceMatrix :
    tensor.IsInjective ∧ tensor.IsSAL ∧ tensor.IsSourceZCL ∧
      (∀ k h, inverseMapFactorization.neighboringOperator k h =
        factorization.neighboringOperator k h) ∧
      (∀ k h, (inverseMapFactorization.neighboringOperator k h).PosSemidef) ∧
      Matrix.IsPrimitive (factorization.activeSectorTraceMatrix p) ∧
      Matrix.trace (factorization.activeSectorTraceMatrix p) = 1 ∧
      (¬ ∃ a b : factorization.ActiveSector p → ℝ,
        factorization.activeSectorTraceMatrix p = Matrix.vecMulVec a b) ∧
      rightPairing * (1 - leftPairing * rightPairing) * leftPairing ≠ 0 := by
  refine ⟨tensor_isInjective, tensor_isSAL, tensor_isSourceZCL,
    inverseMapFactorization_neighboringOperator, ?_, activeSectorTraceMatrix_isPrimitive,
    trace_activeSectorTraceMatrix, activeSectorTraceMatrix_not_rankOne,
    rectangular_remainder_ne_zero⟩
  intro k h
  rw [inverseMapFactorization_neighboringOperator]
  exact neighboringOperator_posSemidef k h

end MPOTensor.ActiveSectorSpanningCounterexample
