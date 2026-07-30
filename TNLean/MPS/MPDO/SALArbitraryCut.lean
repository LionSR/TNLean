/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SimpleLocalStructure

/-!
# SAL and arbitrary-cut strong-subadditivity equality

This file proves the entropy equivalence used in the sectorwise
saturated-area-law argument of arXiv:1606.00608, Appendix C.2.  For the
four-region division of lengths \(m-1,1,N-m-1,1\), saturation of the area law
is equivalent to equality in strong subadditivity for the marginal on the
first three regions.  The converse is stated for all admissible cuts.

## Main declarations

- `MPOTensor.isSSAEquality_tripartite_m_of_isSAL`: SAL gives the arbitrary-cut
  strong-subadditivity equality.
- `MPOTensor.mutualInfoChain_one_eq_of_isSSAEquality_tripartite_m`: the
  equality gives \(I_1=I_m\).
- `MPOTensor.isSAL_of_isSSAEquality_tripartite_m`: the equalities at all
  admissible cuts recover SAL.
- `MPOTensor.isSAL_of_quantumMarkovDecomposition_tripartite_m`: quantum
  Markov decompositions at all admissible cuts recover SAL.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Saturation of the area law gives equality in strong subadditivity for the
three-region marginal obtained from four consecutive regions of lengths
\(m-1,1,N-m-1,1\).  The entropy identity is
\[
  S_{N-1}+S_1=S_m+S_{N-m},
\]
which is equivalent to \(I_1=I_m\) after cancelling the full-chain entropy.

**Local fix (endpoint):** The source writes \(m<\lfloor N/2\rfloor\) at
line 1771, while its SAL chain and final comparison require the endpoint
\(m=\lfloor N/2\rfloor\).  This correction is documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1760--1780. -/
theorem isSSAEquality_tripartite_m_of_isSAL (M : MPOTensor d D)
    (hSAL : IsSAL M) {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N / 2) :
    let hM : (mpo M N).PosSemidef := (Classical.choose hSAL) N (by omega)
    let h3 : (m - 1) + 1 + (N - m - 1) ≤ N := by omega
    let ρ_ABC := (M.reducedBlockState N ((m - 1) + 1 + (N - m - 1)) h3).submatrix
      (tripartiteSplitEquiv d (m - 1) 1 (N - m - 1)).symm
      (tripartiteSplitEquiv d (m - 1) 1 (N - m - 1)).symm
    IsSSAEquality ρ_ABC
      ((reducedBlockState_posSemidef M N ((m - 1) + 1 + (N - m - 1)) h3 hM).submatrix _).1 := by
  classical
  dsimp only
  rw [IsSSAEquality]
  let hMpdo : IsMPDO M := Classical.choose hSAL
  have hNpos : 0 < N := by omega
  have hEq := mutualInfoChain_eq_of_isSAL M hSAL
    (N := N) (L := 1) (L' := m) (by omega) (by omega) hm1 hmN
  simp only [mutualInfoChain] at hEq
  have hEABC := vonNeumannEntropy_tripartiteSplit_eq_blockEntropy M
    (N := N) (a := m - 1) (b := 1) (c := N - m - 1) (by omega) (hMpdo N hNpos)
  have hEC := vonNeumannEntropy_traceC_eq_blockEntropy M
    (N := N) (a := m - 1) (b := 1) (c := N - m - 1) (by omega) (hMpdo N hNpos)
  have hEAC := vonNeumannEntropy_traceAC_eq_blockEntropy M
    (N := N) (a := m - 1) (b := 1) (c := N - m - 1) (by omega) (hMpdo N hNpos)
  have hEA := vonNeumannEntropy_traceA_eq_blockEntropy M
    (N := N) (a := m - 1) (b := 1) (c := N - m - 1) (by omega) (hMpdo N hNpos)
  rw [hEABC, hEAC, hEC, hEA]
  rw [blockEntropy_congr M N
    (show (m - 1) + 1 + (N - m - 1) = N - 1 by omega)
    (by omega) (Nat.sub_le N 1) (hMpdo N hNpos)]
  rw [blockEntropy_congr M N (show (m - 1) + 1 = m by omega)
    (by omega) (by omega) (hMpdo N hNpos)]
  rw [blockEntropy_congr M N (show 1 + (N - m - 1) = N - m by omega)
    (by omega) (Nat.sub_le N m) (hMpdo N hNpos)]
  linarith [hEq]

/-- Conversely, equality in strong subadditivity for the regions of lengths
\(m-1,1,N-m-1\) gives \(I_1=I_m\) on the full periodic chain.

This is the entropy rearrangement used to return to the saturated-area-law
condition in arXiv:1606.00608, Appendix C.2, lines 1770--1780.

**Local fix (endpoint):** The endpoint \(m=\lfloor N/2\rfloor\), needed in
the final comparison, is documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem mutualInfoChain_one_eq_of_isSSAEquality_tripartite_m
    (M : MPOTensor d D) (hMpdo : IsMPDO M) {N m : ℕ}
    (hm1 : 1 ≤ m) (hmN : m ≤ N / 2)
    (hSSA :
      let h3 : (m - 1) + 1 + (N - m - 1) ≤ N := by omega
      let ρ_ABC :=
        (M.reducedBlockState N ((m - 1) + 1 + (N - m - 1)) h3).submatrix
          (tripartiteSplitEquiv d (m - 1) 1 (N - m - 1)).symm
          (tripartiteSplitEquiv d (m - 1) 1 (N - m - 1)).symm
      IsSSAEquality ρ_ABC
        ((reducedBlockState_posSemidef M N ((m - 1) + 1 + (N - m - 1)) h3
          (hMpdo N (by omega))).submatrix _).1) :
    mutualInfoChain M N 1 (by omega) (hMpdo N (by omega)) =
      mutualInfoChain M N m (by omega) (hMpdo N (by omega)) := by
  classical
  have hNpos : 0 < N := by omega
  dsimp only at hSSA
  rw [IsSSAEquality] at hSSA
  simp only [mutualInfoChain]
  have hEABC := vonNeumannEntropy_tripartiteSplit_eq_blockEntropy M
    (N := N) (a := m - 1) (b := 1) (c := N - m - 1) (by omega) (hMpdo N hNpos)
  have hEC := vonNeumannEntropy_traceC_eq_blockEntropy M
    (N := N) (a := m - 1) (b := 1) (c := N - m - 1) (by omega) (hMpdo N hNpos)
  have hEAC := vonNeumannEntropy_traceAC_eq_blockEntropy M
    (N := N) (a := m - 1) (b := 1) (c := N - m - 1) (by omega) (hMpdo N hNpos)
  have hEA := vonNeumannEntropy_traceA_eq_blockEntropy M
    (N := N) (a := m - 1) (b := 1) (c := N - m - 1) (by omega) (hMpdo N hNpos)
  rw [hEABC, hEAC, hEC, hEA] at hSSA
  rw [blockEntropy_congr M N
    (show (m - 1) + 1 + (N - m - 1) = N - 1 by omega)
    (by omega) (Nat.sub_le N 1) (hMpdo N hNpos)] at hSSA
  rw [blockEntropy_congr M N (show (m - 1) + 1 = m by omega)
    (by omega) (by omega) (hMpdo N hNpos)] at hSSA
  rw [blockEntropy_congr M N (show 1 + (N - m - 1) = N - m by omega)
    (by omega) (Nat.sub_le N m) (hMpdo N hNpos)] at hSSA
  linarith [hSSA]

/-- If every four-region marginal with lengths \(m-1,1,N-m-1,1\)
attains equality in strong subadditivity, then the tensor saturates the area
law, provided its periodic operators are positive and have nonzero trace.

**Local fix (endpoint):** The comparison at \(L+1=\lfloor N/2\rfloor\)
corrects the strict inequality printed at source line 1771, as documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1770--1780. -/
theorem isSAL_of_isSSAEquality_tripartite_m (M : MPOTensor d D)
    (hMpdo : IsMPDO M)
    (htrace : ∀ N, 0 < N → (mpo M N).trace ≠ 0)
    (hSSA : ∀ (N m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N / 2),
      let h3 : (m - 1) + 1 + (N - m - 1) ≤ N := by omega
      let ρ_ABC :=
        (M.reducedBlockState N ((m - 1) + 1 + (N - m - 1)) h3).submatrix
          (tripartiteSplitEquiv d (m - 1) 1 (N - m - 1)).symm
          (tripartiteSplitEquiv d (m - 1) 1 (N - m - 1)).symm
      IsSSAEquality ρ_ABC
        ((reducedBlockState_posSemidef M N ((m - 1) + 1 + (N - m - 1)) h3
          (hMpdo N (by omega))).submatrix _).1) :
    IsSAL M := by
  refine ⟨hMpdo, htrace, ?_⟩
  intro N L hL hLN
  have hEqL := mutualInfoChain_one_eq_of_isSSAEquality_tripartite_m
    M hMpdo hL (Nat.le_of_lt hLN) (hSSA N L hL (Nat.le_of_lt hLN))
  have hEqSucc := mutualInfoChain_one_eq_of_isSSAEquality_tripartite_m
    M hMpdo (m := L + 1) (by omega) (by omega)
      (hSSA N (L + 1) (by omega) (by omega))
  exact hEqL.symm.trans hEqSucc

/-- Quantum-Markov decompositions for every admissible three-region marginal
imply saturation of the area law, provided the periodic operators are positive
and have nonzero trace.

This isolates the entropy-theoretic conclusion used in the proof of source
Proposition 4to2: the direct-sum tensor-factor decomposition on the
middle site implies equality in strong subadditivity, and the latter equalities
give SAL.

**Scope restriction (Markov decomposition assumed):** Proposition 4to2 of
arXiv:1606.00608 assumes instead a single translation-invariant commuting bond
and ZCL. Deriving the decompositions below from those hypotheses requires the
Bravyi--Vyalyi spatial decomposition (Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1),
and the subsequent ZCL trace factorization. This missing implication is documented in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

Source: arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines
1606--1612. -/
theorem isSAL_of_quantumMarkovDecomposition_tripartite_m
    (M : MPOTensor d D) (hMpdo : IsMPDO M)
    (htrace : ∀ N, 0 < N → (mpo M N).trace ≠ 0)
    (hMarkov : ∀ (N m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N / 2),
      let h3 : (m - 1) + 1 + (N - m - 1) ≤ N := by omega
      let ρ_ABC :=
        (M.reducedBlockState N ((m - 1) + 1 + (N - m - 1)) h3).submatrix
          (tripartiteSplitEquiv d (m - 1) 1 (N - m - 1)).symm
          (tripartiteSplitEquiv d (m - 1) 1 (N - m - 1)).symm
      Nonempty (Entropy.QuantumMarkovDecomposition ρ_ABC)) :
    IsSAL M := by
  apply isSAL_of_isSSAEquality_tripartite_m M hMpdo htrace
  intro N m hm1 hmN
  dsimp only
  apply Entropy.isSSAEquality_of_quantumMarkovDecomposition
  · constructor
    · exact (reducedBlockState_posSemidef M N
        ((m - 1) + 1 + (N - m - 1)) (by omega) (hMpdo N (by omega))).submatrix _
    · rw [Matrix.trace_submatrix_equiv]
      exact reducedBlockState_trace M N ((m - 1) + 1 + (N - m - 1))
        (by omega) (htrace N (by omega))
  · exact hMarkov N m hm1 hmN

end MPOTensor
