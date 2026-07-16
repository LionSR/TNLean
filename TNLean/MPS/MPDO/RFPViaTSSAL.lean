/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Entropy.MutualInformationDataProcessing
import TNLean.MPS.MPDO.MutualInfoMonotone
import TNLean.MPS.MPDO.RFPViaTSGlobal

/-!
# The conditional mutual-information step for MPDO renormalization fixed points

This file isolates the entropic part of the proof that a mixed-state
renormalization fixed point saturates the area law.  The result below is a
conditional helper, not a formalization of Proposition `propsimple`.  It proves
the two exact finite-chain identifications obtained by transferring one site
across a bipartition and derives the resulting mutual-information equality.
The separate normalization argument uses horizontal canonical form, the MPDO
condition, and the renormalization maps; simplicity is not needed for the
forward implication of the source proposition.

Source: arXiv:1606.00608, Appendix C, lines 1333--1341.  See
`docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex`.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Split a length-`N` configuration into consecutive blocks of lengths `L`
and `K`, and flatten each block to a `Fin` index. -/
noncomputable def chainBiSplitEquiv (d N L K : ℕ) (h : N = L + K) :
    (Fin N → Fin d) ≃ Fin (d ^ L) × Fin (d ^ K) :=
  (Equiv.arrowCongr (finCongr h) (Equiv.refl (Fin d))).trans
    (biSplitEquiv d L K)

/-- The normalized periodic MPO viewed across a consecutive bipartition. -/
noncomputable def splitNormalizedMPO (M : MPOTensor d D) (N L K : ℕ)
    (h : N = L + K) :
    Matrix (Fin (d ^ L) × Fin (d ^ K)) (Fin (d ^ L) × Fin (d ^ K)) ℂ :=
  (normalizedMPO M N).submatrix (chainBiSplitEquiv d N L K h).symm
    (chainBiSplitEquiv d N L K h).symm

/-- Positivity of the normalized state is preserved by the bipartition
reindexing. -/
theorem splitNormalizedMPO_posSemidef (M : MPOTensor d D) (N L K : ℕ)
    (h : N = L + K) (hM : (mpo M N).PosSemidef) :
    (splitNormalizedMPO M N L K h).PosSemidef := by
  exact (normalizedMPO_posSemidef M N hM).submatrix _

/-- A positive-length normalized periodic MPO has unit trace whenever its
unnormalized trace is nonzero. -/
theorem splitNormalizedMPO_trace (M : MPOTensor d D) (N L K : ℕ)
    (h : N = L + K) (htr : (mpo M N).trace ≠ 0) :
    (splitNormalizedMPO M N L K h).trace = 1 := by
  rw [splitNormalizedMPO, Matrix.trace_submatrix_equiv,
    normalizedMPO_trace M N htr]

/-- The localized one-to-two map, with its input and output block
configurations flattened to `Fin` indices. -/
noncomputable def refineFirstBlock
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (n : ℕ) :
    Matrix (Fin (d ^ (n + 1))) (Fin (d ^ (n + 1))) ℂ →ₗ[ℂ]
      Matrix (Fin (d ^ (n + 2))) (Fin (d ^ (n + 2))) ℂ :=
  Matrix.equivReindexMap finFunctionFinEquiv ∘ₗ
    refineFirstSite T n ∘ₗ
      Matrix.equivReindexMap finFunctionFinEquiv.symm

/-- The localized two-to-one map, with its input and output block
configurations flattened to `Fin` indices. -/
noncomputable def coarsenFirstBlock
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    Matrix (Fin (d ^ (n + 2))) (Fin (d ^ (n + 2))) ℂ →ₗ[ℂ]
      Matrix (Fin (d ^ (n + 1))) (Fin (d ^ (n + 1))) ℂ :=
  Matrix.equivReindexMap finFunctionFinEquiv ∘ₗ
    coarsenFirstTwoSites S n ∘ₗ
      Matrix.equivReindexMap finFunctionFinEquiv.symm

/-- Flattening a localized refinement channel preserves the channel
property. -/
theorem refineFirstBlock_isKrausCPTP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hT : IsKrausCPTP T) (n : ℕ) :
    IsKrausCPTP (refineFirstBlock T n) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP finFunctionFinEquiv.symm)
      (refineFirstSite_isKrausCPTP hT n))
    (Matrix.equivReindexMap_isKrausCPTP finFunctionFinEquiv)

/-- Flattening a localized coarse-graining channel preserves the channel
property. -/
theorem coarsenFirstBlock_isKrausCPTP
    {S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ}
    (hS : IsKrausCPTP S) (n : ℕ) :
    IsKrausCPTP (coarsenFirstBlock S n) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP finFunctionFinEquiv.symm)
      (coarsenFirstTwoSites_isKrausCPTP hS n))
    (Matrix.equivReindexMap_isKrausCPTP finFunctionFinEquiv)

/-- Mutual information is congruent under equality of the bipartite density
matrix; the Hermiticity witnesses carry no additional data. -/
private theorem mutualInformation_congr
    {dA dB : ℕ}
    {ρ σ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (h : ρ = σ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Entropy.mutualInformation ρ hρ = Entropy.mutualInformation σ hσ := by
  subst σ
  rfl

/-- Fixing the second block of a flattened bipartition leaves the first-block
physical closure, with the fixed word inserted as its virtual boundary. -/
private theorem splitMPO_slice
    (M : MPOTensor d D) (N L K : ℕ) (h : N = L + K)
    (u v : Fin K → Fin d) :
    Matrix.equivReindexMap finFunctionFinEquiv.symm
        (Matrix.bipartiteSlice
          ((mpo M N).submatrix (chainBiSplitEquiv d N L K h).symm
            (chainBiSplitEquiv d N L K h).symm)
          (finFunctionFinEquiv u) (finFunctionFinEquiv v)) =
      physCloseN M L (evalWord M (List.ofFn u) (List.ofFn v)) := by
  subst N
  ext x y
  simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, chainBiSplitEquiv, biSplitEquiv,
    Matrix.bipartiteSlice, blockSplitEquiv_symm_apply, mpoMatrixEntry,
    List.ofFn_fin_append, evalWord_append]

/-- The preceding slice identity for the normalized periodic MPO. -/
private theorem splitNormalizedMPO_slice
    (M : MPOTensor d D) (N L K : ℕ) (h : N = L + K)
    (u v : Fin K → Fin d) :
    Matrix.equivReindexMap finFunctionFinEquiv.symm
        (Matrix.bipartiteSlice (splitNormalizedMPO M N L K h)
          (finFunctionFinEquiv u) (finFunctionFinEquiv v)) =
      (Matrix.trace (mpo M N))⁻¹ •
        physCloseN M L (evalWord M (List.ofFn u) (List.ofFn v)) := by
  have hs := splitMPO_slice M N L K h u v
  ext x y
  have hsxy := congrFun (congrFun hs x) y
  simpa [splitNormalizedMPO, normalizedMPO, Matrix.equivReindexMap,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.bipartiteSlice, Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun z ↦ (Matrix.trace (mpo M N))⁻¹ * z) hsxy

/-- The local closure equations transfer one site across a flattened
bipartition of a periodic normalized MPO.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
theorem tensorMapBoth_splitNormalizedMPO
    (M : MPOTensor d D) (N a b : ℕ)
    (hIn : N = (a + 1) + (b + 2)) (hOut : N = (a + 2) + (b + 1))
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hSclose : ∀ X, S (physClose2 M X) = physClose1 M X)
    (hTclose : ∀ X, T (physClose1 M X) = physClose2 M X) :
    Matrix.tensorMapBoth (refineFirstBlock T a) (coarsenFirstBlock S b)
        (splitNormalizedMPO M N (a + 1) (b + 2) hIn) =
      splitNormalizedMPO M N (a + 2) (b + 1) hOut := by
  ext p q
  rcases p with ⟨pA, pB⟩
  rcases q with ⟨qA, qB⟩
  simp only [Matrix.tensorMapBoth, Matrix.idTensorMap, Matrix.submatrix_apply,
    Matrix.tensorMapId_apply, Prod.swap_prod_mk]
  simp only [coarsenFirstBlock, LinearMap.coe_comp, Function.comp_apply,
    Matrix.equivReindexMap]
  let uA : Fin (a + 2) → Fin d := finFunctionFinEquiv.symm pA
  let vA : Fin (a + 2) → Fin d := finFunctionFinEquiv.symm qA
  let X : Matrix (Fin D) (Fin D) ℂ :=
    evalWord M (List.ofFn uA) (List.ofFn vA)
  let Y : Matrix (Fin (b + 2) → Fin d) (Fin (b + 2) → Fin d) ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ finFunctionFinEquiv.symm
      finFunctionFinEquiv.symm)
      (Matrix.bipartiteSlice
        ((Matrix.tensorMapId (refineFirstBlock T a)
          (splitNormalizedMPO M N (a + 1) (b + 2) hIn)).submatrix
            Prod.swap Prod.swap) pA qA)
  change (coarsenFirstTwoSites S b Y) (finFunctionFinEquiv.symm pB)
      (finFunctionFinEquiv.symm qB) = _
  have hY : Y = (Matrix.trace (mpo M N))⁻¹ • physCloseN M (b + 2) X := by
    ext u v
    change (refineFirstSite T a
        (Matrix.equivReindexMap finFunctionFinEquiv.symm
          (Matrix.bipartiteSlice
            (splitNormalizedMPO M N (a + 1) (b + 2) hIn)
            (finFunctionFinEquiv u) (finFunctionFinEquiv v)))) uA vA = _
    rw [splitNormalizedMPO_slice M N (a + 1) (b + 2) hIn u v,
      map_smul, refineFirstSite_physCloseN M T hTclose]
    simp only [Matrix.smul_apply, smul_eq_mul, physCloseN_apply]
    congr 1
    exact Matrix.trace_mul_comm _ _
  rw [hY, map_smul, coarsenFirstTwoSites_physCloseN M S hSclose]
  let uB : Fin (b + 1) → Fin d := finFunctionFinEquiv.symm pB
  let vB : Fin (b + 1) → Fin d := finFunctionFinEquiv.symm qB
  have hout := splitNormalizedMPO_slice M N (a + 2) (b + 1) hOut uB vB
  have houtxy := congrFun (congrFun hout uA) vA
  have houtEntry :
      splitNormalizedMPO M N (a + 2) (b + 1) hOut (pA, pB) (qA, qB) =
        (Matrix.trace (mpo M N))⁻¹ *
          Matrix.trace (evalWord M (List.ofFn uA) (List.ofFn vA) *
            evalWord M (List.ofFn uB) (List.ofFn vB)) := by
    simpa [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
      Matrix.reindex_apply, Matrix.bipartiteSlice, Matrix.smul_apply,
      smul_eq_mul, physCloseN_apply, uA, vA, uB, vB] using houtxy
  rw [houtEntry]
  simp only [Matrix.smul_apply, smul_eq_mul, physCloseN_apply]
  congr 1
  exact Matrix.trace_mul_comm _ _

/-- The reverse pair of localized closure maps transfers the site back across
the same bipartition.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C,
lines 1337--1341. -/
theorem tensorMapBoth_splitNormalizedMPO_reverse
    (M : MPOTensor d D) (N a b : ℕ)
    (hIn : N = (a + 1) + (b + 2)) (hOut : N = (a + 2) + (b + 1))
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hSclose : ∀ X, S (physClose2 M X) = physClose1 M X)
    (hTclose : ∀ X, T (physClose1 M X) = physClose2 M X) :
    Matrix.tensorMapBoth (coarsenFirstBlock S a) (refineFirstBlock T b)
        (splitNormalizedMPO M N (a + 2) (b + 1) hOut) =
      splitNormalizedMPO M N (a + 1) (b + 2) hIn := by
  ext p q
  rcases p with ⟨pA, pB⟩
  rcases q with ⟨qA, qB⟩
  simp only [Matrix.tensorMapBoth, Matrix.idTensorMap, Matrix.submatrix_apply,
    Matrix.tensorMapId_apply, Prod.swap_prod_mk]
  simp only [refineFirstBlock, LinearMap.coe_comp, Function.comp_apply,
    Matrix.equivReindexMap]
  let uA : Fin (a + 1) → Fin d := finFunctionFinEquiv.symm pA
  let vA : Fin (a + 1) → Fin d := finFunctionFinEquiv.symm qA
  let X : Matrix (Fin D) (Fin D) ℂ :=
    evalWord M (List.ofFn uA) (List.ofFn vA)
  let Y : Matrix (Fin (b + 1) → Fin d) (Fin (b + 1) → Fin d) ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ finFunctionFinEquiv.symm
      finFunctionFinEquiv.symm)
      (Matrix.bipartiteSlice
        ((Matrix.tensorMapId (coarsenFirstBlock S a)
          (splitNormalizedMPO M N (a + 2) (b + 1) hOut)).submatrix
            Prod.swap Prod.swap) pA qA)
  change (refineFirstSite T b Y) (finFunctionFinEquiv.symm pB)
      (finFunctionFinEquiv.symm qB) = _
  have hY : Y = (Matrix.trace (mpo M N))⁻¹ • physCloseN M (b + 1) X := by
    ext u v
    change (coarsenFirstTwoSites S a
        (Matrix.equivReindexMap finFunctionFinEquiv.symm
          (Matrix.bipartiteSlice
            (splitNormalizedMPO M N (a + 2) (b + 1) hOut)
            (finFunctionFinEquiv u) (finFunctionFinEquiv v)))) uA vA = _
    rw [splitNormalizedMPO_slice M N (a + 2) (b + 1) hOut u v,
      map_smul, coarsenFirstTwoSites_physCloseN M S hSclose]
    simp only [Matrix.smul_apply, smul_eq_mul, physCloseN_apply]
    congr 1
    exact Matrix.trace_mul_comm _ _
  rw [hY, map_smul, refineFirstSite_physCloseN M T hTclose]
  let uB : Fin (b + 2) → Fin d := finFunctionFinEquiv.symm pB
  let vB : Fin (b + 2) → Fin d := finFunctionFinEquiv.symm qB
  have hout := splitNormalizedMPO_slice M N (a + 1) (b + 2) hIn uB vB
  have houtxy := congrFun (congrFun hout uA) vA
  have houtEntry :
      splitNormalizedMPO M N (a + 1) (b + 2) hIn (pA, pB) (qA, qB) =
        (Matrix.trace (mpo M N))⁻¹ *
          Matrix.trace (evalWord M (List.ofFn uA) (List.ofFn vA) *
            evalWord M (List.ofFn uB) (List.ofFn vB)) := by
    simpa [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
      Matrix.reindex_apply, Matrix.bipartiteSlice, Matrix.smul_apply,
      smul_eq_mul, physCloseN_apply, uA, vA, uB, vB] using houtxy
  rw [houtEntry]
  simp only [Matrix.smul_apply, smul_eq_mul, physCloseN_apply]
  congr 1
  exact Matrix.trace_mul_comm _ _

/-- **Conditional Appendix C mutual-information equality.**

Let `A` and `B` have lengths `a+1` and `b+2`.  If applying the localized
one-to-two map to `A` and the localized two-to-one map to `B` gives the same
periodic state with block lengths `a+2` and `b+1`, and the reverse pair of
localized maps recovers the original split state, then the two mutual
informations coincide.

Both finite-chain identifications are derived from the physical-closure
equations above.  The only normalization hypothesis is the nonzero trace of
the `N`-site operator.  The displayed decomposition makes `N` positive, so no
empty-chain condition is used.

Source: arXiv:1606.00608, Appendix C, lines 1333--1341.

**Scope restriction:** This is the conditional entropic helper documented in
`docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex`, not Proposition
`propsimple`. -/
theorem mutualInformation_split_eq_of_local_transfers
    (M : MPOTensor d D) (N a b : ℕ)
    (hIn : N = (a + 1) + (b + 2)) (hOut : N = (a + 2) + (b + 1))
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hS : IsKrausCPTP S) (hT : IsKrausCPTP T)
    (hSclose : ∀ X, S (physClose2 M X) = physClose1 M X)
    (hTclose : ∀ X, T (physClose1 M X) = physClose2 M X) :
    Entropy.mutualInformation
        (splitNormalizedMPO M N (a + 1) (b + 2) hIn)
        (splitNormalizedMPO_posSemidef M N (a + 1) (b + 2) hIn hM).isHermitian =
      Entropy.mutualInformation
        (splitNormalizedMPO M N (a + 2) (b + 1) hOut)
        (splitNormalizedMPO_posSemidef M N (a + 2) (b + 1) hOut hM).isHermitian := by
  have hρ := splitNormalizedMPO_posSemidef M N (a + 1) (b + 2) hIn hM
  have hσ := splitNormalizedMPO_posSemidef M N (a + 2) (b + 1) hOut hM
  have hρtr := splitNormalizedMPO_trace M N (a + 1) (b + 2) hIn htr
  have hσtr := splitNormalizedMPO_trace M N (a + 2) (b + 1) hOut htr
  have hforward := tensorMapBoth_splitNormalizedMPO M N a b hIn hOut S T hSclose hTclose
  have hbackward :=
    tensorMapBoth_splitNormalizedMPO_reverse M N a b hIn hOut S T hSclose hTclose
  have hforward_le :=
    (refineFirstBlock_isKrausCPTP hT a).mutualInformation_tensorMapBoth_le
      (coarsenFirstBlock_isKrausCPTP hS b)
      (splitNormalizedMPO M N (a + 1) (b + 2) hIn) hρ hρtr
  have hbackward_le :=
    (coarsenFirstBlock_isKrausCPTP hS a).mutualInformation_tensorMapBoth_le
      (refineFirstBlock_isKrausCPTP hT b)
      (splitNormalizedMPO M N (a + 2) (b + 1) hOut) hσ hσtr
  have hσρ :
      Entropy.mutualInformation
          (splitNormalizedMPO M N (a + 2) (b + 1) hOut) hσ.isHermitian ≤
        Entropy.mutualInformation
          (splitNormalizedMPO M N (a + 1) (b + 2) hIn) hρ.isHermitian := by
    calc
      _ = Entropy.mutualInformation
          (Matrix.tensorMapBoth (refineFirstBlock T a) (coarsenFirstBlock S b)
            (splitNormalizedMPO M N (a + 1) (b + 2) hIn))
          ((refineFirstBlock_isKrausCPTP hT a).tensorMapBoth_posSemidef
            (coarsenFirstBlock_isKrausCPTP hS b) hρ).isHermitian :=
        (mutualInformation_congr hforward _ _).symm
      _ ≤ _ := hforward_le
  have hρσ :
      Entropy.mutualInformation
          (splitNormalizedMPO M N (a + 1) (b + 2) hIn) hρ.isHermitian ≤
        Entropy.mutualInformation
          (splitNormalizedMPO M N (a + 2) (b + 1) hOut) hσ.isHermitian := by
    calc
      _ = Entropy.mutualInformation
          (Matrix.tensorMapBoth (coarsenFirstBlock S a) (refineFirstBlock T b)
            (splitNormalizedMPO M N (a + 2) (b + 1) hOut))
          ((coarsenFirstBlock_isKrausCPTP hS a).tensorMapBoth_posSemidef
            (refineFirstBlock_isKrausCPTP hT b) hσ).isHermitian :=
        (mutualInformation_congr hbackward _ _).symm
      _ ≤ _ := hbackward_le
  exact le_antisymm hρσ hσρ

/-- A renormalization fixed point has equal bipartite mutual information when
one site is transferred across either side of a nontrivial cut.

This is the conditional entropic conclusion of Appendix C.  It still does not
assert Proposition `propsimple`, because identifying this flattened bipartite
quantity with `mutualInfoChain` and assembling the positive-chain SAL statement
remain separate steps.  The required nonzero trace follows separately from
horizontal canonical form, the MPDO condition, and the renormalization maps;
source simplicity is not used in this implication.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C,
lines 1333--1341.

**Scope restriction:** The explicit nonzero-trace hypothesis is confined to
this helper and is not added to the source proposition; see
`docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex`. -/
theorem mutualInformation_split_eq_of_isRFPViaTS
    (M : MPOTensor d D) (hRFP : IsRFPViaTS M) (N a b : ℕ)
    (hIn : N = (a + 1) + (b + 2)) (hOut : N = (a + 2) + (b + 1))
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    Entropy.mutualInformation
        (splitNormalizedMPO M N (a + 1) (b + 2) hIn)
        (splitNormalizedMPO_posSemidef M N (a + 1) (b + 2) hIn hM).isHermitian =
      Entropy.mutualInformation
        (splitNormalizedMPO M N (a + 2) (b + 1) hOut)
        (splitNormalizedMPO_posSemidef M N (a + 2) (b + 1) hOut hM).isHermitian := by
  obtain ⟨S, T, hS, hT, hSclose, hTclose⟩ := hRFP
  exact mutualInformation_split_eq_of_local_transfers M N a b hIn hOut hM htr
    S T hS hT hSclose hTclose

end MPOTensor
