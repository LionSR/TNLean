/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Entropy.MutualInformationDataProcessing
import TNLean.MPS.MPDO.MutualInfoBridge
import TNLean.MPS.MPDO.RFPViaTSGlobal

/-!
# Saturation of the area law for MPDO renormalization fixed points

This file proves Proposition `propsimple` under the explicit normalization
condition that every positive-length MPO has nonzero trace.  This condition is
implicit in the source's density-operator language.  A normalized BNT-refined
horizontal form supplies it as a corollary, yielding the previously exposed
horizontal-form specialization.

The SAL proof first establishes the two exact finite-chain identities obtained
by transferring one site across a bipartition, applies mutual-information data
processing in both directions, and then identifies bipartite mutual information
with the chain quantity I_L.  The one-site normalization condition and the
vertical-loop trace identities supply the nonzero transfer matrix needed for
source ZCL.  Simplicity is not used in this implication.

Source: arXiv:1606.00608, Appendix C, lines 1333--1341.  See
`docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex`.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ}

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
          ((mpo M N).submatrix (chainBipartitionEquiv d N L K h).symm
            (chainBipartitionEquiv d N L K h).symm)
          (finFunctionFinEquiv u) (finFunctionFinEquiv v)) =
      physCloseN M L (evalWord M (List.ofFn u) (List.ofFn v)) := by
  subst N
  ext x y
  simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, chainBipartitionEquiv, biSplitEquiv,
    Matrix.bipartiteSlice, blockSplitEquiv_symm_apply, mpoMatrixEntry,
    List.ofFn_fin_append, evalWord_append]

/-- The preceding slice identity for the normalized periodic MPO. -/
private theorem bipartitionedNormalizedMPO_slice
    (M : MPOTensor d D) (N L K : ℕ) (h : N = L + K)
    (u v : Fin K → Fin d) :
    Matrix.equivReindexMap finFunctionFinEquiv.symm
        (Matrix.bipartiteSlice (bipartitionedNormalizedMPO M N L K h)
          (finFunctionFinEquiv u) (finFunctionFinEquiv v)) =
      (Matrix.trace (mpo M N))⁻¹ •
        physCloseN M L (evalWord M (List.ofFn u) (List.ofFn v)) := by
  have hs := splitMPO_slice M N L K h u v
  ext x y
  have hsxy := congrFun (congrFun hs x) y
  simpa [bipartitionedNormalizedMPO, normalizedMPO, Matrix.equivReindexMap,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.bipartiteSlice, Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun z ↦ (Matrix.trace (mpo M N))⁻¹ * z) hsxy

/-- The local closure equations transfer one site across a flattened
bipartition of a periodic normalized MPO.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
theorem tensorMapBoth_bipartitionedNormalizedMPO
    (M : MPOTensor d D) (N a b : ℕ)
    (hIn : N = (a + 1) + (b + 2)) (hOut : N = (a + 2) + (b + 1))
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hSclose : ∀ X, S (physClose2 M X) = physClose1 M X)
    (hTclose : ∀ X, T (physClose1 M X) = physClose2 M X) :
    Matrix.tensorMapBoth (refineFirstBlock T a) (coarsenFirstBlock S b)
        (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn) =
      bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut := by
  ext p q
  rcases p with ⟨pA, pB⟩
  rcases q with ⟨qA, qB⟩
  simp only [Matrix.tensorMapBoth, Matrix.idTensorMap]
  simp only [coarsenFirstBlock, Matrix.equivReindexMap]
  let uA : Fin (a + 2) → Fin d := finFunctionFinEquiv.symm pA
  let vA : Fin (a + 2) → Fin d := finFunctionFinEquiv.symm qA
  let X : Matrix (Fin D) (Fin D) ℂ :=
    evalWord M (List.ofFn uA) (List.ofFn vA)
  let Y : Matrix (Fin (b + 2) → Fin d) (Fin (b + 2) → Fin d) ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ finFunctionFinEquiv.symm
      finFunctionFinEquiv.symm)
      (Matrix.bipartiteSlice
        ((Matrix.tensorMapId (refineFirstBlock T a)
          (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn)).submatrix
            Prod.swap Prod.swap) pA qA)
  change (coarsenFirstTwoSites S b Y) (finFunctionFinEquiv.symm pB)
      (finFunctionFinEquiv.symm qB) = _
  have hY : Y = (Matrix.trace (mpo M N))⁻¹ • physCloseN M (b + 2) X := by
    ext u v
    change (refineFirstSite T a
        (Matrix.equivReindexMap finFunctionFinEquiv.symm
          (Matrix.bipartiteSlice
            (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn)
            (finFunctionFinEquiv u) (finFunctionFinEquiv v)))) uA vA = _
    rw [bipartitionedNormalizedMPO_slice M N (a + 1) (b + 2) hIn u v,
      map_smul, refineFirstSite_physCloseN M T hTclose]
    simp only [Matrix.smul_apply, smul_eq_mul, physCloseN_apply]
    congr 1
    exact Matrix.trace_mul_comm _ _
  rw [hY, map_smul, coarsenFirstTwoSites_physCloseN M S hSclose]
  let uB : Fin (b + 1) → Fin d := finFunctionFinEquiv.symm pB
  let vB : Fin (b + 1) → Fin d := finFunctionFinEquiv.symm qB
  have hout := bipartitionedNormalizedMPO_slice M N (a + 2) (b + 1) hOut uB vB
  have houtxy := congrFun (congrFun hout uA) vA
  have houtEntry :
      bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut (pA, pB) (qA, qB) =
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
theorem tensorMapBoth_bipartitionedNormalizedMPO_reverse
    (M : MPOTensor d D) (N a b : ℕ)
    (hIn : N = (a + 1) + (b + 2)) (hOut : N = (a + 2) + (b + 1))
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hSclose : ∀ X, S (physClose2 M X) = physClose1 M X)
    (hTclose : ∀ X, T (physClose1 M X) = physClose2 M X) :
    Matrix.tensorMapBoth (coarsenFirstBlock S a) (refineFirstBlock T b)
        (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut) =
      bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn := by
  ext p q
  rcases p with ⟨pA, pB⟩
  rcases q with ⟨qA, qB⟩
  simp only [Matrix.tensorMapBoth, Matrix.idTensorMap]
  simp only [refineFirstBlock, Matrix.equivReindexMap]
  let uA : Fin (a + 1) → Fin d := finFunctionFinEquiv.symm pA
  let vA : Fin (a + 1) → Fin d := finFunctionFinEquiv.symm qA
  let X : Matrix (Fin D) (Fin D) ℂ :=
    evalWord M (List.ofFn uA) (List.ofFn vA)
  let Y : Matrix (Fin (b + 1) → Fin d) (Fin (b + 1) → Fin d) ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ finFunctionFinEquiv.symm
      finFunctionFinEquiv.symm)
      (Matrix.bipartiteSlice
        ((Matrix.tensorMapId (coarsenFirstBlock S a)
          (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut)).submatrix
            Prod.swap Prod.swap) pA qA)
  change (refineFirstSite T b Y) (finFunctionFinEquiv.symm pB)
      (finFunctionFinEquiv.symm qB) = _
  have hY : Y = (Matrix.trace (mpo M N))⁻¹ • physCloseN M (b + 1) X := by
    ext u v
    change (coarsenFirstTwoSites S a
        (Matrix.equivReindexMap finFunctionFinEquiv.symm
          (Matrix.bipartiteSlice
            (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut)
            (finFunctionFinEquiv u) (finFunctionFinEquiv v)))) uA vA = _
    rw [bipartitionedNormalizedMPO_slice M N (a + 2) (b + 1) hOut u v,
      map_smul, coarsenFirstTwoSites_physCloseN M S hSclose]
    simp only [Matrix.smul_apply, smul_eq_mul, physCloseN_apply]
    congr 1
    exact Matrix.trace_mul_comm _ _
  rw [hY, map_smul, refineFirstSite_physCloseN M T hTclose]
  let uB : Fin (b + 2) → Fin d := finFunctionFinEquiv.symm pB
  let vB : Fin (b + 2) → Fin d := finFunctionFinEquiv.symm qB
  have hout := bipartitionedNormalizedMPO_slice M N (a + 1) (b + 2) hIn uB vB
  have houtxy := congrFun (congrFun hout uA) vA
  have houtEntry :
      bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn (pA, pB) (qA, qB) =
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
theorem mutualInformation_bipartition_eq_of_local_transfers
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
        (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn)
        (bipartitionedNormalizedMPO_posSemidef M N (a + 1) (b + 2) hIn hM).isHermitian =
      Entropy.mutualInformation
        (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut)
        (bipartitionedNormalizedMPO_posSemidef M N (a + 2) (b + 1) hOut hM).isHermitian := by
  have hρ := bipartitionedNormalizedMPO_posSemidef M N (a + 1) (b + 2) hIn hM
  have hσ := bipartitionedNormalizedMPO_posSemidef M N (a + 2) (b + 1) hOut hM
  have hρtr := bipartitionedNormalizedMPO_trace M N (a + 1) (b + 2) hIn htr
  have hσtr := bipartitionedNormalizedMPO_trace M N (a + 2) (b + 1) hOut htr
  have hforward := tensorMapBoth_bipartitionedNormalizedMPO M N a b hIn hOut S T hSclose hTclose
  have hbackward :=
    tensorMapBoth_bipartitionedNormalizedMPO_reverse M N a b hIn hOut S T hSclose hTclose
  have hforward_le :=
    (refineFirstBlock_isKrausCPTP hT a).mutualInformation_tensorMapBoth_le
      (coarsenFirstBlock_isKrausCPTP hS b)
      (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn) hρ hρtr
  have hbackward_le :=
    (coarsenFirstBlock_isKrausCPTP hS a).mutualInformation_tensorMapBoth_le
      (refineFirstBlock_isKrausCPTP hT b)
      (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut) hσ hσtr
  have hσρ :
      Entropy.mutualInformation
          (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut) hσ.isHermitian ≤
        Entropy.mutualInformation
          (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn) hρ.isHermitian := by
    calc
      _ = Entropy.mutualInformation
          (Matrix.tensorMapBoth (refineFirstBlock T a) (coarsenFirstBlock S b)
            (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn))
          ((refineFirstBlock_isKrausCPTP hT a).tensorMapBoth_posSemidef
            (coarsenFirstBlock_isKrausCPTP hS b) hρ).isHermitian :=
        (mutualInformation_congr hforward _ _).symm
      _ ≤ _ := hforward_le
  have hρσ :
      Entropy.mutualInformation
          (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn) hρ.isHermitian ≤
        Entropy.mutualInformation
          (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut) hσ.isHermitian := by
    calc
      _ = Entropy.mutualInformation
          (Matrix.tensorMapBoth (coarsenFirstBlock S a) (refineFirstBlock T b)
            (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut))
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
normalized BNT-refined horizontal form, the MPDO condition, and the
renormalization maps; source simplicity is not used in this implication.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C,
lines 1333--1341.

**Scope restriction:** The explicit nonzero-trace hypothesis is confined to
this helper and is not added to the source proposition; see
`docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex`. -/
theorem mutualInformation_bipartition_eq_of_isRFPViaTS
    (M : MPOTensor d D) (hRFP : IsRFPViaTS M) (N a b : ℕ)
    (hIn : N = (a + 1) + (b + 2)) (hOut : N = (a + 2) + (b + 1))
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    Entropy.mutualInformation
        (bipartitionedNormalizedMPO M N (a + 1) (b + 2) hIn)
        (bipartitionedNormalizedMPO_posSemidef M N (a + 1) (b + 2) hIn hM).isHermitian =
      Entropy.mutualInformation
        (bipartitionedNormalizedMPO M N (a + 2) (b + 1) hOut)
        (bipartitionedNormalizedMPO_posSemidef M N (a + 2) (b + 1) hOut hM).isHermitian := by
  obtain ⟨S, T, hS, hT, hSclose, hTclose⟩ := hRFP
  exact mutualInformation_bipartition_eq_of_local_transfers M N a b hIn hOut hM htr
    S T hS hT hSclose hTclose

private theorem mutualInformation_bipartition_eq_of_isRFPViaTS_of_right_eq
    (M : MPOTensor d D) (hRFP : IsRFPViaTS M)
    (N a b KIn KOut : ℕ) (hKIn : KIn = b + 2) (hKOut : KOut = b + 1)
    (hIn : N = (a + 1) + KIn) (hOut : N = (a + 2) + KOut)
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    Entropy.mutualInformation
        (bipartitionedNormalizedMPO M N (a + 1) KIn hIn)
        (bipartitionedNormalizedMPO_posSemidef M N (a + 1) KIn hIn hM).isHermitian =
      Entropy.mutualInformation
        (bipartitionedNormalizedMPO M N (a + 2) KOut hOut)
        (bipartitionedNormalizedMPO_posSemidef M N (a + 2) KOut hOut hM).isHermitian := by
  subst KIn
  subst KOut
  exact mutualInformation_bipartition_eq_of_isRFPViaTS
    M hRFP N a b hIn hOut hM htr

/-- A matrix product density operator satisfying the local renormalization
fixed-point equations saturates the area law, provided every positive-length
ring has nonzero trace.

The nonvanishing condition is exactly the normalization condition implicit in
the source's density-operator language: it ensures that each positive-length
MPO can be divided by its trace.  With this normalization available, the two
local channels transfer one site across a consecutive bipartition.  Data
processing in both directions gives equality of the bipartite mutual
informations, and `mutualInfoChain_eq_mutualInformation` identifies these with
the chain quantities I_L and I_{L+1}.  No empty-chain condition is used.

Source: arXiv:1606.00608, Proposition `propsimple`, Appendix C,
lines 1333--1341. -/
theorem isSAL_of_isRFPViaTS_of_trace_ne_zero (M : MPOTensor d D)
    (hM : IsMPDO M)
    (hTrace : ∀ N, 0 < N → Matrix.trace (mpo M N) ≠ 0)
    (hRFP : IsRFPViaTS M) : IsSAL M := by
  refine ⟨hM, hTrace, ?_⟩
  intro N L hL hHalf
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  let b := N - (a + 1) - 2
  let N₀ := (a + 1) + (b + 2)
  have hN : N = N₀ := by
    dsimp [N₀, b]
    omega
  clear_value b
  subst N
  have hNpos : 0 < N₀ := by omega
  have htr := hTrace N₀ hNpos
  have hKIn : N₀ - (a + 1) = b + 2 := by
    dsimp [N₀]
    omega
  have hKOut : N₀ - (a + 2) = b + 1 := by
    dsimp [N₀]
    omega
  have hIn : N₀ = (a + 1) + (N₀ - (a + 1)) := by omega
  have hOut : N₀ = (a + 2) + (N₀ - (a + 2)) := by omega
  have hBipartition :=
    mutualInformation_bipartition_eq_of_isRFPViaTS_of_right_eq
      M hRFP N₀ a b (N₀ - (a + 1)) (N₀ - (a + 2))
      hKIn hKOut hIn hOut (hM N₀ hNpos) htr
  calc
    mutualInfoChain M N₀ (a + 1)
        (Nat.le_of_lt (hHalf.trans_le (Nat.div_le_self N₀ 2))) (hM N₀ hNpos) =
      Entropy.mutualInformation
        (bipartitionedNormalizedMPO M N₀ (a + 1) (N₀ - (a + 1)) (by omega))
        ((normalizedMPO_isHermitian M N₀ (hM N₀ hNpos)).submatrix
          (chainBipartitionEquiv d N₀ (a + 1) (N₀ - (a + 1)) (by omega)).symm) :=
      mutualInfoChain_eq_mutualInformation M N₀ (a + 1)
        (Nat.le_of_lt (hHalf.trans_le (Nat.div_le_self N₀ 2))) (hM N₀ hNpos)
    _ = Entropy.mutualInformation
        (bipartitionedNormalizedMPO M N₀ (a + 2) (N₀ - (a + 2)) (by omega))
        ((normalizedMPO_isHermitian M N₀ (hM N₀ hNpos)).submatrix
          (chainBipartitionEquiv d N₀ (a + 2) (N₀ - (a + 2)) (by omega)).symm) := by
      exact hBipartition
    _ = mutualInfoChain M N₀ (a + 2)
        (hHalf.trans_le (Nat.div_le_self N₀ 2)) (hM N₀ hNpos) :=
      (mutualInfoChain_eq_mutualInformation M N₀ (a + 2)
        (hHalf.trans_le (Nat.div_le_self N₀ 2)) (hM N₀ hNpos)).symm

/-- A matrix product density operator in normalized BNT-refined horizontal
form satisfying the local renormalization fixed-point equations saturates the
area law.

Normalized BNT-refined horizontal form supplies the nonzero positive-length
traces that are implicit in the source's density-operator language.  The SAL
argument itself is `isSAL_of_isRFPViaTS_of_trace_ne_zero`.

**Scope restriction (BNT-refined horizontal form):** The horizontal hypothesis
`IsHorizontalCF` is stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, Proposition `propsimple`, Appendix C,
lines 1333--1341, under the canonical-form and density-operator standing
assumptions at lines 623--628 and 849--850. -/
theorem isSAL_of_isRFPViaTS (M : MPOTensor d D)
    (hHorizontal : MPOTensor.IsHorizontalCF M) (hM : IsMPDO M)
    (hRFP : IsRFPViaTS M) : IsSAL M := by
  exact isSAL_of_isRFPViaTS_of_trace_ne_zero M hM
    (trace_mpo_ne_zero_of_isHorizontalCF_isMPDO_isRFPViaTS
      M hHorizontal hM hRFP) hRFP

/-- A matrix product density operator satisfying the local renormalization
fixed-point equations has source zero correlation length and saturates the area
law, provided every positive-length ring has nonzero trace.

Nonzero positive-length traces are the normalization condition implicit in the
source's density-operator language.  The one-site instance, together with the
vertical-loop trace identities, makes the physical trace-transfer matrix
nonzero and hence yields source ZCL.  The full family normalizes the rings used
in the area-law argument.

Source: arXiv:1606.00608, Proposition `propsimple`, Appendix C,
lines 1333--1341. -/
theorem isSourceZCL_and_isSAL_of_isRFPViaTS_of_trace_ne_zero
    (M : MPOTensor d D) (hM : IsMPDO M)
    (hTrace : ∀ N, 0 < N → Matrix.trace (mpo M N) ≠ 0)
    (hRFP : IsRFPViaTS M) : IsSourceZCL M ∧ IsSAL M := by
  have hTransfer : physTraceTransfer M ≠ 0 := by
    intro hZero
    apply hTrace 1 Nat.zero_lt_one
    rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer, hZero]
    simp
  exact ⟨isSourceZCL_of_isRFPViaTS M hRFP hTransfer,
    isSAL_of_isRFPViaTS_of_trace_ne_zero M hM hTrace hRFP⟩

/-- A matrix product density operator in normalized BNT-refined horizontal
form satisfying the local renormalization fixed-point equations has source zero
correlation length and saturates the area law.

Normalized BNT-refined horizontal form supplies the nonzero positive-length
traces that are implicit in the source's density-operator language.  Source ZCL
and SAL then follow from
`isSourceZCL_and_isSAL_of_isRFPViaTS_of_trace_ne_zero`.

**Scope restriction (BNT-refined horizontal form):** The horizontal hypothesis
`IsHorizontalCF` is stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, Proposition `propsimple`, Appendix C,
lines 1333--1341, under the canonical-form and density-operator standing
assumptions at lines 623--628 and 849--850. -/
theorem isSourceZCL_and_isSAL_of_isRFPViaTS (M : MPOTensor d D)
    (hHorizontal : MPOTensor.IsHorizontalCF M) (hM : IsMPDO M)
    (hRFP : IsRFPViaTS M) : IsSourceZCL M ∧ IsSAL M := by
  exact isSourceZCL_and_isSAL_of_isRFPViaTS_of_trace_ne_zero M hM
    (trace_mpo_ne_zero_of_isHorizontalCF_isMPDO_isRFPViaTS
      M hHorizontal hM hRFP) hRFP

end MPOTensor
