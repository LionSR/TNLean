/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Entropy.MutualInformationDataProcessing
import TNLean.MPS.MPDO.LocalPurificationRFP
import TNLean.MPS.MPDO.MutualInfoBridge
import TNLean.MPS.MPDO.PureAreaLaw

/-!
# Mutual-information bound from a local purification

The area-law argument of Wolf--Verstraete--Hastings--Cirac starts from a pure
tensor-network state and applies independent trace-preserving completely
positive maps on the two sides of a spatial cut. This file isolates the
finite-chain mutual-information estimate supplied by that argument.

The theorem does not assert that an arbitrary positive matrix product operator
has such a local purification. This additional existence assertion is absent
from the cited argument and is false without further hypotheses.

## Main definitions

* `MPOTensor.blockSpinAncillaEquiv`: regroups the spin and ancillary
  configurations of a block.
* `MPOTensor.blockAncillaryTraceMap`: traces the ancillary configuration of a
  block.

## Main results

* `MPOTensor.blockAncillaryTraceMap_isKrausCPTP`: the block ancillary trace is
  trace-preserving and completely positive.
* `MPOTensor.blockAncillaryTraceMap_apply` and
  `MPOTensor.tensorMapBoth_blockAncillaryTraceMap_apply`: coefficient formulas
  for one block and for the two sides of a cut.
* `MPOTensor.bipartitionedNormalizedMPO_eq_tensorMapBoth_blockAncillaryTraceMap`:
  an explicit local purification gives the normalized block-channel image
  across every cut.
* `MPOTensor.IsLPDO.exists_bipartitionedNormalizedMPO_eq_blockAncillaryTrace`:
  an LPDO admits purifying data realizing this block-channel identity.
* `MPOTensor.IsLPDO.exists_forall_bipartitionedNormalizedMPO_eq_blockAncillaryTrace`:
  one choice of purifying data realizes the identity across every cut.
* `MPOTensor.mutualInfoChain_le_of_bipartitioned_channel_image`: a matrix product
  density operator obtained by local channels from a pure matrix product state
  satisfies the bound determined by the purifying bond dimension.
* `MPOTensor.mutualInfoChain_le_of_lpdoWitness` and
  `MPOTensor.IsLPDO.exists_mutualInfoChain_le_purifyingBond`: the corresponding
  finite-chain bound for an explicit local-purification representation and for
  LPDOs.

## References

* [Wolf--Verstraete--Hastings--Cirac 2008] arXiv:0704.3906, the mixed-PEPS
  purification paragraph and equation (4).
* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition `PropILILp1` and Appendix C, line 1319.
-/

open scoped Matrix ComplexOrder Kronecker
open Matrix

namespace MPOTensor

variable {d dP D D' : ℕ}

/-- Mutual information is congruent under equality of the density matrix. -/
private theorem mutualInformation_congr
    {dA dB : ℕ}
    {rho sigma : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (h : rho = sigma) (hrho : rho.IsHermitian) (hsigma : sigma.IsHermitian) :
    Entropy.mutualInformation rho hrho = Entropy.mutualInformation sigma hsigma := by
  subst sigma
  rfl

/-- Regroup a block of spin--ancilla indices into its spin configuration and
its ancillary configuration. -/
noncomputable def blockSpinAncillaEquiv (d dK L : ℕ) :
    Fin ((d * dK) ^ L) ≃ Fin (d ^ L) × Fin (dK ^ L) :=
  finFunctionFinEquiv.symm |>.trans
    (Equiv.piCongrRight fun _ : Fin L ↦ finProdFinEquiv.symm) |>.trans
      (Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin d) (fun _ ↦ Fin dK)) |>.trans
        (finFunctionFinEquiv.prodCongr finFunctionFinEquiv)

/-- Decoding a regrouped block joins the spin and ancillary labels at each
site. -/
theorem blockSpinAncillaEquiv_symm_apply (d dK L : ℕ)
    (i : Fin (d ^ L)) (k : Fin (dK ^ L)) (n : Fin L) :
    finFunctionFinEquiv.symm ((blockSpinAncillaEquiv d dK L).symm (i, k)) n =
      finProdFinEquiv (finFunctionFinEquiv.symm i n, finFunctionFinEquiv.symm k n) := by
  simp [blockSpinAncillaEquiv]

/-- Decoding a regrouped block as a function joins its spin and ancillary
configurations pointwise. -/
theorem blockSpinAncillaEquiv_symm_decode (d dK L : ℕ)
    (i : Fin (d ^ L)) (k : Fin (dK ^ L)) :
    finFunctionFinEquiv.symm ((blockSpinAncillaEquiv d dK L).symm (i, k)) =
      fun n ↦ finProdFinEquiv
        (finFunctionFinEquiv.symm i n, finFunctionFinEquiv.symm k n) :=
  funext fun n ↦ blockSpinAncillaEquiv_symm_apply d dK L i k n

/-- Trace the ancillary indices of every site in a block, after regrouping the
spin and ancillary configurations. This is the blockwise analogue of
`ancillaryTraceMap` and is the trace used in the mixed-PEPS purification
argument preceding equation (4) of arXiv:0704.3906. -/
noncomputable def blockAncillaryTraceMap (d dK L : ℕ) :
    Matrix (Fin ((d * dK) ^ L)) (Fin ((d * dK) ^ L)) ℂ →ₗ[ℂ]
      Matrix (Fin (d ^ L)) (Fin (d ^ L)) ℂ :=
  Matrix.partialTraceRightLM ∘ₗ
    Matrix.equivReindexMap (blockSpinAncillaEquiv d dK L)

/-- The ancillary trace on a block is trace-preserving and completely positive.
This is the blockwise channel used in the mixed-PEPS purification argument
leading to equation (4) of arXiv:0704.3906. -/
theorem blockAncillaryTraceMap_isKrausCPTP (d dK L : ℕ) :
    IsKrausCPTP (blockAncillaryTraceMap d dK L) := by
  exact isKrausCPTP_comp
    (Matrix.equivReindexMap_isKrausCPTP (blockSpinAncillaEquiv d dK L))
    Matrix.partialTraceRightLM_isKrausCPTP

/-- Matrix coefficients of the block ancillary trace are obtained by summing
over one ancillary configuration on the bra and ket diagonals. -/
theorem blockAncillaryTraceMap_apply (d dK L : ℕ)
    (X : Matrix (Fin ((d * dK) ^ L)) (Fin ((d * dK) ^ L)) ℂ)
    (i j : Fin (d ^ L)) :
    blockAncillaryTraceMap d dK L X i j =
      ∑ k : Fin (dK ^ L),
        X ((blockSpinAncillaEquiv d dK L).symm (i, k))
          ((blockSpinAncillaEquiv d dK L).symm (j, k)) := by
  rfl

/-- Applying the ancillary traces on both sides of a cut sums independently
over the two ancillary block configurations. -/
theorem tensorMapBoth_blockAncillaryTraceMap_apply (d dK L K : ℕ)
    (X : Matrix (Fin ((d * dK) ^ L) × Fin ((d * dK) ^ K))
      (Fin ((d * dK) ^ L) × Fin ((d * dK) ^ K)) ℂ)
    (i j : Fin (d ^ L)) (x y : Fin (d ^ K)) :
    Matrix.tensorMapBoth (blockAncillaryTraceMap d dK L)
        (blockAncillaryTraceMap d dK K) X (i, x) (j, y) =
      ∑ k : Fin (dK ^ L), ∑ l : Fin (dK ^ K),
        X ((blockSpinAncillaEquiv d dK L).symm (i, k),
            (blockSpinAncillaEquiv d dK K).symm (x, l))
          ((blockSpinAncillaEquiv d dK L).symm (j, k),
            (blockSpinAncillaEquiv d dK K).symm (y, l)) := by
  simp only [Matrix.tensorMapBoth, Matrix.idTensorMap_apply,
    Matrix.bipartiteBlock_apply, Matrix.tensorMapId_apply,
    Matrix.bipartiteSlice_apply, blockAncillaryTraceMap_apply]
  rw [Finset.sum_comm]

/-- Tracing the ancillary configuration of the pure state generated by a
purification tensor gives the finite-chain purification density.

This is the block form of the global purification equation in
arXiv:1606.00608, equation `eq:MPDO-Puri-1` (line 751). -/
theorem blockAncillaryTraceMap_pureState_purificationTensor
    {dK D' N : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) :
    blockAncillaryTraceMap d dK N
        ((MPSTensor.pureState (purificationTensor A) N).submatrix
          finFunctionFinEquiv.symm finFunctionFinEquiv.symm) =
      (purificationDensity A N).submatrix
        finFunctionFinEquiv.symm finFunctionFinEquiv.symm := by
  ext i j
  rw [blockAncillaryTraceMap_apply]
  simp only [Matrix.submatrix_apply, MPSTensor.pureState,
    Matrix.vecMulVec_apply, Pi.star_apply, purificationDensity, Matrix.of_apply]
  have hdecode : ∀ (u : Fin (d ^ N)) (k : Fin (dK ^ N)),
      finFunctionFinEquiv.symm ((blockSpinAncillaEquiv d dK N).symm (u, k)) =
        fun n ↦ finProdFinEquiv (finFunctionFinEquiv.symm u n,
          finFunctionFinEquiv.symm k n) :=
    blockSpinAncillaEquiv_symm_decode d dK N
  simp_rw [hdecode]
  exact ((finFunctionFinEquiv (m := dK) (n := N)).symm.sum_comp
    (fun κ : Fin N → Fin dK ↦
      MPSTensor.mpv (purificationTensor A)
          (fun n ↦ finProdFinEquiv (finFunctionFinEquiv.symm i n, κ n)) *
        star (MPSTensor.mpv (purificationTensor A)
          (fun n ↦ finProdFinEquiv (finFunctionFinEquiv.symm j n, κ n)))))

/-- The finite-chain purification density and its purifying pure state have the
same trace because the ancillary trace is trace-preserving.

This is the normalization identity implicit in the global purification
equation of arXiv:1606.00608, equation `eq:MPDO-Puri-1` (line 751). -/
theorem trace_purificationDensity_eq_pureState
    {dK D' N : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) :
    Matrix.trace (purificationDensity A N) =
      Matrix.trace (MPSTensor.pureState (purificationTensor A) N) := by
  calc
    Matrix.trace (purificationDensity A N) =
        Matrix.trace ((purificationDensity A N).submatrix
          finFunctionFinEquiv.symm finFunctionFinEquiv.symm) :=
      (Matrix.trace_submatrix_equiv finFunctionFinEquiv.symm _).symm
    _ = Matrix.trace (blockAncillaryTraceMap d dK N
          ((MPSTensor.pureState (purificationTensor A) N).submatrix
            finFunctionFinEquiv.symm finFunctionFinEquiv.symm)) :=
      congrArg Matrix.trace
        (blockAncillaryTraceMap_pureState_purificationTensor A).symm
    _ = Matrix.trace ((MPSTensor.pureState (purificationTensor A) N).submatrix
          finFunctionFinEquiv.symm finFunctionFinEquiv.symm) :=
      (blockAncillaryTraceMap_isKrausCPTP d dK N).trace_map _
    _ = Matrix.trace (MPSTensor.pureState (purificationTensor A) N) :=
      Matrix.trace_submatrix_equiv finFunctionFinEquiv.symm _

/-- A purifying MPS with nonzero finite-chain norm has positive bond
dimension. -/
theorem purifyingBondDimension_pos_of_trace_ne_zero
    {dP DP N : ℕ} (A : MPSTensor dP DP)
    (htr : Matrix.trace (MPSTensor.pureState A N) ≠ 0) :
    0 < DP := by
  by_contra hDP
  have hDP0 : DP = 0 := Nat.eq_zero_of_not_pos hDP
  subst DP
  apply htr
  simp [MPSTensor.pureState, MPSTensor.mpv, MPSTensor.coeff, Matrix.trace,
    Matrix.vecMulVec_apply]

/-- The normalized-form finite-chain operator of an explicit local purification
is the image of the corresponding purifying operator under the two block
ancillary traces across any contiguous cut. The identity also holds at common
trace zero, when both normalized-form operators vanish by the convention
`0⁻¹ = 0`.

This is the finite-chain channel identity in the mixed-PEPS purification
argument preceding equation (4) of arXiv:0704.3906, specialized to the local
purification tensor of arXiv:1606.00608, equation `eq:MPDO-Puri-1`
(line 751). It assumes the local-purification representation explicitly and
makes no claim that an arbitrary positive matrix product operator has such a
representation. -/
theorem bipartitionedNormalizedMPO_eq_tensorMapBoth_blockAncillaryTraceMap
    {dK D' : ℕ} (M : MPOTensor d D)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D')
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    (N L K : ℕ) (h : N = L + K) :
    bipartitionedNormalizedMPO M N L K h =
      Matrix.tensorMapBoth (blockAncillaryTraceMap d dK L)
        (blockAncillaryTraceMap d dK K)
        (bipartitionedNormalizedMPO
          (doubledTensor (purificationTensor A)) N L K h) := by
  subst N
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [bipartitionedNormalizedMPO, bipartitionedNormalizedMPO,
    normalizedMPO, normalizedMPO, mpo_eq_purificationDensity A e hM (L + K),
    mpo_doubledTensor, trace_purificationDensity_eq_pureState A]
  rw [tensorMapBoth_blockAncillaryTraceMap_apply]
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, purificationDensity,
    Matrix.of_apply, MPSTensor.pureState, Matrix.vecMulVec_apply, Pi.star_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  rw [← (chainBipartitionEquiv dK (L + K) L K rfl).sum_comp]
  have hjoin (u : Fin (d ^ L)) (v : Fin (d ^ K))
      (κ : Fin (L + K) → Fin dK) :
      (chainBipartitionEquiv (d * dK) (L + K) L K rfl).symm
          ((blockSpinAncillaEquiv d dK L).symm
              (u, ((chainBipartitionEquiv dK (L + K) L K rfl) κ).1),
            (blockSpinAncillaEquiv d dK K).symm
              (v, ((chainBipartitionEquiv dK (L + K) L K rfl) κ).2)) =
        fun n ↦ finProdFinEquiv
          ((chainBipartitionEquiv d (L + K) L K rfl).symm (u, v) n, κ n) := by
    funext n
    simp only [chainBipartitionEquiv, biSplitEquiv, Equiv.symm_trans_apply,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map,
      blockSplitEquiv_symm_apply, Equiv.refl_symm, finCongr_refl,
      Equiv.arrowCongr_refl, Equiv.trans_apply, Equiv.refl_apply]
    rw [blockSpinAncillaEquiv_symm_decode,
      blockSpinAncillaEquiv_symm_decode]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    refine Fin.addCases (fun nl ↦ ?_) (fun nr ↦ ?_) n
    · rw [Fin.append_left, Fin.append_left]
      congr 1
    · rw [Fin.append_right, Fin.append_right]
      congr 1
  refine Finset.sum_congr rfl (fun κ _ ↦ ?_)
  rw [hjoin i x κ, hjoin j y κ]

/-- An LPDO admits a local-purification representation for which the normalized
finite-chain operator across a prescribed cut is obtained from the purifying
operator by the ancillary trace on each block.

This is the existential form of the finite-chain channel identity in the
mixed-PEPS purification argument preceding equation (4) of arXiv:0704.3906,
using the local purification of arXiv:1606.00608, Section 4.3.

**Scope restriction:** the conclusion remains restricted to LPDOs and exposes
the purifying bond dimension. It is not the unrestricted finite-chain estimate
in the MPO bond dimension asserted for every positive MPDO in arXiv:1606.00608,
Proposition 4.5; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem IsLPDO.exists_bipartitionedNormalizedMPO_eq_blockAncillaryTrace
    {M : MPOTensor d D} (hLPDO : IsLPDO M)
    (N L K : ℕ) (h : N = L + K) :
    ∃ (dK D' : ℕ)
      (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ),
      bipartitionedNormalizedMPO M N L K h =
        Matrix.tensorMapBoth
          (blockAncillaryTraceMap d dK L)
          (blockAncillaryTraceMap d dK K)
          (bipartitionedNormalizedMPO
            (doubledTensor (purificationTensor A)) N L K h) := by
  obtain ⟨dK, D', A, e, hcoeff⟩ := hLPDO
  exact ⟨dK, D', A,
    bipartitionedNormalizedMPO_eq_tensorMapBoth_blockAncillaryTraceMap
      M A e hcoeff N L K h⟩

/-- An LPDO admits a single local-purification representation whose normalized
finite-chain operator is obtained by ancillary traces across every cut.

This is the cut-uniform form of the finite-chain channel identity in the
mixed-PEPS purification argument preceding equation (4) of arXiv:0704.3906,
using the local purification of arXiv:1606.00608, Section 4.3.

**Scope restriction:** the conclusion remains restricted to LPDOs and exposes
the purifying bond dimension. It is not the unrestricted finite-chain estimate
in the MPO bond dimension asserted for every positive MPDO in arXiv:1606.00608,
Proposition 4.5; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem IsLPDO.exists_forall_bipartitionedNormalizedMPO_eq_blockAncillaryTrace
    {M : MPOTensor d D} (hLPDO : IsLPDO M) :
    ∃ (dK D' : ℕ)
      (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ),
      ∀ (N L K : ℕ) (h : N = L + K),
        bipartitionedNormalizedMPO M N L K h =
          Matrix.tensorMapBoth
            (blockAncillaryTraceMap d dK L)
            (blockAncillaryTraceMap d dK K)
            (bipartitionedNormalizedMPO
              (doubledTensor (purificationTensor A)) N L K h) := by
  obtain ⟨dK, D', A, e, hcoeff⟩ := hLPDO
  exact ⟨dK, D', A, fun N L K h ↦
    bipartitionedNormalizedMPO_eq_tensorMapBoth_blockAncillaryTraceMap
      M A e hcoeff N L K h⟩

/-- **Mutual-information bound for a local-channel image of a pure matrix
product state.** Let the normalized density operator across the cut
`L | (N - L)` be obtained from the normalized pure state of an MPS tensor `A`
by independent trace-preserving completely positive maps on the two blocks.
Then its mutual information is at most `4 log D'`, where `D'` is the bond
dimension of `A`.

This is the finite-chain estimate proved by the mixed-PEPS purification
argument leading to equation (4) of arXiv:0704.3906, and cited at
arXiv:1606.00608, Appendix C, line 1319.

**Scope restriction:** the channel-image identity is an explicit hypothesis.
For a locally purified tensor it must be derived by tracing the ancillary
physical indices on the two blocks. An arbitrary positive MPO need not possess
such a purification; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem mutualInfoChain_le_of_bipartitioned_channel_image
    (M : MPOTensor d D) (A : MPSTensor dP D') (N L : ℕ) (hL : L ≤ N)
    (S : Matrix (Fin (dP ^ L)) (Fin (dP ^ L)) ℂ →ₗ[ℂ]
      Matrix (Fin (d ^ L)) (Fin (d ^ L)) ℂ)
    (T : Matrix (Fin (dP ^ (N - L))) (Fin (dP ^ (N - L))) ℂ →ₗ[ℂ]
      Matrix (Fin (d ^ (N - L))) (Fin (d ^ (N - L))) ℂ)
    (hS : IsKrausCPTP S) (hT : IsKrausCPTP T)
    (himage : bipartitionedNormalizedMPO M N L (N - L) (by omega) =
      Matrix.tensorMapBoth S T
        (bipartitionedNormalizedMPO (doubledTensor A) N L (N - L) (by omega)))
    (hM : (mpo M N).PosSemidef) (hD' : 0 < D')
    (htrA : Matrix.trace (MPSTensor.pureState A N) ≠ 0) :
    mutualInfoChain M N L hL hM ≤ 4 * Real.log D' := by
  rw [mutualInfoChain_eq_mutualInformation M N L hL hM]
  calc
    Entropy.mutualInformation
          (bipartitionedNormalizedMPO M N L (N - L) (by omega)) _
        = Entropy.mutualInformation
            (Matrix.tensorMapBoth S T
              (bipartitionedNormalizedMPO
                (doubledTensor A) N L (N - L) (by omega))) _ := by
          apply mutualInformation_congr himage
    Entropy.mutualInformation
          (Matrix.tensorMapBoth S T
            (bipartitionedNormalizedMPO (doubledTensor A) N L (N - L) (by omega))) _
        ≤ Entropy.mutualInformation
            (bipartitionedNormalizedMPO (doubledTensor A) N L (N - L) (by omega)) _ := by
          apply hS.mutualInformation_tensorMapBoth_le hT
          · exact bipartitionedNormalizedMPO_posSemidef
              (doubledTensor A) N L (N - L) (by omega) (doubledTensor_posSemidef A N)
          · apply bipartitionedNormalizedMPO_trace
            simpa [mpo_doubledTensor] using htrA
    _ = (doubledTensor A).mutualInfoChain N L hL (doubledTensor_posSemidef A N) := by
          symm
          exact mutualInfoChain_eq_mutualInformation
            (doubledTensor A) N L hL (doubledTensor_posSemidef A N)
    _ ≤ 4 * Real.log D' := mutualInfoChain_doubledTensor_le A N L hL hD' htrA

/-- **Mutual-information bound from explicit local-purification data.** If an
MPO tensor is the ancillary contraction of a purifying MPS tensor, then its
finite-chain mutual information is at most `4 log D'`, where `D'` is the bond
dimension of the purifying MPS.

This is the locally purifiable specialization of the mixed-PEPS argument
leading to equation (4) of arXiv:0704.3906. The local tensor identity is the
purification equation `eq:MPDO-Puri-1` of arXiv:1606.00608 (line 751).

**Scope restriction:** this theorem assumes an explicit local-purification
representation; it does not assert that an arbitrary positive matrix product
operator has a local purification. The bound is in the purifying bond dimension
`D'`, not the MPO bond dimension `D`; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem mutualInfoChain_le_of_lpdoWitness
    {dK D' : ℕ} (M : MPOTensor d D)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D')
    (hcoeff : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    (N L : ℕ) (hL : L ≤ N) (hpos : (mpo M N).PosSemidef)
    (htrA : Matrix.trace
      (MPSTensor.pureState (purificationTensor A) N) ≠ 0) :
    mutualInfoChain M N L hL hpos ≤ 4 * Real.log D' := by
  apply mutualInfoChain_le_of_bipartitioned_channel_image M
    (purificationTensor A) N L hL
    (blockAncillaryTraceMap d dK L)
    (blockAncillaryTraceMap d dK (N - L))
  · exact blockAncillaryTraceMap_isKrausCPTP d dK L
  · exact blockAncillaryTraceMap_isKrausCPTP d dK (N - L)
  · exact bipartitionedNormalizedMPO_eq_tensorMapBoth_blockAncillaryTraceMap
      M A e hcoeff N L (N - L) (by omega)
  · exact purifyingBondDimension_pos_of_trace_ne_zero (purificationTensor A) htrA
  · exact htrA

/-- An LPDO with nonzero finite-chain trace admits purifying data whose bond
dimension controls the finite-chain mutual information.

The witness is precisely the local purification of arXiv:1606.00608,
Section 4.3, and the estimate is the mixed-PEPS channel bound leading to
equation (4) of arXiv:0704.3906.

**Scope restriction:** the conclusion is existential in the purifying bond
dimension and remains restricted to LPDOs. It is not the unrestricted bound in
the MPO bond dimension asserted for arbitrary MPDOs in Proposition 4.5 of
arXiv:1606.00608; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem IsLPDO.exists_mutualInfoChain_le_purifyingBond
    {M : MPOTensor d D} (hLPDO : IsLPDO M)
    (N L : ℕ) (hN : 0 < N) (hL : L ≤ N)
    (htrM : Matrix.trace (mpo M N) ≠ 0) :
    ∃ (dK D' : ℕ)
      (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
      (e : Fin D ≃ Fin D' × Fin D'),
      (∀ i j : Fin d, M i j = (∑ k : Fin dK,
        (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e) ∧
      mutualInfoChain M N L hL (hLPDO.isMPDO N hN) ≤ 4 * Real.log D' := by
  have hpos := hLPDO.isMPDO N hN
  obtain ⟨dK, D', A, e, hcoeff⟩ := hLPDO
  refine ⟨dK, D', A, e, hcoeff, ?_⟩
  have htrA : Matrix.trace
      (MPSTensor.pureState (purificationTensor A) N) ≠ 0 := by
    rw [← trace_purificationDensity_eq_pureState A,
      ← mpo_eq_purificationDensity A e hcoeff N]
    exact htrM
  exact mutualInfoChain_le_of_lpdoWitness M A e hcoeff N L hL hpos htrA

end MPOTensor
