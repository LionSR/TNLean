/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Entropy.MutualInformationDataProcessing
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

## Main result

* `MPOTensor.mutualInfoChain_le_of_bipartitioned_channel_image`: a matrix product
  density operator obtained by local channels from a pure matrix product state
  satisfies the bound determined by the purifying bond dimension.

## References

* [Wolf--Verstraete--Hastings--Cirac 2008] arXiv:0704.3906, the mixed-PEPS
  purification paragraph and equation (4).
* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition `PropILILp1` and Appendix C, line 1319.
-/

open scoped Matrix ComplexOrder
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

/-- Trace the ancillary indices of every site in a block, after regrouping the
spin and ancillary configurations. -/
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
  simp only [Matrix.tensorMapBoth, Matrix.idTensorMap, Matrix.submatrix_apply,
    Prod.swap_prod_mk, Matrix.tensorMapId_apply, Matrix.bipartiteSlice_apply,
    blockAncillaryTraceMap_apply]
  rw [Finset.sum_comm]

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

end MPOTensor
