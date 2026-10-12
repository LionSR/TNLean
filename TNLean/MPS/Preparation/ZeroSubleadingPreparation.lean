/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockIsometryState
import TNLean.MPS.Preparation.DepthUpperBound
import TNLean.MPS.Preparation.ExactFixedPointPolar
import TNLean.MPS.Preparation.ZeroSubleadingSpectrum
import TNLean.MPS.Preparation.RemainderBlocks

/-!
# Exact preparation when the subleading spectrum vanishes

When all nonleading transfer eigenvalues vanish, the nilpotent part of the
transfer map disappears after finitely many sites. Sufficiently long blocks
then have their limiting positive polar factor exactly. The preparation from
fixed-point pairs and block isometries reproduces the periodic MPS exactly.

This finite-block argument treats the endpoint separately from the expressions
containing the inverse correlation length in arXiv:2307.01696, Lemma 1.
A nilpotent Jordan part can survive at shorter lengths.

**Local fix (zero-spectrum endpoint):** The logarithmic block prescription is
replaced by a positive finite length when all subleading eigenvalues vanish.
See `docs/paper-gaps/mswc24_zero_subleading_spectrum_endpoint.tex`.
-/

open scoped BigOperators ComplexOrder

namespace MPSTensor

variable {d D M N : ℕ}

/-- If every positive polar factor is the fixed-point tensor, the state obtained
from fixed-point pairs and the block polar isometries equals the periodic MPS.
The blocks may have unequal lengths.

Source: arXiv:2307.01696, `eq:phi_tilde` and the Supplemental Material,
`eq:app_tidle_phi_1`. This is the exact-factor case of that construction. -/
theorem blockIsometryState_eq_mpvState_of_polarPosTensor_eq_fixedPointTensor
    [NeZero M] (A : MPSTensor d D) (σ : Matrix (Fin D) (Fin D) ℂ)
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (hP : ∀ k, polarPosTensor (blockTensor A (ℓ k)) = fixedPointTensor σ) :
    blockIsometryState A (fixedPointPair σ) hN = mpvState A N := by
  have hB : (fun k => blockTensor A (ℓ k)) =
      fun k => rotatePhysical (polarIsoMatrix (blockTensor A (ℓ k)))
        (fixedPointTensor σ) := by
    funext k
    rw [← hP k]
    exact (rotatePhysical_polarIsoMatrix_polarPosTensor _).symm
  ext s
  rw [blockIsometryState_apply, mpvState_apply, mpv_eq_mpvFamily_blockTensor A hN,
    hB, mpvFamily_rotatePhysical]
  simp only [mpvFamily_const, mpv_fixedPointTensor]

private theorem transferMap_blockTensor_eq_trace_smul_of_subleading_eigenvalues_eq_zero
    (A : MPSTensor d D) (hnormal : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ)
    (hzero : ∀ μ : ℂ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → μ = 0)
    {n : ℕ} (hn : D ^ 2 ≤ n) (X : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.transferMap (blockTensor A n) X = X.trace • σ := by
  rw [transferMap_blockTensor,
    transferMap_pow_eq_fixedPointProj_of_subleading_eigenvalues_eq_zero
      A hnormal hA hσ htr hfix hzero hn]
  simp [fixedPointProj, htr]

/-- For a normal left-canonical tensor with vanishing subleading transfer
spectrum, the preparation from fixed-point pairs is exact whenever every
block has at least \(D^2\) sites. Blocks may have unequal lengths.

This is the exact finite-block endpoint of arXiv:2307.01696, equation (10),
using the transfer decomposition `eq:Ek_decomp` and `eq:B_TM`.
The zero-spectrum hypothesis allows a nilpotent Jordan transient. -/
theorem blockIsometryState_eq_mpvState_of_subleading_eigenvalues_eq_zero
    [NeZero M] (A : MPSTensor d D) (hnormal : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ)
    (hzero : ∀ μ : ℂ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → μ = 0)
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) (hℓ : ∀ k, D ^ 2 ≤ ℓ k) :
    blockIsometryState A (fixedPointPair σ) hN = mpvState A N := by
  apply blockIsometryState_eq_mpvState_of_polarPosTensor_eq_fixedPointTensor
  intro k
  apply polarPosTensor_eq_fixedPointTensor_of_transferMap_eq_trace_smul _ hσ.posSemidef
  exact transferMap_blockTensor_eq_trace_smul_of_subleading_eigenvalues_eq_zero
    A hnormal hA hσ htr hfix hzero (hℓ k)

end MPSTensor

namespace MPSPreparation

open MPSTensor QuantumCircuit

/-- At fixed physical and virtual dimensions, normal left-canonical tensors
whose subleading transfer eigenvalues vanish admit exact preparation in a
depth independent of chain length. This holds at every length
\(N\ge D^2+3D+1\); the unnormalized periodic state already has unit norm.

The construction uses blocks of length \(q=D^2+3D+1\), with the last block
enlarged by the remainder. It is the exact finite-block endpoint of
arXiv:2307.01696, `eq:phi_tilde` and the Supplemental Material,
`eq:app_tidle_phi_1`. It does not substitute zero into a reciprocal correlation length. -/
theorem exists_isPreparedInDepth_normalizedMPVState_of_subleading_eigenvalues_eq_zero
    (d D : ℕ) :
    ∃ T : ℕ, ∀ (A : MPSTensor d D), Kraus.IsNormal A → IsLeftCanonical A →
      ∀ {σ : Matrix (Fin D) (Fin D) ℂ}, σ.PosDef → σ.trace = 1 →
        Kraus.transferMap A σ = σ →
        (∀ μ : ℂ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → μ = 0) →
        ∀ (N : ℕ) (hN0 : D ^ 2 + 3 * D + 1 ≤ N),
          letI : NeZero N := NeZero.of_pos (by omega)
          ‖mpvState A N‖ = 1 ∧
            IsPreparedInDepth T (fun s => normalizedMPVState A N s) := by
  obtain ⟨Cb, hCb⟩ := exists_isPreparedInDepth_blockIsometryState d D
  refine ⟨Cb * (2 * (D ^ 2 + 3 * D + 1)), ?_⟩
  intro A hnormal hA σ hσ htr hfix hzero N hN0
  let q := D ^ 2 + 3 * D + 1
  have hqpos : 0 < q := by dsimp [q]; omega
  have hqN : q ≤ N := hN0
  have : NeZero N := NeZero.of_pos (hqpos.trans_le hqN)
  obtain ⟨m, ℓ, hm, hsum, hℓq, hℓupper⟩ := exists_remainderBlocks hqpos hqN
  have hℓD : ∀ k, D ^ 2 ≤ ℓ k := fun k => by
    have h := hℓq k
    dsimp [q] at h
    omega
  have hℓ3D : ∀ k, 3 * D ≤ ℓ k := fun k => by
    have h := hℓq k
    dsimp [q] at h
    omega
  have hinj : ∀ k, Kraus.IsInjective (blockTensor A (ℓ k)) := by
    intro k
    apply isInjective_of_transferMap_eq_trace_smul _ hσ
    exact transferMap_blockTensor_eq_trace_smul_of_subleading_eigenvalues_eq_zero
      A hnormal hA hσ htr hfix hzero (hℓD k)
  have hω : ∑ p, star (fixedPointPair σ p) * fixedPointPair σ p = 1 := by
    rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
  have heq := blockIsometryState_eq_mpvState_of_subleading_eigenvalues_eq_zero
    A hnormal hA hσ htr hfix hzero hsum hℓD
  have hnorm : ‖mpvState A N‖ = 1 := by
    rw [← heq]
    exact norm_blockIsometryState A hω hsum hinj
  refine ⟨hnorm, ?_⟩
  have hprep := hCb A (fixedPointPair σ) hω ℓ hsum (2 * q) hℓ3D hℓupper hinj
  simpa only [heq, normalizedMPVState, hnorm, Complex.ofReal_one, inv_one, one_smul] using
    hprep

end MPSPreparation
