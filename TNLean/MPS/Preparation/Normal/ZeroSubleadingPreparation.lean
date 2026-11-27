/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.Projection.SpectralProjection
import TNLean.MPS.CanonicalForm.FixedPointApproximation.PositivePartRate
import TNLean.MPS.Transfer.RenormalizationFixedPoint.BlockIsometryState
import TNLean.MPS.Preparation.Normal.DepthUpperBound
import TNLean.MPS.Preparation.Polar.ExactFixedPointPolar
import TNLean.MPS.Preparation.Circuit.RemainderBlocks

/-!
# Exact transfer stabilization when the subleading spectrum vanishes

For a normal left-canonical tensor with a normalized positive definite fixed
point, vanishing subleading transfer eigenvalues imply exact stabilization
after a finite blocking length. Nilpotent Jordan blocks are allowed, so the
transfer map need not equal its fixed-point projection at one site.

This is the finite-block endpoint of the transfer decomposition used in
arXiv:2307.01696, equations `eq:Ek_decomp` and `eq:B_TM`, and the normalized
normal-tensor setting at lines 413--421. It does not interpret the logarithmic
block prescription at lines 843--852 by substituting zero correlation length.

**Local fix (zero-spectrum endpoint):** The logarithmic block prescription is
replaced by a positive finite length when all subleading eigenvalues vanish.
See `docs/paper-gaps/mswc24_zero_subleading_spectrum_endpoint.tex`.

## Exact preparation when the subleading spectrum vanishes

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

open MPTensor

section

open scoped Matrix ComplexOrder MatrixOrder

private theorem pow_finrank_eq_zero_of_eigenvalues_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V)
    (h : ∀ z : ℂ, f.HasEigenvalue z → z = 0) :
    f ^ Module.finrank ℂ V = 0 := by
  have htop : f.maxGenEigenspace 0 = ⊤ := by
    apply top_unique
    rw [← f.iSup_maxGenEigenspace_hasEigenvalue_eq_top]
    refine iSup_le fun z => iSup_le fun hz => ?_
    rw [h z hz]
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.genEigenspace_zero_nat] at htop
  exact LinearMap.ker_eq_top.mp htop

namespace MPSTensor

variable {d D : ℕ}

/-- A normal left-canonical tensor with vanishing subleading transfer spectrum
has transfer powers equal to the fixed-point projection for every length at
least the square of its virtual dimension. Nilpotent transients are included.

This gives the exact finite-block endpoint of arXiv:2307.01696,
`eq:Ek_decomp` and `eq:B_TM`, in the normalized normal-tensor setting at
lines 413--421. The additional zero-subleading-spectrum hypothesis selects
that endpoint; zero correlation length alone is not the hypothesis. -/
theorem transferMap_pow_eq_fixedPointProj_of_subleading_eigenvalues_eq_zero
    (A : MPSTensor d D) (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ)
    (hzero : ∀ μ : ℂ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → μ = 0)
    {n : ℕ} (hn : D ^ 2 ≤ n) :
    Kraus.transferMap A ^ n = fixedPointProj σ (by simp [htr]) := by
  classical
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  have htr' : σ.trace ≠ 0 := by simp [htr]
  let N := Kraus.transferMap A - fixedPointProj σ htr'
  have hspec : ∀ z : ℂ, Module.End.HasEigenvalue N z → z = 0 := by
    intro z hz
    have hbound := norm_le_of_hasEigenvalue_transferMap_sub_fixedPointProj A hNT hA hσ htr'
      hfix (lam₂ := 0) (fun μ hμ hμ1 => by rw [hzero μ hμ hμ1]) hz
    exact norm_le_zero_iff.mp (by simpa using hbound.2)
  have hnil : N ^ (D ^ 2) = 0 := by
    simpa [Module.finrank_matrix, pow_two] using
      pow_finrank_eq_zero_of_eigenvalues_eq_zero N hspec
  have hnpos : 1 ≤ n := (Nat.succ_le_of_lt (pow_pos (NeZero.pos D) 2)).trans hn
  rw [pow_eq_fixedPointProj_add_compl_pow (Kraus.transferMap A) htr'
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hA) hfix hnpos]
  change fixedPointProj σ htr' + N ^ n = fixedPointProj σ htr'
  rw [pow_eq_zero_of_le hn hnil, add_zero]

end MPSTensor

end

section

open scoped BigOperators ComplexOrder
open Kraus (blockTensor)

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
  rw [Kraus.transferMap_blockTensor,
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
            IsPreparedInDepth (Geometry.ring N) T (fun s => normalizedMPVState A N s) := by
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

end
