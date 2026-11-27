/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap.KrausGauge
import TNLean.MPS.Tensor.DirectSum.BlockGauge
import TNLean.MPS.Tensor.DirectSum.SectorDecomposition
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Channel.Peripheral.Spectrum.SpectralRadius
import TNLean.MPS.CanonicalForm.NormalBlocks.TPGauge
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import QICLean.Channel.Irreducible.SpectralRadius
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.Transfer.Irreducible.Periodic
import QICLean.Channel.Irreducible.AdjointFamily
import QICLean.Channel.Irreducible.KrausGauge
import QICLean.Channel.Peripheral.Spectrum.AdjointSpectrum
import QICLean.Channel.Peripheral.Irreducible.GroupStructure
import TNLean.MPS.CanonicalForm.NormalBlocks.ProjectorClosureSpectral
import TNLean.MPS.Transfer.Scaling
import QICLean.Algebra.Combinatorics.ZModCyclicSums
import QICLean.Channel.Peripheral.Spectrum.Conjugation

/-!
# Sectorwise Perron normalization of periodic blocks

This file applies the pure Perron normalization to every representative of a
sector decomposition.  The replacement leaves the multiplicities and their
weights unchanged.  Repeating each representative gauge over all its copies
then gives a block-diagonal similarity of the assembled tensors.

## Main results

* `SectorDecomposition.gaugeEquiv_toTensor_replaceBasis`: representativewise
  pure gauges assemble to a gauge of the full multiplicity-bearing tensor.
* `SectorDecomposition.exists_isPeriodic_replaceBasis`: every spectrally
  periodic representative family has a left-canonical periodic replacement
  with the same multiplicity data.
* `MPSTensor.exists_isPeriodic_of_irreducible_of_isLeftCanonical`,
  `MPSTensor.exists_periodic_blockDecomposition`: positive-weight periodic blocks for an arbitrary
  tensor.
* `MPSTensor.IsSpectrallyPeriodic.exists_isPeriodic_tpGauge`: Perron normalization of spectral
  periodic blocks.
* `IsPrimitiveRoot.powRange_eq_setOf_pow_eq_one`,
  `MPSTensor.exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one`: the period of an
  irreducible-form block.
* `MPSTensor.exists_leftCanonical_periodic_scale_of_irreducible`: periodic normalization of an
  arbitrary nonzero irreducible tensor.

## Reference

De las Cuevas--Cirac--Schuch--Pérez-García, arXiv:1708.00029,
equation `eq:bdnr` and lines 286--332.
-/

open MPTensor

section Normalization

/-!
## Perron normalization of spectral periodic blocks

This file passes from an irreducible periodic block of spectral radius one to a
left-canonical periodic block by a pure Perron similarity.  No scalar rescales
the tensor, so the similarity preserves every matrix-product vector and leaves
the multiplicity matrices of a block-diagonal irreducible form unchanged.

### Main result

* `IsSpectrallyPeriodic.exists_isPeriodic_tpGauge`: a spectrally periodic block
  has a gauge-equivalent trace-preserving representative with the same period.

### Reference

De las Cuevas--Cirac--Schuch--Pérez-García, arXiv:1708.00029, lines 313--332.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.Operator Kraus

namespace MPSTensor

variable {d D m : ℕ}

/-- A spectrally periodic block has a gauge-equivalent left-canonical periodic
representative obtained without scalar rescaling.

The positive-definite adjoint Perron fixed point gives the trace-preserving
gauge.  The transfer map changes by similarity, so irreducibility and the
prescribed roots-of-unity peripheral spectrum are unchanged.

Source: arXiv:1708.00029, lines 313--332. -/
theorem IsSpectrallyPeriodic.exists_isPeriodic_tpGauge
    {A : MPSTensor d D} (hA : IsSpectrallyPeriodic m A) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosDef ∧
      Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i ↦ (A i)ᴴ) σ = σ ∧
      GaugeEquiv A (Kraus.tpGauge (d := d) (D := D) A σ) ∧
      IsPeriodic m (Kraus.tpGauge (d := d) (D := D) A σ) := by
  obtain ⟨σ, hσ, hσfix, hLeft, hGauge, hIrr⟩ :=
    exists_tpGauge_of_irreducible_spectralRadius_one
      hA.irreducible hA.spectral_radius_one
  have hSdet : (CFC.sqrt σ).det ≠ 0 :=
    (Matrix.PosDef.isUnit_det_cfc_sqrt hσ).ne_zero
  have hSinvDet : ((CFC.sqrt σ)⁻¹).det ≠ 0 := by
    simpa [Matrix.det_nonsing_inv] using inv_ne_zero hSdet
  have hPeripheral :
      peripheralEigenvalues
          (Kraus.transferMap (ι := Fin d) (n := Fin D) (Kraus.tpGauge (d := d) (D := D) A σ)) =
        peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) A) := by
    change peripheralEigenvalues (Kraus.mapLM (Kraus.tpGauge A σ)) =
      peripheralEigenvalues (Kraus.mapLM A)
    rw [Kraus.mapLM_tpGauge_eq_similarityMap A σ hσ]
    exact peripheralEigenvalues_similarityMap_eq
      (CFC.sqrt σ)⁻¹ hSinvDet (Kraus.transferMap (ι := Fin d) (n := Fin D) A)
  refine ⟨σ, hσ, hσfix, hGauge, ?_⟩
  exact ⟨hIrr, hLeft, hA.period_pos, hPeripheral.trans hA.peripheral_eq⟩

end MPSTensor

end Normalization

section SectorNormalization

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

namespace SectorDecomposition

/-- Replace the representative tensors of a sector decomposition without
changing their bond dimensions, multiplicities, or weights.

The source normalizes each representative in
$A^i = \bigoplus_j (R_j \otimes A_j^i)$ by a pure similarity, leaving every
diagonal entry of $R_j$ unchanged.

Source: arXiv:1708.00029, equation `eq:bdnr`, lines 286--305, and the
blockwise similarities at lines 313--332. -/
def replaceBasis (P : SectorDecomposition d)
    (B : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j)) :
    SectorDecomposition d where
  basisCount := P.basisCount
  basisDim := P.basisDim
  basis := B
  sectors := P.sectors

/-- The representative indexed by $j$ in the replaced family is $B_j$.

Source context: arXiv:1708.00029, equation `eq:bdnr`, lines 286--305,
with the representativewise similarities at lines 313--332. -/
@[simp]
theorem replaceBasis_basis (P : SectorDecomposition d)
    (B : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j))
    (j : Fin P.basisCount) :
    (P.replaceBasis B).basis j = B j :=
  rfl

/-- Replacing the representatives leaves every multiplicity coefficient
$\sum_q \mu_{j,q}^N$ unchanged.

Source: arXiv:1708.00029, equation `eq:bdnr`, lines 286--305, and the pure
blockwise similarities at lines 313--332. -/
@[simp]
theorem replaceBasis_coeff (P : SectorDecomposition d)
    (B : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j))
    (N : ℕ) (j : Fin P.basisCount) :
    (P.replaceBasis B).coeff N j = P.coeff N j :=
  rfl

/-- Pure gauges of all representatives assemble to a pure gauge of the full
multiplicity-bearing tensor, with every multiplicity weight unchanged.

The global gauge is the flattened block diagonal
$\bigoplus_j (I_{r_j} \otimes X_j)$.  Thus no scalar power is introduced into
the coefficients $\sum_q \mu_{j,q}^N$.

Source: arXiv:1708.00029, equation `eq:bdnr`, lines 286--305, and the
block-diagonal similarity at lines 313--332. -/
theorem gaugeEquiv_toTensor_replaceBasis (P : SectorDecomposition d)
    (B : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j))
    (hGauge : ∀ j, GaugeEquiv (P.basis j) (B j)) :
    GaugeEquiv P.toTensor (P.replaceBasis B).toTensor := by
  classical
  choose X hX using hGauge
  let Xflat := matched_block_gauge (Q := P) X
  have hXflat : ∀ (s : Fin P.totalCopies) (i : Fin d),
      (P.replaceBasis B).flatBasis s i =
        (Xflat s : Matrix (Fin (P.flatDim s)) (Fin (P.flatDim s)) ℂ) *
          P.flatBasis s i *
          (((Xflat s)⁻¹ : GL (Fin (P.flatDim s)) ℂ) :
            Matrix (Fin (P.flatDim s)) (Fin (P.flatDim s)) ℂ) := by
    intro s i
    change B (P.flatIndexEquiv.symm s).1 i =
      (X (P.flatIndexEquiv.symm s).1 : Matrix _ _ ℂ) *
        P.basis (P.flatIndexEquiv.symm s).1 i *
        (((X (P.flatIndexEquiv.symm s).1)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)
    exact hX (P.flatIndexEquiv.symm s).1 i
  refine ⟨globalGaugeOfBlocks Xflat, ?_⟩
  change ∀ i : Fin d,
    toTensorFromBlocks (α := Fin d) (P.flatWeight)
        (P.replaceBasis B).flatBasis i =
      (globalGaugeOfBlocks Xflat : Matrix _ _ ℂ) *
        toTensorFromBlocks (α := Fin d) (P.flatWeight) P.flatBasis i *
        (((globalGaugeOfBlocks Xflat)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)
  exact toTensorFromBlocks_eq_globalGaugeOfBlocks_conj
    (P.flatWeight) P.flatBasis (P.replaceBasis B).flatBasis Xflat hXflat

/-- A spectrally periodic representative family has a left-canonical periodic
replacement with the same multiplicities and weights, and the resulting full
tensor is gauge-equivalent to the original one.

Each representative is normalized by its positive-definite adjoint Perron
fixed point.  Since its spectral radius is already one, this is a pure
similarity rather than a scalar rescaling.  Consequently all diagonal entries
of the multiplicity matrices, and hence all their power-sum coefficients, are
unchanged.

Source: arXiv:1708.00029, lines 313--332, applied to the multiplicity-bearing
form `eq:bdnr` at lines 286--305. -/
theorem exists_isPeriodic_replaceBasis (P : SectorDecomposition d)
    (period : Fin P.basisCount → ℕ)
    (hP : ∀ j, IsSpectrallyPeriodic (period j) (P.basis j)) :
    ∃ B : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j),
      (∀ j, GaugeEquiv (P.basis j) (B j)) ∧
      (∀ j, IsPeriodic (period j) (B j)) ∧
      GaugeEquiv P.toTensor (P.replaceBasis B).toTensor := by
  classical
  choose sigma _hsigma _hfixed hGauge hPeriodic using
    fun j ↦ (hP j).exists_isPeriodic_tpGauge
  let B : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j) :=
    fun j ↦ Kraus.tpGauge (P.basis j) (sigma j)
  have hGaugeB : ∀ j, GaugeEquiv (P.basis j) (B j) := by
    intro j
    simpa [B] using hGauge j
  have hPeriodicB : ∀ j, IsPeriodic (period j) (B j) := by
    intro j
    simpa [B] using hPeriodic j
  exact ⟨B, hGaugeB, hPeriodicB,
    P.gaugeEquiv_toTensor_replaceBasis B hGaugeB⟩

end SectorDecomposition

end MPSTensor

end SectorNormalization

section PeriodExistence

/-!
## The period of an irreducible-form block

The source defines the irreducible form of a tensor by two conditions on each
block: the transfer map is an irreducible completely positive map, and its
spectral radius is one (arXiv:1708.00029, lines 248--261).  The period of such
a block is not a further hypothesis but a consequence: the eigenvalues of
modulus one are exactly the `m`-th roots of unity for some positive `m`
(arXiv:1708.00029, lines 257--258, citing Wolf).

This file derives that consequence.  The block is first put in the
trace-preserving normalization of `eq:unital` (arXiv:1708.00029, line 316) by
the positive-definite adjoint Perron fixed point; the normalized block has a
unital adjoint family, so the cyclic peripheral structure of Wolf Theorem
6.6(1) applies to it.  The normalization is a similarity, so the peripheral
spectrum obtained is that of the original block.

### Main results

* `IsPrimitiveRoot.powRange_eq_setOf_pow_eq_one`: the powers of a primitive
  `m`-th root of unity are exactly the `m`-th roots of unity.
* `MPSTensor.exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one`:
  an irreducible tensor of spectral radius one is spectrally periodic of some
  positive period.

### References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, lines 248--261,
  257--258 and 313--332.
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem
  6.6][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.Operator Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- **The period of an irreducible-form block.**

An MPS tensor whose transfer map is irreducible with spectral radius one — the
two conditions defining the irreducible form of arXiv:1708.00029, lines
248--261 — is spectrally periodic of some positive period.  The period is the
derived one of arXiv:1708.00029, lines 257--258: the eigenvalues of modulus one
of the transfer map are exactly the `m`-th roots of unity.

The proof passes to the trace-preserving normalization of arXiv:1708.00029,
equation `eq:unital`, line 316, by the positive-definite adjoint Perron fixed
point.  For the normalized block the conjugate-transposed Kraus family is
unital and its map is the trace adjoint of the transfer map, so the cyclic
peripheral structure of Wolf Theorem 6.6(1) applies with the forward Perron
fixed point as the required positive-definite adjoint fixed point.  Complex
conjugation carries the resulting peripheral spectrum back to that of the
transfer map, and the normalization is a similarity, so the peripheral spectrum
is that of the original tensor.

Source: arXiv:1708.00029, lines 248--261, 257--258 and 313--332;
Wolf, *Quantum Channels & Operations*, Theorem 6.6(1). -/
theorem exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
    {A : MPSTensor d D}
    (hIrr : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) A)
    (hRadius :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin D) A)) = 1) :
    ∃ m : ℕ, IsSpectrallyPeriodic m A := by
  classical
  have hD : D ≠ 0 :=
    matrix_dim_ne_zero_of_spectralRadius_eq_one
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap (ι := Fin d) (n := Fin D) A))
      hRadius
  have : NeZero D := ⟨hD⟩
  obtain ⟨σ, hσ, -, hLeft, -, hIrrB⟩ :=
    exists_tpGauge_of_irreducible_spectralRadius_one hIrr hRadius
  set B : MPSTensor d D := Kraus.tpGauge (d := d) (D := D) A σ with hBdef
  have hSdet : (CFC.sqrt σ).det ≠ 0 :=
    (Matrix.PosDef.isUnit_det_cfc_sqrt hσ).ne_zero
  have hSinvDet : ((CFC.sqrt σ)⁻¹).det ≠ 0 := by
    simpa [Matrix.det_nonsing_inv] using inv_ne_zero hSdet
  -- The normalization is a similarity, so it changes neither the spectral
  -- radius nor the peripheral spectrum.
  have hRadB :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin D) B)) = 1 := by
    change spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.mapLM B)) = 1
    rw [hBdef, Kraus.mapLM_tpGauge_eq_similarityMap A σ hσ,
      spectralRadius_similarityMap_eq (D := D) (CFC.sqrt σ)⁻¹ hSinvDet]
    exact hRadius
  have hPerB :
      peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) B) =
        peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) A) := by
    change peripheralEigenvalues (Kraus.mapLM B) = peripheralEigenvalues (Kraus.mapLM A)
    rw [hBdef, Kraus.mapLM_tpGauge_eq_similarityMap A σ hσ]
    exact peripheralEigenvalues_similarityMap_eq
      (CFC.sqrt σ)⁻¹ hSinvDet (Kraus.transferMap (ι := Fin d) (n := Fin D) A)
  -- The normalized block is nonzero, being trace preserving.
  have hLeft' : ∑ i : Fin d, (B i)ᴴ * B i = 1 := hLeft
  have hBne : ∃ i, B i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hone : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
      rw [← hLeft']
      exact Finset.sum_eq_zero fun i _ => by rw [hzero i]; simp
    exact one_ne_zero hone
  have hIrrMapB : IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) B) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hIrrB
  -- Its forward Perron eigenvector is a fixed point, since the spectral radius is one.
  obtain ⟨ρ, r, hρ, hr, hρeig⟩ :=
    exists_posDef_transferMap_eigenvector_of_irreducible (d := d) (n := D) B hIrrB hBne
  have hrRad :
      (spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin D) B))).toReal = r :=
    spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp
      (Kraus.transferMap (ι := Fin d) (n := Fin D) B) (Kraus.transferMap_isCPMap B) hIrrMapB
      ρ r hρ hr hρeig
  have hr_one : r = 1 := by
    rw [hRadB, ENNReal.toReal_one] at hrRad
    exact hrRad.symm
  have hρfix : Kraus.transferMap (ι := Fin d) (n := Fin D) B ρ = ρ := by
    rw [hρeig, hr_one]
    simp
  -- The conjugate-transposed family of the normalized block is unital, and its
  -- map is the trace adjoint of the transfer map.
  have hUnital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) (fun i => (B i)ᴴ) := by
    change ∑ i : Fin d, (B i)ᴴ * ((B i)ᴴ)ᴴ = 1
    simpa using hLeft'
  have hIrrAdj : IsIrreducibleMap (Kraus.mapLM (fun i => (B i)ᴴ)) :=
    Kraus.isIrreducibleMap_mapLM_conjTranspose B hIrrMapB
  have hAdjFix : Kraus.adjointMap (fun i => (B i)ᴴ) ρ = ρ := by
    rw [Kraus.adjointMap_conjTranspose_eq_map]
    exact hρfix
  obtain ⟨m, γ, hm, hγ, hset⟩ :=
    PeripheralSpectrum.peripheral_eigenvalues_cyclic_structure
      (fun i => (B i)ᴴ) hUnital ρ hρ hAdjFix hIrrAdj
  have : NeZero m := ⟨hm.ne'⟩
  -- Transport the peripheral spectrum across the conjugation.
  have hStarB :
      star '' peripheralEigenvalues (Kraus.mapLM B) = {μ : ℂ | μ ^ m = 1} := by
    rw [← Kraus.peripheralEigenvalues_mapLM_conjTranspose B, hset]
    exact hγ.powRange_eq_setOf_pow_eq_one
  have hPerBset :
      peripheralEigenvalues (Kraus.mapLM B) = {μ : ℂ | μ ^ m = 1} := by
    ext μ
    constructor
    · intro hμ
      have himg : star μ ∈ star '' peripheralEigenvalues (Kraus.mapLM B) :=
        Set.mem_image_of_mem _ hμ
      rw [hStarB] at himg
      have hpow : (star μ) ^ m = 1 := himg
      simpa using congrArg star hpow
    · intro hμ
      have hpow : (star μ) ^ m = 1 := by
        simpa using congrArg star (show μ ^ m = 1 from hμ)
      have hstar : star μ ∈ star '' peripheralEigenvalues (Kraus.mapLM B) := by
        rw [hStarB]
        exact hpow
      obtain ⟨x, hx, hxe⟩ := hstar
      have hxμ : x = μ := star_injective hxe
      exact hxμ ▸ hx
  refine ⟨m, hIrr, hRadius, hm, ?_⟩
  rw [← hPerB]
  exact hPerBset

end MPSTensor

end PeriodExistence

section BlockDecomposition

/-!
## Positive-weight periodic blocks for an arbitrary tensor

The irreducible decomposition of arXiv:1708.00029, Proposition `thm:irr`,
followed by its trace-preserving normalization `eq:unital`, gives periodic
left-canonical blocks with positive real weights. Equality is at positive
physical lengths; removing zero blocks can reduce the bond dimension.

This decomposition does not yet group repeated blocks into a basis, diagonalize
fixed points, or decompose the blocks after an arbitrary prescribed blocking.

### References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, Proposition
  `thm:irr`, lines 238--271, and `eq:unital`, lines 313--320.
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition
  6.1][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.Operator Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- Every irreducible left-canonical tensor of positive bond dimension has a period.
Source: arXiv:1708.00029, lines 248–258 and `eq:unital`; Wolf Proposition 6.1. -/
theorem exists_isPeriodic_of_irreducible_of_isLeftCanonical [NeZero D]
    (A : MPSTensor d D) (hIrr : Kraus.IsIrreducibleFamily A)
    (hA : IsLeftCanonical A) : ∃ m, IsPeriodic m A := by
  have hRad := (Kraus.isPositiveMap_mapLM A).spectralRadius_eq_one_of_tracePreserving
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hA)
  obtain ⟨m, hm⟩ :=
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one hIrr hRad
  exact ⟨m, hIrr, hA, hm.period_pos, hm.peripheral_eq⟩

/-- An arbitrary tensor has the same positive-length MPVs as a direct sum of periodic
left-canonical tensors with strictly positive real weights and total bond dimension at most D.
Source: arXiv:1708.00029, Proposition `thm:irr`, lines 238–271, and `eq:unital`, lines 313–320.
No blocking of the physical sites is performed. -/
theorem exists_periodic_blockDecomposition (A : MPSTensor d D) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)) (period : Fin r → ℕ),
      (∀ k, IsPeriodic (period k) (blocks k)) ∧
      (∀ k, 0 < μ k) ∧ (∀ k, 0 < dim k) ∧
      SameMPV₂Pos A (toTensorFromBlocks (μ := μ) blocks) ∧
      ∑ k, dim k ≤ D := by
  obtain ⟨r, dim, μ, blocks, hIrr, hTP, hμ, hDim, hSame, hBound⟩ :=
    exists_tp_gauge_from_arbitrary A
  have hp : ∀ k, ∃ m, IsPeriodic m (blocks k) := by
    intro k
    let : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
    exact exists_isPeriodic_of_irreducible_of_isLeftCanonical (blocks k) (hIrr k) (hTP k)
  choose period hperiod using hp
  exact ⟨r, dim, μ, blocks, period, hperiod, hμ, hDim, hSame, hBound⟩

end MPSTensor

end BlockDecomposition

section ScaledNormalization

/-!
## Periodic normalization of an arbitrary nonzero irreducible tensor

Every nonzero irreducible MPS tensor becomes, after a nonzero scalar rescaling
and a gauge transformation, left-canonical with a transfer map of spectral
radius one and peripheral spectrum the `m`-th roots of unity for some positive
`m`: a periodic block in the sense of `IsPeriodic`.  This generalizes
`MPSTensor.exists_leftCanonical_normalTensor_scale_of_isNormal`
(`TNLean/MPS/FundamentalTheorem/SectorBNT/PowerSumCoefficients.lean`), which
covers only the period-one (algebraically normal) case, to tensors that may be
genuinely periodic.

This is the trace-reduction normalization step of
`Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/t1_unblocked.tex`,
§"Trace reduction and explicit multiplicities": rescaling a nonzero
irreducible composition factor `T_a` by `s_a⁻¹ = ρ(𝓔_{T_a})^{-1/2}` and gauging
by the positive-definite fixed point of the rescaled adjoint transfer map
produces the normalized periodic representative `A_a`.

### Main result

* `MPSTensor.exists_leftCanonical_periodic_scale_of_irreducible`
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.Operator Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- **Periodic normalization of a nonzero irreducible tensor.**

For a nonzero irreducible tensor `A`, rescaling by `ζ = ρ(𝓔_A)^{-1/2}` and
gauging by the positive-definite fixed point of the trace-preserving
normalization produces a left-canonical representative `B` whose transfer map
has spectral radius one and peripheral spectrum the `m`-th roots of unity for
some positive `m`.  The scalar `ζ` records the rescaling in the matrix product
vectors.

Source: `t1_unblocked.tex`, §"Trace reduction and explicit multiplicities",
equations `moa-t1:factor-normalization`. -/
theorem exists_leftCanonical_periodic_scale_of_irreducible
    [NeZero D] {A : MPSTensor d D}
    (hIrr : Kraus.IsIrreducibleFamily A) (hA : ∃ i, A i ≠ 0) :
    ∃ (B : MPSTensor d D) (ζ : ℂ) (m : ℕ), ζ ≠ 0 ∧
      GaugeEquiv (fun i => ζ • A i) B ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) ∧
      IsPeriodic m B := by
  classical
  obtain ⟨ρ, r, hρ, hr, hEig⟩ := exists_posDef_transferMap_eigenvector_of_irreducible A hIrr hA
  have hIrrMap : IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) A) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr
  have hRad :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (Kraus.transferMap (ι := Fin d) (n := Fin D) A)) =
        ENNReal.ofReal r :=
    spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp
      (Kraus.transferMap A) (Kraus.transferMap_isCPMap A) hIrrMap ρ r hρ hr hEig
  set ζ : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ) with hζ_def
  have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hζ : ζ ≠ 0 := by
    simp only [hζ_def, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact hsqrt_pos.ne'
  have hnormζ : ‖ζ‖ = (Real.sqrt r)⁻¹ := by
    rw [hζ_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsqrt_pos)]
  have hIrrScaled : Kraus.IsIrreducibleFamily (fun i => ζ • A i) :=
    isIrreducibleFamily_smul hζ A hIrr
  have hRadScaled :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => ζ • A i))) = 1 := by
    rw [spectralRadius_transferMap_smul ζ hζ A, hRad]
    have hval : ‖ζ‖ ^ 2 * r = 1 := by
      rw [hnormζ, inv_pow, Real.sq_sqrt hr.le]
      field_simp
    have hnnreal : ‖ζ‖₊ ^ 2 * r.toNNReal = 1 := by
      apply NNReal.coe_injective
      push_cast [Real.coe_toNNReal r hr.le]
      exact hval
    change (↑‖ζ‖₊ : ENNReal) ^ 2 * (↑r.toNNReal : ENNReal) = 1
    rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, hnnreal, ENNReal.coe_one]
  obtain ⟨m, hSpec⟩ :=
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one hIrrScaled hRadScaled
  obtain ⟨σ, hσ, hσfix, hGauge, hPer⟩ := hSpec.exists_isPeriodic_tpGauge
  refine ⟨Kraus.tpGauge (d := d) (D := D) (fun i => ζ • A i) σ, ζ, m, hζ, hGauge, ?_, hPer⟩
  intro N τ
  rw [← hGauge.sameMPV N τ]
  simp only [mpv, coeff]
  rw [Kraus.evalWord_smul]
  simp [List.length_ofFn, Matrix.trace_smul]

end MPSTensor

end ScaledNormalization
