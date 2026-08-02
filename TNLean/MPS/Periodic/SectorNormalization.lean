/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Normalization
import TNLean.MPS.SharedInfra.BlockGauge
import TNLean.MPS.SharedInfra.SectorDecomposition

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

## Reference

De las Cuevas--Cirac--Schuch--Pérez-García, arXiv:1708.00029,
equation `eq:bdnr` and lines 286--332.
-/

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

/-- Duplicate a representative gauge over every copy of that representative
in the flattened sector coordinates.

For gauges $X_j$, this is the family whose direct sum is
$\bigoplus_j (I_{r_j} \otimes X_j)$.

Source: arXiv:1708.00029, equation `eq:bdnr`, lines 286--305, and the
block-diagonal similarity described at lines 313--332. -/
private noncomputable def flatGaugeOfBasis (P : SectorDecomposition d)
    (X : (j : Fin P.basisCount) → GL (Fin (P.basisDim j)) ℂ) :
    (s : Fin P.totalCopies) → GL (Fin (P.flatDim s)) ℂ :=
  fun s ↦ by
    change GL (Fin (P.basisDim (P.flatIndexEquiv.symm s).1)) ℂ
    exact X (P.flatIndexEquiv.symm s).1

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
  let Xflat := P.flatGaugeOfBasis X
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
    toTensorFromBlocks (d := d) (P.flatWeight)
        (P.replaceBasis B).flatBasis i =
      (globalGaugeOfBlocks Xflat : Matrix _ _ ℂ) *
        toTensorFromBlocks (d := d) (P.flatWeight) P.flatBasis i *
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
    fun j ↦ tpGauge (P.basis j) (sigma j)
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
