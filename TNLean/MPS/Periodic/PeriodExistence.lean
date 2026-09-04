/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Channel.Irreducible.AdjointFamily
import QICLean.Channel.Irreducible.KrausGauge
import QICLean.Channel.Irreducible.SpectralRadius
import QICLean.Channel.Peripheral.AdjointSpectrum
import QICLean.Channel.Peripheral.GroupStructure
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.Periodic.Defs

/-!
# The period of an irreducible-form block

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

## Main results

* `IsPrimitiveRoot.powRange_eq_setOf_pow_eq_one`: the powers of a primitive
  `m`-th root of unity are exactly the `m`-th roots of unity.
* `MPSTensor.exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one`:
  an irreducible tensor of spectral radius one is spectrally periodic of some
  positive period.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, lines 248--261,
  257--258 and 313--332.
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem
  6.6][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.Operator Kraus

/-- The powers of a primitive `m`-th root of unity in `ℂ` are exactly the
solutions of `μ ^ m = 1`. -/
theorem IsPrimitiveRoot.powRange_eq_setOf_pow_eq_one {m : ℕ} [NeZero m] {γ : ℂ}
    (hγ : IsPrimitiveRoot γ m) :
    {z : ℂ | ∃ k : Fin m, z = γ ^ (k : ℕ)} = {μ : ℂ | μ ^ m = 1} := by
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, hγ.pow_eq_one, one_pow]
  · intro hz
    obtain ⟨i, hi, hip⟩ := hγ.eq_pow_of_pow_eq_one hz
    exact ⟨⟨i, hi⟩, hip.symm⟩

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
    (hIrr : Kraus.IsIrreducibleFamily (d := d) (D := D) A)
    (hRadius :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (d := d) (D := D) A)) = 1) :
    ∃ m : ℕ, IsSpectrallyPeriodic m A := by
  classical
  have hD : D ≠ 0 :=
    matrix_dim_ne_zero_of_spectralRadius_eq_one
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap (d := d) (D := D) A))
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
          (Kraus.transferMap (d := d) (D := D) B)) = 1 := by
    change spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.mapLM B)) = 1
    rw [hBdef, Kraus.mapLM_tpGauge_eq_similarityMap A σ hσ,
      spectralRadius_similarityMap_eq (D := D) (CFC.sqrt σ)⁻¹ hSinvDet]
    exact hRadius
  have hPerB :
      peripheralEigenvalues (Kraus.transferMap (d := d) (D := D) B) =
        peripheralEigenvalues (Kraus.transferMap (d := d) (D := D) A) := by
    change peripheralEigenvalues (Kraus.mapLM B) = peripheralEigenvalues (Kraus.mapLM A)
    rw [hBdef, Kraus.mapLM_tpGauge_eq_similarityMap A σ hσ]
    exact peripheralEigenvalues_similarityMap_eq
      (CFC.sqrt σ)⁻¹ hSinvDet (Kraus.transferMap (d := d) (D := D) A)
  -- The normalized block is nonzero, being trace preserving.
  have hLeft' : ∑ i : Fin d, (B i)ᴴ * B i = 1 := hLeft
  have hBne : ∃ i, B i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hone : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
      rw [← hLeft']
      exact Finset.sum_eq_zero fun i _ => by rw [hzero i]; simp
    exact one_ne_zero hone
  have hIrrMapB : IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) B) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hIrrB
  -- Its forward Perron eigenvector is a fixed point, since the spectral radius is one.
  obtain ⟨ρ, r, hρ, hr, hρeig⟩ :=
    exists_posDef_transferMap_eigenvector_of_irreducible (d := d) (n := D) B hIrrB hBne
  have hrRad :
      (spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (d := d) (D := D) B))).toReal = r :=
    spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp
      (Kraus.transferMap (d := d) (D := D) B) (Kraus.transferMap_isCPMap B) hIrrMapB
      ρ r hρ hr hρeig
  have hr_one : r = 1 := by
    rw [hRadB, ENNReal.toReal_one] at hrRad
    exact hrRad.symm
  have hρfix : Kraus.transferMap (d := d) (D := D) B ρ = ρ := by
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
