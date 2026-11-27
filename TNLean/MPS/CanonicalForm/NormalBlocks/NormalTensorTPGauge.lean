/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.KrausGauge
import QICLean.Channel.Irreducible.SpectralRadius
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Channel.Peripheral.Spectrum.Conjugation
import TNLean.MPS.CanonicalForm.NormalBlocks.ProjectorClosureSpectral
import TNLean.MPS.CanonicalForm.PhysicalReindex
import TNLean.MPS.Transfer.Irreducible.PerronGauge

/-!
# Trace-preserving Perron gauges of normal tensors

For a normal tensor, irreducible Perron--Frobenius theory gives positive-definite
right and left eigenvectors of the transfer map.  The spectral-radius-one
normalization forces both Perron eigenvalues to be one.  Gauging with the left
eigenvector therefore gives a trace-preserving tensor without any scalar
rescaling, and peripheral primitivity and irreducibility survive this gauge.

The physical alphabet is an arbitrary finite type.

## Main statements

* `GaugeEquiv.transferMap_eq_similarityMap`: gauge-equivalent tensors have
  similar transfer maps.
* `GaugeEquiv.transferMap_comp_self_eq_smul_iff`: transfer quasi-idempotence is
  invariant under gauge equivalence.
* `IsNormalTensor.of_gaugeEquiv`: CPSV normal-tensor status is invariant under
  gauge equivalence.
* `exists_tpGauge_of_irreducible_spectralRadius_one`: an irreducible
  spectral-radius-one tensor admits a pure trace-preserving Perron gauge.
* `IsNormalTensor.exists_tpGauge`: a normal tensor admits a pure
  trace-preserving Perron gauge.
* `IsNormalTensor.exists_apply_ne_zero`: a normal tensor has a nonzero letter.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, lines 219--235
  and 264--268.
* Pérez-García--Verstraete--Wolf--Cirac, arXiv:1708.00029, lines 313--332.
* Wolf, *Quantum Channels & Operations*, Theorem 6.3.
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder Kraus

namespace MPSTensor

variable {α : Type*} [Fintype α] {D : ℕ}

/-- The trace-adjoint identity for the transfer map of a tensor.

**Local bridge (QICLean `Kraus.trace_mul_mapLM_adjoint`):** the QICLean statement is stated only
for families indexed by `Fin n`; this lemma relabels the physical alphabet along
`Fintype.equivFin` and is removed when that statement is generalized. -/
private theorem trace_mul_transferMap_adjoint (A : MPTensor α (Fin D))
    (σ ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (σ * Kraus.transferMap A ρ) =
      Matrix.trace (Kraus.transferMap (fun i => (A i)ᴴ) σ * ρ) := by
  classical
  let e := (Fintype.equivFin α).symm
  have h : Matrix.trace (σ * Kraus.transferMap (Kraus.reindexPhysical e A) ρ) =
      Matrix.trace (Kraus.transferMap (Kraus.reindexPhysical e fun i => (A i)ᴴ) σ * ρ) :=
    Kraus.trace_mul_mapLM_adjoint (Kraus.reindexPhysical e A) rfl σ ρ
  rwa [Kraus.transferMap_reindexPhysical_equiv, Kraus.transferMap_reindexPhysical_equiv] at h

/-- Trace-preserving gauging by a positive-definite matrix preserves irreducibility of a tensor
whose transfer map is irreducible.

**Local bridge (QICLean `Kraus.isIrreducibleFamily_tpGauge_of_isIrreducibleMap`):** the QICLean
statement is stated only for families indexed by `Fin d`; this lemma relabels the physical
alphabet along `Fintype.equivFin` and is removed when that statement is generalized. -/
private theorem isIrreducibleFamily_tpGauge_of_isIrreducibleMap (A : MPTensor α (Fin D))
    (σ : Matrix (Fin D) (Fin D) ℂ) (hσ : σ.PosDef)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A)) :
    Kraus.IsIrreducibleFamily (Kraus.tpGauge A σ) := by
  classical
  let e := (Fintype.equivFin α).symm
  have hIrr' : IsIrreducibleMap (Kraus.transferMap (Kraus.reindexPhysical e A)) := by
    rwa [Kraus.transferMap_reindexPhysical_equiv]
  have h : Kraus.IsIrreducibleFamily (Kraus.reindexPhysical e (Kraus.tpGauge A σ)) :=
    Kraus.isIrreducibleFamily_tpGauge_of_isIrreducibleMap (Kraus.reindexPhysical e A) σ hσ hIrr'
  exact (isIrreducibleFamily_reindexPhysical_equiv e _).1 h

/-- Trace-preserving gauging by a positive-definite matrix preserves primitivity of the transfer
map.

**Local bridge (QICLean `Kraus.isPrimitive_mapLM_tpGauge_iff`):** the QICLean statement is stated
only for families indexed by `Fin d`; this lemma relabels the physical alphabet along
`Fintype.equivFin` and is removed when that statement is generalized. -/
private theorem isPrimitive_transferMap_tpGauge_iff (A : MPTensor α (Fin D))
    (σ : Matrix (Fin D) (Fin D) ℂ) (hσ : σ.PosDef) :
    _root_.IsPrimitive (Kraus.transferMap (Kraus.tpGauge A σ)) ↔
      _root_.IsPrimitive (Kraus.transferMap A) := by
  classical
  let e := (Fintype.equivFin α).symm
  have h : _root_.IsPrimitive (Kraus.transferMap (Kraus.reindexPhysical e (Kraus.tpGauge A σ))) ↔
      _root_.IsPrimitive (Kraus.transferMap (Kraus.reindexPhysical e A)) :=
    Kraus.isPrimitive_mapLM_tpGauge_iff (Kraus.reindexPhysical e A) σ hσ
  rwa [Kraus.transferMap_reindexPhysical_equiv, Kraus.transferMap_reindexPhysical_equiv] at h

/-- The transfer maps of gauge-equivalent tensors are related by the standard
congruence similarity of completely positive maps.

Source: arXiv:1606.00608, lines 219--223 define the transfer map and lines
264--268 give the invertible gauge relation. -/
theorem _root_.MPTensor.GaugeEquiv.transferMap_eq_similarityMap {A B : MPTensor α (Fin D)}
    (h : GaugeEquiv A B) :
    ∃ C : Matrix (Fin D) (Fin D) ℂ, C.det ≠ 0 ∧
      Kraus.transferMap (ι := α) (n := Fin D) B =
        similarityMap (D := D) C (Kraus.transferMap (ι := α) (n := Fin D) A) := by
  obtain ⟨X, hX⟩ := h
  refine ⟨((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), ?_, ?_⟩
  · exact Matrix.GeneralLinearGroup.det_ne_zero (X⁻¹ : GL (Fin D) ℂ)
  · apply LinearMap.ext
    intro Y
    have hXdet : IsUnit ((X : Matrix (Fin D) (Fin D) ℂ).det) :=
      Ne.isUnit (Matrix.GeneralLinearGroup.det_ne_zero X)
    have hX_inv_inv :
        ((X : Matrix (Fin D) (Fin D) ℂ)⁻¹)⁻¹ =
          (X : Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.nonsing_inv_nonsing_inv (X : Matrix (Fin D) (Fin D) ℂ) hXdet
    have hXstar_det : IsUnit (((X : Matrix (Fin D) (Fin D) ℂ)ᴴ).det) := by
      simpa [Matrix.det_conjTranspose] using IsUnit.star hXdet
    have hXstar_inv_inv :
        (((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)⁻¹)⁻¹ =
          (X : Matrix (Fin D) (Fin D) ℂ)ᴴ :=
      Matrix.nonsing_inv_nonsing_inv
        ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ) hXstar_det
    calc
      Kraus.transferMap (ι := α) (n := Fin D) B Y =
          ∑ x : α,
            ((X : Matrix (Fin D) (Fin D) ℂ) * A x *
              (X : Matrix (Fin D) (Fin D) ℂ)⁻¹) * Y *
              (((X : Matrix (Fin D) (Fin D) ℂ) * A x *
                (X : Matrix (Fin D) (Fin D) ℂ)⁻¹)ᴴ) := by
            simp [hX]
      _ = ∑ x : α,
            (X : Matrix (Fin D) (Fin D) ℂ) *
              (A x * ((X : Matrix (Fin D) (Fin D) ℂ)⁻¹ * Y *
                ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)⁻¹) * (A x)ᴴ) *
              (X : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
            refine Finset.sum_congr rfl ?_
            intro x _
            simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
              Matrix.mul_assoc]
      _ = (X : Matrix (Fin D) (Fin D) ℂ) *
            (∑ x : α,
              A x * ((X : Matrix (Fin D) (Fin D) ℂ)⁻¹ * Y *
                ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)⁻¹) * (A x)ᴴ) *
            (X : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
            simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
      _ = similarityMap (D := D)
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
            (Kraus.transferMap (ι := α) (n := Fin D) A) Y := by
            simp [similarityMap, Matrix.conjTranspose_nonsing_inv,
              hX_inv_inv, hXstar_inv_inv, Matrix.mul_assoc]

/-- Gauge equivalence transports quasi-idempotence of the transfer map. -/
theorem _root_.MPTensor.GaugeEquiv.transferMap_comp_self_eq_smul_iff {A B : MPTensor α (Fin D)}
    (h : GaugeEquiv A B) (c : ℂ) :
    Kraus.transferMap (ι := α) (n := Fin D) B ∘ₗ Kraus.transferMap (ι := α) (n := Fin D) B =
        c • Kraus.transferMap (ι := α) (n := Fin D) B ↔
      Kraus.transferMap (ι := α) (n := Fin D) A ∘ₗ
        Kraus.transferMap (ι := α) (n := Fin D) A =
        c • Kraus.transferMap (ι := α) (n := Fin D) A := by
  obtain ⟨C, hC, hMap⟩ := h.transferMap_eq_similarityMap
  let e := (Matrix.congruenceLinearEquiv C hC).symm.conjAlgEquiv ℂ
  have hSimilarity (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ) :
      similarityMap (D := D) C E = e E := by
    apply LinearMap.ext
    intro X
    ext i j
    simp [e, similarityMap, LinearEquiv.conjAlgEquiv_apply, Matrix.mul_assoc]
  rw [hMap, hSimilarity]
  constructor
  · intro hPoly
    apply e.injective
    rw [← Module.End.mul_eq_comp] at hPoly ⊢
    simpa using hPoly
  · intro hPoly
    rw [← Module.End.mul_eq_comp] at hPoly ⊢
    simpa using congrArg e hPoly

section IsNormalTensor

open MPTensor.IsNormalTensor

/-- Transport normal-tensor status backward along a gauge equivalence.

The transfer maps are similar, hence have the same spectral radius and
peripheral spectrum; irreducibility is transported through the corresponding
irreducible-map similarity.

Source: arXiv:1606.00608, lines 233--235 define normal tensors and lines
264--268 give the invertible gauge relation between normal representatives. -/
theorem _root_.MPTensor.IsNormalTensor.of_gaugeEquiv {A B : MPTensor α (Fin D)} (hB : IsNormalTensor B)
    (hGauge : GaugeEquiv A B) :
    IsNormalTensor A := by
  obtain ⟨C, hC, hMap⟩ := hGauge.transferMap_eq_similarityMap
  refine ⟨?_, ?_, ?_⟩
  · have hIrrB : IsIrreducibleMap (Kraus.transferMap (ι := α) (n := Fin D) B) :=
      Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB.no_invariant_proj
    have hIrrA : IsIrreducibleMap (Kraus.transferMap (ι := α) (n := Fin D) A) := by
      have hIrrSim : IsIrreducibleMap
          (similarityMap (D := D) C (Kraus.transferMap (ι := α) (n := Fin D) A)) := by
        simpa [hMap] using hIrrB
      exact (isIrreducibleMap_similarity_iff (D := D) hC).1 hIrrSim
    exact Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hIrrA
  · have hsr := hB.spectral_radius_one
    rw [hMap] at hsr
    rw [spectralRadius_similarityMap_eq (D := D) C hC
      (Kraus.transferMap (ι := α) (n := Fin D) A)] at hsr
    exact hsr
  · have hPrim := hB.primitive_transfer
    rw [hMap] at hPrim
    exact (IsPrimitive.similarityMap_iff (D := D) C hC
      (Kraus.transferMap (ι := α) (n := Fin D) A)).1 hPrim

end IsNormalTensor

/-- An irreducible tensor of spectral radius one admits a trace-preserving Perron gauge with no
scalar rescaling.

The positive-definite right and left Perron eigenvectors have the same positive eigenvalue.  The
spectral-radius-one hypothesis forces this eigenvalue to be one, so the left Perron eigenvector is
an adjoint fixed point of the original transfer map.  Gauging by its positive square root is
therefore a pure similarity, is left-canonical, and preserves irreducibility.

Source: arXiv:1708.00029, lines 313--332; Wolf, *Quantum Channels & Operations*, Theorem 6.3. -/
theorem exists_tpGauge_of_irreducible_spectralRadius_one
    {A : MPTensor α (Fin D)}
    (hIrr : Kraus.IsIrreducibleFamily A)
    (hRadius :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (ι := α) (n := Fin D) A)) = 1) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosDef ∧
      Kraus.transferMap (ι := α) (n := Fin D) (fun i => (A i)ᴴ) σ = σ ∧
      IsLeftCanonical (Kraus.tpGauge (ι := α) (D := D) A σ) ∧
      GaugeEquiv A (Kraus.tpGauge (ι := α) (D := D) A σ) ∧
      Kraus.IsIrreducibleFamily (Kraus.tpGauge (ι := α) (D := D) A σ) := by
  have hD : D ≠ 0 :=
    matrix_dim_ne_zero_of_spectralRadius_eq_one
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap (ι := α) (n := Fin D) A))
      hRadius
  let : NeZero D := ⟨hD⟩
  have hA : ∃ i, A i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hmap : Kraus.transferMap (ι := α) (n := Fin D) A = 0 := by
      ext X a b
      simp [hzero]
    have hspectral := hRadius
    rw [hmap] at hspectral
    simp at hspectral
  have hIrrMap : IsIrreducibleMap (Kraus.transferMap (ι := α) (n := Fin D) A) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr
  obtain ⟨ρ, r, hρ, hr, hρeig⟩ :=
    exists_posDef_transferMap_eigenvector_of_irreducible A hIrr hA
  have hradius :
      (spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (ι := α) (n := Fin D) A))).toReal = r :=
    spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp
      (Kraus.transferMap (ι := α) (n := Fin D) A) (Kraus.transferMap_isCPMap A) hIrrMap
      ρ r hρ hr hρeig
  have hradius_one :
      (spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (ι := α) (n := Fin D) A))).toReal = 1 := by
    rw [hRadius]
    simp
  have hr_one : r = 1 := hradius.symm.trans hradius_one
  obtain ⟨σ, t, hσ, ht, hσeig⟩ :=
    exists_posDef_adjoint_eigenvector A hIrr hA
  have htrace : Matrix.trace (σ * Kraus.transferMap (ι := α) (n := Fin D) A ρ) =
      Matrix.trace
        (Kraus.transferMap (ι := α) (n := Fin D) (fun i => (A i)ᴴ) σ * ρ) :=
    trace_mul_transferMap_adjoint A σ ρ
  have htr_ne : Matrix.trace (σ * ρ) ≠ 0 := by
    exact ne_of_gt (hσ.trace_mul_pos_of_posSemidef_of_ne_zero
      hρ.posSemidef (Matrix.PosDef.isUnit hρ).ne_zero)
  have hscalar : (r : ℂ) * Matrix.trace (σ * ρ) =
      (t : ℂ) * Matrix.trace (σ * ρ) := by
    calc
      (r : ℂ) * Matrix.trace (σ * ρ) =
          Matrix.trace (σ * ((r : ℂ) • ρ)) := by
            rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      _ = Matrix.trace (σ * Kraus.transferMap (ι := α) (n := Fin D) A ρ) := by rw [hρeig]
      _ = Matrix.trace
          (Kraus.transferMap (ι := α) (n := Fin D) (fun i => (A i)ᴴ) σ * ρ) := htrace
      _ = Matrix.trace (((t : ℂ) • σ) * ρ) := by rw [hσeig]
      _ = (t : ℂ) * Matrix.trace (σ * ρ) := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hrt : r = t := by
    have hc : (r : ℂ) = (t : ℂ) := mul_right_cancel₀ htr_ne hscalar
    exact_mod_cast hc
  have ht_one : t = 1 := hrt ▸ hr_one
  have hσfix : Kraus.transferMap (ι := α) (n := Fin D) (fun i => (A i)ᴴ) σ = σ := by
    simpa [ht_one] using hσeig
  have hTP : IsLeftCanonical (Kraus.tpGauge (ι := α) (D := D) A σ) :=
    Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint A σ hσ hσfix
  have hGauge : GaugeEquiv A (Kraus.tpGauge (ι := α) (D := D) A σ) :=
    gaugeEquiv_tpGauge A σ hσ
  have hGaugeIrr : Kraus.IsIrreducibleFamily (Kraus.tpGauge (ι := α) (D := D) A σ) :=
    isIrreducibleFamily_tpGauge_of_isIrreducibleMap A σ hσ hIrrMap
  exact ⟨σ, hσ, hσfix, hTP, hGauge, hGaugeIrr⟩

/-- A normal tensor admits a trace-preserving gauge with no scalar rescaling.

The tensor is normal in the sense of arXiv:1606.00608, lines 231--235: its
transfer map has spectral radius one and unique peripheral eigenvalue one.
The spectral-radius normalization forces positive bond dimension. The
positive-definite left Perron eigenvector consequently has eigenvalue one, so
the usual Perron gauge is a pure similarity of the original tensor. -/
theorem _root_.MPTensor.IsNormalTensor.exists_tpGauge
    {A : MPTensor α (Fin D)} (h : IsNormalTensor A) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosDef ∧
      Kraus.transferMap (ι := α) (n := Fin D) (fun i => (A i)ᴴ) σ = σ ∧
      IsLeftCanonical (Kraus.tpGauge (ι := α) (D := D) A σ) ∧
      GaugeEquiv A (Kraus.tpGauge (ι := α) (D := D) A σ) ∧
      _root_.IsPrimitive
        (Kraus.transferMap (ι := α) (n := Fin D) (Kraus.tpGauge (ι := α) (D := D) A σ)) ∧
      Kraus.IsIrreducibleFamily (Kraus.tpGauge (ι := α) (D := D) A σ) := by
  obtain ⟨σ, hσ, hσfix, hTP, hGauge, hIrr⟩ :=
    exists_tpGauge_of_irreducible_spectralRadius_one
      h.no_invariant_proj h.spectral_radius_one
  have hPrim : _root_.IsPrimitive
      (Kraus.transferMap (ι := α) (n := Fin D) (Kraus.tpGauge (ι := α) (D := D) A σ)) :=
    (isPrimitive_transferMap_tpGauge_iff A σ hσ).2 h.primitive_transfer
  exact ⟨σ, hσ, hσfix, hTP, hGauge, hPrim, hIrr⟩


/-- A normal tensor has a nonzero letter.

Indeed, if every letter vanished, then its transfer map and hence its spectral
radius would vanish, contradicting the spectral-radius-one normalization of
arXiv:1606.00608, lines 231--235. -/
theorem _root_.MPTensor.IsNormalTensor.exists_apply_ne_zero
    {A : MPTensor α (Fin D)} (h : IsNormalTensor A) : ∃ i, A i ≠ 0 := by
  have : NeZero D := ⟨h.bondDim_ne_zero⟩
  by_contra hzero
  push Not at hzero
  have hmap : Kraus.transferMap (ι := α) (n := Fin D) A = 0 := by
    ext X a b
    simp [hzero]
  have hspectral := h.spectral_radius_one
  rw [hmap] at hspectral
  simp at hspectral

end MPSTensor
