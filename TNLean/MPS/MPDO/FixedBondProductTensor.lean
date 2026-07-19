/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingFormBridge
import TNLean.MPS.MPDO.CyclicEdgeWeightTensor
import TNLean.MPS.MPDO.VerticalCF
import TNLean.MPS.Overlap.NormalTensorDichotomy

/-!
# Fixed matrix-product representations of commuting-bond products

This file records the exact interface required to compare a fixed
translation-invariant commuting bond with a normal matrix-product tensor.  It
also constructs the representation whenever the bond product is already
written as a cyclic nearest-neighbor scalar weight, and transports the source
positive realization from lengths at least two to eventual nonzero MPV
proportionality.

Normality is deliberately not included in the representation datum. An
arbitrary representation may contain an additional all-zero virtual summand,
which cannot be removed by a nonzero scalar. Proposition C.8 instead selects
its bond from the physical-sector factorization of the source tensor; that
selected product family has the source tensor itself as a representative.

## Main declarations

* `MPOTensor.TranslationInvariantBondData.FixedProductTensorData`
* `MPOTensor.TranslationInvariantBondData.CyclicEdgeWeightForm`
* `MPOTensor.TranslationInvariantBondData.CyclicEdgeWeightForm.toFixedProductTensorData`
* `MPOTensor.EtaLocalStructureData.eventuallyNonzeroProportionalMPV₂_fixedProductTensor`
* `MPOTensor.EtaLocalStructureData.exists_unit_phase_power_mpo_eq_product_of_normal_smul`
* `MPOTensor.EtaLocalStructureData.mpo_eq_positive_power_product_of_normal_smul`

## References

* arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
  1570--1593.
-/

open scoped BigOperators Matrix

namespace MPOTensor

variable {d D : ℕ}

namespace TranslationInvariantBondData

/-- A chain-independent matrix-product tensor whose closed operator family is
exactly the product of all translates of one fixed commuting bond.

The positive bond dimension is part of the datum.  No normality is assumed.

Local interface motivated by arXiv:1606.00608, Appendix C.2, Proposition C.8
(`3to4`), lines 1570--1593.  The cited proposition gives proportionality to a
fixed commuting-bond product; it does not construct this exact tensor datum. -/
structure FixedProductTensorData (data : TranslationInvariantBondData d) where
  /-- Bond dimension of the representing tensor. -/
  bondDim : ℕ
  /-- The representing bond space is nonzero. -/
  bondDim_pos : 0 < bondDim
  /-- The chain-independent matrix-product tensor. -/
  tensor : MPOTensor d bondDim
  /-- Exact entrywise realization of every finite-chain bond product in the
  source range. -/
  mpo_eq_product :
    ∀ (N : ℕ) (hN : 2 ≤ N),
      mpo tensor N = (data.toCommutingFormData hN).product

/-- A fixed bond product written entrywise as one cyclic nearest-neighbor
scalar weight in the current one-site coordinates.

This is the scalar form of the right-hand side of equation `sigmaNK2`.  The
same weight is used at every site and every chain length.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
structure CyclicEdgeWeightForm (data : TranslationInvariantBondData d) where
  /-- The chain-independent weight on two consecutive ket--bra pairs. -/
  weight : Fin d → Fin d → Fin d → Fin d → ℂ
  /-- Entrywise cyclic product formula at every length in the source range. -/
  product_apply :
    ∀ (N : ℕ) (hN : 2 ≤ N),
      letI : NeZero N := ⟨by omega⟩
      ∀ (sigma tau : Fin N → Fin d),
        (data.toCommutingFormData hN).product sigma tau =
          ∏ n : Fin N,
            weight (sigma n) (tau n) (sigma (n + 1)) (tau (n + 1))

/-- A cyclic nearest-neighbor scalar weight gives a fixed matrix-product
representation of bond dimension `d * d`.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
noncomputable def CyclicEdgeWeightForm.toFixedProductTensorData
    [NeZero d] {data : TranslationInvariantBondData d}
    (form : CyclicEdgeWeightForm data) : FixedProductTensorData data where
  bondDim := d * d
  bondDim_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
  tensor := cyclicEdgeWeightTensor form.weight
  mpo_eq_product := by
    intro N hN
    letI : NeZero N := ⟨by omega⟩
    ext sigma tau
    rw [mpo_cyclicEdgeWeightTensor]
    exact (form.product_apply N hN sigma tau).symm

end TranslationInvariantBondData

namespace EtaLocalStructureData

variable {M : MPOTensor d D}

private theorem fixedProduct_ne_zero_of_mpvOverlap_ne_zero
    (data : EtaLocalStructureData M)
    {N : ℕ} (hN : 2 ≤ N)
    (hOverlap : MPSTensor.mpvOverlap M.toMPSTensor M.toMPSTensor N ≠ 0) :
    (data.bondData.toCommutingFormData hN).product ≠ 0 := by
  classical
  have hExists : ∃ ρ : Fin N → Fin (d * d),
      MPSTensor.mpv M.toMPSTensor ρ ≠ 0 := by
    by_contra h
    push Not at h
    apply hOverlap
    simp only [MPSTensor.mpvOverlap]
    apply Finset.sum_eq_zero
    intro ρ _hρ
    rw [h ρ, zero_mul]
  obtain ⟨ρ, hρ⟩ := hExists
  let σ : Fin N → Fin d := fun n ↦ (ρ n).divNat
  let τ : Fin N → Fin d := fun n ↦ (ρ n).modNat
  have hρeq : (fun n ↦ finProdFinEquiv (σ n, τ n)) = ρ := by
    funext n
    simpa [σ, τ] using (finProdFinEquiv.apply_symm_apply (ρ n))
  have hMpo : mpo M N σ τ ≠ 0 := by
    rw [← MPSTensor.mpv_toMPSTensor_pairConfig, hρeq]
    exact hρ
  obtain ⟨c, hc, hReal⟩ := data.realizes_mpo N hN
  intro hProduct
  apply hMpo
  rw [hReal, hProduct, smul_zero, Matrix.zero_apply]

/-- A fixed tensor representation of the commuting-bond product converts the
positive source realization, which begins at length two, into eventual
nonzero proportionality of the doubled-index matrix-product vectors.

No length-one realization is assumed.  No normality or geometric law for the
length-dependent scalar is asserted.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1570--1593. -/
theorem eventuallyNonzeroProportionalMPV₂_fixedProductTensor
    (data : EtaLocalStructureData M)
    (repr : TranslationInvariantBondData.FixedProductTensorData data.bondData) :
    MPSTensor.EventuallyNonzeroProportionalMPV₂
      M.toMPSTensor repr.tensor.toMPSTensor := by
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  obtain ⟨c, hc, hreal⟩ := data.realizes_mpo N hN
  refine ⟨(c : ℂ), ?_, ?_⟩
  · exact_mod_cast ne_of_gt hc
  · intro rho
    let sigma : Fin N → Fin d := fun n ↦ (rho n).divNat
    let tau : Fin N → Fin d := fun n ↦ (rho n).modNat
    have hrho : (fun n ↦ finProdFinEquiv (sigma n, tau n)) = rho := by
      funext n
      simpa [sigma, tau] using (finProdFinEquiv.apply_symm_apply (rho n))
    rw [← hrho]
    rw [MPSTensor.mpv_toMPSTensor_pairConfig,
      MPSTensor.mpv_toMPSTensor_pairConfig]
    rw [hreal, repr.mpo_eq_product N hN]
    rfl

/-- If one positive rescaling of a fixed product tensor is normal, then its
comparison with a normal source tensor already has one geometric coefficient:
a unit phase times the positive rescaling, raised to the chain length.

Thus the existence of a rescaled normal representative is not independent of
the geometric-scalar problem. This statement does not assert that the
fixed product tensor, or any rescaling of it, is normal.

Source context: arXiv:1606.00608, Appendix C.2, Proposition C.8 (label:
3to4), lines 1570--1593, together with Corollary eqV, lines 1121--1128. The
distinction between source-selected and arbitrary presentations is documented in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

**Scope restriction (positive normal rescaling):** The hypothesis `hRepr`
assumes that the positively rescaled fixed-product tensor is normal. This
hypothesis is absent from Proposition C.8 (label: 3to4). It is false for an
arbitrary supplied representation after adjoining an all-zero virtual summand;
the source-selected bond instead uses the source tensor itself. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_unit_phase_power_mpo_eq_product_of_normal_smul
    [NeZero D]
    (data : EtaLocalStructureData M)
    (repr : TranslationInvariantBondData.FixedProductTensorData data.bondData)
    (s : ℝ) (hs : 0 < s)
    (hM : MPSTensor.IsNormalTensor M.toMPSTensor)
    (hRepr : MPSTensor.IsNormalTensor
      (fun i ↦ (s : ℂ) • repr.tensor.toMPSTensor i)) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ (N : ℕ) (hN : 2 ≤ N),
      mpo M N = ((ζ * (s : ℂ)) ^ N) • (data.bondData.toCommutingFormData hN).product := by
  letI : NeZero repr.bondDim := ⟨Nat.ne_of_gt repr.bondDim_pos⟩
  have hsℂ : (s : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hs
  have hProp : MPSTensor.EventuallyNonzeroProportionalMPV₂ M.toMPSTensor
      (fun i ↦ (s : ℂ) • repr.tensor.toMPSTensor i) := by
    filter_upwards [data.eventuallyNonzeroProportionalMPV₂_fixedProductTensor repr]
      with N hN
    rcases hN with ⟨c, hc, hEq⟩
    refine ⟨c / (s : ℂ) ^ N, div_ne_zero hc (pow_ne_zero N hsℂ), ?_⟩
    intro σ
    rw [MPSTensor.mpv_smul, hEq σ]
    field_simp
  rcases hProp.exists_unit_phase_power_of_isNormalTensor hM hRepr with
    ⟨ζ, hζ, hPhase⟩
  refine ⟨ζ, hζ, ?_⟩
  intro N hN
  ext σ τ
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
    hPhase N (by omega), MPSTensor.mpv_smul,
    MPSTensor.mpv_toMPSTensor_pairConfig, repr.mpo_eq_product N hN]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, mul_pow]

/-- Under the hypotheses of
`exists_unit_phase_power_mpo_eq_product_of_normal_smul`, positivity of the
source realization removes the unit phase.  Consequently the same positive
rescaling that makes the fixed product tensor normal is the base of the
geometric realization scalar.

The proof uses two sufficiently large consecutive lengths, not lengths one or
two.  Normality of the source makes its self-overlap, and hence the fixed bond
product, nonzero at those lengths.

Source context: arXiv:1606.00608, Appendix C.2, Proposition C.8 (label:
3to4), lines 1570--1593, together with Corollary eqV, lines 1121--1128. The
arbitrary-presentation hypothesis is discussed in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

**Scope restriction (positive normal rescaling):** The hypothesis `hRepr`
assumes that the positively rescaled fixed-product tensor is normal. This
hypothesis is absent from Proposition C.8 (label: 3to4). It is false for an
arbitrary supplied representation after adjoining an all-zero virtual summand;
the source-selected bond instead uses the source tensor itself. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem mpo_eq_positive_power_product_of_normal_smul
    [NeZero D]
    (data : EtaLocalStructureData M)
    (repr : TranslationInvariantBondData.FixedProductTensorData data.bondData)
    (s : ℝ) (hs : 0 < s)
    (hM : MPSTensor.IsNormalTensor M.toMPSTensor)
    (hRepr : MPSTensor.IsNormalTensor
      (fun i ↦ (s : ℂ) • repr.tensor.toMPSTensor i)) :
    ∀ (N : ℕ) (hN : 2 ≤ N),
      mpo M N = ((s : ℂ) ^ N) • (data.bondData.toCommutingFormData hN).product := by
  rcases data.exists_unit_phase_power_mpo_eq_product_of_normal_smul
      repr s hs hM hRepr with ⟨ζ, hζ, hGeo⟩
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hM.selfOverlap_tendsto_one
    (1 / 2) (by norm_num)
  let N := max K 2
  have hKN : K ≤ N := le_max_left K 2
  have hN : 2 ≤ N := le_max_right K 2
  have hOverlapN : MPSTensor.mpvOverlap M.toMPSTensor M.toMPSTensor N ≠ 0 := by
    intro hZero
    have hDist := hK N hKN
    rw [hZero] at hDist
    norm_num at hDist
  have hOverlapSucc :
      MPSTensor.mpvOverlap M.toMPSTensor M.toMPSTensor (N + 1) ≠ 0 := by
    intro hZero
    have hDist := hK (N + 1) (by omega)
    rw [hZero] at hDist
    norm_num at hDist
  have hProductN : (data.bondData.toCommutingFormData hN).product ≠ 0 :=
    fixedProduct_ne_zero_of_mpvOverlap_ne_zero data hN hOverlapN
  have hNSucc : 2 ≤ N + 1 := by omega
  have hProductSucc :
      (data.bondData.toCommutingFormData hNSucc).product ≠ 0 :=
    fixedProduct_ne_zero_of_mpvOverlap_ne_zero data hNSucc hOverlapSucc
  obtain ⟨cN, hcN, hRealN⟩ := data.realizes_mpo N hN
  obtain ⟨cSucc, hcSucc, hRealSucc⟩ := data.realizes_mpo (N + 1) hNSucc
  have hScalarN : (ζ * (s : ℂ)) ^ N = (cN : ℂ) := by
    apply sub_eq_zero.mp
    apply (smul_eq_zero.mp ?_).resolve_right hProductN
    rw [sub_smul, (hGeo N hN).symm.trans hRealN, sub_self]
  have hScalarSucc : (ζ * (s : ℂ)) ^ (N + 1) = (cSucc : ℂ) := by
    apply sub_eq_zero.mp
    apply (smul_eq_zero.mp ?_).resolve_right hProductSucc
    rw [sub_smul, (hGeo (N + 1) hNSucc).symm.trans hRealSucc, sub_self]
  let x : ℂ := ζ * (s : ℂ)
  have hxMul : x * (cN : ℂ) = (cSucc : ℂ) := by
    rw [← hScalarN, ← hScalarSucc]
    simp only [x, pow_succ]
    rw [mul_comm]
  have hcNℂ : (cN : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hcN
  have hx : x = ((cSucc / cN : ℝ) : ℂ) := by
    calc
      x = (cSucc : ℂ) / (cN : ℂ) := (eq_div_iff hcNℂ).2 hxMul
      _ = ((cSucc / cN : ℝ) : ℂ) := by norm_cast
  have hnormx : ‖x‖ = s := by
    simp [x, hζ, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hRatio : cSucc / cN = s := by
    have hNorm := congrArg norm hx
    rw [hnormx, Complex.norm_real,
      Real.norm_of_nonneg (div_pos hcSucc hcN).le] at hNorm
    exact hNorm.symm
  have hxS : x = (s : ℂ) := by
    rw [hx]
    exact_mod_cast hRatio
  have hζOne : ζ = 1 := by
    apply (mul_right_cancel₀ (by exact_mod_cast ne_of_gt hs : (s : ℂ) ≠ 0))
    simpa [x] using hxS
  intro L hL
  simpa [hζOne] using hGeo L hL

end EtaLocalStructureData

end MPOTensor
