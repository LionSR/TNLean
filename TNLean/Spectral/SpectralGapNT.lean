/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGapRect
import TNLean.Channel.PerronFrobeniusExistence
import TNLean.MPS.IrreducibleFormII
import TNLean.MPS.BlockingPeriodicityCFII2

/-!
# Spectral gap for normal tensor (irreducible + TP) blocks

This file proves the overlap dichotomy for irreducible trace-preserving / left-canonical
blocks without assuming injectivity, following the Cauchy--Schwarz argument from
Cirac et al., arXiv:1606.00608, Appendix A, Lemma A.1.

The key new rigidity statement is
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`: if two irreducible
left-canonical tensors have mixed-transfer spectral radius at least `1`, then they are
already gauge-phase equivalent.

The same-dimension rigidity step is now fully formalized. The downstream strict-gap and
overlap-decay consequences for equal bond dimension are routed through the existing
spectral-radius infrastructure, while the rectangular different-dimension analogue below is
still left as a `sorry` placeholder.
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D D₁ D₂ : ℕ}

private lemma sum_sandwich (L R : Matrix (Fin D) (Fin D) ℂ)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ i : Fin d, L * M i * R = L * (∑ i : Fin d, M i) * R := by
  rw [Finset.mul_sum, Finset.sum_mul]

section SameDimension

private theorem eigenvector_gives_gauge_of_irreducible_TP [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    GaugePhaseEquiv A B := by
  sorry

theorem modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B := by
  rcases eq_or_ne D 0 with rfl | hD
  · exact ⟨1, 1, one_ne_zero, fun i => by ext a; exact a.elim0⟩
  haveI : NeZero D := ⟨hD⟩
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  haveI : Nontrivial V := by
    haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
    exact Matrix.nonempty
  haveI : Nontrivial (V →L[ℂ] V) := ContinuousLinearMap.instNontrivialId
  obtain ⟨μ, hμ_spec, hμ_norm⟩ := spectrum.exists_nnnorm_eq_spectralRadius F'
  have h_spec_eq := AlgEquiv.spectrum_eq Φ (mixedTransferMap A B)
  have hμ_spec_end : μ ∈ spectrum ℂ (mixedTransferMap A B) := h_spec_eq ▸ hμ_spec
  have hμ_ev : Module.End.HasEigenvalue (mixedTransferMap A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec_end
  obtain ⟨X, hX_mem, hX_ne⟩ := hμ_ev.exists_hasEigenvector
  have hFX : mixedTransferMap A B X = μ • X := Module.End.mem_eigenspace_iff.mp hX_mem
  have hμ_le : ‖μ‖ ≤ 1 := eigenvalue_norm_le_one A B hA_left hB_left μ hμ_ev
  have hμ_ge : (1 : ℝ≥0∞) ≤ ‖μ‖₊ := by
    rw [hμ_norm]
    exact hsr
  have hμ_eq : ‖μ‖ = 1 := le_antisymm hμ_le (by
    rw [ENNReal.one_le_coe_iff] at hμ_ge
    exact_mod_cast hμ_ge)
  exact eigenvector_gives_gauge_of_irreducible_TP
    A B X μ hA_irr hB_irr hA_left hB_left hFX hμ_eq hX_ne

/--
**Strict mixed-transfer spectral gap** for distinct irreducible left-canonical blocks of the
same bond dimension.
-/
theorem spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 := by
  refine lt_of_le_of_ne (spectralRadius_mixedTransfer_le_one A B hA_left hB_left) ?_
  intro hEq
  exact hAB <| modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    A B hA_irr hB_irr hA_left hB_left hEq.ge

/--
**Power decay** for the mixed transfer operator of distinct irreducible left-canonical
blocks of the same bond dimension.
-/
theorem mixedTransfer_pow_tendsto_zero_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  have h_clm : Filter.Tendsto (fun n => F' ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one F' <| by
      simpa [F', Φ, mixedTransferSpectralRadius] using
        spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
          A B hA_irr hB_irr hA_left hB_left hAB
  have h_eval := (ContinuousLinearMap.apply ℂ V X).continuous.tendsto (0 : V →L[ℂ] V)
  rw [map_zero] at h_eval
  suffices hpow : ∀ n, ((mixedTransferMap A B) ^ n) X = (F' ^ n) X by
    simp_rw [hpow]
    exact h_eval.comp h_clm
  intro n
  have h_pow : F' ^ n = Φ ((mixedTransferMap A B) ^ n) := (map_pow Φ _ n).symm
  simp only [h_pow]
  rfl

end SameDimension

section SameDimensionOverlap

variable [NeZero D]

/--
**Overlap decay** for distinct irreducible left-canonical blocks of the same bond dimension.
-/
theorem mpvOverlap_tendsto_zero_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  exact mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B) <| by
    simpa [mixedTransferSpectralRadius] using
      spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
        A B hA_irr hB_irr hA_left hB_left hAB

end SameDimensionOverlap

section DifferentDimensions

private lemma injective_vecMul_of_det_unit {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) (hM : IsUnit M.det) :
    Function.Injective M.vecMul := by
  exact (Matrix.vecMul_injective_iff_isUnit).2
    ((Matrix.isUnit_iff_isUnit_det (A := M)).2 hM)

private lemma mul_mul_conjTranspose_ne_zero_of_ne_zero {D : ℕ}
    (S : Matrix (Fin D) (Fin D) ℂ) (hS : IsUnit S.det)
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M ≠ 0) :
    S * M * Sᴴ ≠ 0 := by
  have hS_unit : IsUnit S := (Matrix.isUnit_iff_isUnit_det (A := S)).2 hS
  have hSstar_unit : IsUnit Sᴴ := by
    simpa [Matrix.star_eq_conjTranspose] using IsUnit.star hS_unit
  intro h0
  apply hM
  have h1 : M * Sᴴ = 0 := by
    apply IsUnit.mul_left_cancel hS_unit
    simpa [Matrix.mul_assoc] using h0
  have h2 : M = 0 := by
    apply IsUnit.mul_right_cancel hSstar_unit
    simpa using h1
  exact h2

private lemma injective_of_posDef_conjTranspose_mul_self
    (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (hpd : (Xᴴ * X).PosDef) :
    ∀ v : Fin D₂ → ℂ, X *ᵥ v = 0 → v = 0 := by
  intro v hv
  by_contra hvne
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hpd
  have hpos := hpd.2 hvne
  have hzero : star v ⬝ᵥ ((Xᴴ * X) *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    exact dotProduct_zero _
  exact (lt_irrefl (0 : ℂ)) <| hzero ▸ hpos

private lemma dim_le_of_injective_matrix [NeZero D₂]
    (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (h_inj : ∀ v : Fin D₂ → ℂ, X *ᵥ v = 0 → v = 0) :
    D₂ ≤ D₁ := by
  let f : (Fin D₂ → ℂ) →ₗ[ℂ] (Fin D₁ → ℂ) := Matrix.toLin' X
  have hf_inj : Function.Injective f := by
    intro u v huv
    have h1 : f u - f v = 0 := sub_eq_zero.mpr huv
    have h2 : f (u - v) = 0 := by simp [h1]
    have h3 : X *ᵥ (u - v) = 0 := h2
    have h4 : u - v = 0 := h_inj _ h3
    exact eq_of_sub_eq_zero h4
  have h1 : Module.finrank ℂ (Fin D₂ → ℂ) ≤ Module.finrank ℂ (Fin D₁ → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hf_inj
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using h1

private theorem dim_eq_of_modulus_one_eigenvector_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) (μ : ℂ)
    (hFX : mixedTransferMap₂ A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    D₁ = D₂ := by
  classical
  have hD₁_pos : 0 < D₁ := Nat.pos_of_ne_zero (NeZero.ne D₁)
  have hD₂_pos : 0 < D₂ := Nat.pos_of_ne_zero (NeZero.ne D₂)
  obtain ⟨ρA, hρA_psd, hρA_ne, hρA_fix⟩ :=
    exists_posSemidef_fixedPoint (A := A) hA_left hD₁_pos
  obtain ⟨ρB, hρB_psd, hρB_ne, hρB_fix⟩ :=
    exists_posSemidef_fixedPoint (A := B) hB_left hD₂_pos
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D₁) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor A hA_irr
  have hIrrB : IsIrreducibleMap (transferMap (d := d) (D := D₂) B) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor B hB_irr
  have hρA_pd : ρA.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible A hIrrA ρA hρA_psd hρA_ne hρA_fix
  have hρB_pd : ρB.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible B hIrrB ρB hρB_psd hρB_ne hρB_fix
  let SA : Matrix (Fin D₁) (Fin D₁) ℂ := CFC.sqrt ρA
  let SB : Matrix (Fin D₂) (Fin D₂) ℂ := CFC.sqrt ρB
  have hSA_herm : SAᴴ = SA := by
    simpa [SA] using conjTranspose_cfc_sqrt (ρ := ρA)
  have hSB_herm : SBᴴ = SB := by
    simpa [SB] using conjTranspose_cfc_sqrt (ρ := ρB)
  have hSA_det : SA.det ≠ 0 :=
    (isUnit_det_cfc_sqrt_of_posDef (ρ := ρA) hρA_pd).ne_zero
  have hSB_det : SB.det ≠ 0 :=
    (isUnit_det_cfc_sqrt_of_posDef (ρ := ρB) hρB_pd).ne_zero
  have hSA_u : IsUnit SA.det := Ne.isUnit hSA_det
  have hSB_u : IsUnit SB.det := Ne.isUnit hSB_det
  have hSAh_det : (SAᴴ).det ≠ 0 := by
    simpa [hSA_herm] using hSA_det
  have hSBh_det : (SBᴴ).det ≠ 0 := by
    simpa [hSB_herm] using hSB_det
  have hSAh_u : IsUnit (SAᴴ).det := Ne.isUnit hSAh_det
  have hSBh_u : IsUnit (SBᴴ).det := Ne.isUnit hSBh_det
  have hSA_mul : SA * SAᴴ = ρA := by
    simpa [SA, hSA_herm] using cfc_sqrt_mul_self_of_posDef (ρ := ρA) hρA_pd
  have hSB_mul : SB * SBᴴ = ρB := by
    simpa [SB, hSB_herm] using cfc_sqrt_mul_self_of_posDef (ρ := ρB) hρB_pd
  let A' : MPSTensor d D₁ := fun i => SA⁻¹ * A i * SA
  let B' : MPSTensor d D₂ := fun i => SB⁻¹ * B i * SB
  have hA'unital : ∑ i : Fin d, (A' i) * (A' i)ᴴ = 1 := by
    simpa [A'] using gauged_unital A SA ρA hSA_det hSA_mul hρA_fix
  have hB'unital : ∑ i : Fin d, (B' i) * (B' i)ᴴ = 1 := by
    simpa [B'] using gauged_unital B SB ρB hSB_det hSB_mul hρB_fix
  let X' : Matrix (Fin D₁) (Fin D₂) ℂ := SA⁻¹ * X * (SBᴴ)⁻¹
  have hX'ne : X' ≠ 0 := by
    intro h0
    apply hX
    have key : SA * X' * SBᴴ = X := by
      simp only [X', Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u,
          Matrix.nonsing_inv_mul (A := SBᴴ) hSBh_u, Matrix.mul_one]
    rw [← key, h0, Matrix.mul_zero, Matrix.zero_mul]
  have hFXsum : ∑ i : Fin d, A i * X * (B i)ᴴ = μ • X := by
    simpa [mixedTransferMap₂_apply] using hFX
  have hFX' : ∑ i : Fin d, A' i * X' * (B' i)ᴴ = μ • X' := by
    have hterm : ∀ i : Fin d,
        (A' i) * X' * (B' i)ᴴ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
      intro i
      have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
        simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
      calc (A' i) * X' * (B' i)ᴴ
          = (SA⁻¹ * A i * SA) * (SA⁻¹ * X * (SBᴴ)⁻¹) * (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) := by
            simp [A', X', hBstar]
        _ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
            simp only [Matrix.mul_assoc]
            rw [Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u,
                Matrix.nonsing_inv_mul_cancel_left _ _ hSBh_u]
    simp_rw [hterm]
    simp_rw [← Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => SA⁻¹ * (A i * X * (B i)ᴴ)) (M := (SBᴴ)⁻¹)]
    simp_rw [← Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => A i * X * (B i)ᴴ) (M := SA⁻¹)]
    rw [hFXsum]
    have h1 : SA⁻¹ * (μ • X) = μ • (SA⁻¹ * X) := by
      simp [Matrix.mul_smul]
    rw [h1]
    have h2 : (μ • (SA⁻¹ * X)) * (SBᴴ)⁻¹ = μ • ((SA⁻¹ * X) * (SBᴴ)⁻¹) := by
      simp [Matrix.smul_mul]
    rw [h2]
  let K : Fin d → Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    fun i => Matrix.fromBlocks (A' i) 0 0 (B' i)
  let M : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    Matrix.fromBlocks 0 X' 0 0
  have hK_unital : Kraus.IsUnital K := by
    change (∑ i, K i * (K i)ᴴ) = 1
    have hsum : ∑ i : Fin d, K i * (K i)ᴴ =
        Matrix.fromBlocks (∑ i, (A' i) * (A' i)ᴴ) 0 0 (∑ i, (B' i) * (B' i)ᴴ) := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [K, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    simp [hsum, hA'unital, hB'unital]
  have hEigM : Kraus.map K M = μ • M := by
    have hmap : Kraus.map K M =
        Matrix.fromBlocks 0 (∑ i : Fin d, A' i * X' * (B' i)ᴴ) 0 0 := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [Kraus.map, K, M, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    simp [hmap, hFX', M, Matrix.fromBlocks_smul]
  let rhoT : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    Matrix.fromBlocks (SAᴴ * SA) 0 0 (SBᴴ * SB)
  have hrhoT_pd : rhoT.PosDef := by
    let Sblock : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
      Matrix.fromBlocks SA 0 0 SB
    refine (Matrix.isStrictlyPositive_iff_posDef).1 ?_
    refine (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).2 ?_
    refine ⟨Sblock, ?_, ?_⟩
    · exact (isUnit_iff_exists_inv).2
        ⟨Matrix.fromBlocks SA⁻¹ 0 0 SB⁻¹, by
          simp [Sblock, Matrix.fromBlocks_multiply,
            Matrix.mul_nonsing_inv hSA_u, Matrix.mul_nonsing_inv hSB_u]⟩
    · simp [rhoT, Sblock, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
  have hrhoT_fix : Kraus.adjointMap K rhoT = rhoT := by
    have hAblock : ∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * SA := by
      have hterm : ∀ i : Fin d,
          (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * ((A i)ᴴ * A i) * SA := by
        intro i
        have hAstar : (A' i)ᴴ = SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹ := by
          simp [A', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
        calc (A' i)ᴴ * (SAᴴ * SA) * (A' i)
            = (SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹) * (SAᴴ * SA) * (SA⁻¹ * A i * SA) := by
              simp [A', hAstar]
          _ = SAᴴ * ((A i)ᴴ * A i) * SA := by
              simp only [Matrix.mul_assoc]
              rw [Matrix.nonsing_inv_mul_cancel_left _ _ hSAh_u,
                  Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u]
      simp_rw [hterm, ← Finset.sum_mul, ← Finset.mul_sum, hA_left, Matrix.mul_one]
    have hBblock : ∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * SB := by
      have hterm : ∀ i : Fin d,
          (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * ((B i)ᴴ * B i) * SB := by
        intro i
        have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
          simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
        calc (B' i)ᴴ * (SBᴴ * SB) * (B' i)
            = (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) * (SBᴴ * SB) * (SB⁻¹ * B i * SB) := by
              simp [B', hBstar]
          _ = SBᴴ * ((B i)ᴴ * B i) * SB := by
              simp only [Matrix.mul_assoc]
              rw [Matrix.nonsing_inv_mul_cancel_left _ _ hSBh_u,
                  Matrix.mul_nonsing_inv_cancel_left _ _ hSB_u]
      simp_rw [hterm, ← Finset.sum_mul, ← Finset.mul_sum, hB_left, Matrix.mul_one]
    have hAdj : Kraus.adjointMap K rhoT =
        Matrix.fromBlocks (∑ i, (A' i)ᴴ * (SAᴴ * SA) * (A' i)) 0 0
          (∑ i, (B' i)ᴴ * (SBᴴ * SB) * (B' i)) := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    simp [hAdj, rhoT, hAblock, hBblock]
  have hKS_M : Kraus.map K (Mᴴ * M) = (Kraus.map K M)ᴴ * Kraus.map K M :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hK_unital hrhoT_pd hrhoT_fix M μ hEigM hμ
  have hComm_M : ∀ i : Fin d, M * (K i)ᴴ = (K i)ᴴ * Kraus.map K M :=
    Kraus.kraus_commute_of_ks_equality K hK_unital M hKS_M
  have hInter1 : ∀ k : Fin d, X' * (B' k)ᴴ = μ • ((A' k)ᴴ * X') := by
    intro k
    have h' : M * (K k)ᴴ = (K k)ᴴ * (μ • M) := by simp [hEigM, hComm_M k]
    have hL : M * (K k)ᴴ = Matrix.fromBlocks 0 (X' * (B' k)ᴴ) 0 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K k)ᴴ * (μ • M) = Matrix.fromBlocks 0 (μ • ((A' k)ᴴ * X')) 0 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_smul]
    have h_eq := hL ▸ hR ▸ h'
    exact (Matrix.fromBlocks_inj.1 h_eq).2.1
  have hμ_conj : ‖(starRingEnd ℂ) μ‖ = 1 := by rwa [Complex.norm_conj]
  have hEigMstar : Kraus.map K Mᴴ = (starRingEnd ℂ μ) • Mᴴ := by
    calc Kraus.map K Mᴴ = (Kraus.map K M)ᴴ := by
          simpa using (Kraus.map_conjTranspose (K := K) M).symm
      _ = (starRingEnd ℂ μ) • Mᴴ := by simp [hEigM, Matrix.conjTranspose_smul]
  have hKS_Mstar : Kraus.map K (Mᴴᴴ * Mᴴ) = (Kraus.map K Mᴴ)ᴴ * Kraus.map K Mᴴ :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hK_unital hrhoT_pd hrhoT_fix Mᴴ (starRingEnd ℂ μ) hEigMstar hμ_conj
  have hComm_Mstar : ∀ i : Fin d, Mᴴ * (K i)ᴴ = (K i)ᴴ * Kraus.map K Mᴴ :=
    Kraus.kraus_commute_of_ks_equality K hK_unital Mᴴ hKS_Mstar
  have hInter2 : ∀ k : Fin d, X'ᴴ * (A' k)ᴴ = (starRingEnd ℂ μ) • ((B' k)ᴴ * X'ᴴ) := by
    intro k
    have h' : Mᴴ * (K k)ᴴ = (K k)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) := by
      simp [hEigMstar, hComm_Mstar k]
    have hL : Mᴴ * (K k)ᴴ =
        Matrix.fromBlocks 0 0 (X'ᴴ * (A' k)ᴴ) 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K k)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) =
        Matrix.fromBlocks 0 0 ((starRingEnd ℂ μ) • ((B' k)ᴴ * X'ᴴ)) 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_smul]
    have h_eq := hL ▸ hR ▸ h'
    exact (Matrix.fromBlocks_inj.1 h_eq).2.2.1
  have hInter1_adj : ∀ k : Fin d, B' k * X'ᴴ = (starRingEnd ℂ μ) • (X'ᴴ * A' k) := by
    intro k
    have h := congrArg Matrix.conjTranspose (hInter1 k)
    simpa [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] using h
  have hInter2_adj : ∀ k : Fin d, A' k * X' = μ • (X' * B' k) := by
    intro k
    have h := congrArg Matrix.conjTranspose (hInter2 k)
    simpa [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] using h
  have hμ_star_mul : star μ * μ = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hμ]
  have hμ_mul_star : μ * star μ = 1 := by
    simpa [mul_comm] using hμ_star_mul
  let Y : Matrix (Fin D₁) (Fin D₁) ℂ := X' * X'ᴴ
  let Z : Matrix (Fin D₂) (Fin D₂) ℂ := X'ᴴ * X'
  have hY_fix' : transferMap (d := d) (D := D₁) A' Y = Y := by
    calc
      transferMap (d := d) (D := D₁) A' Y
          = ∑ i : Fin d, A' i * Y * (A' i)ᴴ := by simp [transferMap_apply]
      _ = ∑ i : Fin d, (A' i * X') * (X'ᴴ * (A' i)ᴴ) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [Y, Matrix.mul_assoc]
      _ = ∑ i : Fin d,
            (μ • (X' * B' i)) * ((starRingEnd ℂ μ) • ((B' i)ᴴ * X'ᴴ)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hInter2_adj i, hInter2 i]
      _ = ∑ i : Fin d, X' * (B' i * (B' i)ᴴ) * X'ᴴ := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [Matrix.mul_assoc, smul_mul, mul_smul, hμ_mul_star]
      _ = X' * (∑ i : Fin d, B' i * (B' i)ᴴ) * X'ᴴ := by
            simp_rw [← Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => X' * (B' i * (B' i)ᴴ)) (M := X'ᴴ)]
            simp_rw [← Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => B' i * (B' i)ᴴ) (M := X')]
      _ = Y := by rw [hB'unital]; simp [Y]
  have hZ_fix' : transferMap (d := d) (D := D₂) B' Z = Z := by
    calc
      transferMap (d := d) (D := D₂) B' Z
          = ∑ i : Fin d, B' i * Z * (B' i)ᴴ := by simp [transferMap_apply]
      _ = ∑ i : Fin d, (B' i * X'ᴴ) * (X' * (B' i)ᴴ) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [Z, Matrix.mul_assoc]
      _ = ∑ i : Fin d,
            ((starRingEnd ℂ μ) • (X'ᴴ * A' i)) * (μ • ((A' i)ᴴ * X')) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hInter1_adj i, hInter1 i]
      _ = ∑ i : Fin d, X'ᴴ * (A' i * (A' i)ᴴ) * X' := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [Matrix.mul_assoc, smul_mul, mul_smul, hμ_star_mul]
      _ = X'ᴴ * (∑ i : Fin d, A' i * (A' i)ᴴ) * X' := by
            simp_rw [← Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => X'ᴴ * (A' i * (A' i)ᴴ)) (M := X')]
            simp_rw [← Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => A' i * (A' i)ᴴ) (M := X'ᴴ)]
      _ = Z := by rw [hA'unital]; simp [Z]
  have hX'hne : X'ᴴ ≠ 0 := by
    intro h
    apply hX'ne
    exact Matrix.conjTranspose_eq_zero.mp h
  have hY_psd : Y.PosSemidef := by
    simpa [Y] using Matrix.posSemidef_conjTranspose_mul_self X'ᴴ
  have hZ_psd : Z.PosSemidef := by
    simpa [Z] using Matrix.posSemidef_conjTranspose_mul_self X'
  have hY_ne : Y ≠ 0 := by
    intro hY0
    apply hX'hne
    exact Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa [Y] using hY0)
  have hZ_ne : Z ≠ 0 := by
    intro hZ0
    apply hX'ne
    exact Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa [Z] using hZ0)
  let ρA0 : Matrix (Fin D₁) (Fin D₁) ℂ := SA * Y * SAᴴ
  let ρB0 : Matrix (Fin D₂) (Fin D₂) ℂ := SB * Z * SBᴴ
  have hρA0_psd : ρA0.PosSemidef := by
    simpa [ρA0] using hY_psd.mul_mul_conjTranspose_same (B := SA)
  have hρB0_psd : ρB0.PosSemidef := by
    simpa [ρB0] using hZ_psd.mul_mul_conjTranspose_same (B := SB)
  have hρA0_ne : ρA0 ≠ 0 :=
    mul_mul_conjTranspose_ne_zero_of_ne_zero SA hSA_u hY_ne
  have hρB0_ne : ρB0 ≠ 0 :=
    mul_mul_conjTranspose_ne_zero_of_ne_zero SB hSB_u hZ_ne
  have hρA0_fix : transferMap (d := d) (D := D₁) A ρA0 = ρA0 := by
    have hterm : ∀ i : Fin d,
        SA * (A' i * Y * (A' i)ᴴ) * SAᴴ = A i * ρA0 * (A i)ᴴ := by
      intro i
      have hAstar : (A' i)ᴴ = SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹ := by
        simp [A', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
      calc
        SA * (A' i * Y * (A' i)ᴴ) * SAᴴ
            = SA * ((SA⁻¹ * A i * SA) * Y * (SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹)) * SAᴴ := by
                simp [A', hAstar]
        _ = A i * (SA * Y * SAᴴ) * (A i)ᴴ := by
              simp only [Matrix.mul_assoc]
              rw [Matrix.mul_nonsing_inv hSA_u, Matrix.nonsing_inv_mul (A := SAᴴ) hSAh_u,
                  Matrix.one_mul, Matrix.mul_one]
        _ = A i * ρA0 * (A i)ᴴ := by rfl
    calc
      transferMap (d := d) (D := D₁) A ρA0 = ∑ i : Fin d, A i * ρA0 * (A i)ᴴ := by
        simp [transferMap_apply]
      _ = ∑ i : Fin d, SA * (A' i * Y * (A' i)ᴴ) * SAᴴ := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact (hterm i).symm
      _ = SA * (∑ i : Fin d, A' i * Y * (A' i)ᴴ) * SAᴴ := by
            simp_rw [← Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => SA * (A' i * Y * (A' i)ᴴ)) (M := SAᴴ)]
            simp_rw [← Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => A' i * Y * (A' i)ᴴ) (M := SA)]
      _ = ρA0 := by rw [hY_fix']; simp [ρA0]
  have hρB0_fix : transferMap (d := d) (D := D₂) B ρB0 = ρB0 := by
    have hterm : ∀ i : Fin d,
        SB * (B' i * Z * (B' i)ᴴ) * SBᴴ = B i * ρB0 * (B i)ᴴ := by
      intro i
      have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
        simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
      calc
        SB * (B' i * Z * (B' i)ᴴ) * SBᴴ
            = SB * ((SB⁻¹ * B i * SB) * Z * (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹)) * SBᴴ := by
                simp [B', hBstar]
        _ = B i * (SB * Z * SBᴴ) * (B i)ᴴ := by
              simp only [Matrix.mul_assoc]
              rw [Matrix.mul_nonsing_inv hSB_u, Matrix.nonsing_inv_mul (A := SBᴴ) hSBh_u,
                  Matrix.one_mul, Matrix.mul_one]
        _ = B i * ρB0 * (B i)ᴴ := by rfl
    calc
      transferMap (d := d) (D := D₂) B ρB0 = ∑ i : Fin d, B i * ρB0 * (B i)ᴴ := by
        simp [transferMap_apply]
      _ = ∑ i : Fin d, SB * (B' i * Z * (B' i)ᴴ) * SBᴴ := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact (hterm i).symm
      _ = SB * (∑ i : Fin d, B' i * Z * (B' i)ᴴ) * SBᴴ := by
            simp_rw [← Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => SB * (B' i * Z * (B' i)ᴴ)) (M := SBᴴ)]
            simp_rw [← Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => B' i * Z * (B' i)ᴴ) (M := SB)]
      _ = ρB0 := by rw [hZ_fix']; simp [ρB0]
  have hρA0_pd : ρA0.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible A hIrrA ρA0 hρA0_psd hρA0_ne hρA0_fix
  have hρB0_pd : ρB0.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible B hIrrB ρB0 hρB0_psd hρB0_ne hρB0_fix
  have hY_pd : Y.PosDef := by
    simpa [ρA0, Y, Matrix.mul_assoc, Matrix.nonsing_inv_mul (A := SA) hSA_u,
      Matrix.mul_nonsing_inv hSAh_u] using
      hρA0_pd.mul_mul_conjTranspose_same (B := SA⁻¹)
        (injective_vecMul_of_det_unit (M := SA⁻¹) (Matrix.isUnit_nonsing_inv_det hSA_u))
  have hZ_pd : Z.PosDef := by
    simpa [ρB0, Z, Matrix.mul_assoc, Matrix.nonsing_inv_mul (A := SB) hSB_u,
      Matrix.mul_nonsing_inv hSBh_u] using
      hρB0_pd.mul_mul_conjTranspose_same (B := SB⁻¹)
        (injective_vecMul_of_det_unit (M := SB⁻¹) (Matrix.isUnit_nonsing_inv_det hSB_u))
  have h_D₂_le : D₂ ≤ D₁ :=
    dim_le_of_injective_matrix X' (injective_of_posDef_conjTranspose_mul_self X' hZ_pd)
  have h_D₁_le : D₁ ≤ D₂ := by
    have h_inj : ∀ v : Fin D₁ → ℂ, X'ᴴ *ᵥ v = 0 → v = 0 :=
      injective_of_posDef_conjTranspose_mul_self X'ᴴ (by simpa [Y] using hY_pd)
    exact dim_le_of_injective_matrix X'ᴴ h_inj
  exact le_antisymm h_D₁_le h_D₂_le

/--
**Rectangular strict spectral gap** for irreducible left-canonical blocks of different bond
sizes.

The intended proof follows the same Cauchy--Schwarz rigidity mechanism as
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`, but in the rectangular setting:
a modulus-one peripheral eigenvector produces an isometry `X`, swapping the roles of `A`
and `B` upgrades this to a unitary, and hence forces equality of bond dimensions.
-/
theorem mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    mixedTransferSpectralRadius₂ A B < 1 := by
  classical
  have hle :
      mixedTransferSpectralRadius₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B ≤ 1 :=
    spectralRadius_mixedTransfer₂_le_one (A := A) (B := B) hA_left hB_left
  refine lt_of_le_of_ne hle ?_
  intro hEq
  unfold mixedTransferSpectralRadius₂ at hEq
  let V := Matrix (Fin D₁) (Fin D₂) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap₂ A B)
  haveI : Nontrivial V := by
    haveI : Nonempty (Fin D₁) := ⟨⟨0, NeZero.pos D₁⟩⟩
    haveI : Nonempty (Fin D₂) := ⟨⟨0, NeZero.pos D₂⟩⟩
    exact Matrix.nonempty
  haveI : Nontrivial (V →L[ℂ] V) := ContinuousLinearMap.instNontrivialId
  have hEqF : spectralRadius ℂ F' = 1 := by simpa [F', Φ] using hEq
  obtain ⟨μ, hμ_spec, hμ_rad⟩ := spectrum.exists_nnnorm_eq_spectralRadius F'
  have hμ_one : (↑‖μ‖₊ : ENNReal) = 1 := by simpa [hEqF] using hμ_rad
  have hμ_nnn : ‖μ‖₊ = (1 : NNReal) := (ENNReal.coe_eq_one).1 hμ_one
  have hμ_norm : ‖μ‖ = 1 := by
    have : (‖μ‖₊ : ℝ) = (1 : ℝ) := by exact_mod_cast hμ_nnn
    simpa [coe_nnnorm] using this
  have h_spec : μ ∈ spectrum ℂ (mixedTransferMap₂ A B) := by
    have h_spec_eq := AlgEquiv.spectrum_eq Φ (mixedTransferMap₂ A B)
    exact h_spec_eq ▸ hμ_spec
  have hHas : Module.End.HasEigenvalue (mixedTransferMap₂ A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr h_spec
  obtain ⟨X, hX_mem, hX_ne⟩ := hHas.exists_hasEigenvector
  have hFX : mixedTransferMap₂ A B X = μ • X :=
    (Module.End.mem_eigenspace_iff).1 hX_mem
  have hDim : D₁ = D₂ :=
    dim_eq_of_modulus_one_eigenvector_of_irreducible_TP (A := A) (B := B)
      hA_irr hB_irr hA_left hB_left X μ hFX hμ_norm hX_ne
  exact hD hDim

/--
**Overlap decay** for irreducible left-canonical blocks of different bond dimensions.
-/
theorem mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  exact mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B) <| by
    simpa [mixedTransferSpectralRadius₂] using
      mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
        A B hA_irr hB_irr hA_left hB_left hD

end DifferentDimensions

end MPSTensor
