/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.Irreducible.IrreducibleChannel
import TNLean.MPS.Transfer.Correlation.Correlations
import TNLean.MPS.CanonicalForm.Correlation.DecayingCorrelations
import TNLean.MPS.CanonicalForm.Correlation.WindowCorrelator
import TNLean.MPS.Transfer.Primitivity.Equivalence
import QICLean.Analysis.Norm.MatrixOperatorSpace

/-!
# Finite-size corrections to the correlator of a normal matrix product state

This file controls the difference between the connected correlator
`G_N(X,Y;s) = ⟨X_1 Y_s⟩ - ⟨X_1⟩⟨Y_s⟩` in the normalized vector `φ_N` and its limit
`Tr E_X((E_A - P)^{s-L-1}(E_Y(ρ)))`, for a normal tensor in the gauge
`∑ (A^i)† A^i = 1`, `E_A(ρ) = ρ`, `ρ > 0`, `Tr ρ = 1`. These are the finite-size
steps of the chapter's proof of `thm:ldp_decaying_correlations`, which make precise
the large-`N` limit in arXiv:2307.01696, Supplemental Material, proof of Lemma 2.

## Main declarations

* `exists_compl_pow_bound`: Gelfand decay of `E_A - P` in operator norm at every
  rate above `|λ₂|`.
* `mpvConnectedCorrelator_eq_of_compl`: the connected correlator written through
  powers of `E_A - P`.
* `Complex.norm_div_sub_div_mul_div_sub_le`: the algebraic perturbation estimate.
-/

open scoped Matrix BigOperators InnerProductSpace NNReal ENNReal ComplexOrder
  Matrix.Norms.Operator

namespace MPSTensor

variable {d D : ℕ}

/-! ### The limit correlator and finite-size corrections -/

/-- The limit correlator is bilinear in the observables. This is used for the
correlators of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem limitCorrelator_smul_smul (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (L : ℕ)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (a b : ℂ) (t : ℕ) :
    limitCorrelator A ρ htr L (a • X) (b • Y) t = a * b * limitCorrelator A ρ htr L X Y t := by
  simp only [limitCorrelator, physicalConnectedCorrelator, ← physicalObservableTransferₗ_apply,
    map_smul, ← smul_sub, LinearMap.smul_apply, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The limit correlator of the zero observable vanishes. This is used for the
correlators of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem limitCorrelator_zero_left (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (L : ℕ)
    (Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (t : ℕ) :
    limitCorrelator A ρ htr L 0 Y t = 0 := by
  simp [limitCorrelator, physicalConnectedCorrelator, ← physicalObservableTransferₗ_apply]

/-- The limit correlator of the zero observable vanishes. This is used for the
correlators of arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem limitCorrelator_zero_right (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (L : ℕ)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (t : ℕ) :
    limitCorrelator A ρ htr L X 0 t = 0 := by
  simp [limitCorrelator, physicalConnectedCorrelator, ← physicalObservableTransferₗ_apply]

/-- For `t + 1 ≤ s`, `e^{-(s-1)/ξ} ≤ |λ|^t`, where `ξ = -1/log|λ|` is the correlation
length (arXiv:2307.01696, Supplemental Material, Lemma 2, eq. (auxform2)). -/
theorem exp_neg_div_correlationLength_le_norm_pow {lam : ℂ} (hpos : 0 < ‖lam‖)
    (hlog : Real.log ‖lam‖ < 0) {t s : ℕ} (hts : t + 1 ≤ s) :
    Real.exp (-((s : ℝ) - 1) / correlationLength lam) ≤ ‖lam‖ ^ t := by
  have hξ' : -((s : ℝ) - 1) / correlationLength lam = ((s : ℝ) - 1) * Real.log ‖lam‖ := by
    unfold correlationLength
    field_simp
  rw [hξ', ← Real.exp_log (pow_pos hpos t), Real.log_pow, Real.exp_le_exp]
  have hts' : (t : ℝ) + 1 ≤ s := by exact_mod_cast hts
  nlinarith

/-- The powers of the complement `E_A - P` of the fixed-point projection decay at every
rate `r` above `|λ₂|` in operator norm.

This is the step "Gelfand's formula gives `‖(E_A - P)^n‖ ≤ C_r r^n`" of the chapter's
proof of `thm:ldp_decaying_correlations`, which makes precise the
expansion `E_1^{N-s-1} = |R_1⟩⟨L_1| + …` of arXiv:2307.01696, Supplemental Material,
proof of Lemma 2. -/
theorem exists_compl_pow_bound [NeZero D] {A : MPSTensor d D} {L : ℕ} (hL1 : 1 ≤ L)
    (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : Kraus.transferMap A ρ = ρ)
    (hρtr : Matrix.trace ρ = 1) (htr : Matrix.trace ρ ≠ 0) {lam₂ : ℂ}
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {r : ℝ} (hr : ‖lam₂‖ < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
        ((Kraus.transferMap A - fixedPointProj ρ htr) ^ k)‖ ≤ C * r ^ k := by
  classical
  set E := Kraus.transferMap A with hE_def
  set P := fixedPointProj ρ htr with hP_def
  set T := E - P with hT_def
  have hTP : IsTracePreservingMap E := Kraus.isTracePreservingMap_mapLM_of_isTP A hA
  have hr0 : 0 < r := (norm_nonneg _).trans_lt hr
  have hNormal : Kraus.IsNormal A := ⟨L, hL1, hL⟩
  have hPer : IsPrimitive (Kraus.transferMap A) :=
    isPrimitive_transferMap_of_isNormal A hA hNormal
  have hIrr : IsIrreducibleMap (Kraus.transferMap A) :=
    isIrreducibleMap_transferMap_of_isNormal A hNormal
  have hCh : IsChannel E := Kraus.isChannel_mapLM A hA
  obtain ⟨htr', hgap⟩ := spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
    E hCh hIrr hPer ρ hρ.posSemidef (fun h ↦ htr (by rw [h, Matrix.trace_zero])) hρfix
  let Φ : (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) :=
    Module.End.toContinuousLinearMap _
  have hPform : ∀ Z, P Z = Matrix.trace Z • ρ := fun Z ↦ by
    simp [hP_def, fixedPointProj, hρtr]
  have hPE : ∀ Z, P (E Z) = P Z := fun Z ↦ by rw [hPform, hPform, hTP Z]
  have hTeig : ∀ ν, Module.End.HasEigenvalue T ν → ‖ν‖ ≤ ‖lam₂‖ := by
    intro ν hν
    by_cases hν0 : ν = 0
    · rw [hν0, norm_zero]
      exact norm_nonneg _
    obtain ⟨w, hw⟩ := hν.exists_hasEigenvector
    have hTw : T w = ν • w := hw.apply_eq_smul
    have hPw : P w = 0 := by
      have h1 : P (T w) = 0 := by
        rw [hT_def, LinearMap.sub_apply, map_sub, hPE, hP_def, fixedPointProj_idempotent,
          sub_self]
      rw [hTw, map_smul] at h1
      exact (smul_eq_zero.mp h1).resolve_left hν0
    have hEw : E w = ν • w := by
      have h2 : E w = T w + P w := by rw [hT_def, LinearMap.sub_apply, sub_add_cancel]
      rw [h2, hTw, hPw, add_zero]
    have hEν : Module.End.HasEigenvalue E ν :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hEw, hw.2⟩
    have hν1 : ν ≠ 1 := by
      rintro rfl
      have hmem : (1 : ℂ) ∈ spectrum ℂ (Φ T) := by
        rw [AlgEquiv.spectrum_eq]
        exact hν.mem_spectrum
      have hle : ((‖(1 : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) ≤ spectralRadius ℂ (Φ T) :=
        le_iSup₂ (f := fun z (_ : z ∈ quasispectrum ℂ (Φ T)) ↦ ((‖z‖₊ : ℝ≥0) : ℝ≥0∞)) 1
          (spectrum_subset_quasispectrum ℂ (Φ T) hmem)
      rw [nnnorm_one, ENNReal.coe_one] at hle
      exact absurd (lt_of_le_of_lt hle hgap) (lt_irrefl 1)
    exact hmax ν hEν hν1
  have hspec : spectralRadius ℂ (Φ T) < (r.toNNReal : ℝ≥0∞) := by
    apply spectrum.spectralRadius_lt_of_forall_lt
    intro z hz
    rw [AlgEquiv.spectrum_eq] at hz
    have hz' : Module.End.HasEigenvalue T z := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.coe_toNNReal _ hr0.le]
    exact lt_of_le_of_lt (hTeig z hz') hr
  obtain ⟨C, hC0, hC⟩ := geometric_bound_of_spectralRadius_lt (Φ T) r.toNNReal hspec
  refine ⟨C, hC0, fun k ↦ ?_⟩
  have h1 := hC k
  simp only [Real.coe_toNNReal _ hr0.le] at h1
  rw [map_pow]
  exact h1

/-- The connected correlator on `N = L + t + L + n` sites, with `X` on the first `L`
sites and `Y` on the sites `L + t + 1, …, 2L + t`, written through the complement
`T = E_A - P` of the fixed-point projection. Here `α = Tr E_X(ρ)`,
`β = Tr E_Y(ρ)`, and the remainders are traces against powers of `T`.

This is the expansion of the connected correlator `Δ` in arXiv:2307.01696,
Supplemental Material, proof of Lemma 2, after substituting
`E_1^m = |R_1⟩⟨L_1| + (E_1 - |R_1⟩⟨L_1|)^m`. -/
theorem mpvConnectedCorrelator_eq_of_compl {A : MPSTensor d D} {L : ℕ}
    (hA : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρfix : Kraus.transferMap A ρ = ρ) (hρtr : Matrix.trace ρ = 1)
    (htr : Matrix.trace ρ ≠ 0) (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ)
    {t n : ℕ} (ht : 1 ≤ t) (hn : 1 ≤ n) :
    mpvConnectedCorrelator A (L + t + L + n) 0 (L + t) X Y =
      (Matrix.trace (physicalObservableTransfer A L X ρ) *
          Matrix.trace (physicalObservableTransfer A L Y ρ) +
          limitCorrelator A ρ htr L X Y t +
          LinearMap.trace ℂ _ (physicalObservableTransfer A L X * Kraus.transferMap A ^ t *
            physicalObservableTransfer A L Y *
            (Kraus.transferMap A - fixedPointProj ρ htr) ^ n)) /
        (1 + LinearMap.trace ℂ _ ((Kraus.transferMap A - fixedPointProj ρ htr) ^
          (L + t + L + n))) -
      (Matrix.trace (physicalObservableTransfer A L X ρ) +
          LinearMap.trace ℂ _ (physicalObservableTransfer A L X *
            (Kraus.transferMap A - fixedPointProj ρ htr) ^ (t + (L + n)))) /
        (1 + LinearMap.trace ℂ _ ((Kraus.transferMap A - fixedPointProj ρ htr) ^
          (L + t + L + n))) *
      ((Matrix.trace (physicalObservableTransfer A L Y ρ) +
          LinearMap.trace ℂ _ (physicalObservableTransfer A L Y *
            (Kraus.transferMap A - fixedPointProj ρ htr) ^ (n + (L + t)))) /
        (1 + LinearMap.trace ℂ _ ((Kraus.transferMap A - fixedPointProj ρ htr) ^
          (L + t + L + n)))) := by
  classical
  set E := Kraus.transferMap A with hE_def
  set P := fixedPointProj ρ htr with hP_def
  set T := E - P with hT_def
  have hTP : IsTracePreservingMap E := Kraus.isTracePreservingMap_mapLM_of_isTP A hA
  have hEk : ∀ k, 1 ≤ k → E ^ k = P + T ^ k := fun k hk ↦
    pow_eq_fixedPointProj_add_compl_pow E htr hTP hρfix hk
  have hPform : ∀ Z, P Z = Matrix.trace Z • ρ := fun Z ↦ by
    simp [hP_def, fixedPointProj, hρtr]
  have htrFP : ∀ F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      LinearMap.trace ℂ _ (F * P) = Matrix.trace (F ρ) := by
    intro F
    have hFP : F * P = (Matrix.traceLinearMap (Fin D) ℂ ℂ).smulRight (F ρ) := by
      apply LinearMap.ext
      intro Z
      rw [Module.End.mul_apply, hPform, map_smul, LinearMap.smulRight_apply,
        Matrix.traceLinearMap_apply]
    rw [hFP, LinearMap.trace_smulRight, Matrix.traceLinearMap_apply]
  have hP1 : LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) P = 1 := fixedPointProj_trace ρ htr
  have eXY := inner_mpvState_placeAlong_chainWindow_mul A t n X Y
  have eX := inner_mpvState_placeAlong_chainWindow_mul A t n X 1
  rw [ManyBody.placeAlong_one, mul_one, physicalObservableTransfer_one] at eX
  have eY := inner_mpvState_placeAlong_chainWindow_mul A t n 1 Y
  rw [ManyBody.placeAlong_one, one_mul, physicalObservableTransfer_one] at eY
  have eZ := inner_mpvState_placeAlong_chainWindow_mul A (L := L) t n 1 1
  rw [ManyBody.placeAlong_one, ManyBody.placeAlong_one, mul_one,
    physicalObservableTransfer_one] at eZ
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply] at eZ
  rw [mpvConnectedCorrelator, mpvExpectation_eq_div, mpvExpectation_eq_div,
    mpvExpectation_eq_div, eXY, eX, eY, eZ]
  have hZ : LinearMap.trace ℂ _ (E ^ L * E ^ t * E ^ L * E ^ n) =
      1 + LinearMap.trace ℂ _ (T ^ (L + t + L + n)) := by
    rw [← pow_add, ← pow_add, ← pow_add, hEk _ (by omega), map_add, hP1]
  have hX : LinearMap.trace ℂ _ (physicalObservableTransfer A L X * E ^ t * E ^ L * E ^ n) =
      Matrix.trace (physicalObservableTransfer A L X ρ) +
        LinearMap.trace ℂ _ (physicalObservableTransfer A L X * T ^ (t + (L + n))) := by
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, hEk _ (by omega), mul_add, map_add,
      htrFP]
  have hY : LinearMap.trace ℂ _ (E ^ L * E ^ t * physicalObservableTransfer A L Y * E ^ n) =
      Matrix.trace (physicalObservableTransfer A L Y ρ) +
        LinearMap.trace ℂ _ (physicalObservableTransfer A L Y * T ^ (n + (L + t))) := by
    rw [← pow_add, mul_assoc, LinearMap.trace_mul_comm, mul_assoc, ← pow_add,
      hEk _ (by omega), mul_add, map_add, htrFP]
  have hXY : LinearMap.trace ℂ _
      (physicalObservableTransfer A L X * E ^ t * physicalObservableTransfer A L Y * E ^ n) =
      Matrix.trace (physicalObservableTransfer A L X ρ) *
          Matrix.trace (physicalObservableTransfer A L Y ρ) +
        limitCorrelator A ρ htr L X Y t +
        LinearMap.trace ℂ _ (physicalObservableTransfer A L X * E ^ t *
          physicalObservableTransfer A L Y * T ^ n) := by
    rw [limitCorrelator_eq_compl_pow_of_pos A ρ htr hA hρfix L X Y ht,
      hEk n hn, mul_add, map_add, htrFP]
    congr 1
    simp only [Module.End.mul_apply, hEk t ht, LinearMap.add_apply, hPform, map_add,
      map_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  rw [hZ, hX, hY, hXY]

end MPSTensor
