/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.IrreducibleChannel
import TNLean.Algebra.ExponentialSumWindow
import TNLean.MPS.Core.Correlations
import TNLean.MPS.Preparation.CorrelatorFiniteSize
import TNLean.Wielandt.Primitivity.Equivalence

/-!
# Exponentially decaying correlations of a normal matrix product state

This file proves the correlation estimate of arXiv:2307.01696, Supplemental
Material, Lemma 2, in the form of the chapter entry
`thm:ldp_decaying_correlations`: for a normal tensor with correlation length
`ξ > 0`, in the gauge `∑ (A^i)† A^i = 1`, `E_A(ρ) = ρ`, `ρ > 0`, `Tr ρ = 1`,
there are Hermitian observables `O, O'` of norm one on `L` sites and constants
`c > 0`, `K ∈ {1, 2}`, `s₀` such that every window of `K` consecutive
separations `s ≥ s₀` contains an `s'` with `|G_N(O,O';s')| ≥ c e^{-(s'-1)/ξ}`
for every `N ≥ 3s'`.

The observables are chosen from an eigenvector of the transfer map for the
subleading eigenvalue `λ₂`. The map `E_A - P` preserves Hermitian matrices, so a
Hermitian vector `v` and a Hermitian functional `ℓ` can be chosen with
`ℓ((E_A - P)^t v) = λ₂^t` when `λ₂` is real and `λ₂^t + conj(λ₂)^t` otherwise.
The limit correlator is then an exponential sum with at most two unimodular
frequencies, and the Vandermonde window estimate bounds it below at one of any
`K` consecutive separations. The finite-size corrections are controlled by
Gelfand's formula for `E_A - P`, whose spectral radius is `|λ₂|`, in
`TNLean.MPS.Preparation.CorrelatorFiniteSize`.

## Main declarations

* `exists_isHermitian_physicalObservableTransfer_eq`: Hermitian observables
  realize every map preserving Hermitian matrices.
* `exists_hermitian_vector_functional_compl_pow`: the Hermitian vector and functional.
* `exists_decayingCorrelations`: the chapter statement.
-/

open scoped Matrix BigOperators InnerProductSpace NNReal ENNReal ComplexOrder
  Matrix.Norms.Operator

namespace MPSTensor

variable {d D : ℕ}

/-! ### Hermitian observables -/

/-- The inserted transfer map of the adjoint observable is `E_{X†}(Z) = E_X(Z†)†`.
This is the reality of the maps `E_O` of Hermitian observables used in
arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem physicalObservableTransfer_conjTranspose (A : MPSTensor d D) (L : ℕ)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (Z : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A L Xᴴ Z = (physicalObservableTransfer A L X Zᴴ)ᴴ := by
  simp only [physicalObservableTransfer, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply, Matrix.mul_assoc]
  rw [Finset.sum_comm]

/-- Every linear map preserving Hermitian matrices is the inserted transfer map of a
Hermitian observable on `L` sites, provided the products of `L` matrices of `A`
span the matrix algebra. This is the choice of Hermitian `O, O'` with prescribed
`E_O` in arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem exists_isHermitian_physicalObservableTransfer_eq {A : MPSTensor d D} {L : ℕ}
    (hL : Kraus.IsNBlkInjective A L)
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hΦ : ∀ Z, Φ Zᴴ = (Φ Z)ᴴ) :
    ∃ X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ, X.IsHermitian ∧
      physicalObservableTransfer A L X = Φ := by
  obtain ⟨X₀, hX₀⟩ := exists_physicalObservableTransfer_eq hL Φ
  refine ⟨(1 / 2 : ℂ) • (X₀ + X₀ᴴ), ?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  · apply LinearMap.ext
    intro Z
    rw [← physicalObservableTransferₗ_apply, map_smul, map_add, LinearMap.smul_apply,
      LinearMap.add_apply, physicalObservableTransferₗ_apply, physicalObservableTransferₗ_apply,
      physicalObservableTransfer_conjTranspose, hX₀, hΦ, Matrix.conjTranspose_conjTranspose,
      ← two_smul ℂ (Φ Z), smul_smul]
    norm_num

/-! ### The transfer map on Hermitian matrices and on its eigenvectors -/

/-- An eigenvector of a trace-preserving transfer map for an eigenvalue other than `1`
is traceless. This is used for the correlators of arXiv:2307.01696, Supplemental
Material, proof of Lemma 2. -/
theorem trace_eq_zero_of_transferMap_eq_smul {A : MPSTensor d D}
    (hA : ∑ i, (A i)ᴴ * A i = 1) {R : Matrix (Fin D) (Fin D) ℂ} {lam : ℂ}
    (hR : Kraus.transferMap A R = lam • R) (hlam : lam ≠ 1) : Matrix.trace R = 0 := by
  have h : Matrix.trace (Kraus.transferMap A R) = Matrix.trace R :=
    Kraus.isTracePreservingMap_mapLM_of_isTP A hA R
  rw [hR, Matrix.trace_smul, smul_eq_mul] at h
  have : (lam - 1) * Matrix.trace R = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hlam)

/-- On an eigenvector for an eigenvalue other than `1`, the complement `E_A - P` of the
fixed-point projection acts as the eigenvalue. This is used for the correlators of
arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem compl_pow_apply_of_transferMap_eq_smul {A : MPSTensor d D}
    (hA : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (htr : Matrix.trace ρ ≠ 0) {R : Matrix (Fin D) (Fin D) ℂ} {lam : ℂ}
    (hR : Kraus.transferMap A R = lam • R) (hlam : lam ≠ 1) (t : ℕ) :
    ((Kraus.transferMap A - fixedPointProj ρ htr) ^ t) R = lam ^ t • R := by
  have htrR := trace_eq_zero_of_transferMap_eq_smul hA hR hlam
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hR]
    simp [fixedPointProj, htrR, smul_smul, pow_succ, mul_comm]

/-- A Hermitian vector and a Hermitian linear functional whose pairing along the powers
of `E_A - P` is an exponential sum with at most two unimodular frequencies at the
rate `|λ|`. For real `λ` it is `λ^t`, for non-real `λ` it is `λ^t + conj(λ)^t`.

This replaces the choice "`⟨L_1|E_O|R_2⟩⟨L_2|E_{O'}|R_1⟩ = c' > 0`" of arXiv:2307.01696,
Supplemental Material, proof of Lemma 2, by one compatible with Hermitian
observables: for non-real `λ₂` the eigenvector `R_2` is not Hermitian, and a
Hermitian observable pairs it with its adjoint, the eigenvector for `conj(λ₂)`. -/
theorem exists_hermitian_vector_functional_compl_pow {A : MPSTensor d D}
    (hA : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (htr : Matrix.trace ρ ≠ 0) {lam : ℂ}
    (hlam : Module.End.HasEigenvalue (Kraus.transferMap A) lam) (hlam1 : lam ≠ 1)
    (hlam0 : lam ≠ 0) :
    ∃ (ℓ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ) (v : Matrix (Fin D) (Fin D) ℂ),
      vᴴ = v ∧ (∀ Z, ℓ Zᴴ = star (ℓ Z)) ∧
      ∃ (K : ℕ) (μ : Fin K → ℂ) (a : Fin K → ℂ), 1 ≤ K ∧ K ≤ 2 ∧ (star lam = lam → K = 1) ∧
        Function.Injective μ ∧ (∀ j, ‖μ j‖ = 1) ∧ a ≠ 0 ∧
        ∀ t : ℕ, ℓ (((Kraus.transferMap A - fixedPointProj ρ htr) ^ t) v) =
          (‖lam‖ : ℂ) ^ t * ∑ j, a j * μ j ^ t := by
  classical
  obtain ⟨R, hRv⟩ := hlam.exists_hasEigenvector
  have hRE : Kraus.transferMap A R = lam • R := hRv.apply_eq_smul
  have hR0 : R ≠ 0 := hRv.2
  have hRHE : Kraus.transferMap A Rᴴ = star lam • Rᴴ := by
    rw [show Kraus.transferMap A Rᴴ = (Kraus.transferMap A R)ᴴ from
      (Kraus.map_conjTranspose A R).symm, hRE, Matrix.conjTranspose_smul]
  have hnorm0 : (‖lam‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hlam0
  have hpowdiv : ∀ (z : ℂ) (t : ℕ), (‖lam‖ : ℂ) ^ t * (z / ‖lam‖) ^ t = z ^ t := by
    intro z t
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hnorm0)]
  have hnormdiv : ∀ z : ℂ, ‖z‖ = ‖lam‖ → ‖z / (‖lam‖ : ℂ)‖ = 1 := by
    intro z hz
    rw [norm_div, hz, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr hlam0)]
  by_cases hreal : star lam = lam
  · -- A Hermitian eigenvector for the real eigenvalue `λ`.
    obtain ⟨H, hHh, hH0, hHE⟩ : ∃ H : Matrix (Fin D) (Fin D) ℂ,
        Hᴴ = H ∧ H ≠ 0 ∧ Kraus.transferMap A H = lam • H := by
      by_cases h1 : R + Rᴴ = 0
      · refine ⟨Complex.I • (R - Rᴴ), ?_, ?_, ?_⟩
        · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
            Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_I, neg_smul,
            ← smul_neg, neg_sub]
        · intro h
          apply hR0
          have h2 : R - Rᴴ = 0 := (smul_eq_zero.mp h).resolve_left Complex.I_ne_zero
          have h3 : (2 : ℂ) • R = 0 := by
            rw [two_smul]
            calc R + R = (R + Rᴴ) + (R - Rᴴ) := by abel
              _ = 0 := by rw [h1, h2, add_zero]
          exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
        · rw [map_smul, map_sub, hRE, hRHE, hreal, ← smul_sub, smul_comm]
      · exact ⟨R + Rᴴ, by rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
          add_comm], h1, by rw [map_add, hRE, hRHE, hreal, smul_add]⟩
    set c : ℂ := Matrix.trace (H * H) with hc_def
    have hc : c ≠ 0 := by
      intro h
      apply hH0
      refine Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ?_
      rw [hHh]
      exact h
    have hcstar : star c = c := by
      rw [hc_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hHh]
    let ℓ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
      c⁻¹ • (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulLeft ℂ H)
    have hℓ : ∀ Z, ℓ Z = c⁻¹ * Matrix.trace (H * Z) := fun Z ↦ rfl
    refine ⟨ℓ, H, hHh, ?_, 1, fun _ ↦ lam / ‖lam‖, fun _ ↦ 1, le_rfl, by norm_num,
      fun _ ↦ rfl, Function.injective_of_subsingleton _, fun _ ↦ hnormdiv lam rfl,
      fun h ↦ one_ne_zero (congrFun h 0), ?_⟩
    · intro Z
      rw [hℓ, hℓ, star_mul', star_inv₀, hcstar, ← Matrix.trace_conjTranspose,
        Matrix.conjTranspose_mul, hHh, Matrix.trace_mul_comm]
    · intro t
      rw [compl_pow_apply_of_transferMap_eq_smul hA htr hHE hlam1, map_smul, hℓ,
        ← hc_def, inv_mul_cancel₀ hc, smul_eq_mul, mul_one, Fin.sum_univ_one, one_mul,
        hpowdiv]
  · -- For non-real `λ`, pair `R` with its adjoint.
    have hstar1 : star lam ≠ 1 := fun h ↦ hlam1 (by rw [← star_star lam, h, star_one])
    obtain ⟨i, j, hij⟩ : ∃ i j, R i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hR0 (Matrix.ext h)
    have hδ : lam - star lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hreal)
    let g : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun Z ↦ Z i j
        map_add' := fun Z W ↦ by simp
        map_smul' := fun c Z ↦ by simp }
    let f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
      ((lam - star lam) * R i j)⁻¹ •
        g.comp (Kraus.transferMap A - star lam • LinearMap.id)
    have hfR : f R = 1 := by
      change ((lam - star lam) * R i j)⁻¹ *
        (Kraus.transferMap A R - star lam • R) i j = 1
      rw [hRE, ← sub_smul, Matrix.smul_apply, smul_eq_mul]
      exact inv_mul_cancel₀ (mul_ne_zero hδ hij)
    have hfRH : f Rᴴ = 0 := by
      change ((lam - star lam) * R i j)⁻¹ *
        (Kraus.transferMap A Rᴴ - star lam • Rᴴ) i j = 0
      rw [hRHE, sub_self, Matrix.zero_apply, mul_zero]
    let ℓ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun Z ↦ f Z + star (f Zᴴ)
        map_add' := fun Z W ↦ by
          simp only [map_add, Matrix.conjTranspose_add, star_add]
          ring
        map_smul' := fun c Z ↦ by
          simp only [map_smul, Matrix.conjTranspose_smul, smul_eq_mul, star_mul', star_star,
            RingHom.id_apply]
          ring }
    have hℓ : ∀ Z, ℓ Z = f Z + star (f Zᴴ) := fun Z ↦ rfl
    have hℓR : ℓ R = 1 := by rw [hℓ, hfR, hfRH, star_zero, add_zero]
    have hℓRH : ℓ Rᴴ = 1 := by
      rw [hℓ, hfRH, Matrix.conjTranspose_conjTranspose, hfR, star_one, zero_add]
    refine ⟨ℓ, R + Rᴴ, by rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm], ?_, 2, ![lam / ‖lam‖, star lam / ‖lam‖], ![1, 1], by norm_num, le_rfl,
      fun h ↦ absurd h hreal, ?_, ?_, fun h ↦ one_ne_zero (congrFun h 0), ?_⟩
    · intro Z
      rw [hℓ, hℓ, Matrix.conjTranspose_conjTranspose, star_add, star_star, add_comm]
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exfalso
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
          Matrix.cons_val_one, Matrix.cons_val_fin_one] at hab
        exact hreal ((div_left_inj' hnorm0).mp hab).symm
      · exfalso
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Fin.zero_eta, Matrix.cons_val_zero] at hab
        exact hreal ((div_left_inj' hnorm0).mp hab)
      · rfl
    · intro k
      fin_cases k
      · exact hnormdiv lam rfl
      · exact hnormdiv (star lam) (norm_star lam)
    · intro t
      rw [map_add, compl_pow_apply_of_transferMap_eq_smul hA htr hRE hlam1,
        compl_pow_apply_of_transferMap_eq_smul hA htr hRHE hstar1, map_add, map_smul,
        map_smul, hℓR, hℓRH, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        smul_eq_mul, mul_one, one_mul, mul_add, hpowdiv]

/-! ### The observables and the estimate -/

/-- Hermitian observables of norm one on `L` sites whose limit correlator is
`|λ|^t ∑_j a_j μ_j^t` with at most two distinct unimodular frequencies and `a ≠ 0`.

This is the choice of observables `O, O'` in arXiv:2307.01696, Supplemental
Material, proof of Lemma 2, adapted to Hermitian observables and normalized to
norm one as in the statement of Lemma 2. -/
theorem exists_normalized_observables_limitCorrelator {A : MPSTensor d D} {L : ℕ}
    (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρh : ρᴴ = ρ) (hρtr : Matrix.trace ρ = 1)
    (htr : Matrix.trace ρ ≠ 0) {lam : ℂ}
    (hlam : Module.End.HasEigenvalue (Kraus.transferMap A) lam) (hlam1 : lam ≠ 1)
    (hlam0 : lam ≠ 0) :
    ∃ O O' : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      O.IsHermitian ∧ O'.IsHermitian ∧
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) O‖ = 1 ∧
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) O'‖ = 1 ∧
      ∃ (K : ℕ) (μ : Fin K → ℂ) (a : Fin K → ℂ), 1 ≤ K ∧ K ≤ 2 ∧ (star lam = lam → K = 1) ∧
        Function.Injective μ ∧ (∀ j, ‖μ j‖ = 1) ∧ a ≠ 0 ∧
        ∀ t : ℕ, limitCorrelator A ρ htr L O O' t = (‖lam‖ : ℂ) ^ t * ∑ j, a j * μ j ^ t := by
  classical
  have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam0
  obtain ⟨ℓ, v, hv, hℓ, K, μ, a, hK1, hK2, hKreal, hμ, hμ1, ha, hform⟩ :=
    exists_hermitian_vector_functional_compl_pow hA htr hlam hlam1 hlam0
  obtain ⟨X, hXh, hXE⟩ := exists_isHermitian_physicalObservableTransfer_eq hL (ℓ.smulRight ρ)
    (fun Z ↦ by
      rw [LinearMap.smulRight_apply, LinearMap.smulRight_apply, hℓ,
        Matrix.conjTranspose_smul, hρh])
  obtain ⟨Y, hYh, hYE⟩ := exists_isHermitian_physicalObservableTransfer_eq hL
    ((Matrix.traceLinearMap (Fin D) ℂ ℂ).smulRight v)
    (fun Z ↦ by
      rw [LinearMap.smulRight_apply, LinearMap.smulRight_apply,
        Matrix.traceLinearMap_apply, Matrix.traceLinearMap_apply, Matrix.trace_conjTranspose,
        Matrix.conjTranspose_smul, hv])
  have hG : ∀ t, limitCorrelator A ρ htr L X Y t =
      (‖lam‖ : ℂ) ^ t * ∑ j, a j * μ j ^ t := by
    intro t
    rw [← hform t]
    simp only [limitCorrelator, hXE, hYE, LinearMap.smulRight_apply,
      Matrix.traceLinearMap_apply, hρtr, one_smul, Matrix.trace_smul, smul_eq_mul, mul_one]
  obtain ⟨c₁, hc₁, hwin₁⟩ := Complex.exists_window_le_norm_sum_mul_pow hμ hμ1 ha
  obtain ⟨u₁, hu₁⟩ := hwin₁ 0
  have hGu : limitCorrelator A ρ htr L X Y (0 + u₁) ≠ 0 := by
    rw [hG]
    refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hpos.ne')) fun h ↦ ?_
    rw [h, norm_zero] at hu₁
    linarith
  have hX0 : X ≠ 0 := fun h ↦ hGu (by rw [h, limitCorrelator_zero_left])
  have hY0 : Y ≠ 0 := fun h ↦ hGu (by rw [h, limitCorrelator_zero_right])
  have hnormpos : ∀ Z : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ, Z ≠ 0 →
      0 < ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) Z‖ := by
    intro Z hZ
    refine norm_pos_iff.mpr fun h ↦ hZ ?_
    simpa using h
  have hherm : ∀ (c : ℝ) (Z : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ), Z.IsHermitian →
      ((c : ℂ) • Z).IsHermitian := by
    intro c Z hZ
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hZ.eq, Complex.star_def,
      Complex.conj_ofReal]
  have hnorm1 : ∀ Z : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      0 < ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) Z‖ →
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ)
        (((‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) Z‖⁻¹ : ℝ) : ℂ) • Z)‖ = 1 := by
    intro Z hZ
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hZ,
      inv_mul_cancel₀ hZ.ne']
  set nX : ℝ := ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) X‖ with hnX_def
  set nY : ℝ := ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) Y‖ with hnY_def
  have hnX : 0 < nX := hnormpos X hX0
  have hnY : 0 < nY := hnormpos Y hY0
  have hκ : (0 : ℝ) < nX⁻¹ * nY⁻¹ := mul_pos (inv_pos.mpr hnX) (inv_pos.mpr hnY)
  refine ⟨((nX⁻¹ : ℝ) : ℂ) • X, ((nY⁻¹ : ℝ) : ℂ) • Y, hherm _ _ hXh, hherm _ _ hYh,
    hnorm1 X hnX, hnorm1 Y hnY, K, μ, fun j ↦ ((nX⁻¹ * nY⁻¹ : ℝ) : ℂ) * a j, hK1, hK2,
    hKreal, hμ,
    hμ1, ?_, ?_⟩
  · intro h
    apply ha
    funext j
    have hj := congrFun h j
    simp only [Pi.zero_apply] at hj
    exact (mul_eq_zero.mp hj).resolve_left (by exact_mod_cast hκ.ne')
  · intro t
    have hsum : ∑ j, ((nX⁻¹ * nY⁻¹ : ℝ) : ℂ) * a j * μ j ^ t =
        ((nX⁻¹ * nY⁻¹ : ℝ) : ℂ) * ∑ j, a j * μ j ^ t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hsum, limitCorrelator_smul_smul, hG]
    push_cast
    ring

/-- **Exponentially decaying correlations** (chapter entry
`thm:ldp_decaying_correlations`; arXiv:2307.01696, Supplemental Material, Lemma 2,
in the chapter's corrected form).

Let `A` be a tensor whose products of `L ≥ 1` matrices span the matrix algebra (so
`A` is normal), in the gauge `∑ (A^i)† A^i = 1`, `E_A(ρ) = ρ`, `ρ > 0`, `Tr ρ = 1`
of the chapter display `eq:ldp_normal_gauge` (the gauge of arXiv:2307.01696,
eq. (5)), and let `λ₂` be an eigenvalue of `E_A` of largest modulus other than `1`,
with correlation length `ξ = -1/log|λ₂| > 0`. Then there are Hermitian operators
`O, O'` on `L` sites of norm one, a constant `c > 0`, an integer `K ∈ {1, 2}`, with
`K = 1` when `λ₂` is real, and `s₀ ≥ L + 2` such that for every `s ≥ s₀` some
`s' ∈ {s, …, s + K - 1}` satisfies
`|G_N(O,O';s')| ≥ c e^{-(s'-1)/ξ}` for every `N ≥ 3s'`, where
`G_N(O,O';s') = ⟨O_1 O'_{s'}⟩ - ⟨O_1⟩⟨O'_{s'}⟩` in the normalized vector `φ_N`
with `O` on the sites `1, …, L` and `O'` on the sites `s', …, s'+L-1`.

**Local fix (arXiv:2307.01696, Supplemental Material, Lemma 2):** the source
asserts, for injective `A` and `L = 1`, the bound at every `s > 1` for large `N`,
with vanishing one-point functions. For complex `λ₂` the limit correlator of
Hermitian observables is `|λ₂|^t (μ^t + conj(μ)^t)` up to scale, which can vanish
at individual separations; the statement therefore takes the bound in windows of
`K` consecutive separations and uses the connected correlator. Documented in
`docs/paper-gaps/mswc24_decaying_correlations_windowed_connected.tex`. -/
theorem exists_decayingCorrelations {A : MPSTensor d D} {L : ℕ} (hL1 : 1 ≤ L)
    (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : Kraus.transferMap A ρ = ρ)
    (hρtr : Matrix.trace ρ = 1) {lam₂ : ℂ}
    (hlam₂ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₂) (hlam₂1 : lam₂ ≠ 1)
    (hmax : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hξ : 0 < correlationLength lam₂) :
    ∃ O O' : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      O.IsHermitian ∧ O'.IsHermitian ∧
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) O‖ = 1 ∧
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) O'‖ = 1 ∧
      ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 1 ≤ K ∧ K ≤ 2 ∧ (star lam₂ = lam₂ → K = 1) ∧
        ∃ s₀ : ℕ, L + 2 ≤ s₀ ∧
          ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + K ∧ ∀ N, 3 * s' ≤ N →
            c * Real.exp (-((s' : ℝ) - 1) / correlationLength lam₂) ≤
              ‖mpvConnectedCorrelator A N 0 (s' - 1) O O'‖ := by
  classical
  /- Elementary facts about the gauge and `λ₂`. -/
  have htr : Matrix.trace ρ ≠ 0 := by rw [hρtr]; exact one_ne_zero
  have : NeZero D := ⟨by rintro rfl; simp [Matrix.trace] at hρtr⟩
  have hlog : Real.log ‖lam₂‖ < 0 := by
    by_contra h
    push Not at h
    have : correlationLength lam₂ ≤ 0 := by
      unfold correlationLength
      exact div_nonpos_iff.mpr (Or.inr ⟨by norm_num, h⟩)
    linarith
  have hpos : 0 < ‖lam₂‖ := by
    rcases (norm_nonneg lam₂).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hlog
      exact absurd hlog (lt_irrefl 0)
  have hlt1 : ‖lam₂‖ < 1 := (Real.log_neg_iff hpos).mp hlog
  have hlam0 : lam₂ ≠ 0 := norm_pos_iff.mp hpos
  /- The observables. -/
  obtain ⟨O, O', hOh, hO'h, hOn, hO'n, K, μ, a, hK1, hK2, hKreal, hμ, hμ1, ha, hGO⟩ :=
    exists_normalized_observables_limitCorrelator hL hA hρ.1 hρtr htr hlam₂ hlam₂1 hlam0
  obtain ⟨c₀, hc₀, hwin⟩ := Complex.exists_window_le_norm_sum_mul_pow hμ hμ1 ha
  /- The rate `r` and the decay of `E_A - P`. -/
  set r : ℝ := (‖lam₂‖ + Real.sqrt ‖lam₂‖) / 2 with hr_def
  have hsq : ‖lam₂‖ < Real.sqrt ‖lam₂‖ := by
    rw [Real.lt_sqrt hpos.le]
    nlinarith
  have hsq1 : Real.sqrt ‖lam₂‖ < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow]
    exact hlt1
  have hr1 : ‖lam₂‖ < r := by rw [hr_def]; linarith
  have hr2 : r < Real.sqrt ‖lam₂‖ := by rw [hr_def]; linarith
  have hr0 : 0 < r := hpos.trans hr1
  have hrlt1 : r < 1 := hr2.trans hsq1
  have hrsq : r ^ 2 < ‖lam₂‖ := (Real.lt_sqrt hr0.le).mp hr2
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_compl_pow_bound hL1 hL hA hρ hρfix hρtr htr hmax hr1
  /- A submultiplicative size of linear maps dominating the trace. -/
  obtain ⟨Ct', hCt'1, hCt'⟩ : ∃ Ct' : ℝ, 1 ≤ Ct' ∧
      ∑ p : Fin D, ∑ q : Fin D, ‖Matrix.single p q (1 : ℂ)‖ ≤ Ct' :=
    ⟨_, le_max_right _ 1, le_max_left _ _⟩
  obtain ⟨Nm, hNm⟩ : ∃ Nm : (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) → ℝ,
      ∀ F, Nm F = Ct' * ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) F‖ :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨C, hC_def⟩ : ∃ C : ℝ, C = Ct' * C₁ := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC_def]; exact mul_pos (by linarith) hC₁0
  have hNm0 : ∀ F, 0 ≤ Nm F := fun F ↦ by
    rw [hNm F]; exact mul_nonneg (by linarith) (norm_nonneg _)
  have hNmul : ∀ F G, Nm (F * G) ≤ Nm F * Nm G := by
    intro F G
    rw [hNm, hNm, hNm, map_mul]
    set x := ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) F‖
    set y := ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) G‖
    have hx : 0 ≤ x := norm_nonneg _
    have hy : 0 ≤ y := norm_nonneg _
    calc Ct' * ‖Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) F *
          Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) G‖ ≤ Ct' * (x * y) := by
          gcongr; exact norm_mul_le _ _
      _ ≤ Ct' * x * (Ct' * y) := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Ct')
            (by linarith : (0 : ℝ) ≤ Ct' - 1)) (mul_nonneg hx hy)]
  have hNadd : ∀ F G, Nm (F + G) ≤ Nm F + Nm G := by
    intro F G
    rw [hNm, hNm, hNm, map_add, ← mul_add]
    gcongr
    exact norm_add_le _ _
  have hNtr : ∀ F, ‖LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) F‖ ≤ Nm F := fun F ↦ by
    rw [hNm]
    exact (Matrix.norm_linearMap_trace_le_mul_norm F).trans (by gcongr)
  have hNT : ∀ k : ℕ, Nm ((Kraus.transferMap A - fixedPointProj ρ htr) ^ k) ≤ C * r ^ k := by
    intro k
    rw [hNm, hC_def, mul_assoc]
    gcongr
    exact hC₁ k
  clear hNm hC_def hC₁ hC₁0 hCt' hCt'1
  set E := Kraus.transferMap A with hE_def
  set P := fixedPointProj ρ htr with hP_def
  set T := E - P with hT_def
  have hTP : IsTracePreservingMap E := Kraus.isTracePreservingMap_mapLM_of_isTP A hA
  have hEk : ∀ k, 1 ≤ k → E ^ k = P + T ^ k := fun k hk ↦
    pow_eq_fixedPointProj_add_compl_pow E htr hTP hρfix hk
  have hEkn : ∀ k, 1 ≤ k → Nm (E ^ k) ≤ Nm P + C := fun k hk ↦ by
    rw [hEk k hk]
    refine (hNadd _ _).trans (add_le_add le_rfl ?_)
    have h1 := hNT k
    have h2 : r ^ k ≤ 1 := pow_le_one₀ hr0.le hrlt1.le
    nlinarith
  /- Constants. -/
  set EX := physicalObservableTransfer A L O with hEX_def
  set EY := physicalObservableTransfer A L O' with hEY_def
  set α : ℂ := Matrix.trace (EX ρ) with hα_def
  set β : ℂ := Matrix.trace (EY ρ) with hβ_def
  set B : ℝ := 1 + Nm EX + Nm EY + Nm EX * (Nm P + C) * Nm EY with hB_def
  have hB0 : 0 ≤ Nm EX * (Nm P + C) * Nm EY :=
    mul_nonneg (mul_nonneg (hNm0 _) (add_nonneg (hNm0 _) hC0.le)) (hNm0 _)
  have hBX : Nm EX ≤ B := by have := hNm0 EY; rw [hB_def]; linarith
  have hBY : Nm EY ≤ B := by have := hNm0 EX; rw [hB_def]; linarith
  have hB1 : 1 ≤ B := by have := hNm0 EX; have := hNm0 EY; rw [hB_def]; linarith
  set K₀ : ℝ := B * C with hK₀_def
  have hK₀ : 0 < K₀ := mul_pos (by linarith) hC0
  set M : ℝ := ‖α‖ + ‖β‖ + ∑ j, ‖a j‖ with hM_def
  have hsumnn : 0 ≤ ∑ j, ‖a j‖ := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hM : 0 ≤ M := add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hsumnn
  set q : ℝ := r ^ 2 / ‖lam₂‖ with hq_def
  have hq0 : 0 < q := div_pos (pow_pos hr0 2) hpos
  have hq1 : q < 1 := by rw [hq_def, div_lt_one hpos]; exact hrsq
  have hqr : ∀ t : ℕ, r ^ (2 * t) = q ^ t * ‖lam₂‖ ^ t := by
    intro t
    rw [pow_mul, ← mul_pow, hq_def, div_mul_cancel₀ _ hpos.ne']
  set δ : ℝ := min (1 / (2 * K₀)) (c₀ / (8 * (M + 2) ^ 2 * K₀)) with hδ_def
  have hM2 : 0 < 8 * (M + 2) ^ 2 * K₀ :=
    mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) 2)) hK₀
  have hδ : 0 < δ := lt_min (one_div_pos.mpr (mul_pos two_pos hK₀)) (div_pos hc₀ hM2)
  obtain ⟨t₀, ht₀⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨O, O', hOh, hO'h, hOn, hO'n, c₀ / 2, half_pos hc₀, K, hK1, hK2, hKreal, L + 2 + t₀,
    by omega, ?_⟩
  intro s hs
  obtain ⟨u, hu⟩ := hwin (s - L - 1)
  have huK := u.isLt
  refine ⟨s + u, by omega, by omega, ?_⟩
  intro N hN
  set t' : ℕ := s - L - 1 + u with ht'_def
  have hs'1 : s + (u : ℕ) - 1 = L + t' := by omega
  have ht'1 : 1 ≤ t' := by omega
  have ht₀' : t₀ ≤ t' := by omega
  obtain ⟨n, rfl⟩ : ∃ n, N = L + t' + L + n := ⟨N - (L + t' + L), by omega⟩
  have hn : 2 * t' ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  rw [hs'1, mpvConnectedCorrelator_eq_of_compl hL1 hA hρfix hρtr htr O O' ht'1 hn1]
  /- Bounds on the finite-size corrections. -/
  have hrpow : ∀ k, n ≤ k → r ^ k ≤ r ^ n := fun k hk ↦
    pow_le_pow_of_le_one hr0.le hrlt1.le hk
  have htrT : ∀ (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (k : ℕ),
      Nm F ≤ B → n ≤ k → ‖LinearMap.trace ℂ _ (F * T ^ k)‖ ≤ K₀ * r ^ n := by
    intro F k hF hk
    calc ‖LinearMap.trace ℂ _ (F * T ^ k)‖ ≤ Nm (F * T ^ k) := hNtr _
      _ ≤ Nm F * Nm (T ^ k) := hNmul _ _
      _ ≤ B * (C * r ^ n) := by
          gcongr
          · exact hNm0 _
          · exact (hNT k).trans (mul_le_mul_of_nonneg_left (hrpow k hk) hC0.le)
      _ = K₀ * r ^ n := by rw [hK₀_def]; ring
  have hbZ : ‖LinearMap.trace ℂ _ (T ^ (L + t' + L + n))‖ ≤ K₀ * r ^ n := by
    have h1 := hrpow (L + t' + L + n) (by omega)
    have h2 : C * r ^ n ≤ K₀ * r ^ n := by
      calc C * r ^ n = 1 * (C * r ^ n) := (one_mul _).symm
        _ ≤ B * (C * r ^ n) :=
          mul_le_mul_of_nonneg_right hB1 (mul_nonneg hC0.le (pow_nonneg hr0.le _))
        _ = K₀ * r ^ n := by rw [hK₀_def]; ring
    exact (hNtr _).trans ((hNT _).trans ((mul_le_mul_of_nonneg_left h1 hC0.le).trans h2))
  have hbX := htrT EX (t' + (L + n)) hBX (by omega)
  have hbY := htrT EY (n + (L + t')) hBY (by omega)
  have hbXY := htrT (EX * E ^ t' * EY) n (by
    calc Nm (EX * E ^ t' * EY) ≤ Nm EX * Nm (E ^ t') * Nm EY := by
          refine (hNmul _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (hNmul _ _) (hNm0 _)
      _ ≤ Nm EX * (Nm P + C) * Nm EY := by
          gcongr
          · exact hNm0 _
          · exact hNm0 _
          · exact hEkn t' ht'1
      _ ≤ B := by
          have := hNm0 EX; have := hNm0 EY; rw [hB_def]; linarith) le_rfl
  set g : ℂ := limitCorrelator A ρ htr L O O' t' with hg_def
  have hbg : ‖g‖ ≤ ∑ j, ‖a j‖ := by
    rw [hg_def, hGO, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    calc ‖lam₂‖ ^ t' * ‖∑ j, a j * μ j ^ t'‖ ≤ 1 * ∑ j, ‖a j‖ := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) hlt1.le
          · refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_))
            rw [norm_mul, norm_pow, hμ1, one_pow, mul_one]
      _ = ∑ j, ‖a j‖ := one_mul _
  have hglow : c₀ * ‖lam₂‖ ^ t' ≤ ‖g‖ := by
    rw [hg_def, hGO, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      mul_comm c₀]
    exact mul_le_mul_of_nonneg_left hu (pow_nonneg (norm_nonneg _) _)
  have hrn : r ^ n ≤ q ^ t' * ‖lam₂‖ ^ t' := by
    rw [← hqr]
    exact pow_le_pow_of_le_one hr0.le hrlt1.le hn
  have hqt : q ^ t' ≤ δ :=
    (pow_le_pow_of_le_one hq0.le hq1.le ht₀').trans ht₀.le
  have hlampow : ‖lam₂‖ ^ t' ≤ 1 := pow_le_one₀ (norm_nonneg _) hlt1.le
  have hε : K₀ * r ^ n ≤ 1 / 2 := by
    have h1 : δ ≤ 1 / (2 * K₀) := min_le_left _ _
    have h2 : r ^ n ≤ δ :=
      hrn.trans ((mul_le_of_le_one_right (pow_nonneg hq0.le _) hlampow).trans hqt)
    calc K₀ * r ^ n ≤ K₀ * (1 / (2 * K₀)) := by gcongr; exact h2.trans h1
      _ = 1 / 2 := by rw [mul_one_div, mul_comm 2 K₀, ← div_div, div_self hK₀.ne']
  have hdiff := Complex.norm_div_sub_div_mul_div_sub_le (a := α) (b := β) (g := g)
    (mul_nonneg hK₀.le (pow_nonneg hr0.le _)) hε hM
    (by rw [add_sub_cancel_left]; exact hbZ)
    (by rw [add_sub_cancel_left]; exact hbXY)
    (by rw [add_sub_cancel_left]; exact hbX)
    (by rw [add_sub_cancel_left]; exact hbY)
    (by rw [hM_def]; linarith [norm_nonneg β])
    (by rw [hM_def]; linarith [norm_nonneg α])
    (hbg.trans (by rw [hM_def]; linarith [norm_nonneg α, norm_nonneg β]))
  have hsmall : 4 * (M + 2) ^ 2 * (K₀ * r ^ n) ≤ c₀ / 2 * ‖lam₂‖ ^ t' := by
    have h1 : δ ≤ c₀ / (8 * (M + 2) ^ 2 * K₀) := min_le_right _ _
    have hMK : 0 < 8 * (M + 2) ^ 2 * K₀ := hM2
    have h3 : 8 * (M + 2) ^ 2 * K₀ * δ ≤ c₀ := by
      rw [le_div_iff₀ hMK] at h1
      linarith
    have hl := pow_nonneg (norm_nonneg lam₂) t'
    calc 4 * (M + 2) ^ 2 * (K₀ * r ^ n) ≤ 4 * (M + 2) ^ 2 * (K₀ * (δ * ‖lam₂‖ ^ t')) := by
          gcongr
          exact hrn.trans (mul_le_mul_of_nonneg_right hqt hl)
      _ = (8 * (M + 2) ^ 2 * K₀ * δ) / 2 * ‖lam₂‖ ^ t' := by ring
      _ ≤ c₀ / 2 * ‖lam₂‖ ^ t' := by gcongr
  have key : ∀ x : ℂ, ‖x - g‖ ≤ 4 * (M + 2) ^ 2 * (K₀ * r ^ n) →
      c₀ / 2 * ‖lam₂‖ ^ t' ≤ ‖x‖ := by
    intro x hx
    have h := norm_sub_norm_le g (g - x)
    rw [sub_sub_cancel, norm_sub_rev] at h
    linarith
  refine le_trans ?_ (key _ hdiff)
  gcongr
  exact exp_neg_div_correlationLength_le_norm_pow hpos hlog (by omega)
end MPSTensor
