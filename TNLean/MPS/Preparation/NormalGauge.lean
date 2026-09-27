/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.FundamentalTheorem.SectorBNT.PowerSumCoefficients
import TNLean.MPS.Preparation.ApproximationError

/-!
# The gauge of a normal tensor used for state preparation

arXiv:2307.01696 calls a tensor *normal* if "(i) it is irreducible (`A^i` have no nontrivial
common invariant subspace), and (ii) `E_A` has a unique largest eigenvalue `λ_1 = 1` and no other
of the same magnitude", defines "Its correlation length [...] via the subleading eigenvalue
`ξ = -1/ln(|λ_2|)`", and states that "After a gauge transformation [...] `E_A` of a normal tensor
can be brought into the form" `E_A = |ρ⟩⟨1| + R` of its eq. (5), that is,
`∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(ρ) = ρ`, `ρ > 0`, `Tr ρ = 1` (chapter equation `eq:ldp_normal_gauge`).
This file proves that reduction and records what it leaves unchanged.

* `IsNormalTensor.exists_normalGauge`: a normal tensor in the source's sense (`IsNormalTensor`)
  is gauge equivalent, with no rescaling, to a tensor `B` in the gauge `eq:ldp_normal_gauge`,
  together with a length `L ≥ 1` at which `B` is injective.
* `exists_normalGauge_of_isNormal`: a tensor normal in the sense of eventual block injectivity
  (`Kraus.IsNormal`, the chapter's `def:normal`) reaches such a `B` after a nonzero rescaling
  `ζ • A` and a gauge. The eigenvalues of `E_B` are those of `E_A` divided by the leading
  eigenvalue `λ₁` of `E_A`, and `φ_N(B) = ζ^N φ_N(A)`.
* `hasEigenvalue_transferMap_iff_of_gaugeEquiv`, `transferMap_smul_eq_norm_sq_smul`: the eigenvalues of the
  transfer map are invariant under a gauge and scale by `|ζ|²` under `A ↦ ζ • A`.
* `normalizedMPVState_eq_of_gaugeEquiv`, `norm_inner_normalizedMPVState_smul`: the normalized
  periodic vector `φ_N/‖φ_N‖` is unchanged by a gauge, and changed only by a phase by a
  rescaling.
-/

open scoped Matrix BigOperators InnerProductSpace ComplexOrder ComplexConjugate

namespace MPSTensor

variable {d D : ℕ}

/-! ### Eigenvalues of the transfer map under gauges and rescalings -/

/-- A gauge `Bⁱ = X Aⁱ X⁻¹` maps an eigenvector `Y` of `E_A` to the eigenvector `X Y X†` of `E_B`
with the same eigenvalue.

This is the invariance of the spectrum of `E_A` under the gauge transformation of
arXiv:2307.01696, the sentence before eq. (5) ("After a gauge transformation"). -/
theorem hasEigenvalue_transferMap_of_gaugeEquiv {A B : MPSTensor d D} (h : GaugeEquiv A B)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (Kraus.transferMap A) μ) :
    Module.End.HasEigenvalue (Kraus.transferMap B) μ := by
  obtain ⟨X, hX⟩ := h
  obtain ⟨Y, hY⟩ := hμ.exists_hasEigenvector
  have hYeq : Kraus.transferMap A Y = μ • Y := Module.End.mem_eigenspace_iff.mp hY.1
  set Xm : Matrix (Fin D) (Fin D) ℂ := (X : Matrix (Fin D) (Fin D) ℂ)
  set Xi : Matrix (Fin D) (Fin D) ℂ := ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hXiX : Xi * Xm = 1 := by
    simp only [Xi, Xm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXHi : Xmᴴ * Xiᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hXiX, Matrix.conjTranspose_one]
  refine hasEigenvalue_of_eigenvector_eq _ μ (Xm * Y * Xmᴴ) ?_ ?_
  · have hB : ∀ i, B i = Xm * A i * Xi := fun i => by rw [hX i]
    have key : Kraus.transferMap B (Xm * Y * Xmᴴ) = Xm * Kraus.transferMap A Y * Xmᴴ := by
      simp only [Kraus.transferMap_apply, hB, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Xi Xm, hXiX, Matrix.one_mul, ← Matrix.mul_assoc Xmᴴ Xiᴴ, hXHi,
        Matrix.one_mul]
    rw [key, hYeq, Matrix.mul_smul, Matrix.smul_mul]
  · intro h0
    apply hY.2
    have : Xi * (Xm * Y * Xmᴴ) * Xiᴴ = Y := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXiX, Matrix.one_mul, Matrix.mul_assoc, hXHi,
        Matrix.mul_one]
    rw [← this, h0, Matrix.mul_zero, Matrix.zero_mul]

/-- Gauge-equivalent tensors have transfer maps with the same eigenvalues. -/
theorem hasEigenvalue_transferMap_iff_of_gaugeEquiv {A B : MPSTensor d D} (h : GaugeEquiv A B)
    (μ : ℂ) :
    Module.End.HasEigenvalue (Kraus.transferMap A) μ ↔
      Module.End.HasEigenvalue (Kraus.transferMap B) μ :=
  ⟨hasEigenvalue_transferMap_of_gaugeEquiv h, hasEigenvalue_transferMap_of_gaugeEquiv h.symm⟩

/-- Rescaling the tensor by `ζ` multiplies its transfer map by `|ζ|²`. -/
theorem transferMap_smul_eq_norm_sq_smul (ζ : ℂ) (A : MPSTensor d D) :
    Kraus.transferMap (ζ • A) = ((‖ζ‖ ^ 2 : ℝ) : ℂ) • Kraus.transferMap A := by
  apply LinearMap.ext
  intro Y
  rw [LinearMap.smul_apply, Complex.ofReal_pow, ← Complex.mul_conj']
  exact transferMap_smul ζ A Y

/-- The eigenvalues of `c • f` are `c` times those of `f`, for `c ≠ 0`. -/
theorem _root_.Module.End.hasEigenvalue_smul_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) {c : ℂ} (hc : c ≠ 0) (μ : ℂ) :
    Module.End.HasEigenvalue (c • f) (c * μ) ↔ Module.End.HasEigenvalue f μ := by
  have step : ∀ (g : V →ₗ[ℂ] V) (a ν : ℂ), Module.End.HasEigenvalue g ν →
      Module.End.HasEigenvalue (a • g) (a * ν) := by
    intro g a ν hν
    obtain ⟨x, hx⟩ := hν.exists_hasEigenvector
    refine hasEigenvalue_of_eigenvector_eq _ _ x ?_ hx.2
    rw [LinearMap.smul_apply, Module.End.mem_eigenspace_iff.mp hx.1, smul_smul]
  refine ⟨fun h => ?_, step f c μ⟩
  have := step _ c⁻¹ _ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul, ← mul_assoc, inv_mul_cancel₀ hc,
    one_mul] at this

/-! ### Normalized periodic vectors under gauges and rescalings -/

/-- A gauge leaves the normalized periodic vector `φ_N/‖φ_N‖` unchanged, since it leaves every
trace `Tr(A^{i_1} ⋯ A^{i_N})` of arXiv:2307.01696, eq. (3), unchanged. -/
theorem normalizedMPVState_eq_of_gaugeEquiv {A B : MPSTensor d D} (h : GaugeEquiv A B)
    (N : ℕ) : normalizedMPVState A N = normalizedMPVState B N := by
  have : mpvState A N = mpvState B N := by
    ext σ
    simp only [mpvState_apply]
    exact h.sameMPV N σ
  simp only [normalizedMPVState, this]

/-- If `φ_N(B) = c φ_N(A)` with `c ≠ 0`, the overlaps of the normalized vectors with any vector
have the same modulus: the normalized vectors differ by the phase `c/|c|`. -/
theorem norm_inner_normalizedMPVState_smul {A : MPSTensor d D} {D' : ℕ} {B : MPSTensor d D'}
    {N : ℕ} {c : ℂ} (hc : c ≠ 0) (h : mpvState B N = c • mpvState A N)
    (v : MPVSpace d N) :
    ‖⟪normalizedMPVState B N, v⟫_ℂ‖ = ‖⟪normalizedMPVState A N, v⟫_ℂ‖ := by
  simp only [normalizedMPVState, h, norm_smul, inner_smul_left, norm_mul, RCLike.norm_conj,
    Complex.ofReal_mul, mul_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  field_simp

/-! ### The gauge `eq:ldp_normal_gauge` -/

/-- **The gauge of a normal tensor.** A normal tensor in the sense of arXiv:2307.01696 (the
definition after eq. (4): irreducible, with `E_A` having "a unique largest eigenvalue
`λ_1 = 1` and no other of the same magnitude"; `IsNormalTensor`) is gauge equivalent, without
rescaling, to a tensor `B` with `∑ᵢ (Bⁱ)† Bⁱ = 1` and a fixed point `E_B(ρ) = ρ`, `ρ > 0`,
`Tr ρ = 1`; the products of `L` matrices of `B` span the matrix algebra for some `L ≥ 1`.

This is the gauge transformation of arXiv:2307.01696 stated before its eq. (5): the gauge is
`B^i = σ^{1/2} A^i σ^{-1/2}` with `σ > 0` the fixed point of the dual transfer map. -/
theorem IsNormalTensor.exists_normalGauge {A : MPSTensor d D} (hA : IsNormalTensor A) :
    ∃ (B : MPSTensor d D) (L : ℕ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      GaugeEquiv A B ∧ 1 ≤ L ∧ Kraus.IsNBlkInjective B L ∧ ∑ i, (B i)ᴴ * B i = 1 ∧
        ρ.PosDef ∧ Kraus.transferMap B ρ = ρ ∧ ρ.trace = 1 := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨σ, -, -, hTP, hGauge, -, -⟩ := hA.exists_tpGauge
  set B := Kraus.tpGauge (d := d) (D := D) A σ
  have hNB : Kraus.IsNormal B := isNormal_of_gaugeEquiv hA.isNormal hGauge
  obtain ⟨L, hL0, hL⟩ := hNB
  obtain ⟨ρ, hρ, hfix, -⟩ := isNormal_implies_stronglyIrreducible B hTP ⟨L, hL0, hL⟩
  have htr : 0 < ρ.trace := hρ.trace_pos
  refine ⟨B, L, (ρ.trace)⁻¹ • ρ, hGauge, hL0, hL, hTP, hρ.smul (inv_pos.mpr htr), ?_, ?_⟩
  · rw [map_smul, hfix]
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htr.ne']

/-- **The gauge of a tensor normal by block injectivity.** Let the products of some fixed number
of matrices of `A` span the matrix algebra (`Kraus.IsNormal`, the chapter's `def:normal`), and let
`λ₁` be an eigenvalue of `E_A` of largest modulus. Then `λ₁ ≠ 0` and there are a scalar `ζ ≠ 0`
and a tensor `B` gauge equivalent to `ζ • A` such that `B` is in the gauge
`∑ᵢ (Bⁱ)† Bⁱ = 1`, `E_B(ρ) = ρ`, `ρ > 0`, `Tr ρ = 1` of arXiv:2307.01696, eq. (5), with the
products of `L ≥ 1` matrices of `B` spanning the matrix algebra; the eigenvalues of `E_B` are
those of `E_A` divided by `λ₁`; and `φ_N(B) = ζ^N φ_N(A)`.

This is the reduction taken without loss of generality in the chapter's proof of
`thm:ldp_depth_lower_bound`: arXiv:2307.01696 normalizes the leading eigenvalue to
"`λ_1 = 1`" in its definition of a normal tensor, and reaches eq. (5) "After a gauge
transformation". -/
theorem exists_normalGauge_of_isNormal {A : MPSTensor d D} (hA : Kraus.IsNormal A) {lam₁ : ℂ}
    (hlam₁ : Module.End.HasEigenvalue (Kraus.transferMap A) lam₁)
    (hlam₁max : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ ≤ ‖lam₁‖) :
    lam₁ ≠ 0 ∧ ∃ (B : MPSTensor d D) (ζ : ℂ) (L : ℕ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      ζ ≠ 0 ∧ GaugeEquiv (ζ • A) B ∧ 1 ≤ L ∧ Kraus.IsNBlkInjective B L ∧
        ∑ i, (B i)ᴴ * B i = 1 ∧ ρ.PosDef ∧ Kraus.transferMap B ρ = ρ ∧ ρ.trace = 1 ∧
        (∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ ↔
          Module.End.HasEigenvalue (Kraus.transferMap B) (μ / lam₁)) ∧
        ∀ N, mpvState B N = ζ ^ N • mpvState A N := by
  have hD : D ≠ 0 := by
    rintro rfl
    obtain ⟨Y, hY⟩ := hlam₁.exists_hasEigenvector
    exact hY.2 (Subsingleton.elim Y 0)
  have : NeZero D := ⟨hD⟩
  obtain ⟨B, ζ, hζ, hG, hmpv, hLC, hNB⟩ := exists_leftCanonical_normalTensor_scale_of_isNormal hA
  obtain ⟨B', L, ρ, hG', hL1, hL, hTP, hρ, hfix, htr⟩ := hNB.exists_normalGauge
  set c : ℂ := ((‖ζ‖ ^ 2 : ℝ) : ℂ) with hc_def
  have hc : c ≠ 0 := by
    rw [hc_def]
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hζ)
  have hGB : GaugeEquiv (ζ • A) B' := hG.trans hG'
  have heig : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ ↔
      Module.End.HasEigenvalue (Kraus.transferMap B') (c * μ) := fun μ => by
    rw [← hasEigenvalue_transferMap_iff_of_gaugeEquiv hGB, transferMap_smul_eq_norm_sq_smul,
      Module.End.hasEigenvalue_smul_iff _ hc]
  /- `c λ₁` is an eigenvalue of `E_{B'}` of largest modulus; since `1` is an eigenvalue of
  `E_{B'}` and all have modulus at most one, `c λ₁ = 1` by primitivity. -/
  have hNB' : IsNormalTensor B' := hNB.of_gaugeEquiv hG'.symm
  have h1 : Module.End.HasEigenvalue (Kraus.transferMap B') 1 :=
    hasEigenvalue_of_eigenvector_eq _ 1 ρ (by rw [one_smul, hfix]) (Matrix.PosDef.isUnit hρ).ne_zero
  have hle1 : ∀ ν, Module.End.HasEigenvalue (Kraus.transferMap B') ν → ‖ν‖ ≤ 1 :=
    fun ν hν => Kraus.eigenvalue_norm_le_one_of_isTP B' hTP ν hν
  have hcl : c * lam₁ = 1 := by
    have hmem := (heig lam₁).1 hlam₁
    refine hNB'.primitive_transfer.unique_peripheral _ hmem (le_antisymm (hle1 _ hmem) ?_)
    obtain ⟨μ, hμ⟩ : ∃ μ, c * μ = 1 := ⟨c⁻¹, mul_inv_cancel₀ hc⟩
    have hμA := (heig μ).2 (hμ ▸ h1)
    have := hlam₁max μ hμA
    have hμn : ‖c‖ * ‖μ‖ = 1 := by rw [← norm_mul, hμ, norm_one]
    rw [norm_mul]
    calc (1 : ℝ) = ‖c‖ * ‖μ‖ := hμn.symm
      _ ≤ ‖c‖ * ‖lam₁‖ := by gcongr
  have hl0 : lam₁ ≠ 0 := by rintro rfl; simp at hcl
  have hdiv : ∀ μ, μ / lam₁ = c * μ := fun μ => by
    rw [div_eq_iff hl0, mul_comm c μ, mul_assoc, hcl, mul_one]
  refine ⟨hl0, B', ζ, L, ρ, hζ, hGB, hL1, hL, hTP, hρ, hfix, htr, fun μ => ?_, fun N => ?_⟩
  · rw [hdiv]; exact heig μ
  · ext σ
    simp only [mpvState_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← hG'.sameMPV N σ, hmpv N σ]

end MPSTensor
