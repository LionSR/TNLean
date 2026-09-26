/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CStarSqrtHolder
import TNLean.Algebra.MatrixEntryNorm
import TNLean.MPS.Core.Correlations
import TNLean.MPS.Preparation.ApproximatingState

/-!
# Rate of convergence of the positive part

Let `A` be a normal tensor in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1`
(arXiv:2307.01696, eq. (5)), let `λ₂` bound the moduli of the eigenvalues of `E_A` other than
`1`, with correlation length `ξ = -1/log|λ₂|`, and let `0 < γ < 1/2`. This file proves the
first two steps of the approximation estimate of Piroli, Styliaris, and Cirac (arXiv:2103.13367,
Supplemental Material, "Proof of Theorem MPS_classification"):

1. **Transfer-map gap.** `‖E_A^n(X) - Tr(X) σ‖ ≤ C e^{-2γ n/ξ} ‖X‖` (compare eq. `difference`,
   `‖R‖_F ≤ Λ(q) e^{-qα}` with `|λ₁| = e^{-qα}` for the blocked transfer matrix); the rate
   `e^{-2γ/ξ} = |λ₂|^{2γ}` exceeds the spectral radius of `E_A - |σ⟩⟨1|` because `2γ < 1`.
2. **Positive parts.** The positive part `P_q` of the polar decomposition of the `q`-site blocked
   tensor satisfies `‖P_q - P_∞‖ ≤ K e^{-γ q/ξ}` (eq. `intermediate`), from the rearrangement
   `P_q² - P_∞² ≅ E_A^q - |σ⟩⟨1|` and `‖√a - √b‖ ≤ √‖a - b‖` (`CFC.norm_sqrt_sub_sqrt_le` in
   `TNLean.Algebra.CStarSqrtHolder`).

The rate `e^{-γ q/ξ}` of step 2 feeds the telescoping estimate in
`TNLean.MPS.Preparation.ApproximationError`.

## Main declarations

* `MPSTensor.exists_norm_transferMap_pow_sub_le` — the transfer-map gap.
* `MPSTensor.exists_norm_polarPos_blockTensor_sub_le` — the rate of `P_q → P_∞`.

## References

* arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification" (eqs.
  `difference` and `intermediate`).
* arXiv:2307.01696, eqs. (5) and (8), and eq. (S9) for the range `0 < γ < 1/2`.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-! ### The transfer-map gap at rate `e^{-2γ/ξ}` -/

/-- `-γ/ξ = γ log|λ₂|` for the correlation length `ξ = -1/log|λ₂|` (the value `ξ = 0` at
`λ₂ = 0`, or at `|λ₂| = 1`, gives `0` on both sides). -/
theorem neg_div_correlationLength (γ : ℝ) (lam₂ : ℂ) :
    -γ / correlationLength lam₂ = γ * Real.log ‖lam₂‖ := by
  unfold correlationLength
  rcases eq_or_ne (Real.log ‖lam₂‖) 0 with h | h
  · simp [h]
  · field_simp

/-- For `0 < γ < 1/2`, the rate `e^{-2γ/ξ} = |λ₂|^{2γ}` strictly exceeds every `a < 1` with
`a ≤ |λ₂|`. This is where `γ < 1/2` enters: `|λ₂|^{2γ} > |λ₂|` for `|λ₂| < 1`.

arXiv:2307.01696, eq. (S9) (`0 < γ < 1/2`), and arXiv:2103.13367, the choice `β < α/2` after
eq. `finished`. -/
theorem lt_exp_neg_div_correlationLength_sq {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2)
    {lam₂ : ℂ} {a : ℝ} (ha1 : a < 1) (ha : a ≤ ‖lam₂‖) :
    a < Real.exp (-γ / correlationLength lam₂) ^ 2 := by
  rw [neg_div_correlationLength, ← Real.exp_nat_mul]
  push_cast
  rcases le_or_gt 0 (Real.log ‖lam₂‖) with hl | hl
  · have : 1 ≤ Real.exp (2 * (γ * Real.log ‖lam₂‖)) := Real.one_le_exp (by positivity)
    linarith
  · have ht : 0 < ‖lam₂‖ := by
      rcases (norm_nonneg lam₂).lt_or_eq with h | h
      · exact h
      · rw [← h, Real.log_zero] at hl; exact absurd hl (lt_irrefl 0)
    calc a ≤ ‖lam₂‖ := ha
      _ = Real.exp (Real.log ‖lam₂‖) := (Real.exp_log ht).symm
      _ < Real.exp (2 * (γ * Real.log ‖lam₂‖)) := Real.exp_lt_exp.2 (by nlinarith)

/-- The eigenvalues of `E_A - |σ⟩⟨1|` for a normal tensor: each has modulus `< 1` and at most
`|λ₂|` when `λ₂` bounds the moduli of the eigenvalues of `E_A` other than `1`.

arXiv:2103.13367, the decomposition `τ_AA = τ_BB + R` before eq. `difference`: `R` carries the
Jordan blocks of the subleading eigenvalues. -/
theorem norm_le_of_hasEigenvalue_transferMap_sub_fixedPointProj [NeZero D] (A : MPSTensor d D)
    (hN : IsNormalTensor A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace ≠ 0) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {z : ℂ} (hz : Module.End.HasEigenvalue (Kraus.transferMap A - fixedPointProj σ htr) z) :
    ‖z‖ < 1 ∧ ‖z‖ ≤ ‖lam₂‖ := by
  classical
  have hCh := Kraus.isChannel_mapLM A hA
  have hIrr := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hN.no_invariant_proj
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at htr
  refine ⟨compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel _ hCh hIrr σ hfix hσ0
    htr hN.primitive_transfer z hz, ?_⟩
  obtain ⟨X, hX⟩ := hz.exists_hasEigenvector
  have hNX := Module.End.mem_eigenspace_iff.mp hX.1
  have hEX : Kraus.transferMap A X = z • X + fixedPointProj σ htr X := by
    rw [← sub_eq_iff_eq_add]; exact hNX
  by_cases htrX : X.trace = 0
  · have hPX : fixedPointProj σ htr X = 0 := by simp [fixedPointProj, htrX]
    rw [hPX, add_zero] at hEX
    refine hlam z (hasEigenvalue_of_eigenvector_eq _ z X hEX hX.2) fun hz1 => hX.2 ?_
    rw [hz1, one_smul] at hEX
    exact fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel hCh hIrr X hEX htrX
  · have htp := hCh.tp X
    rw [hEX, Matrix.trace_add, Matrix.trace_smul] at htp
    have hPtr : (fixedPointProj σ htr X).trace = X.trace := by
      change ((X.trace / σ.trace) • σ).trace = X.trace
      rw [Matrix.trace_smul, smul_eq_mul, div_mul_cancel₀ _ htr]
    rw [hPtr, smul_eq_mul, add_eq_right, mul_eq_zero] at htp
    rw [htp.resolve_right htrX, norm_zero]
    exact norm_nonneg _

open scoped Matrix.Norms.L2Operator in
/-- **Transfer-map gap.** Let `A` be normal in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`,
`σ > 0`, `Tr σ = 1`, let `λ₂` bound the moduli of the eigenvalues of `E_A` other than `1`, with
correlation length `ξ`, and let `0 < γ < 1/2`. Then there is `C > 0` with
`‖E_A^n(X) - Tr(X) σ‖ ≤ C e^{-2γ n/ξ} ‖X‖` for all `n` and `X`.

arXiv:2103.13367, eq. `difference`: `‖R‖_F ≤ Λ(q) e^{-qα}` with `|λ₁| = e^{-qα}` for the blocked
transfer matrix, where `R = τ_AA - τ_BB` is the remainder of the `q`-blocked transfer matrix. Here
the unblocked `E_A^n` is bounded directly, and the polynomial prefactor `Λ` is absorbed into the
rate `e^{-2γ/ξ} > |λ₂|`. -/
theorem exists_norm_transferMap_pow_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
      ‖(Kraus.transferMap A ^ n) X - X.trace • σ‖ ≤
        C * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ n * ‖X‖ := by
  classical
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  have hCh := Kraus.isChannel_mapLM A hA
  have htr' : σ.trace ≠ 0 := by simp [htr]
  let Φ : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) ≃ₐ[ℂ] _ :=
    Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
  let N := Kraus.transferMap A - fixedPointProj σ htr'
  set x := Real.exp (-γ / correlationLength lam₂)
  let r : ℝ≥0 := ⟨x ^ 2, by positivity⟩
  have hrad : spectralRadius ℂ (Φ N) < (r : ℝ≥0∞) := by
    refine spectrum.spectralRadius_lt_of_forall_lt _ fun z hz => ?_
    rw [AlgEquiv.spectrum_eq] at hz
    obtain ⟨h1, h2⟩ := norm_le_of_hasEigenvalue_transferMap_sub_fixedPointProj A hNT hA hσ htr'
      hfix hlam (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    exact lt_exp_neg_div_correlationLength_sq hγ0 hγ h1 h2
  obtain ⟨C₀, hC₀, hgeom⟩ := geometric_apply_bound_of_spectralRadius_lt (Φ N) r hrad
  let P' := Φ (fixedPointProj σ htr')
  refine ⟨C₀ + (1 + ‖P'‖), by positivity, fun n X => ?_⟩
  have hPX : fixedPointProj σ htr' X = X.trace • σ := by
    change (X.trace / σ.trace) • σ = X.trace • σ
    rw [htr, div_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_zero, mul_one, Module.End.one_apply, ← hPX]
    calc ‖X - fixedPointProj σ htr' X‖ ≤ ‖X‖ + ‖P' X‖ := norm_sub_le _ _
      _ ≤ ‖X‖ + ‖P'‖ * ‖X‖ := by gcongr; exact P'.le_opNorm X
      _ ≤ (C₀ + (1 + ‖P'‖)) * ‖X‖ := by nlinarith [norm_nonneg X]
  · have hpow := pow_eq_fixedPointProj_add_compl_pow (E := Kraus.transferMap A) htr' hCh.tp
      hfix hn
    calc ‖(Kraus.transferMap A ^ n) X - X.trace • σ‖ = ‖((Φ N) ^ n) X‖ := by
          rw [hpow, ← hPX, LinearMap.add_apply, add_sub_cancel_left, ← map_pow]; rfl
      _ ≤ C₀ * (r : ℝ) ^ n * ‖X‖ := hgeom n X
      _ ≤ (C₀ + (1 + ‖P'‖)) * (x ^ 2) ^ n * ‖X‖ := by
          have : 0 ≤ ‖P'‖ := norm_nonneg _
          have hr : (r : ℝ) = x ^ 2 := rfl
          rw [hr]
          gcongr
          linarith

/-! ### The positive part approaches the fixed point at rate `e^{-γ q/ξ}` -/

open scoped Matrix.Norms.L2Operator in
/-- **Entrywise transfer of the gap.** If `‖E^n(X) - Tr(X) σ‖ ≤ C rⁿ ‖X‖`, then a matrix whose
entries are entries of `E^n(Y_{ab}) - Tr(Y_{ab}) σ`, for a fixed family of matrices `Y_{ab}` and
fixed positions, has norm at most `K rⁿ`, with `K` independent of `n`. Both the Gram matrices
of the blocked tensor and the transfer matrices of `E_A^n` are such rearrangements. -/
theorem exists_norm_le_of_entry_eq_pow_sub {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (E : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (σ : Matrix (Fin D) (Fin D) ℂ) {C r : ℝ} (hC : 0 ≤ C)
    (hgap : ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
      ‖(E ^ n) X - X.trace • σ‖ ≤ C * r ^ n * ‖X‖)
    (Y : ι → κ → Matrix (Fin D) (Fin D) ℂ) (i j : ι → κ → Fin D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (G : Matrix ι κ ℂ),
      (∀ a b, G a b = ((E ^ n) (Y a b) - (Y a b).trace • σ) (i a b) (j a b)) →
        ‖G‖ ≤ K * r ^ n := by
  classical
  obtain ⟨K₂, hK₂, hent⟩ := Matrix.exists_norm_entry_le_mul_l2_opNorm (m := Fin D) (n := Fin D)
  refine ⟨∑ a, ∑ b, K₂ * C * ‖Y a b‖ * ‖(Matrix.single a b 1 : Matrix ι κ ℂ)‖,
    by positivity, fun n G hG => ?_⟩
  refine (Matrix.l2_opNorm_le_sum_norm_entry _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [hG]
  calc ‖((E ^ n) (Y a b) - (Y a b).trace • σ) (i a b) (j a b)‖ *
        ‖(Matrix.single a b 1 : Matrix ι κ ℂ)‖
      ≤ (K₂ * (C * r ^ n * ‖Y a b‖)) * ‖(Matrix.single a b 1 : Matrix ι κ ℂ)‖ := by
        gcongr
        exact (hent _ _ _).trans (by gcongr; exact hgap n _)
    _ = K₂ * C * ‖Y a b‖ * ‖(Matrix.single a b 1 : Matrix ι κ ℂ)‖ * r ^ n := by ring


/-- The entries of `σᵀ ⊗ 1` are those of the rank-one map `X ↦ Tr(X) σ`, rearranged as in
`conjTranspose_physicalMatrix_mul_apply`. -/
theorem transpose_kronecker_one_apply (σ : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D × Fin D) :
    (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) a b =
      ((Matrix.single b.2 a.2 (1 : ℂ)).trace • σ) b.1 a.1 := by
  by_cases hab : a.2 = b.2
  · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hab, Matrix.trace_single_eq_same]
  · simp [Matrix.kroneckerMap_apply, hab, Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]

open scoped Matrix.Norms.L2Operator in
/-- **Gram matrices.** In the setting of `exists_norm_transferMap_pow_sub_le`, the Gram matrix
`B_q† B_q = P_q²` of the `q`-site blocked tensor is `e^{-2γ q/ξ}`-close to
`σᵀ ⊗ 1 = P_∞²`.

arXiv:2103.13367, eq. `difference` (`τ_AA = τ_BB + R`, read with the lower lines as input). -/
theorem exists_norm_gram_blockTensor_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖(physicalMatrix (blockTensor A q))ᴴ * physicalMatrix (blockTensor A q) -
          σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q := by
  obtain ⟨C, hC, hgap⟩ := exists_norm_transferMap_pow_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K, hK, h⟩ := exists_norm_le_of_entry_eq_pow_sub (Kraus.transferMap A) σ hC.le hgap
    (fun (a b : Fin D × Fin D) => Matrix.single b.2 a.2 (1 : ℂ))
    (fun _ b => b.1) (fun a _ => a.1)
  refine ⟨K, hK, fun q => h q _ fun a b => ?_⟩
  rw [Matrix.sub_apply, conjTranspose_physicalMatrix_mul_apply, transferMap_blockTensor,
    transpose_kronecker_one_apply, Matrix.sub_apply]

/-- The fixed-point tensor `P_∞`, read as a `D² × D²` matrix, is the square root of
`σᵀ ⊗ 1`. -/
theorem sqrt_transpose_kronecker_one {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) :
    CFC.sqrt (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) =
      (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
  rw [(Matrix.posSemidef_transpose_iff.2 hσ).sqrt_kronecker Matrix.PosSemidef.one,
    CFC.sqrt_one, hσ.sqrt_transpose]

open scoped Matrix.Norms.L2Operator in
/-- **Positive parts.** In the setting of `exists_norm_transferMap_pow_sub_le`, the positive
part `P_q = (B_q† B_q)^{1/2}` of the `q`-site blocked tensor satisfies
`‖P_q - P_∞‖ ≤ K e^{-γ q/ξ}`, with `P_∞ = (√σ)ᵀ ⊗ 1`.

arXiv:2103.13367, eq. `intermediate`: `‖A' - B'‖_∞ ≤ √‖(A')†A' - (B')†B'‖`. -/
theorem exists_norm_polarPos_blockTensor_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖Matrix.polarPos (physicalMatrix (blockTensor A q)) -
          (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  obtain ⟨K, hK, h⟩ := exists_norm_gram_blockTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun q => ?_⟩
  have h1 := CFC.norm_sqrt_sub_sqrt_le
    (Matrix.posSemidef_conjTranspose_mul_self (physicalMatrix (blockTensor A q))).nonneg
    ((Matrix.posSemidef_transpose_iff.2 hσ.posSemidef).kronecker Matrix.PosSemidef.one).nonneg
  rw [sqrt_transpose_kronecker_one hσ.posSemidef] at h1
  refine h1.trans ?_
  have hx : 0 ≤ Real.exp (-γ / correlationLength lam₂) ^ q := by positivity
  calc Real.sqrt ‖(physicalMatrix (blockTensor A q))ᴴ * physicalMatrix (blockTensor A q) -
        σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖
      ≤ Real.sqrt (K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q) :=
        Real.sqrt_le_sqrt (h q)
    _ = Real.sqrt K * Real.exp (-γ / correlationLength lam₂) ^ q := by
        rw [Real.sqrt_mul hK, ← pow_mul, mul_comm 2 q, pow_mul, Real.sqrt_sq hx]

end MPSTensor
