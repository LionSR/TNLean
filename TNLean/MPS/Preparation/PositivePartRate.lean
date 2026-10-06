/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CStarSqrtLipschitz
import TNLean.Algebra.MatrixEntryNorm
import TNLean.MPS.Core.Correlations
import TNLean.MPS.Preparation.ApproximatingState

/-!
# Rate of convergence of the positive part

Let `A` be a normal tensor in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1`
(arXiv:2307.01696, eq. (5)), let `λ₂` bound the moduli of the eigenvalues of `E_A` other than
`1`, with correlation length `ξ = -1/log|λ₂|`, and let `0 < γ < 1`. This file proves the
first two steps of the approximation estimate of Piroli, Styliaris, and Cirac (arXiv:2103.13367,
Supplemental Material, "Proof of Theorem MPS_classification"):

1. **Transfer-map gap.** `‖E_A^n(X) - Tr(X) σ‖ ≤ C e^{-γ n/ξ} ‖X‖` (compare arXiv:2103.13367,
   eq. (21), `‖R‖_F ≤ Λ(q) e^{-qα}` with `|λ₁| = e^{-qα}` for the blocked transfer matrix); the rate
   `e^{-γ/ξ} = |λ₂|^γ` exceeds the spectral radius of `E_A - |σ⟩⟨1|` because `γ < 1`.
2. **Positive parts.** The positive part `P_q` of the polar decomposition of the `q`-site blocked
   tensor satisfies `‖P_q - P_∞‖ ≤ K e^{-γ q/ξ}`, from the rearrangement
   `P_q² - P_∞² ≅ E_A^q - |σ⟩⟨1|` and the Lipschitz bound `‖√a - √b‖ ≤ ‖a - b‖ / √c` for
   `b ≥ c > 0` (`CFC.norm_sqrt_sub_sqrt_le_div` in `TNLean.Algebra.CStarSqrtLipschitz`), which
   applies because `P_∞² = σᵀ ⊗ 1` is positive definite.

The earlier estimates use the Hölder bound `‖√a - √b‖ ≤ √‖a - b‖` in step 2
(arXiv:2103.13367, Supplemental Material, eq. (26)), which halves the exponent. This gives the
rate `e^{-βq}` with `β < α/2` of arXiv:2103.13367, eq. (34), and the range `0 < γ < 1/2` of
arXiv:2307.01696, Lemma 1 and Supplemental Material, eq. (S9). The Lipschitz step at the positive
definite point `P_∞²` is taken from arXiv:2606.24475, App. B3, eqs. (S27)–(S32), where it is
proved for diagonalizable transfer matrices; eqs. (S33)–(S38) there extend it to the remaining
normal tensors at every correlation length larger than `ξ`. The proof here covers every normal
tensor directly, from the spectral radius of `E_A - |σ⟩⟨1|`. The rate `e^{-γ q/ξ}` of step 2
feeds the telescoping estimate in `TNLean.MPS.Preparation.ApproximationError`.

## Main declarations

* `MPSTensor.exp_neg_div_correlationLength_le_one` — `e^{-γ/ξ} ≤ 1` for `|λ₂| ≤ 1`.
* `MPSTensor.exists_norm_transferMap_pow_sub_le` — the transfer-map gap.
* `MPSTensor.exists_norm_gram_transferMatrix_sub_le` — uniform two-sided Gram/transfer bounds.
* `MPSTensor.exists_norm_polarPos_blockTensor_sub_le` — the rate of `P_q → P_∞`.

## References

* arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification" (eqs.
  (21), (26) and (34)).
* arXiv:2307.01696, eqs. (5) and (8), and Lemma 1 and eq. (S9) for the range `0 < γ < 1/2`.
* arXiv:2606.24475, App. B3, eqs. (S27)–(S38), for the Lipschitz step.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-! ### The transfer-map gap at rate `e^{-γ/ξ}` -/

/-- `-γ/ξ = γ log|λ₂|` for the correlation length `ξ = -1/log|λ₂|` (the value `ξ = 0` at
`λ₂ = 0`, or at `|λ₂| = 1`, gives `0` on both sides). -/
theorem neg_div_correlationLength (γ : ℝ) (lam₂ : ℂ) :
    -γ / correlationLength lam₂ = γ * Real.log ‖lam₂‖ := by
  unfold correlationLength
  rcases eq_or_ne (Real.log ‖lam₂‖) 0 with h | h
  · simp [h]
  · field_simp

/-- `e^{-2γ/ξ} = (e^{-γ/ξ})²`. -/
theorem exp_neg_two_mul_div_correlationLength (γ : ℝ) (lam₂ : ℂ) :
    Real.exp (-(2 * γ) / correlationLength lam₂) =
      Real.exp (-γ / correlationLength lam₂) ^ 2 := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e^{-γ/ξ} ≤ 1` for `|λ₂| ≤ 1` and `γ ≥ 0`. -/
theorem exp_neg_div_correlationLength_le_one {γ : ℝ} (hγ0 : 0 ≤ γ) {lam₂ : ℂ}
    (hl : ‖lam₂‖ ≤ 1) : Real.exp (-γ / correlationLength lam₂) ≤ 1 := by
  rw [neg_div_correlationLength, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos hγ0 (Real.log_nonpos (norm_nonneg _) hl)

/-- For `0 < γ < 1`, the rate `e^{-γ/ξ} = |λ₂|^γ` strictly exceeds every `a < 1` with
`a ≤ |λ₂|`. This is where `γ < 1` enters: `|λ₂|^γ > |λ₂|` for `|λ₂| < 1`. -/
theorem lt_exp_neg_div_correlationLength {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1)
    {lam₂ : ℂ} {a : ℝ} (ha1 : a < 1) (ha : a ≤ ‖lam₂‖) :
    a < Real.exp (-γ / correlationLength lam₂) := by
  rw [neg_div_correlationLength]
  rcases le_or_gt 0 (Real.log ‖lam₂‖) with hl | hl
  · have : 1 ≤ Real.exp (γ * Real.log ‖lam₂‖) := Real.one_le_exp (by positivity)
    linarith
  · have ht : 0 < ‖lam₂‖ := by
      rcases (norm_nonneg lam₂).lt_or_eq with h | h
      · exact h
      · rw [← h, Real.log_zero] at hl; exact absurd hl (lt_irrefl 0)
    calc a ≤ ‖lam₂‖ := ha
      _ = Real.exp (Real.log ‖lam₂‖) := (Real.exp_log ht).symm
      _ < Real.exp (γ * Real.log ‖lam₂‖) := Real.exp_lt_exp.2 (by nlinarith)

/-- The eigenvalues of `E_A - |σ⟩⟨1|` for a normal tensor: each has modulus `< 1` and at most
`|λ₂|` when `λ₂` bounds the moduli of the eigenvalues of `E_A` other than `1`.

arXiv:2103.13367, the decomposition `τ_AA = τ_BB + R` before eq. `eq:difference`: `R` carries the
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
correlation length `ξ`, and let `0 < γ < 1`. Then there is `C > 0` with
`‖E_A^n(X) - Tr(X) σ‖ ≤ C e^{-γ n/ξ} ‖X‖` for all `n` and `X`.

arXiv:2103.13367, Supplemental Material, eq. (21), bounds `‖R‖_F ≤ Λ(q) e^{-qα}` with
`|λ₁| = e^{-qα}` for the blocked transfer matrix, where `R = τ_AA - τ_BB` is the remainder of
the `q`-blocked transfer matrix. Here the unblocked `E_A^n` is bounded directly, and the
polynomial prefactor `Λ` is absorbed into the rate `e^{-γ/ξ} > |λ₂|`. -/
theorem exists_norm_transferMap_pow_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
      ‖(Kraus.transferMap A ^ n) X - X.trace • σ‖ ≤
        C * Real.exp (-γ / correlationLength lam₂) ^ n * ‖X‖ := by
  classical
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  have hCh := Kraus.isChannel_mapLM A hA
  have htr' : σ.trace ≠ 0 := by simp [htr]
  let Φ : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) ≃ₐ[ℂ] _ :=
    Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
  let N := Kraus.transferMap A - fixedPointProj σ htr'
  set x := Real.exp (-γ / correlationLength lam₂)
  let r : ℝ≥0 := ⟨x, by positivity⟩
  have hrad : spectralRadius ℂ (Φ N) < (r : ℝ≥0∞) := by
    refine spectrum.spectralRadius_lt_of_forall_lt _ fun z hz => ?_
    rw [AlgEquiv.spectrum_eq] at hz
    obtain ⟨h1, h2⟩ := norm_le_of_hasEigenvalue_transferMap_sub_fixedPointProj A hNT hA hσ htr'
      hfix hlam (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    exact lt_exp_neg_div_correlationLength hγ0 hγ h1 h2
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
      _ ≤ (C₀ + (1 + ‖P'‖)) * x ^ n * ‖X‖ := by
          have : 0 ≤ ‖P'‖ := norm_nonneg _
          have hr : (r : ℝ) = x := rfl
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
/-- The Gram and transfer errors are uniformly equivalent whenever their reference entries
are related by the same reshuffling as the actual tensor. The constant depends only on the
bond dimension and is chosen before the tensor, reference map, and reference matrix.
Both matrix norms are `L²` operator norms. The entry identity is the regrouping in
arXiv:2307.01696, eq. (8), and arXiv:2103.13367, Supplemental Material, eqs. (19) and (21). -/
theorem exists_norm_gram_transferMatrix_sub_le_of_entries (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {d : ℕ} (A : MPSTensor d D)
      (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
      (G : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ),
      (∀ a b, G a b = T (Matrix.single b.2 a.2 1) b.1 a.1) →
      (‖(physicalMatrix A)ᴴ * physicalMatrix A - G‖ ≤
        K * ‖transferMatrix (Kraus.transferMap A) - transferMatrix T‖) ∧
      (‖transferMatrix (Kraus.transferMap A) - transferMatrix T‖ ≤
        K * ‖(physicalMatrix A)ᴴ * physicalMatrix A - G‖) := by
  classical
  let R : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    { toFun := fun T a b => T (a.1, b.1) (a.2, b.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Rc := LinearMap.toContinuousLinearMap R
  have hbound (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
      ‖Rc X‖ ≤ (‖Rc‖ + 1) * ‖X‖ :=
    (Rc.le_opNorm X).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg X))
  refine ⟨‖Rc‖ + 1, by positivity, fun {d} A T G hG => ?_⟩
  have hgram : (physicalMatrix A)ᴴ * physicalMatrix A - G =
      Rc (transferMatrix (Kraus.transferMap A) - transferMatrix T) := by
    ext a b
    rw [Matrix.sub_apply, conjTranspose_physicalMatrix_mul_apply, hG]
    rfl
  constructor
  · rw [hgram]
    exact hbound _
  · have hinv : transferMatrix (Kraus.transferMap A) - transferMatrix T =
        Rc ((physicalMatrix A)ᴴ * physicalMatrix A - G) := by
      rw [hgram]
      rfl
    rw [hinv]
    exact hbound _

open scoped Matrix.Norms.L2Operator in
/-- The physical Gram error and transfer-matrix error bound one another in the `L²`
operator norm, with one positive constant depending only on the bond dimension. The
constant is chosen before the physical dimension, tensor, and positive semidefinite
reference. No trace normalization, fixed-point, or faithfulness hypothesis is needed.

The reshuffling is an involutive linear permutation of entries, as in arXiv:2103.13367,
Supplemental Material, equations (19) and (21), and arXiv:2307.01696, equation (8).
Positivity is used only to identify the transfer map of `fixedPointTensor σ` with
`X ↦ Tr(X) σ`; the reset-map reshuffling itself is an algebraic identity. -/
theorem exists_norm_gram_transferMatrix_sub_le (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {d : ℕ} (A : MPSTensor d D)
      (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosSemidef →
      (‖(physicalMatrix A)ᴴ * physicalMatrix A -
          σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * ‖transferMatrix (Kraus.transferMap A) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖) ∧
      (‖transferMatrix (Kraus.transferMap A) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
        K * ‖(physicalMatrix A)ᴴ * physicalMatrix A -
          σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖) := by
  obtain ⟨K, hK, h⟩ := exists_norm_gram_transferMatrix_sub_le_of_entries D
  refine ⟨K, hK, fun {d} A σ hσ => h A _ _ fun a b => ?_⟩
  rw [transpose_kronecker_one_apply, transferMap_fixedPointTensor_apply hσ]

open scoped Matrix.Norms.L2Operator in
/-- **Gram matrices.** In the setting of `exists_norm_transferMap_pow_sub_le`, the Gram matrix
`B_q† B_q = P_q²` of the `q`-site blocked tensor is `e^{-γ q/ξ}`-close to
`σᵀ ⊗ 1 = P_∞²`.

arXiv:2103.13367, Supplemental Material, eqs. (19) and (21) (`τ_AA = τ_BB + R`, read with the
lower lines as input). -/
theorem exists_norm_gram_blockTensor_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖(physicalMatrix (blockTensor A q))ᴴ * physicalMatrix (blockTensor A q) -
          σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q := by
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
/-- **Positive parts.** In the setting of `exists_norm_transferMap_pow_sub_le`, with
`0 < γ < 1`, the positive part `P_q = (B_q† B_q)^{1/2}` of the `q`-site blocked tensor satisfies
`‖P_q - P_∞‖ ≤ K e^{-γ q/ξ}`, with `P_∞ = (√σ)ᵀ ⊗ 1`.

arXiv:2103.13367, Supplemental Material, eq. (26) and the sentence after it, applies the Hölder
bound `‖√X - √Y‖_∞ ≤ √‖X - Y‖_∞` to `\tilde{A} = √(A†A)` and `\tilde{B} = √(B†B)`. This halves
the exponent and gives the range `0 < γ < 1/2` of arXiv:2307.01696, Lemma 1 and Supplemental
Material, eq. (S9). Here `P_∞² = σᵀ ⊗ 1` is positive definite, so the square root is Lipschitz
at that point (`CFC.norm_sqrt_sub_sqrt_le_div`), and the rate of the Gram matrices passes to the
positive parts with the same exponent. This Lipschitz step is due to Murota, Sauvage, Ballarin,
Matos, and Rinaldi, arXiv:2606.24475, App. B3, eqs. (S27)–(S32), for diagonalizable transfer
matrices; eqs. (S33)–(S38) there extend it to the remaining normal tensors at every correlation
length larger than `ξ`. -/
theorem exists_norm_polarPos_blockTensor_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖Matrix.polarPos (physicalMatrix (blockTensor A q)) -
          (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  obtain ⟨K, hK, h⟩ := exists_norm_gram_blockTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  have hpd : (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).PosDef :=
    (Matrix.PosDef.transpose_iff.2 hσ).kronecker Matrix.PosDef.one
  have hsp : IsStrictlyPositive (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := hpd.isStrictlyPositive
  obtain ⟨L, hL, hlip⟩ := hsp.exists_norm_sqrt_sub_sqrt_le
  refine ⟨L * K, by positivity, fun q => ?_⟩
  have h1 := hlip _
    (Matrix.posSemidef_conjTranspose_mul_self (physicalMatrix (blockTensor A q))).nonneg
  rw [sqrt_transpose_kronecker_one hσ.posSemidef] at h1
  rw [mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left (h q) hL)

end MPSTensor
