/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import TNLean.MPS.Core.Correlations
import TNLean.MPS.Preparation.ApproximatingState

/-!
# Rate of convergence of the positive part

Let `A` be a normal tensor in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1`
(arXiv:2307.01696, eq. (5)), let `λ₂` bound the moduli of the eigenvalues of `E_A` other than
`1`, with correlation length `ξ = -1/log|λ₂|`, and let `0 < γ < 1/2`. This file proves the
first two steps of the approximation estimate of Piroli, Styliaris, and Cirac (arXiv:2103.13367,
Supplemental Material, "Proof of Theorem MPS_classification"):

1. **Transfer-map gap.** `‖E_A^n(X) - Tr(X) σ‖ ≤ C e^{-2γ n/ξ} ‖X‖` (eq. `difference`); the rate
   `e^{-2γ/ξ} = |λ₂|^{2γ}` exceeds the spectral radius of `E_A - |σ⟩⟨1|` because `2γ < 1`.
2. **Positive parts.** The positive part `P_q` of the polar decomposition of the `q`-site blocked
   tensor satisfies `‖P_q - P_∞‖ ≤ K e^{-γ q/ξ}` (eq. `intermediate`), from the rearrangement
   `P_q² - P_∞² ≅ E_A^q - |σ⟩⟨1|` and `‖√a - √b‖ ≤ √‖a - b‖`.

The rate `e^{-γ q/ξ}` of step 2 feeds the telescoping estimate in
`TNLean.MPS.Preparation.ApproximationError`.

## Main declarations

* `CFC.norm_sqrt_sub_sqrt_le` — `‖√a - √b‖ ≤ √‖a - b‖` in a C⋆-algebra.
* `MPSTensor.exists_norm_transferMap_pow_sub_le` — the transfer-map gap.
* `MPSTensor.exists_norm_polarPos_blockTensor_sub_le` — the rate of `P_q → P_∞`.

## References

* arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification" (eqs.
  `difference` and `intermediate`).
* arXiv:2307.01696, eqs. (5) and (8), and eq. (S9) for the range `0 < γ < 1/2`.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal


/-! ### Square roots in a C⋆-algebra -/

/-- A selfadjoint element with `-r ≤ a ≤ r` has norm at most `r`. -/
theorem IsSelfAdjoint.norm_le_of_le_algebraMap {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h₁ : a ≤ algebraMap ℝ A r) (h₂ : -algebraMap ℝ A r ≤ a) : ‖a‖ ≤ r := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim a 0, norm_zero]; exact hr
  have hup := (le_algebraMap_iff_spectrum_le (R := ℝ) ha).1 h₁
  have hlo := (algebraMap_le_iff_le_spectrum (R := ℝ) ha).1 (by rwa [map_neg])
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
  · exact hup _ h
  · linarith [hlo _ h]

/-- Upper half of `CFC.norm_sqrt_sub_sqrt_le`: `√a - √b ≤ √‖a - b‖`. -/
theorem CFC.sqrt_sub_sqrt_le_algebraMap {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    CFC.sqrt a - CFC.sqrt b ≤ algebraMap ℝ A (Real.sqrt ‖a - b‖) := by
  set ε := ‖a - b‖
  set S := CFC.sqrt b
  set c := algebraMap ℝ A (Real.sqrt ε)
  have h₁ : a ≤ b + algebraMap ℝ A ε :=
    sub_le_iff_le_add'.1 (IsSelfAdjoint.le_algebraMap_norm_self (ha.isSelfAdjoint.sub hb.isSelfAdjoint))
  have hS : 0 ≤ S := CFC.sqrt_nonneg b
  have hcS : c * S = Real.sqrt ε • S := (Algebra.smul_def _ _).symm
  have hSc : S * c = Real.sqrt ε • S := by rw [← Algebra.commutes, hcS]
  have hcc : c * c = algebraMap ℝ A ε := by
    rw [← map_mul, Real.mul_self_sqrt (norm_nonneg _)]
  have hc : 0 ≤ c := by
    simp only [c, Algebra.algebraMap_eq_smul_one]; exact smul_nonneg (Real.sqrt_nonneg _) zero_le_one
  have hsq : b + algebraMap ℝ A ε ≤ (S + c) ^ 2 := by
    have hexp : (S + c) ^ 2 = b + algebraMap ℝ A ε + (Real.sqrt ε • S + Real.sqrt ε • S) := by
      rw [sq, add_mul, mul_add, mul_add, CFC.sqrt_mul_sqrt_self b hb, hcS, hSc, hcc]
      abel
    rw [hexp]
    exact le_add_of_nonneg_right
      (add_nonneg (smul_nonneg (Real.sqrt_nonneg _) hS) (smul_nonneg (Real.sqrt_nonneg _) hS))
  have h₂ : CFC.sqrt a ≤ S + c :=
    calc CFC.sqrt a ≤ CFC.sqrt (b + algebraMap ℝ A ε) := CFC.sqrt_le_sqrt _ _ h₁
      _ ≤ CFC.sqrt ((S + c) ^ 2) := CFC.sqrt_le_sqrt _ _ hsq
      _ = S + c := CFC.sqrt_sq (S + c) (add_nonneg hS hc)
  exact sub_le_iff_le_add'.2 h₂

/-- **Square roots are `1/2`-Hölder**: for `a, b ≥ 0` in a C⋆-algebra,
`‖√a - √b‖ ≤ √‖a - b‖`.

arXiv:2103.13367, eq. `intermediate` (the bound `‖√X - √Y‖_∞ ≤ √‖X - Y‖_∞` for `X, Y ≥ 0`,
quoted there from Bhatia). -/
theorem CFC.norm_sqrt_sub_sqrt_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖CFC.sqrt a - CFC.sqrt b‖ ≤ Real.sqrt ‖a - b‖ := by
  refine IsSelfAdjoint.norm_le_of_le_algebraMap
    ((CFC.sqrt_nonneg a).isSelfAdjoint.sub (CFC.sqrt_nonneg b).isSelfAdjoint)
    (Real.sqrt_nonneg _) (CFC.sqrt_sub_sqrt_le_algebraMap ha hb) ?_
  have h := CFC.sqrt_sub_sqrt_le_algebraMap hb ha
  rw [norm_sub_rev] at h
  rw [neg_le, neg_sub]
  exact h

/-! ### Entries and norms of matrices -/

section MatrixEntries

open scoped Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The operator norm of a matrix is at most the sum of its entries weighted by the norms of the
matrix units. -/
theorem Matrix.l2_opNorm_le_sum_norm_entry (M : Matrix m n ℂ) :
    ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖(Matrix.single i j 1 : Matrix m n ℂ)‖ := by
  conv_lhs => rw [M.matrix_eq_sum_single]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], norm_smul]

omit [DecidableEq m] in
/-- The entries of a matrix are bounded by a fixed multiple of its operator norm. -/
theorem Matrix.exists_norm_entry_le_mul_l2_opNorm :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Y : Matrix m n ℂ) (i : m) (j : n), ‖Y i j‖ ≤ K * ‖Y‖ := by
  let f : m → n → (Matrix m n ℂ →L[ℂ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  refine ⟨∑ i, ∑ j, ‖f i j‖, by positivity, fun Y i j => ?_⟩
  calc ‖Y i j‖ = ‖f i j Y‖ := rfl
    _ ≤ ‖f i j‖ * ‖Y‖ := (f i j).le_opNorm Y
    _ ≤ (∑ i, ∑ j, ‖f i j‖) * ‖Y‖ := by
        gcongr
        exact (Finset.single_le_sum (f := fun j => ‖f i j‖) (fun _ _ => by positivity)
          (Finset.mem_univ j)).trans (Finset.single_le_sum
            (f := fun i => ∑ j, ‖f i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))

/-- A linear map between finite-dimensional normed spaces is bounded. -/
theorem LinearMap.exists_norm_apply_le_mul {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E →ₗ[ℂ] F) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖f x‖ ≤ K * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap f‖, norm_nonneg _,
    fun x => (LinearMap.toContinuousLinearMap f).le_opNorm x⟩

end MatrixEntries

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

arXiv:2103.13367, eq. `difference`: `‖R^q‖ ≤ Λ(q) e^{-αq}` with `e^{-α} = |λ₁|`; the polynomial
prefactor `Λ(q)` is absorbed into the rate `e^{-2γ/ξ} > |λ₂|`. -/
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
  obtain ⟨K₂, hK₂, hent⟩ :=
    Matrix.exists_norm_entry_le_mul_l2_opNorm (m := Fin D) (n := Fin D)
  set r := Real.exp (-γ / correlationLength lam₂) ^ 2
  refine ⟨∑ a : Fin D × Fin D, ∑ b : Fin D × Fin D,
    K₂ * C * ‖(Matrix.single b.2 a.2 1 : Matrix (Fin D) (Fin D) ℂ)‖ *
      ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖,
    by positivity, fun q => ?_⟩
  refine (Matrix.l2_opNorm_le_sum_norm_entry _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  set Y : Matrix (Fin D) (Fin D) ℂ := Matrix.single b.2 a.2 1
  have hab : ((physicalMatrix (blockTensor A q))ᴴ * physicalMatrix (blockTensor A q) -
      σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) a b =
      ((Kraus.transferMap A ^ q) Y - Y.trace • σ) b.1 a.1 := by
    rw [Matrix.sub_apply, conjTranspose_physicalMatrix_mul_apply, transferMap_blockTensor,
      transpose_kronecker_one_apply, Matrix.sub_apply]
  rw [hab]
  have hr : 0 ≤ r := by positivity
  calc ‖((Kraus.transferMap A ^ q) Y - Y.trace • σ) b.1 a.1‖ *
        ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖
      ≤ (K₂ * (C * r ^ q * ‖Y‖)) *
          ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ := by
        gcongr
        exact (hent _ _ _).trans (by gcongr; exact hgap q Y)
    _ = K₂ * C * ‖Y‖ *
          ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ * r ^ q := by
        ring

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

arXiv:2103.13367, eq. `intermediate`: `‖Ã - B̃‖_∞ ≤ √‖Ã†Ã - B̃†B̃‖`. -/
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
