/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.MPVOverlapDecay
import TNLean.QPF.Assembly
import TNLean.Channel.FixedPoint.CanonicalGauge
import TNLean.Channel.Schwarz.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Rectangular spectral gap for the mixed transfer operator

When two MPS tensors `A : MPSTensor d D₁` and `B : MPSTensor d D₂` have **different bond
dimensions** `D₁ ≠ D₂`, the spectral radius of the rectangular mixed transfer operator
`mixedTransferMap₂ A B` is strictly less than 1 (assuming both tensors are injective and
normalized).

This is the "dimension-mismatch" spectral gap: if the bond dimensions differ, then the overlap
`∑ σ, mpv A σ * conj(mpv B σ)` decays to zero exponentially.

## Main results

* `mixedTransferSpectralRadius₂_lt_one_of_dim_ne`: strict spectral gap for dimension-mismatched
  normalized injective tensors
* `mpvOverlap_tendsto_zero_of_dim_ne`: the MPV overlap tends to zero when `D₁ ≠ D₂`

## Proof outline

1. **Eigenvalue bound ≤ 1**: Frobenius-norm contraction adapted to the rectangular setting.
2. **Equality case implies D₁ = D₂**: Block-embed into `Fin D₁ ⊕ Fin D₂`, apply
   Kadison–Schwarz equality to extract Kraus-level intertwining, then show `ker X = 0`
   and `ker X† = 0` using injectivity of the generators, which forces `D₁ = D₂`.
3. Contraposition gives `D₁ ≠ D₂ ⟹ spectralRadius < 1`.

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007, Lemma 5.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators NNReal ENNReal Matrix.Norms.Elementwise
  Matrix.Norms.Operator

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  instGCFiniteDimensionalMatrixCLM
  instGCNormedAddCommGroupMatrixCLM
  instGCNormedRingMatrixCLM
  instGCNormedAlgebraMatrixCLM
  instGCCompleteSpaceMatrixCLM

/-! ## Rectangular spectral radius abbreviation -/

/-- The **spectral radius** of the rectangular mixed transfer operator. -/
noncomputable def mixedTransferSpectralRadius₂
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
      (mixedTransferMap₂ A B))

theorem mixedTransferSpectralRadius₂_eq
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    mixedTransferSpectralRadius₂ A B =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
          (mixedTransferMap₂ A B)) := rfl

/-! ## Rectangular Frobenius norm and Euclidean-space embedding

The general definitions `frobSq`, `matToES`, and their basic API are imported from
`TNLean.Spectral.FrobeniusNorm`.  We introduce `frobSq₂` as a deprecated alias kept
for local readability, and add the mixed-shape submultiplicativity lemma. -/

/-- Deprecated alias: `frobSq₂ = frobSq` for rectangular matrices.
Kept for local readability in this file. -/
noncomputable abbrev frobSq₂ (X : Matrix (Fin D₁) (Fin D₂) ℂ) : ℝ := frobSq X

private lemma norm_matToES_rect_mul_le
    (A : Matrix (Fin D₁) (Fin D₁) ℂ) (B : Matrix (Fin D₁) (Fin D₂) ℂ) :
    ‖matToES (A * B)‖ ≤ ‖matToES A‖ * ‖matToES B‖ := by
  have h : ‖matToES (A * B)‖ ^ 2 ≤ (‖matToES A‖ * ‖matToES B‖) ^ 2 := by
    rw [norm_matToES_sq, mul_pow, norm_matToES_sq, norm_matToES_sq]
    -- Frobenius submultiplicativity for mixed-shape matrices
    simp only [frobSq, Matrix.mul_apply]
    calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
        ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            norm_sq_sum_mul_le _ _
      _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
          (congr 1; exact Finset.sum_comm)
  nlinarith [Real.sqrt_le_sqrt h, Real.sqrt_sq (norm_nonneg (matToES (A * B))),
    Real.sqrt_sq (mul_nonneg (norm_nonneg (matToES A)) (norm_nonneg (matToES B)))]

/-! ## Hilbert–Schmidt contraction for the rectangular mixed transfer -/

section HSContraction

/-- Right-sum identity: `∑_σ ‖X · w_B(σ)†‖_F² = ‖X‖_F²` for rectangular X.

The proof uses trace cycling: `frobSq(v M†) = tr(M† M · v† v).re`, then sum over σ. -/
private lemma sum_frobSq₂_right (B : MPSTensor d D₂) (hB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (v : Matrix (Fin D₁) (Fin D₂) ℂ) (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq₂ (v * (evalWord B (List.ofFn σ))ᴴ) = frobSq₂ v := by
  -- Trace-cycle: tr((v M†)† (v M†)) = tr(M† M v† v)
  have trace_cycle : ∀ M : Matrix (Fin D₂) (Fin D₂) ℂ,
      ((v * Mᴴ)ᴴ * (v * Mᴴ)).trace = (Mᴴ * M * (vᴴ * v)).trace := by
    intro M
    have h1 : (v * Mᴴ)ᴴ = M * vᴴ := by
      simp [Matrix.conjTranspose_mul]
    rw [h1]
    rw [Matrix.mul_assoc M vᴴ _, ← Matrix.mul_assoc vᴴ v Mᴴ,
      ← Matrix.mul_assoc M (vᴴ * v) Mᴴ,
      Matrix.trace_mul_comm (M * (vᴴ * v)) Mᴴ,
      ← Matrix.mul_assoc Mᴴ M (vᴴ * v)]
  -- Apply trace cycling to the sum.
  simp_rw [frobSq_trace]
  conv_lhs => arg 2; ext σ; rw [trace_cycle (evalWord B (List.ofFn σ))]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
    word_conjTranspose_mul_sum B hB n, Matrix.one_mul]

/-- Word Frobenius norm sum for square matrices: `∑_σ ‖w_K(σ)‖_F² = D₁`. -/
private lemma sum_frobSq₂_words (K : MPSTensor d D₁) (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1)
    (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq₂ (evalWord K (List.ofFn σ)) = (D₁ : ℝ) := by
  simp_rw [frobSq_trace]
  rw [← Complex.re_sum, ← Matrix.trace_sum, word_conjTranspose_mul_sum K hK n]
  simp [Matrix.trace_one, Fintype.card_fin]

/-- **Uniform Frobenius-norm bound**: `‖F₂^n(X)‖_F² ≤ D₁² · ‖X‖_F²` for the rectangular
mixed transfer operator. -/
private lemma hs_contraction_rect [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) (n : ℕ) :
    frobSq₂ (((mixedTransferMap₂ A B) ^ n) X) ≤ (D₁ : ℝ) ^ 2 * frobSq₂ X := by
  rw [mixedTransferMap₂_pow_apply, show (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ) =
    (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) from by
    congr 1; ext σ; rw [Matrix.mul_assoc]]
  rw [show frobSq₂ (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) =
    ‖matToES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ^ 2 from
    (norm_matToES_sq _).symm]
  set fA := fun σ : Fin n → Fin d => ‖matToES (evalWord A (List.ofFn σ))‖ with hfA_def
  set fB := fun σ : Fin n → Fin d =>
    ‖matToES (X * (evalWord B (List.ofFn σ))ᴴ)‖ with hfB_def
  have h_chain : ‖matToES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ≤
    ∑ σ : Fin n → Fin d, fA σ * fB σ :=
    ((by rw [matToES_finset_sum]; exact norm_sum_le _ _) : ‖matToES _‖ ≤ _).trans
      (Finset.sum_le_sum fun σ _ => norm_matToES_rect_mul_le _ _)
  have h_A : ∑ σ : Fin n → Fin d, fA σ ^ 2 = (D₁ : ℝ) := by
    simp_rw [hfA_def, norm_matToES_sq]; exact sum_frobSq₂_words A hA_norm n
  have h_B : ∑ σ : Fin n → Fin d, fB σ ^ 2 = frobSq₂ X := by
    simp_rw [hfB_def, norm_matToES_sq]; exact sum_frobSq₂_right B hB_norm X n
  calc ‖matToES _‖ ^ 2
      ≤ (∑ σ : Fin n → Fin d, fA σ * fB σ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_chain 2
    _ ≤ (∑ σ, fA σ ^ 2) * (∑ σ, fB σ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ fA fB
    _ = (D₁ : ℝ) * frobSq₂ X := by rw [h_A, h_B]
    _ ≤ (D₁ : ℝ) ^ 2 * frobSq₂ X := by
        nlinarith [sq_nonneg ((D₁ : ℝ) - 1), frobSq_nonneg X,
          show (1 : ℝ) ≤ D₁ from by exact_mod_cast NeZero.one_le (n := D₁)]

end HSContraction

/-! ## Eigenvalue bound -/

section EigenvalueBound

/-- Every eigenvalue of the rectangular mixed transfer operator has modulus ≤ 1. -/
theorem eigenvalue_norm_le_one₂ [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedTransferMap₂ A B) μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ.exists_hasEigenvector
  have hFv := Module.End.mem_eigenspace_iff.mp hv_mem
  by_contra h_gt; push Not at h_gt
  have h_pos := frobSq_pos_of_ne_zero v hv_ne
  have h_bound : ∀ n : ℕ, ‖μ‖ ^ (2 * n) ≤ (D₁ : ℝ) ^ 2 := fun n => by
    have h1 := hs_contraction_rect A B v hA_norm hB_norm n
    rw [eigenvector_pow _ v μ hFv n] at h1
    simp only [frobSq₂, frobSq_smul, norm_pow] at h1
    calc ‖μ‖ ^ (2 * n) = (‖μ‖ ^ n) ^ 2 := by ring
    _ ≤ _ := le_of_mul_le_mul_right (by linarith) h_pos
  have htend := tendsto_pow_atTop_atTop_of_one_lt (by nlinarith : 1 < ‖μ‖ ^ 2)
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨n, hn⟩ := htend ((D₁ : ℝ) ^ 2 + 1)
  linarith [h_bound n, show (‖μ‖ ^ 2) ^ n = ‖μ‖ ^ (2 * n) from by ring, hn n le_rfl]

/-- **Spectral radius bound**: `ρ(F₂) ≤ 1` for normalized tensors. -/
theorem spectralRadius_mixedTransfer₂_le_one
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    mixedTransferSpectralRadius₂ A B ≤ 1 := by
  rw [mixedTransferSpectralRadius₂_eq]
  rcases eq_or_ne D₁ 0 with rfl | hD₁
  · have : Subsingleton (Matrix (Fin 0) (Fin D₂) ℂ) := ⟨fun a b => by ext i; exact i.elim0⟩
    have : Subsingleton (Matrix (Fin 0) (Fin D₂) ℂ →L[ℂ] Matrix (Fin 0) (Fin D₂) ℂ) :=
      ContinuousLinearMap.uniqueOfLeft.instSubsingleton
    rw [spectrum.SpectralRadius.of_subsingleton]; exact zero_le _
  · rcases eq_or_ne D₂ 0 with rfl | hD₂
    · have : Subsingleton (Matrix (Fin D₁) (Fin 0) ℂ) := ⟨fun a b => by ext i j; exact j.elim0⟩
      have : Subsingleton (Matrix (Fin D₁) (Fin 0) ℂ →L[ℂ] Matrix (Fin D₁) (Fin 0) ℂ) :=
        ContinuousLinearMap.uniqueOfLeft.instSubsingleton
      rw [spectrum.SpectralRadius.of_subsingleton]; exact zero_le _
    · haveI : NeZero D₁ := ⟨hD₁⟩
      haveI : NeZero D₂ := ⟨hD₂⟩
      have h_spec := AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap
        (Matrix (Fin D₁) (Fin D₂) ℂ)) (mixedTransferMap₂ A B)
      apply iSup₂_le; intro k hk
      rw [ENNReal.coe_le_one_iff]
      exact_mod_cast eigenvalue_norm_le_one₂ A B hA_norm hB_norm k
        (Module.End.hasEigenvalue_iff_mem_spectrum.mpr (h_spec ▸ hk))

end EigenvalueBound

/-! ## Modulus-1 eigenvalue implies equal dimensions -/

section DimensionEquality

/-- Core algebraic lemma: if there is an eigenvector of `mixedTransferMap₂ A B` with eigenvalue
of modulus 1, then `D₁ = D₂`.

This is the rectangular analogue of `eigenvector_gives_gauge` from `SpectralGap.lean`,
but instead of constructing a gauge equivalence, we derive equality of dimensions. -/
private theorem dim_eq_of_modulus_one_eigenvector [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) (μ : ℂ)
    (hFX : mixedTransferMap₂ A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    D₁ = D₂ := by
  classical
  obtain ⟨ρA, hρA⟩ := injective_transfer_unique_fixed_point' A hA hA_norm
  obtain ⟨ρB, hρB⟩ := injective_transfer_unique_fixed_point' B hB hB_norm
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).1
      (hρA.pos_def.isStrictlyPositive) with ⟨S0A, hS0A_unit, hρA_eq'⟩
  have hρA_eq : ρA = S0Aᴴ * S0A := by
    simpa [Matrix.star_eq_conjTranspose] using hρA_eq'
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).1
      (hρB.pos_def.isStrictlyPositive) with ⟨S0B, hS0B_unit, hρB_eq'⟩
  have hρB_eq : ρB = S0Bᴴ * S0B := by
    simpa [Matrix.star_eq_conjTranspose] using hρB_eq'
  let SA : Matrix (Fin D₁) (Fin D₁) ℂ := S0Aᴴ
  let SB : Matrix (Fin D₂) (Fin D₂) ℂ := S0Bᴴ
  -- Determinant facts
  have hSA_det : SA.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A := SA)).1
      (by simpa [SA, Matrix.star_eq_conjTranspose] using IsUnit.star hS0A_unit)).ne_zero
  have hSB_det : SB.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A := SB)).1
      (by simpa [SB, Matrix.star_eq_conjTranspose] using IsUnit.star hS0B_unit)).ne_zero
  have hSA_u := Ne.isUnit hSA_det
  have hSB_u := Ne.isUnit hSB_det
  have hSAh_det : (SAᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSA_det
  have hSBh_det : (SBᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSB_det
  have hSAh_u := Ne.isUnit hSAh_det
  have hSBh_u := Ne.isUnit hSBh_det
  have hSA_mul : SA * SAᴴ = ρA := by
    calc SA * SAᴴ = S0Aᴴ * S0A := by simp [SA]
    _ = ρA := by simpa using hρA_eq.symm
  have hSB_mul : SB * SBᴴ = ρB := by
    calc SB * SBᴴ = S0Bᴴ * S0B := by simp [SB]
    _ = ρB := by simpa using hρB_eq.symm
  let A' : MPSTensor d D₁ := gaugeTensor SA A
  let B' : MPSTensor d D₂ := gaugeTensor SB B
  let X' : Matrix (Fin D₁) (Fin D₂) ℂ := gaugeEigenvector SA SB X
  have hcore := gauged_intertwining_core
    (A := A) (B := B) (SA := SA) (SB := SB) (ρA := ρA) (ρB := ρB)
    hSA_det hSB_det hSA_mul hSB_mul hρA.fixed hρB.fixed hA_norm hB_norm X μ hFX hμ hX
  rcases hcore with ⟨_, _, hX'ne_raw, hInter1_raw, hInter2_raw⟩
  have hX'ne : X' ≠ 0 := by
    simpa [X', gaugeEigenvector] using hX'ne_raw
  have hInter1 : ∀ i : Fin d, X' * (B' i)ᴴ = μ • ((A' i)ᴴ * X') := by
    intro i
    simpa [A', B', X', gaugeTensor, gaugeEigenvector, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc] using hInter1_raw i
  have hInter2 : ∀ i : Fin d, A' i * X' = μ • X' * B' i := by
    intro i
    simpa [A', B', X', gaugeTensor, gaugeEigenvector] using hInter2_raw i
  have hA' : IsInjective A' := by
    simpa [A'] using isInjective_conjugate (d := d) A hA SA hSA_det
  have hB' : IsInjective B' := by
    simpa [B'] using isInjective_conjugate (d := d) B hB SB hSB_det
  exact dim_eq_of_gauged_intertwining A' B' X' μ hA' hB' hX'ne hInter1 hInter2

end DimensionEquality

/-! ## Main theorem -/

section MainTheorem

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for the rectangular continuous endomorphism space needs a local
-- heartbeat bump during the spectral-radius extraction.
/-- **Dimension-mismatch spectral gap**: the spectral radius of the rectangular mixed transfer
operator is strictly less than 1 when the bond dimensions differ. -/
theorem mixedTransferSpectralRadius₂_lt_one_of_dim_ne
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    mixedTransferSpectralRadius₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B < 1 := by
  classical
  have hle :
      mixedTransferSpectralRadius₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B ≤ 1 :=
    spectralRadius_mixedTransfer₂_le_one (A := A) (B := B) hA_norm hB_norm
  refine lt_of_le_of_ne hle ?_
  intro hEq
  -- Set `F` to be the continuous-linear version of the mixed transfer map.
  rw [mixedTransferSpectralRadius₂_eq] at hEq
  set F : (Matrix (Fin D₁) (Fin D₂) ℂ) →L[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ :=
    (Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ)) (mixedTransferMap₂ A B)
  have hEqF : spectralRadius ℂ F = 1 := by simpa [F] using hEq
  -- If `spectralRadius = 1`, pick `μ ∈ spectrum` with `‖μ‖ = 1`.
  -- Use `@` to supply the `instGC*` instances explicitly, avoiding a `UniformSpace` diamond
  -- between the strong topology and the operator-norm topology on `E →L[ℂ] E`.
  obtain ⟨μ, hμ_spec, hμ_rad⟩ :=
    @spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ℂ _ _
      (instGCNormedRingMatrixCLM D₁ D₂) (instGCNormedAlgebraMatrixCLM D₁ D₂)
      (instGCCompleteSpaceMatrixCLM D₁ D₂) inferInstance (a := F)
      (@spectrum.nonempty _ (instGCNormedRingMatrixCLM D₁ D₂)
        (instGCNormedAlgebraMatrixCLM D₁ D₂) (instGCCompleteSpaceMatrixCLM D₁ D₂) inferInstance F)
  have hμ_one : (↑‖μ‖₊ : ENNReal) = 1 := by simpa [hEqF] using hμ_rad
  have hμ_nnn : ‖μ‖₊ = (1 : NNReal) := (ENNReal.coe_eq_one).1 hμ_one
  have hμ_norm : ‖μ‖ = 1 := by
    have : (‖μ‖₊ : ℝ) = (1 : ℝ) := by exact_mod_cast hμ_nnn
    simpa [coe_nnnorm] using this
  -- Convert `μ ∈ spectrum` to an eigenvalue of the linear map `mixedTransferMap₂ A B`.
  have h_spec :=
    AlgEquiv.spectrum_eq
      (Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ)) (mixedTransferMap₂ A B)
  have hμ_spec' : μ ∈ spectrum ℂ (mixedTransferMap₂ A B) := by
    have : μ ∈ spectrum ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
          (mixedTransferMap₂ A B)) := by
      simpa [F] using hμ_spec
    simpa [h_spec] using this
  have hHas : Module.End.HasEigenvalue (mixedTransferMap₂ A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec'
  obtain ⟨X, hX_mem, hX_ne⟩ := hHas.exists_hasEigenvector
  have hFX : mixedTransferMap₂ A B X = μ • X :=
    (Module.End.mem_eigenspace_iff).1 hX_mem
  -- A modulus-one eigenvalue forces `D₁ = D₂`, contradicting `hD`.
  have hDim : D₁ = D₂ :=
    dim_eq_of_modulus_one_eigenvector (A := A) (B := B)
      hA hB hA_norm hB_norm X μ hFX hμ_norm hX_ne
  exact hD hDim

/-- **Overlap decay for dimension-mismatched tensors**: `mpvOverlap A B N → 0` when `D₁ ≠ D₂`. -/
theorem mpvOverlap_tendsto_zero_of_dim_ne
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  have hlt := mixedTransferSpectralRadius₂_lt_one_of_dim_ne A B hA hB hA_norm hB_norm hD
  exact mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one A B hlt

end MainTheorem

end MPSTensor
