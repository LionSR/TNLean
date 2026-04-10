/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.MixedTransfer
import TNLean.Spectral.FrobeniusNorm
import TNLean.Spectral.GaugeConstruction
import TNLean.QPF.Assembly
import TNLean.Channel.FixedPoint.CanonicalGauge
import TNLean.Channel.Schwarz.Basic
import TNLean.Algebra.MatrixAux
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Spectral gap for the mixed transfer operator

The key analytic ingredient: if a linear operator on a finite-dimensional
space has spectral radius strictly less than 1, then its iterates converge
to zero. This is the mechanism by which the mixed transfer operator
`F_{AB}` for distinct blocks `A ≠ B` decays, enabling block separation.

## Main results

* `eigenvalue_norm_le_one`: every eigenvalue of `F_{AB}` has modulus ≤ 1
* `spectralRadius_mixedTransfer_le_one`: `ρ(F_{AB}) ≤ 1` for normalized tensors
* `spectralRadius_mixedTransfer_lt_one`: strict spectral gap for non-equivalent blocks
* `mixedTransfer_pow_tendsto_zero`: `F_{AB}^n → 0` for distinct blocks

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007.
* [Evans1978Spectral] Evans, Hanche-Olsen, *Spectral properties of positive
  maps on C*-algebras*, 1978.
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

section SpectralConvergence

/-! ### Normed algebra structure on matrices -/

noncomputable scoped instance : NormedRing (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedRing

noncomputable scoped instance : NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAlgebra

attribute [local instance]
  instGCFiniteDimensionalMatrixCLM
  instGCNormedAddCommGroupMatrixCLM
  instGCNormedRingMatrixCLM
  instGCNormedAlgebraMatrixCLM
  instGCCompleteSpaceMatrixCLM

/-! ### Spectral radius of the mixed transfer operator -/

/-- The **spectral radius** of the mixed transfer operator. -/
noncomputable def mixedTransferSpectralRadius (A B : MPSTensor d D) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B))

theorem mixedTransferSpectralRadius_eq (A B : MPSTensor d D) :
    mixedTransferSpectralRadius A B =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (mixedTransferMap A B)) := rfl

/-! ### Frobenius norm squared

The definition and basic API (`frobSq`, `frobSq_nonneg`, `frobSq_eq_zero_iff`,
`frobSq_pos_of_ne_zero`, `frobSq_smul`, `frobSq_trace`, `matToES`, …) are
provided by `TNLean.Spectral.FrobeniusNorm` for general rectangular matrices.
Below we add the square-matrix-specific lemma `frobSq_mul_le`. -/

/-- `frobSq X = ∑ i j, ‖X i j‖²` (definitional; kept for backward compatibility). -/
lemma frobSq_eq_sum (X : Matrix (Fin D) (Fin D) ℂ) :
    frobSq X = ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 := rfl


/-! ### Eigenvector iteration -/

/-- If `F(v) = μ • v`, then `F^n(v) = μ^n • v`. -/
lemma eigenvector_pow {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (F : V →ₗ[ℂ] V) (v : V) (μ : ℂ) (h : F v = μ • v) (n : ℕ) :
    (F ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    change (F ^ n) (F v) = _
    rw [h, map_smul, ih, smul_smul, mul_comm]; ring_nf

/-! ### Helper lemmas for the HS contraction bound -/

/-- Iterated TP condition: `∑_σ evalWord(K,σ)† evalWord(K,σ) = I`. -/
lemma word_conjTranspose_mul_sum (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1) (n : ℕ) :
    ∑ σ : Fin n → Fin d,
      (evalWord K (List.ofFn σ))ᴴ * evalWord K (List.ofFn σ) = 1 := by
  induction n with
  | zero => simp [Finset.univ_unique]
  | succ n ih =>
    rw [sum_fin_succ_eq]
    simp_rw [List.ofFn_cons, evalWord, Matrix.conjTranspose_mul,
      show ∀ A B C D : Matrix (Fin D) (Fin D) ℂ,
        A * B * (C * D) = A * (B * C) * D from fun _ _ _ _ => by simp [Matrix.mul_assoc]]
    rw [Finset.sum_comm]
    simp_rw [Matrix.sum_mul_mul
      (M := fun i => (K i)ᴴ * K i), hK, Matrix.mul_one]
    exact ih

/-- The standard transfer map preserves trace (for TP tensors). -/
lemma trace_transferMap (A : MPSTensor d D) (Z : Matrix (Fin D) (Fin D) ℂ)
    (hA : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    Matrix.trace (transferMap (d := d) (D := D) A Z) = Matrix.trace Z := by
  rw [transferMap_apply, Matrix.trace_sum]
  conv_lhs => arg 2; ext i; rw [show Matrix.trace (A i * Z * (A i)ᴴ) =
    Matrix.trace ((A i)ᴴ * A i * Z) from by
      rw [Matrix.trace_mul_comm (A i * Z) _, Matrix.mul_assoc]]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hA, one_mul]

/-! ### Hilbert–Schmidt contraction for the mixed transfer operator

The Euclidean-space embedding `matToES` and its basic API are imported from
`TNLean.Spectral.FrobeniusNorm`.  Below we add square-matrix submultiplicativity. -/

private lemma frobSq_mul_le (A B : Matrix (Fin D) (Fin D) ℂ) :
    frobSq (A * B) ≤ frobSq A * frobSq B := by
  simp only [frobSq, Matrix.mul_apply]
  calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
      ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_sq_sum_mul_le _ _
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by congr 1; exact Finset.sum_comm

private lemma norm_matToES_mul_le (A B : Matrix (Fin D) (Fin D) ℂ) :
    ‖matToES (A * B)‖ ≤ ‖matToES A‖ * ‖matToES B‖ := by
  have h : ‖matToES (A * B)‖ ^ 2 ≤ (‖matToES A‖ * ‖matToES B‖) ^ 2 := by
    rw [norm_matToES_sq, mul_pow, norm_matToES_sq, norm_matToES_sq]; exact frobSq_mul_le A B
  nlinarith [Real.sqrt_le_sqrt h, Real.sqrt_sq (norm_nonneg (matToES (A * B))),
    Real.sqrt_sq (mul_nonneg (norm_nonneg (matToES A)) (norm_nonneg (matToES B)))]

private lemma trace_cycle_for_frobSq (w v : Matrix (Fin D) (Fin D) ℂ) :
    (w * vᴴ * (v * wᴴ)).trace = (wᴴ * w * (vᴴ * v)).trace := by
  rw [Matrix.mul_assoc w vᴴ _, ← Matrix.mul_assoc vᴴ v wᴴ,
      ← Matrix.mul_assoc w (vᴴ * v) wᴴ,
      Matrix.trace_mul_comm (w * (vᴴ * v)) wᴴ,
      ← Matrix.mul_assoc wᴴ w (vᴴ * v)]

private lemma sum_frobSq_right (B : MPSTensor d D) (hB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (v : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq (v * (evalWord B (List.ofFn σ))ᴴ) = frobSq v := by
  simp only [frobSq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  conv_lhs => arg 2; ext σ; rw [trace_cycle_for_frobSq (evalWord B (List.ofFn σ)) v]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
      word_conjTranspose_mul_sum B hB n, Matrix.one_mul]

private lemma sum_frobSq_words (K : MPSTensor d D) (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1)
    (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq (evalWord K (List.ofFn σ)) = (D : ℝ) := by
  simp only [frobSq_trace]
  rw [← Complex.re_sum, ← Matrix.trace_sum, word_conjTranspose_mul_sum K hK n]
  simp [Matrix.trace_one, Fintype.card_fin]

/-- **Uniform Frobenius-norm bound**: `‖F_{AB}^n(X)‖_F² ≤ D² · ‖X‖_F²`. -/
private lemma hs_contraction_mixedTransfer [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) (n : ℕ) :
    frobSq (((mixedTransferMap A B) ^ n) X) ≤ (D : ℝ) ^ 2 * frobSq X := by
  rw [mixedTransferMap_pow_apply, show (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ) =
    (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) from by
    congr 1; ext σ; rw [Matrix.mul_assoc]]
  rw [show frobSq (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) =
    ‖matToES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ^ 2 from
    (norm_matToES_sq _).symm]
  set fA := fun σ : Fin n → Fin d => ‖matToES (evalWord A (List.ofFn σ))‖ with hfA_def
  set fB := fun σ : Fin n → Fin d => ‖matToES (X * (evalWord B (List.ofFn σ))ᴴ)‖ with hfB_def
  have h_chain : ‖matToES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ≤
    ∑ σ : Fin n → Fin d, fA σ * fB σ :=
    ((by rw [matToES_finset_sum]; exact norm_sum_le _ _) : ‖matToES _‖ ≤ _).trans
      (Finset.sum_le_sum fun σ _ => norm_matToES_mul_le _ _)
  have h_A : ∑ σ : Fin n → Fin d, fA σ ^ 2 = (D : ℝ) := by
    simp_rw [hfA_def, norm_matToES_sq]; exact sum_frobSq_words A hA_norm n
  have h_B : ∑ σ : Fin n → Fin d, fB σ ^ 2 = frobSq X := by
    simp_rw [hfB_def, norm_matToES_sq]; exact sum_frobSq_right B hB_norm X n
  calc ‖matToES _‖ ^ 2
      ≤ (∑ σ : Fin n → Fin d, fA σ * fB σ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_chain 2
    _ ≤ (∑ σ, fA σ ^ 2) * (∑ σ, fB σ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ fA fB
    _ = (D : ℝ) * frobSq X := by rw [h_A, h_B]
    _ ≤ (D : ℝ) ^ 2 * frobSq X := by
        nlinarith [sq_nonneg ((D : ℝ) - 1), frobSq_nonneg X,
          show (1 : ℝ) ≤ D from by exact_mod_cast NeZero.one_le (n := D)]

/-! ### Eigenvalue bound -/

/-- **Every eigenvalue of the mixed transfer operator has modulus ≤ 1.** -/
theorem eigenvalue_norm_le_one [NeZero D]
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedTransferMap A B) μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ.exists_hasEigenvector
  have hFv := Module.End.mem_eigenspace_iff.mp hv_mem
  by_contra h_gt; push Not at h_gt
  have h_pos := frobSq_pos_of_ne_zero v hv_ne
  have h_bound : ∀ n : ℕ, ‖μ‖ ^ (2 * n) ≤ (D : ℝ) ^ 2 := fun n => by
    have h1 := hs_contraction_mixedTransfer A B v hA_norm hB_norm n
    rw [eigenvector_pow _ v μ hFv n, frobSq_smul, norm_pow] at h1
    calc ‖μ‖ ^ (2 * n) = (‖μ‖ ^ n) ^ 2 := by ring
    _ ≤ _ := le_of_mul_le_mul_right (by linarith) h_pos
  have htend := tendsto_pow_atTop_atTop_of_one_lt (by nlinarith : 1 < ‖μ‖ ^ 2)
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨n, hn⟩ := htend ((D : ℝ) ^ 2 + 1)
  linarith [h_bound n, show (‖μ‖ ^ 2) ^ n = ‖μ‖ ^ (2 * n) from by ring, hn n le_rfl]

/-- **Spectral radius bound**: `ρ(F_{AB}) ≤ 1` for normalized tensors. -/
theorem spectralRadius_mixedTransfer_le_one
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    mixedTransferSpectralRadius A B ≤ 1 := by
  rw [mixedTransferSpectralRadius_eq]
  rcases eq_or_ne D 0 with rfl | hD
  · have : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := ⟨fun a b => by ext i; exact i.elim0⟩
    have : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ →L[ℂ] Matrix (Fin 0) (Fin 0) ℂ) :=
      ContinuousLinearMap.uniqueOfLeft.instSubsingleton
    rw [spectrum.SpectralRadius.of_subsingleton]; exact zero_le _
  · haveI : NeZero D := ⟨hD⟩
    have h_spec := AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap
      (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B)
    apply iSup₂_le; intro k hk
    rw [ENNReal.coe_le_one_iff]
    exact_mod_cast eigenvalue_norm_le_one A B hA_norm hB_norm k
      (Module.End.hasEigenvalue_iff_mem_spectrum.mpr (h_spec ▸ hk))

/-! ### Helper lemmas for the eigenvalue rigidity theorem -/

/-
**Eigenvector implies gauge** (the algebraic core of eigenvalue rigidity).

If `∑ A_i X B_i† = μX` where `X ≠ 0`, `|μ| = 1`, both tensors are injective
and normalized, then `A` and `B` are gauge-phase equivalent.

Proof strategy:

1. **X is invertible**: The kernel of X is invariant under all B_i†
   (from `∑ A_i X B_i† = μX` and `∑ A_i† A_i = I`). By injectivity of B,
   the B_i† span all matrices, so ker(X) is invariant under everything.
   If ker(X) ≠ {0}, then X = 0, contradiction.

2. **Per-index relation**: Set `C_i = X⁻¹ A_i X`. From the eigenvector equation,
   `∑ C_i B_i† = μI`. By Cauchy-Schwarz on the Hilbert-Schmidt inner product:
   `D² = |tr(∑ C_i B_i†)|² = |∑⟨B_i, C_i⟩|² ≤ (∑‖C_i‖²)(∑‖B_i‖²) = tr(∑C_i†C_i)·D`.
   So `tr(∑ C_i†C_i) ≥ D`. Also `∑(C_i - μB_i)†(C_i - μB_i) = ∑C_i†C_i - I ≥ 0`
   (the trace computation uses `∑B_i†B_i = I` and `∑C_iB_i† = μI`).
   Together with `E_A(XX†) = XX†` (which follows from QPF theory applied to
   the unique PD fixed point of the transfer map), one obtains
   `tr(∑C_i†C_i) = D`, so the PSD matrix `∑(C_i - μB_i)†(C_i - μB_i)` has
   trace 0, forcing `C_i = μB_i` for each i, i.e., `B_i = μ⁻¹X⁻¹A_iX`.

References:
* Pérez-García et al., Matrix Product State Representations (2007), Lemma 5
* Wolf, Quantum Channels & Operations (2012), §6.2
-/

-- (The old auxiliary lemmas `eigenvector_det_ne_zero` / `per_index_from_eigenvector`
-- were based on a too-strong per-index statement for the raw eigenvector.
-- The new proof establishes invertibility + intertwining directly inside
-- `eigenvector_gives_gauge` using left-canonical gauge + weighted KS equality.)

section
open scoped MatrixOrder

/-- **Eigenvector implies gauge equivalence** (PGVWC 2007, Lemma 5; Wolf 2012, §6.2).

If `F_{AB}(X) = μ • X` with `X ≠ 0` and `‖μ‖ = 1`, then injective normalized tensors
`A` and `B` are gauge-phase equivalent.

The proof passes to the left-canonical gauge, uses the equality case of the Hilbert--Schmidt
contraction to obtain Kraus-level intertwining, shows that the resulting intertwiner is
invertible, and then upgrades the intertwining relation to gauge equivalence. -/
private lemma eigenvector_gives_gauge [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    GaugePhaseEquiv A B := by
  classical
  obtain ⟨ρA, hρA⟩ := injective_transfer_unique_fixed_point' (A := A) hA hA_norm
  obtain ⟨ρB, hρB⟩ := injective_transfer_unique_fixed_point' (A := B) hB hB_norm
  have hρA_fix : transferMap (d := d) (D := D) A ρA = ρA := hρA.fixed
  have hρB_fix : transferMap (d := d) (D := D) B ρB = ρB := hρB.fixed
  have hρA_pd : ρA.PosDef := hρA.pos_def
  have hρB_pd : ρB.PosDef := hρB.pos_def
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).1 hρA_pd.isStrictlyPositive with
    ⟨S0A, hS0A_unit, hρA_eq⟩
  let SA : Matrix (Fin D) (Fin D) ℂ := S0Aᴴ
  have hSA_unit : IsUnit SA := by
    simpa [SA, Matrix.star_eq_conjTranspose] using (IsUnit.star hS0A_unit)
  have hSA_det : SA.det ≠ 0 := by
    have hdet_unit : IsUnit SA.det := (Matrix.isUnit_iff_isUnit_det (A := SA)).1 hSA_unit
    exact hdet_unit.ne_zero
  have hSA_mul : SA * SAᴴ = ρA := by
    calc
      SA * SAᴴ = S0Aᴴ * (S0Aᴴ)ᴴ := by rfl
      _ = S0Aᴴ * S0A := by simp
      _ = ρA := by simpa [Matrix.star_eq_conjTranspose] using hρA_eq.symm
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).1 hρB_pd.isStrictlyPositive with
    ⟨S0B, hS0B_unit, hρB_eq⟩
  let SB : Matrix (Fin D) (Fin D) ℂ := S0Bᴴ
  have hSB_unit : IsUnit SB := by
    simpa [SB, Matrix.star_eq_conjTranspose] using (IsUnit.star hS0B_unit)
  have hSB_det : SB.det ≠ 0 := by
    have hdet_unit : IsUnit SB.det := (Matrix.isUnit_iff_isUnit_det (A := SB)).1 hSB_unit
    exact hdet_unit.ne_zero
  have hSB_mul : SB * SBᴴ = ρB := by
    calc
      SB * SBᴴ = S0Bᴴ * (S0Bᴴ)ᴴ := by rfl
      _ = S0Bᴴ * S0B := by simp
      _ = ρB := by simpa [Matrix.star_eq_conjTranspose] using hρB_eq.symm
  let A' : MPSTensor d D := gaugeTensor SA A
  let B' : MPSTensor d D := gaugeTensor SB B
  let X' : Matrix (Fin D) (Fin D) ℂ := gaugeEigenvector SA SB X
  have hFX₂ : mixedTransferMap₂ A B X = μ • X := by
    simpa [mixedTransferMap_apply, mixedTransferMap₂_apply] using hFX
  have hcore := gauged_intertwining_core
    (A := A) (B := B) (SA := SA) (SB := SB) (ρA := ρA) (ρB := ρB)
    hSA_det hSB_det hSA_mul hSB_mul hρA_fix hρB_fix hA_norm hB_norm X μ hFX₂ hμ hX
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
  have hB' : IsInjective B' := by
    simpa [B'] using isInjective_conjugate (d := d) B hB SB hSB_det
  have hker : ∀ k : Fin d, ∀ v, X' *ᵥ v = 0 → X' *ᵥ ((B' k)ᴴ *ᵥ v) = 0 := by
    intro k v hv
    have h1 : X' *ᵥ ((B' k)ᴴ *ᵥ v) = (X' * (B' k)ᴴ) *ᵥ v := by
      simp [Matrix.mulVec_mulVec]
    rw [h1, hInter1 k, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hv, Matrix.mulVec_zero, smul_zero]
  have h_all :
      ∀ (M0 : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ),
        X' *ᵥ v = 0 → X' *ᵥ (M0 *ᵥ v) = 0 :=
    ker_all_of_inj (B := B') hB' X' hker
  have hdetX' : X'.det ≠ 0 := det_ne_zero_of_ker_all (X := X') hX'ne h_all
  exact gaugePhaseEquiv_of_gauged_intertwining
    (A := A) (B := B) (SA := SA) (SB := SB) (X' := X') (μ := μ)
    hSA_det hSB_det (Ne.isUnit hdetX') hμ (by
      intro i
      simpa [A', B'] using hInter2 i)

end

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search for the finite-dimensional continuous endomorphism space of matrices
-- needs a local heartbeat bump during the spectral-radius extraction.
/-- **Eigenvalue rigidity** (Pérez-García et al. 2007, Lemma 5):
if the mixed transfer spectral radius is ≥ 1, then A and B are
gauge-phase equivalent. -/
theorem modulus_one_eigenvalue_implies_gauge
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B := by
  -- Edge case: D = 0
  rcases eq_or_ne D 0 with rfl | hD
  · -- For D = 0, all matrices are trivially equal; any GL element works
    exact ⟨1, 1, one_ne_zero, fun i => by ext a; exact a.elim0⟩
  haveI : NeZero D := ⟨hD⟩
  -- Step 1: Extract eigenvalue with |μ| = 1 and eigenvector X ≠ 0
  -- The spectral radius equals 1 (≥ 1 from hypothesis, ≤ 1 already proved)
  set V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  haveI : Nontrivial V := by
    haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
    exact Matrix.nonempty
  haveI : Nontrivial (V →L[ℂ] V) := ContinuousLinearMap.instNontrivialId
  -- Spectral radius is achieved
  obtain ⟨μ, hμ_spec, hμ_norm⟩ := spectrum.exists_nnnorm_eq_spectralRadius F'
  -- Transfer to eigenvalue of the linear map
  have h_spec_eq := AlgEquiv.spectrum_eq Φ (mixedTransferMap A B)
  have hμ_spec_end : μ ∈ spectrum ℂ (mixedTransferMap A B) := h_spec_eq ▸ hμ_spec
  have hμ_ev : Module.End.HasEigenvalue (mixedTransferMap A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec_end
  obtain ⟨X, hX_mem, hX_ne⟩ := hμ_ev.exists_hasEigenvector
  have hFX : mixedTransferMap A B X = μ • X := Module.End.mem_eigenspace_iff.mp hX_mem
  -- Step 2: Show |μ| = 1
  have hμ_le : ‖μ‖ ≤ 1 := eigenvalue_norm_le_one A B hA_norm hB_norm μ hμ_ev
  have hμ_ge : (1 : ℝ≥0∞) ≤ ‖μ‖₊ := by rw [hμ_norm]; exact hsr
  have hμ_eq : ‖μ‖ = 1 := le_antisymm hμ_le (by
    rw [ENNReal.one_le_coe_iff] at hμ_ge; exact_mod_cast hμ_ge)
  -- Step 3: Apply the core algebraic lemma
  exact eigenvector_gives_gauge A B X μ hA hB hA_norm hB_norm hFX hμ_eq hX_ne

/-- **Spectral gap for distinct blocks**: `ρ(F_{AB}) < 1` when `A ≇ B`. -/
theorem spectralRadius_mixedTransfer_lt_one
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 :=
  lt_of_le_of_ne (spectralRadius_mixedTransfer_le_one A B hA_norm hB_norm)
    fun h => hAB (modulus_one_eigenvalue_implies_gauge A B hA hB hA_norm hB_norm h.ge)

/-! ### Power convergence from spectral radius bound -/

/-- **Powers tend to zero when spectral radius < 1.** -/
theorem pow_tendsto_zero_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (h : spectralRadius ℂ a < 1) :
    Filter.Tendsto (fun n => a ^ n) Filter.atTop (nhds 0) := by
  obtain ⟨r, hr_above, hr_below⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hr_lt_one : r < 1 := ENNReal.coe_lt_coe.mp (by rwa [ENNReal.coe_one])
  have hev2 : ∀ᶠ n in Filter.atTop, ‖a ^ n‖₊ < r ^ n := by
    have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
    filter_upwards [gelfand.eventually (eventually_lt_nhds hr_above),
      Filter.eventually_gt_atTop 0] with n hn hn_pos
    rw [one_div, ENNReal.rpow_inv_lt_iff (Nat.cast_pos.mpr hn_pos)] at hn
    rw [ENNReal.rpow_natCast] at hn
    exact_mod_cast hn
  apply squeeze_zero_norm' (a := fun n => (r : ℝ) ^ n)
  · filter_upwards [hev2] with n hn
    rw [← coe_nnnorm, ← NNReal.coe_pow]; exact_mod_cast hn.le
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg (by exact_mod_cast hr_lt_one)

/-! ### Application to mixed transfer convergence -/

/-- **Mixed transfer iterates decay for distinct blocks**: `F_{AB}^n(X) → 0`. -/
theorem mixedTransfer_pow_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  have h_clm : Filter.Tendsto (fun n => F' ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one F'
      (spectralRadius_mixedTransfer_lt_one A B hA hB hA_norm hB_norm hAB)
  have h_eval := (ContinuousLinearMap.apply ℂ V X).continuous.tendsto (0 : V →L[ℂ] V)
  rw [map_zero] at h_eval
  suffices ∀ n, ((mixedTransferMap A B) ^ n) X = (F' ^ n) X by
    simp_rw [this]; exact h_eval.comp h_clm
  intro n
  have h_pow : F' ^ n = Φ ((mixedTransferMap A B) ^ n) := (map_pow Φ _ n).symm
  simp only [h_pow]; rfl

end SpectralConvergence

end MPSTensor

/-! ## Uniform spectral gap from finite eigenvalue set -/

/-- **Uniform spectral gap from finitely many eigenvalues with modulus < 1.**

If an endomorphism has finitely many eigenvalues, and every eigenvalue `μ ≠ 1` satisfies
`‖μ‖ < 1`, then there exists a uniform gap `δ > 0` such that `‖μ‖ ≤ 1 - δ` for all
non-unit eigenvalues. This is a general finite-dimensional argument via `Finset.max'`. -/
theorem uniform_spectral_gap_of_finite_lt_one
    {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]
    {E : V →ₗ[K] V}
    (hfin : Set.Finite {μ : K | Module.End.HasEigenvalue E μ})
    (hlt : ∀ μ, Module.End.HasEigenvalue E μ → μ ≠ 1 → ‖μ‖ < 1) :
    ∃ δ > 0, ∀ μ, Module.End.HasEigenvalue E μ → μ ≠ 1 → ‖μ‖ ≤ 1 - δ := by
  classical
  let S := {μ : K | Module.End.HasEigenvalue E μ ∧ μ ≠ 1}
  have hSfin : S.Finite := hfin.subset fun μ hμ => hμ.1
  by_cases hS : S.Nonempty
  · -- Nonempty: take δ = 1 - max{‖μ‖ | μ ∈ S}
    let norms := hSfin.toFinset.image (fun μ => ‖μ‖)
    have hnorms_ne : norms.Nonempty := by
      obtain ⟨μ₀, hμ₀⟩ := hS
      exact ⟨‖μ₀‖, Finset.mem_image.mpr ⟨μ₀, hSfin.mem_toFinset.mpr hμ₀, rfl⟩⟩
    set r := norms.max' hnorms_ne with r_def
    have hr_lt : r < 1 := by
      rw [r_def, Finset.max'_lt_iff]
      intro x hx
      obtain ⟨μ, hμS, rfl⟩ := Finset.mem_image.mp hx
      exact hlt μ (hSfin.mem_toFinset.mp hμS).1 (hSfin.mem_toFinset.mp hμS).2
    refine ⟨1 - r, by linarith, fun μ hμ hne => ?_⟩
    have hμS : μ ∈ S := ⟨hμ, hne⟩
    have hμ_norm_mem : ‖μ‖ ∈ norms :=
      Finset.mem_image.mpr ⟨μ, hSfin.mem_toFinset.mpr hμS, rfl⟩
    linarith [Finset.le_max' norms ‖μ‖ hμ_norm_mem]
  · -- Empty: no non-1 eigenvalues, δ = 1 works vacuously
    exact ⟨1, one_pos, fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ hS⟩
