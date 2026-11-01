/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleWallGramAsymptotics
import QICLean.Analysis.MatrixTraceInequalities
import QICLean.Analysis.OperatorMean.PowerDerivative
import QICLean.Channel.KrausCPTP

/-!
# Linear bounds for the moving-wall Gram matrix

The normalized Gram limit gives a uniform linear bound for its
weighted trace. A faithful left density dominates a positive multiple of
the identity, which controls the unweighted Gram trace. Consequently the
positive Gram matrix has a linear operator-norm bound.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1230–1310.
These are bounds on the single-wall coefficient matrices used by
pinned endpoint terms, not assumed estimates on the two-wall trial.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace Topology
open Filter

namespace MPSTensor

variable {d a b : ℕ}

/-- The one-wall Gram weight is uniformly bounded in norm by a
constant times its length. The bound is derived from its mixed-series
limit; arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallGramWeight_norm_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.IsHermitian)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖uncleWallGramWeight A B R ρ n‖ ≤ C * n := by
  have hlim := (uncleWallGramWeight_normalized_tendsto A B R ρ hρ hA hB hSpect).norm
  let B₀ := ‖uncleWallNormSlope A B R ρ‖ + 1
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  have hev : ∀ᶠ n : ℕ in atTop,
      ‖((n : ℝ)⁻¹) • uncleWallGramWeight A B R ρ n‖ < B₀ :=
    hlim.eventually (eventually_lt_nhds (by dsimp [B₀]; linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let S := ∑ k ∈ Finset.range N, ‖uncleWallGramWeight A B R ρ k‖
  let C := B₀ + S
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n ↦ ?_⟩
  by_cases hn0 : n = 0
  · subst n
    simp [uncleWallGramWeight]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  by_cases hn : N ≤ n
  · have hscaled : (n : ℝ)⁻¹ * ‖uncleWallGramWeight A B R ρ n‖ ≤ B₀ := by
      simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnreal.le)] using
        (hN n hn).le
    have hmain : ‖uncleWallGramWeight A B R ρ n‖ ≤ B₀ * (n : ℝ) := by
      calc
        ‖uncleWallGramWeight A B R ρ n‖ =
            (n : ℝ) * ((n : ℝ)⁻¹ * ‖uncleWallGramWeight A B R ρ n‖) := by
              rw [← mul_assoc, mul_inv_cancel₀ hnreal.ne', one_mul]
        _ ≤ (n : ℝ) * B₀ := mul_le_mul_of_nonneg_left hscaled hnreal.le
        _ = B₀ * (n : ℝ) := mul_comm _ _
    exact hmain.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hnreal.le)
  · have hsmall : ‖uncleWallGramWeight A B R ρ n‖ ≤ S :=
      Finset.single_le_sum (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    have hBC : S ≤ C := by dsimp [C]; linarith
    have hone : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hnpos)
    exact hsmall.trans (hBC.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hC.le))

/-- A faithful density uniformly controls the unweighted wall Gram
trace by its weighted trace. Source: arXiv:1210.6613, the faithful fixed
densities in the normalized standard form used by Lemma lowenergystates. -/
theorem uncleWallGram_trace_re_le_weight
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      (Matrix.trace (uncleWallGram A B R n)).re ≤ K * (uncleWallGramWeight A B R ρ n).re := by
  obtain ⟨c, hc, hlow⟩ := hρ.exists_pos_smul_one_le
  refine ⟨c⁻¹, inv_pos.mpr hc, fun n ↦ ?_⟩
  have hdiff : (ρ - c • (1 : Matrix (Fin a) (Fin a) ℂ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hlow)
  have htr := (Complex.nonneg_iff.mp
    (hdiff.trace_mul_nonneg (uncleWallGram_posSemidef A B R n))).1
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at htr
  have hle : c * (Matrix.trace (uncleWallGram A B R n)).re ≤
      (uncleWallGramWeight A B R ρ n).re := by
    change 0 ≤ (uncleWallGramWeight A B R ρ n).re -
      c * (Matrix.trace (uncleWallGram A B R n)).re at htr
    linarith
  calc
    (Matrix.trace (uncleWallGram A B R n)).re =
        c⁻¹ * (c * (Matrix.trace (uncleWallGram A B R n)).re) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ c⁻¹ * (uncleWallGramWeight A B R ρ n).re :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hc.le)

/-- The unweighted one-wall Gram trace is uniformly linear in the
word length under source faithful stationary/unital normalizations and
mixed spectral damping; arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallGram_trace_re_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (Matrix.trace (uncleWallGram A B R n)).re ≤ C * n := by
  obtain ⟨K, hK, hdom⟩ := uncleWallGram_trace_re_le_weight A B R ρ hρ
  obtain ⟨C, hC, hbound⟩ :=
    uncleWallGramWeight_norm_le_mul A B R ρ hρ.isHermitian hA hB hSpect
  refine ⟨K * C, mul_pos hK hC, fun n ↦ ?_⟩
  calc
    (Matrix.trace (uncleWallGram A B R n)).re ≤
        K * (uncleWallGramWeight A B R ρ n).re := hdom n
    _ ≤ K * ‖uncleWallGramWeight A B R ρ n‖ :=
      mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hK.le
    _ ≤ K * (C * n) := mul_le_mul_of_nonneg_left (hbound n) hK.le
    _ = K * C * n := (mul_assoc _ _ _).symm

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- The rectangular wall Kraus map is bounded by the unweighted
Gram trace times its input norm. This uses each wall word and the
rectangular Hilbert--Schmidt trace bound; arXiv:1210.6613, transfer estimates
in the proof of Lemma lowenergystates. -/
theorem uncleWallGramMap_apply_l2_opNorm_le_trace
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (n : ℕ)
    (X : Matrix (Fin b) (Fin b) ℂ) :
    ‖Matrix.rectangularKrausMap
        (fun σ : Fin n → Fin d ↦ uncleDomainWallWord A B R (List.ofFn σ)) X‖ ≤
      (Matrix.trace (uncleWallGram A B R n)).re * ‖X‖ := by
  let W := fun σ : Fin n → Fin d ↦ uncleDomainWallWord A B R (List.ofFn σ)
  have hterm (σ : Fin n → Fin d) :
      ‖W σ * X * (W σ)ᴴ‖ ≤ (Matrix.trace (W σ * (W σ)ᴴ)).re * ‖X‖ := by
    calc
      ‖W σ * X * (W σ)ᴴ‖ ≤ (‖W σ‖ * ‖X‖) * ‖(W σ)ᴴ‖ :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
          (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ = ‖W σ‖ ^ 2 * ‖X‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring
      _ ≤ (Matrix.trace ((W σ)ᴴ * W σ)).re * ‖X‖ :=
        mul_le_mul_of_nonneg_right
          (Matrix.l2_opNorm_sq_le_trace_conjTranspose_mul_self_re (W σ)) (norm_nonneg X)
      _ = (Matrix.trace (W σ * (W σ)ᴴ)).re * ‖X‖ := by
        rw [Matrix.trace_mul_comm (W σ)ᴴ (W σ)]
  change ‖∑ σ, W σ * X * (W σ)ᴴ‖ ≤ _
  calc
    ‖∑ σ, W σ * X * (W σ)ᴴ‖ ≤ ∑ σ, ‖W σ * X * (W σ)ᴴ‖ := norm_sum_le _ _
    _ ≤ ∑ σ, (Matrix.trace (W σ * (W σ)ᴴ)).re * ‖X‖ :=
      Finset.sum_le_sum fun σ _ ↦ hterm σ
    _ = (Matrix.trace (uncleWallGram A B R n)).re * ‖X‖ := by
      rw [← Finset.sum_mul]
      congr 1
      simp only [uncleWallGram, Matrix.trace_sum, Complex.re_sum, W]

/-- The rectangular moving-wall map has a uniform linear bound in
the Euclidean matrix operator norm, derived from its Gram trace.
Source: arXiv:1210.6613, transfer estimates in Lemma lowenergystates. -/
theorem uncleWallGramMap_apply_l2_opNorm_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ X : Matrix (Fin b) (Fin b) ℂ,
      ‖Matrix.rectangularKrausMap
          (fun σ : Fin n → Fin d ↦ uncleDomainWallWord A B R (List.ofFn σ)) X‖ ≤
        C * n * ‖X‖ := by
  obtain ⟨C, hC, hbound⟩ := uncleWallGram_trace_re_le_mul A B R ρ hρ hA hB hSpect
  exact ⟨C, hC, fun n X ↦ (uncleWallGramMap_apply_l2_opNorm_le_trace A B R n X).trans
    (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg X))⟩

/-- The one-wall Gram matrix has a uniform linear bound in the
Euclidean operator norm. This follows from its positive trace bound;
arXiv:1210.6613, endpoint norm estimates in Lemma lowenergystates. -/
theorem uncleWallGram_l2_opNorm_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖uncleWallGram A B R n‖ ≤ C * n := by
  obtain ⟨C, hC, hbound⟩ := uncleWallGram_trace_re_le_mul A B R ρ hρ hA hB hSpect
  exact ⟨C, hC, fun n ↦
    (uncleWallGram_posSemidef A B R n).l2_opNorm_le_trace_re.trans (hbound n)⟩

end OperatorNorm

end MPSTensor
