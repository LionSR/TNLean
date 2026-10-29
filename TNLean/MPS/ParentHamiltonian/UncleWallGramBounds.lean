/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleWallGramAsymptotics
import QICLean.Analysis.MatrixTraceInequalities
import QICLean.Analysis.OperatorMean.PowerDerivative

/-!
# Linear bounds for the actual moving-wall Gram matrix

The actual normalized Gram limit gives a uniform linear bound for its
weighted trace. A faithful left density dominates a positive multiple of
the identity, which controls the unweighted Gram trace. Consequently the
actual positive Gram matrix has a linear operator-norm bound.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1230–1310.
These are bounds on the actual single-wall coefficient matrices used by
pinned endpoint terms, not assumed estimates on the two-wall trial.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace Topology
open Filter

namespace MPSTensor

variable {d a b : ℕ}

/-- The actual one-wall Gram weight is uniformly bounded in norm by a
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

/-- A faithful density uniformly controls the actual unweighted wall Gram
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
    Matrix.trace_smul, Complex.sub_re, RCLike.smul_re] at htr
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

/-- The actual unweighted one-wall Gram trace is uniformly linear in the
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

/-- The actual one-wall Gram matrix has a uniform linear bound in the
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
