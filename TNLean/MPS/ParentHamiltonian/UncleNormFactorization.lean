/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTrialTransferNorm
import TNLean.MPS.ParentHamiltonian.UnclePrimitiveTransfer
import TNLean.MPS.ParentHamiltonian.UncleWallGramBounds
import QICLean.Channel.Peripheral.UnitalKraus
import QICLean.Analysis.TraceMulBound
import QICLean.Analysis.OperatorNormConvergence

/-!
# Quantitative factorization of the actual two-wall transfer contraction

The exact finite transfer identity is approximated by the two actual
canonical rank-one contractions. Pure transfer powers converge by source
block injectivity and unital normalization, and the actual moving-wall
maps have linear bounds. This derives a geometric factorization error;
neither factorization nor norm growth is assumed.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1230–1265.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open Filter

namespace MPSTensor

variable {d a b : ℕ}

private theorem uncleUnital_pow_norm_le (A : MPSTensor d a)
    (hU : Kraus.mapLM A 1 = 1) (n : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
    ‖((Kraus.mapLM A) ^ n) X‖ ≤ ‖X‖ := by
  have hCP : IsKrausCP (Kraus.mapLM A) := Kraus.isCPMap_mapLM A
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change ‖Kraus.mapLM A (((Kraus.mapLM A) ^ n) X)‖ ≤ ‖X‖
      exact (hCP.norm_apply_le_of_map_one_eq_one hU _).trans ih

/-- Replacing the actual separated transfer powers by their canonical
contractions gives an error bounded by a quadratic length factor times a
geometric sequence. The leading term is the product of the two actual
finite wall Gram weights. Source: arXiv:1210.6613, proof of Lemma
lowenergystates, lines 1230–1265. -/
theorem uncleTwoWallTransfer_factorization_bound [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hIA : Kraus.IsInjective A) (hIB : Kraus.IsInjective B)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef) (htrA : Matrix.trace ρA = 1)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef) (htrB : Matrix.trace ρB = 1)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB)
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C z : ℝ, 0 < C ∧ 0 < z ∧ z < 1 ∧ ∀ N : ℕ, 0 < N →
      ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
          (uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0) -
        uncleWallGramWeight A B R ρA (N + 1) * uncleWallGramWeight B A L ρB (N + 1)‖ ≤
        C * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N := by
  classical
  obtain ⟨cA, rA, hcA, hrA, hrA1, hdecA⟩ :=
    uncleTransfer_pow_sub_projection_bound A hIA hUA ρA htrA hFA
  obtain ⟨cB, rB, hcB, hrB, hrB1, hdecB⟩ :=
    uncleTransfer_pow_sub_projection_bound B hIB hUB ρB htrB hFB
  obtain ⟨cR, hcR, hwallR⟩ := uncleWallGramMap_apply_l2_opNorm_le_mul A B R ρA hρA hFA hUB hAB
  obtain ⟨cL, hcL, hwallL⟩ := uncleWallGramMap_apply_l2_opNorm_le_mul B A L ρB hρB hFB hUA hBA
  have hGR (n : ℕ) (X : Matrix (Fin b) (Fin b) ℂ) :
      ‖uncleWallGramMap A B R n X‖ ≤ cR * n * ‖X‖ := by
    simpa only [uncleWallGramMap] using hwallR n X
  have hGL (n : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleWallGramMap B A L n X‖ ≤ cL * n * ‖X‖ := by
    simpa only [uncleWallGramMap] using hwallL n X
  let fA := (Matrix.traceLinearMap (Fin a) ℂ ℂ).comp
    (mulLeftLinearMap (n := Fin a) ℂ ρA)
  let fB := (Matrix.traceLinearMap (Fin b) ℂ ℂ).comp
    (mulLeftLinearMap (n := Fin b) ℂ ρB)
  let PA := fA.smulRight (1 : Matrix (Fin a) (Fin a) ℂ)
  let PB := fB.smulRight (1 : Matrix (Fin b) (Fin b) ℂ)
  have hPA (X : Matrix (Fin a) (Fin a) ℂ) : ‖PA X‖ ≤ ‖X‖ := by
    change ‖Matrix.trace (ρA * X) • (1 : Matrix (Fin a) (Fin a) ℂ)‖ ≤ ‖X‖
    simpa only [norm_smul, norm_one, mul_one, htrA, Complex.one_re, one_mul] using
      hρA.posSemidef.norm_trace_mul_le X
  let T := fun N ↦ (Kraus.mapLM A ^ (2 * N)).comp ((uncleWallGramMap A B R (N + 1)).comp
    ((Kraus.mapLM B ^ (2 * N - 1)).comp (uncleWallGramMap B A L (N + 1))))
  let U := fun N ↦ PA.comp ((uncleWallGramMap A B R (N + 1)).comp
    (PB.comp (uncleWallGramMap B A L (N + 1))))
  let z := max rA rB
  have hz : 0 < z := lt_of_lt_of_le hrA (le_max_left _ _)
  have hz1 : z < 1 := max_lt hrA1 hrB1
  let K := cR * cL * (cA + cB)
  have hK : 0 < K := by dsimp [K]; positivity
  have hpoint (N : ℕ) (hN : 0 < N) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖(T N - U N) X‖ ≤ K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N * ‖X‖ := by
    let m : ℝ := ((N + 1 : ℕ) : ℝ)
    let Y := uncleWallGramMap B A L (N + 1) X
    let Z := uncleWallGramMap A B R (N + 1) (((Kraus.mapLM B) ^ (2 * N - 1)) Y)
    let W := uncleWallGramMap A B R (N + 1) (PB Y)
    have hY : ‖Y‖ ≤ cL * m * ‖X‖ := hGL (N + 1) X
    have hZ : ‖Z‖ ≤ cR * m * (cL * m * ‖X‖) := by
      calc
        ‖Z‖ ≤ cR * m * ‖((Kraus.mapLM B) ^ (2 * N - 1)) Y‖ := hGR (N + 1) _
        _ ≤ cR * m * ‖Y‖ := mul_le_mul_of_nonneg_left
          (uncleUnital_pow_norm_le B hUB _ _) (by positivity)
        _ ≤ cR * m * (cL * m * ‖X‖) := mul_le_mul_of_nonneg_left hY (by positivity)
    have hrateA : rA ^ (2 * N) ≤ z ^ N :=
      (pow_le_pow_left₀ hrA.le (show rA ≤ z from le_max_left _ _) (2 * N)).trans
        (pow_le_pow_of_le_one hz.le hz1.le (by omega))
    have hrateB : rB ^ (2 * N - 1) ≤ z ^ N :=
      (pow_le_pow_left₀ hrB.le (show rB ≤ z from le_max_right _ _) (2 * N - 1)).trans
        (pow_le_pow_of_le_one hz.le hz1.le (by omega))
    have hfirst : ‖((Kraus.mapLM A) ^ (2 * N)) Z - PA Z‖ ≤
        cA * z ^ N * (cR * m * (cL * m * ‖X‖)) :=
      (hdecA (2 * N) (by omega) Z).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hrateA hcA.le) hZ
          (norm_nonneg _) (by positivity))
    have hdiff : ‖((Kraus.mapLM B) ^ (2 * N - 1)) Y - PB Y‖ ≤
        cB * z ^ N * (cL * m * ‖X‖) :=
      (hdecB (2 * N - 1) (by omega) Y).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hrateB hcB.le) hY
          (norm_nonneg _) (by positivity))
    have hsecond : ‖PA (uncleWallGramMap A B R (N + 1)
        (((Kraus.mapLM B) ^ (2 * N - 1)) Y - PB Y))‖ ≤
        cR * m * (cB * z ^ N * (cL * m * ‖X‖)) :=
      (hPA _).trans ((hGR (N + 1) _).trans
        (mul_le_mul_of_nonneg_left hdiff (by positivity)))
    change ‖((Kraus.mapLM A) ^ (2 * N)) Z - PA W‖ ≤ _
    have hsub : ((Kraus.mapLM A) ^ (2 * N)) Z - PA W =
        (((Kraus.mapLM A) ^ (2 * N)) Z - PA Z) +
          PA (uncleWallGramMap A B R (N + 1)
            (((Kraus.mapLM B) ^ (2 * N - 1)) Y - PB Y)) := by
      dsimp [Z, W]
      simp only [map_sub]
      abel
    rw [hsub]
    calc
      _ ≤ ‖((Kraus.mapLM A) ^ (2 * N)) Z - PA Z‖ +
          ‖PA (uncleWallGramMap A B R (N + 1)
            (((Kraus.mapLM B) ^ (2 * N - 1)) Y - PB Y))‖ := norm_add_le _ _
      _ ≤ cA * z ^ N * (cR * m * (cL * m * ‖X‖)) +
          cR * m * (cB * z ^ N * (cL * m * ‖X‖)) := add_le_add hfirst hsecond
      _ = K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N * ‖X‖ := by dsimp [K, m]; ring
  let V := Matrix (Fin a) (Fin a) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  letI : FiniteDimensional ℂ (V →L[ℂ] V) := Φ.toLinearEquiv.finiteDimensional
  let tr : (V →L[ℂ] V) →L[ℂ] ℂ :=
    ((LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap
  refine ⟨(‖tr‖ + 1) * K, z, by positivity, hz, hz1, fun N hN ↦ ?_⟩
  have hnorm : ‖Φ (T N - U N)‖ ≤ K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hpoint N hN)
  have hT : uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0 = T N := by
    simp [uncleTwoWallTransfer, T]
  have hU : LinearMap.trace ℂ V (U N) =
      uncleWallGramWeight A B R ρA (N + 1) * uncleWallGramWeight B A L ρB (N + 1) :=
    trace_uncleWallGram_rankOne_factorization A B R L ρA ρB (N + 1) (N + 1)
  calc
    _ = ‖tr (Φ (T N - U N))‖ := by
      rw [hT, ← hU]
      change _ = ‖LinearMap.trace ℂ V (T N - U N)‖
      rw [map_sub]
    _ ≤ ‖tr‖ * ‖Φ (T N - U N)‖ := tr.le_opNorm _
    _ ≤ ‖tr‖ * (K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg tr)
    _ ≤ (‖tr‖ + 1) * (K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (‖tr‖ + 1) * K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N := by ring

/-- The squared norm of the actual source trial, divided by the squared
moving-window length, converges to the product of the genuine limiting
wall coefficients. No positive-slope or norm-growth premise is required.
Source: arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleTwoWallTrialSource_normalized_norm_sq_tendsto [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hIA : Kraus.IsInjective A) (hIB : Kraus.IsInjective B)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef) (htrA : Matrix.trace ρA = 1)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef) (htrB : Matrix.trace ρB = 1)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB)
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    Tendsto (fun N : ℕ ↦
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)‖ ^ 2 / ((N + 1 : ℕ) : ℝ) ^ 2) atTop
      (𝓝 ((uncleWallNormSlope A B R ρA * uncleWallNormSlope B A L ρB).re)) := by
  obtain ⟨C, z, _, hz, hz1, hbound⟩ := uncleTwoWallTransfer_factorization_bound
    A B R L hIA hIB hUA hUB ρA hρA htrA ρB hρB htrB hFA hFB hAB hBA
  let m := fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)
  let s := fun N : ℕ ↦
    ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)‖ ^ 2
  let w := fun N : ℕ ↦
    (uncleWallGramWeight A B R ρA (N + 1) * uncleWallGramWeight B A L ρB (N + 1)).re /
      (m N) ^ 2
  let e := fun N : ℕ ↦ s N / (m N) ^ 2 - w N
  have habs : ∀ᶠ N : ℕ in atTop, |e N| ≤ C * z ^ N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hm : 0 < m N := by dsimp [m]; positivity
    dsimp only [e, w, s]
    rw [norm_uncleTwoWallTrialSource_sq_eq_trace_transfer A B R L N hN]
    rw [← sub_div, ← Complex.sub_re]
    calc
      _ = |(LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
          (uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0) -
          uncleWallGramWeight A B R ρA (N + 1) *
            uncleWallGramWeight B A L ρB (N + 1)).re| / (m N) ^ 2 := by
              rw [abs_div, abs_of_nonneg (sq_nonneg (m N))]
      _ ≤ ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
          (uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0) -
          uncleWallGramWeight A B R ρA (N + 1) *
            uncleWallGramWeight B A L ρB (N + 1)‖ / (m N) ^ 2 :=
              div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (sq_nonneg _)
      _ ≤ (C * (m N) ^ 2 * z ^ N) / (m N) ^ 2 :=
        div_le_div_of_nonneg_right (hbound N hN) (sq_nonneg _)
      _ = C * z ^ N := by
        rw [mul_right_comm C ((m N) ^ 2) (z ^ N),
          mul_div_cancel_right₀ _ (pow_ne_zero 2 (ne_of_gt hm))]
  have hgeom : Tendsto (fun N : ℕ ↦ C * z ^ N) atTop (𝓝 (0 : ℝ)) := by
    have hC : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
    simpa only [mul_zero] using hC.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hz.le hz1)
  have he : Tendsto e atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using habs) hgeom
  have hR := (uncleWallGramWeight_normalized_tendsto A B R ρA hρA.isHermitian
    hFA hUB hAB).comp (tendsto_add_atTop_nat 1)
  have hL := (uncleWallGramWeight_normalized_tendsto B A L ρB hρB.isHermitian
    hFB hUA hBA).comp (tendsto_add_atTop_nat 1)
  have hw : Tendsto w atTop
      (𝓝 ((uncleWallNormSlope A B R ρA * uncleWallNormSlope B A L ρB).re)) := by
    have hprod := (Complex.continuous_re.tendsto _).comp (hR.mul hL)
    refine Tendsto.congr (fun N ↦ ?_) hprod
    dsimp only [w, m, Function.comp_apply]
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero,
      div_eq_mul_inv, inv_pow]
    ring
  change Tendsto (fun N : ℕ ↦ s N / (m N) ^ 2) atTop _
  simpa only [e, sub_add_cancel, zero_add] using he.add hw

end MPSTensor
