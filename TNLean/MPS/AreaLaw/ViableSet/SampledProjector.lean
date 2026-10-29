/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.PowerProjector
import QICLean.Probability.MatrixBernstein
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.UniformOn

/-!
# The sampled approximate ground-state projector

Landau, Vazirani and Vidick replace the power projector `A = C^m n^{-m} ∑_I P_I` of
`TNLean.MPS.AreaLaw.ViableSet.PowerProjector`, with `C = (1 - ε₀/n)⁻¹`, by the average
`K = C^m ℓ⁻¹ ∑_{j=1}^ℓ P_{I_j}` of `ℓ` terms of the expansion, the words `I_j` chosen independently
and uniformly from the `n^m` words of length `m` in the letters `0, …, n - 1` (Definition
`d:sagsp`). Each sampled term `C^m P_I` has mean `A`, and `‖C^m P_I - A‖ ≤ C^m + 1` because every
letter `P_i = 1 - H_i` is a contraction and `‖A‖ = 1`. The matrix Bernstein inequality
(Theorem `t:mcb`, proved in QICLean) then bounds `P(‖K - A‖ ≥ t)`, and the scalar Bernstein
inequality, the case of `1 × 1` matrices, bounds the number of occurrences of each letter in each
word. A union bound gives Corollary `c:agsp` with explicit `ℓ` and `κ`, and a witness: a choice of
words for which both properties hold.

The probability space is the product `Fin ℓ → Fin m → Fin n` of `ℓ m` independent uniform letters.
The ground energy satisfies `0 ≤ ε₀ ≤ n - 1` (`groundEnergy_nonneg_and_le`), so `C ≥ 1` is well
defined; neither bound is assumed.

**Local fix (number of sampled words):** the source states `ℓ = n^{O(1/ε)}`, using
`C^{2m} = n^{O(1/ε)}` at `m = Θ((n/ε) log (q(n)/c_ε))` (line 644). Since
`C^m ≤ exp (ε₀ m/(n - ε₀))` (`powerNormalization_pow_le_exp`), this holds when `ε₀/ε` is bounded,
but it fails when `ε₀` grows linearly in `n`, which the hypotheses `0 ≤ H_i ≤ 1` allow. The
corollary is therefore formalized with `ℓ` explicit in `R = C^m + 1`,
`ℓ = ⌈(2R² + 2Rη/3) η⁻² log (8 q^n n³)⌉ + 1`, and `powerNormalization_pow_ceil_le` gives
`C^m ≤ n (1/η)^{ε₀/Δ}` at the logarithmic power, which is polynomial when `ε₀/Δ` is bounded. The
multiplicity bound `κ = ⌈2m/n + 2 log (4 ℓ n⁴)⌉` inherits the term `log ℓ`. Documented in
`docs/paper-gaps/lvv13_runtime_ground_energy.tex`.

The words range over the `n` letters of the padded expansion, whose last letter is the identity;
see `docs/paper-gaps/lvv13_power_expansion_padding.tex`.

## Main definitions

* `TNLean.MPS.AreaLaw.wordMeasure`, `TNLean.MPS.AreaLaw.sampleMeasure`: the uniform laws of one
  word and of `ℓ` independent words.
* `TNLean.MPS.AreaLaw.powerNormalization`: the constant `C = (1 - ε₀/n)⁻¹`.
* `TNLean.MPS.AreaLaw.sampledProjector`: the sampling operator `K` of Definition `d:sagsp`.
* `TNLean.MPS.AreaLaw.letterCount`: the number of occurrences of a letter in a word.
* `TNLean.MPS.AreaLaw.sampledProjectorWordCount`, `TNLean.MPS.AreaLaw.sampledProjectorLetterBound`:
  the explicit `ℓ` and `κ`.

## Main results

* `TNLean.MPS.AreaLaw.integral_scaledBondComplementWord`: `E[C^m P_I] = A`.
* `TNLean.MPS.AreaLaw.norm_scaledBondComplementWord_sub_le`: `‖C^m P_I - A‖ ≤ C^m + 1`.
* `TNLean.MPS.AreaLaw.measureReal_le_norm_sampledProjector_sub_le`: the accuracy tail.
* `TNLean.MPS.AreaLaw.measureReal_exists_le_letterCount_le`: the multiplicity tail.
* `TNLean.MPS.AreaLaw.one_sub_le_measureReal_sampledProjector`,
  `TNLean.MPS.AreaLaw.one_sub_inv_pow_three_le_measureReal_sampledProjector`: Corollary `c:agsp`,
  probability form.
* `TNLean.MPS.AreaLaw.exists_sampledProjector`: Corollary `c:agsp`, existence form, with the rank
  bound of equation `e:decomp` for every sampled word.
* `TNLean.MPS.AreaLaw.powerNormalization_pow_le_exp`,
  `TNLean.MPS.AreaLaw.powerNormalization_pow_ceil_le`: the size of `C^m`.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`: the
  decomposition `e:decomp`, lines 584–588; the expansion `eq:a-exp`, lines 606–609; Definition
  `d:sagsp`, line 611; Theorem `t:mcb`, lines 616–624; Corollary `c:agsp` and its proof,
  lines 626–649.
* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12
  (2012), Theorem 1.6.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-! ### The probability space of sampled words -/

/-- The uniform law of a word of length `m` in the letters `Fin L`: its letters are independent
and uniform, so every word has probability `n^{-m}`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 611 ("chosen uniformly at random from all terms"). -/
noncomputable def wordMeasure (m L : ℕ) : Measure (Fin m → Fin L) :=
  Measure.pi fun _ ↦ uniformOn Set.univ

/-- The law of `ℓ` independent uniform words of length `m`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 611. -/
noncomputable def sampleMeasure (ℓ m L : ℕ) : Measure (Fin ℓ → Fin m → Fin L) :=
  Measure.pi fun _ ↦ wordMeasure m L

/-- With at least one letter, the law of a word is a probability measure. -/
instance (m L : ℕ) [NeZero L] : IsProbabilityMeasure (wordMeasure m L) := by
  unfold wordMeasure
  infer_instance

/-- With at least one letter, the law of a sample is a probability measure. -/
instance (ℓ m L : ℕ) [NeZero L] : IsProbabilityMeasure (sampleMeasure ℓ m L) := by
  unfold sampleMeasure
  infer_instance

/-- Every word of length `m` has probability `n^{-m}`. -/
theorem measureReal_wordMeasure_singleton (m L : ℕ) [NeZero L] (I : Fin m → Fin L) :
    (wordMeasure m L).real {I} = ((L : ℝ) ^ m)⁻¹ := by
  have hI : ({I} : Set (Fin m → Fin L)) = Set.univ.pi fun p ↦ {I p} := by
    ext J
    simp [funext_iff]
  rw [measureReal_def, hI, wordMeasure, Measure.pi_pi]
  simp [uniformOn_univ]


/-! ### The sampled projector -/

/-- The normalization `C = (1 - ε₀/n)⁻¹` of the power projector. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 606. -/
noncomputable def powerNormalization (L : ℕ) (E₀ : ℝ) : ℝ :=
  (1 - E₀ / L)⁻¹

/-- One sampled term `C^m P_I`, the random matrix `X_i` of the proof of Corollary `c:agsp`.
Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, line 641. -/
noncomputable def scaledBondComplementWord
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {m : ℕ}
    (I : Fin m → Fin L) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  powerNormalization L E₀ ^ m • bondComplementWord h I

/-- **Definition `d:sagsp`.** The sampling approximate ground-state projector
`K = C^m ℓ⁻¹ ∑_{j=1}^ℓ P_{I_j}` of the words `I_1, …, I_ℓ`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 611; the words are drawn by `sampleMeasure`. -/
noncomputable def sampledProjector
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  powerNormalization L E₀ ^ m • ((ℓ : ℝ)⁻¹ • ∑ k, bondComplementWord h (I k))

/-- The sampled projector is the average of the sampled terms `C^m P_{I_j}`, the form in which
Theorem `t:mcb` applies (`algo53.tex`, line 641). -/
theorem sampledProjector_eq_average
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) :
    sampledProjector h E₀ I = (ℓ : ℝ)⁻¹ • ∑ k, scaledBondComplementWord h E₀ (I k) := by
  simp only [sampledProjector, scaledBondComplementWord, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- The ground energy lies between `0` and `n - 1`: `0 ≤ H ≤ n - 1` and `ε₀ = ⟨Γ, HΓ⟩`. Hence
`C = (1 - ε₀/n)⁻¹` is well defined and at least one. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 283–284 and 607. -/
theorem groundEnergy_nonneg_and_le [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) :
    0 ≤ E₀ ∧ E₀ + 1 ≤ L := by
  obtain ⟨hΓ, hHΓ, -⟩ := hgs
  set H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
  have hH : H.PosSemidef := posSemidef_sum Finset.univ fun i _ ↦ h0 i
  have hHu : H ≤ ((L - 1 : ℕ) : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) := by
    simpa only [H, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul] using
      Finset.sum_le_card_nsmul Finset.univ h 1 fun i _ ↦ h1 i
  have hE : RCLike.re ⟪Γ, toEuclideanLin H Γ⟫_ℂ = E₀ := by
    have : toEuclideanLin H Γ = (E₀ : ℂ) • Γ := hHΓ
    rw [this, inner_smul_right, inner_self_eq_norm_sq_to_K, hΓ]
    simp
  have hlow := (isPositive_toEuclideanLin_iff.mpr hH).re_inner_nonneg_right Γ
  have hup := (isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp hHu)).re_inner_nonneg_right Γ
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, map_sub] at hup
  have hc : RCLike.re ⟪Γ, toEuclideanLin (((L - 1 : ℕ) : ℝ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) Γ⟫_ℂ = ((L - 1 : ℕ) : ℝ) := by
    rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, toEuclideanLin_one_apply,
      inner_smul_right, inner_self_eq_norm_sq_to_K, hΓ]
    simp
  rw [hc] at hup
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  rw [Nat.cast_sub hL, Nat.cast_one] at hup
  constructor <;> linarith

/-- A letter `P_i = 1 - H_i` is a contraction, since `0 ≤ P_i ≤ 1`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 606 and 641. -/
theorem norm_bondComplement_le_one
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1) (i : Fin L) :
    ‖bondComplement h i‖ ≤ 1 := by
  have hP0 : 0 ≤ paddedBond h i := by
    unfold paddedBond
    split_ifs
    exacts [(h0 _).nonneg, le_rfl]
  have hP1 : paddedBond h i ≤ 1 := by
    unfold paddedBond
    split_ifs
    exacts [h1 _, zero_le_one]
  have hB0 : 0 ≤ bondComplement h i := sub_nonneg.mpr hP1
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hB0).mpr (sub_le_self _ hP0)

/-- A word `P_I` in the letters is a contraction, so `‖C^m P_I‖ ≤ C^m`. Landau, Vazirani and
Vidick, arXiv:1307.5143v1, `algo53.tex`, line 641. -/
theorem norm_bondComplementWord_le_one
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1) {m : ℕ} (I : Fin m → Fin L) :
    ‖bondComplementWord h I‖ ≤ 1 := by
  have key : ∀ l : List (Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ a ∈ l, ‖a‖ ≤ 1) → ‖l.prod‖ ≤ 1 := by
    intro l
    induction l with
    | nil =>
      intro _
      exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ zero_le_one).mpr le_rfl
    | cons a l ih =>
      intro hl
      rw [List.prod_cons]
      calc ‖a * l.prod‖ ≤ ‖a‖ * ‖l.prod‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (hl a (by simp)) (ih fun b hb ↦ hl b (by simp [hb]))
            (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  refine key _ fun a ha ↦ ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  exact norm_bondComplement_le_one h h0 h1 _

/-- With `0 ≤ ε₀ < n`, the normalization `C` is at least one, so `R = C^m + 1 ≥ 1`. -/
theorem one_le_powerNormalization [NeZero L] {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀L : E₀ < L) :
    1 ≤ powerNormalization L E₀ := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_neZero L)
  have h1 : 0 < 1 - E₀ / L := by rw [sub_pos, div_lt_one hL]; exact hE₀L
  have h2 : 1 - E₀ / L ≤ 1 := sub_le_self _ (div_nonneg hE₀ hL.le)
  exact one_le_inv₀ h1 |>.mpr h2

/-- **The mean of a sampled term.** For a uniform word `I`, `E[C^m P_I] = A`, by the expansion
`eq:a-exp`. Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 606–611 and
641. -/
theorem integral_scaledBondComplementWord [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) (m : ℕ) :
    ∫ I, scaledBondComplementWord h E₀ I ∂wordMeasure m L = powerProjector (∑ i, h i) L E₀ m := by
  rw [integral_fintype (Integrable.of_finite), powerProjector_eq_sum_bondComplementWord
    (Nat.pos_of_neZero L), Finset.smul_sum]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  rw [measureReal_wordMeasure_singleton, scaledBondComplementWord, smul_smul, powerNormalization,
    ← Complex.coe_smul]
  push_cast
  ring_nf

/-- **The deviation bound `R = C^m + 1`.** Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`algo53.tex`, line 641. -/
theorem norm_scaledBondComplementWord_sub_le [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) {m : ℕ} (I : Fin m → Fin L) :
    ‖scaledBondComplementWord h E₀ I - powerProjector (∑ i, h i) L E₀ m‖ ≤
      powerNormalization L E₀ ^ m + 1 := by
  obtain ⟨hE₀, hE₀L⟩ := groundEnergy_nonneg_and_le h h0 h1 hgs
  have hC : 0 ≤ powerNormalization L E₀ ^ m :=
    pow_nonneg (zero_le_one.trans (one_le_powerNormalization hE₀ (by linarith))) m
  calc _ ≤ ‖scaledBondComplementWord h E₀ I‖ + ‖powerProjector (∑ i, h i) L E₀ m‖ :=
        norm_sub_le _ _
    _ ≤ powerNormalization L E₀ ^ m * 1 + 1 := by
        rw [norm_powerProjector (Nat.pos_of_neZero L) h h0 h1 hgs hΔ m,
          scaledBondComplementWord, norm_smul, Real.norm_of_nonneg hC]
        gcongr
        exact norm_bondComplementWord_le_one h h0 h1 I
    _ = _ := by rw [mul_one]

/-- **Accuracy of the sampled projector** (item 1 of Corollary `c:agsp`, in the
non-asymptotic form given by Theorem `t:mcb`). For `ℓ ≥ 1` independent uniform words and
`t > 0`, `P(‖K - A‖ ≥ t) ≤ 2 q^n exp (-ℓ t² / (2 R² + 2 R t / 3))` with `R = C^m + 1`.
Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 616–624 and 640–643. -/
theorem measureReal_le_norm_sampledProjector_sub_le [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) (ℓ m : ℕ) [NeZero ℓ]
    {t : ℝ} (ht : 0 < t) :
    (sampleMeasure ℓ m L).real
        {I | t ≤ ‖sampledProjector h E₀ I - powerProjector (∑ i, h i) L E₀ m‖} ≤
      2 * q ^ L * Real.exp (-(ℓ * t ^ 2 / (2 * (powerNormalization L E₀ ^ m + 1) ^ 2 +
        2 * (powerNormalization L E₀ ^ m + 1) * t / 3))) := by
  set A := powerProjector (∑ i, h i) L E₀ m
  set R := powerNormalization L E₀ ^ m + 1
  obtain ⟨hE₀, hE₀L⟩ := groundEnergy_nonneg_and_le h h0 h1 hgs
  have hR1 : 1 ≤ R := le_add_of_nonneg_left
    (pow_nonneg (zero_le_one.trans (one_le_powerNormalization hE₀ (by linarith))) m)
  rcases isEmpty_or_nonempty (Fin L → Fin q) with hd | hd
  · have : {I : Fin ℓ → Fin m → Fin L |
        t ≤ ‖sampledProjector h E₀ I - A‖} = ∅ := by
      ext I
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [Subsingleton.elim (sampledProjector h E₀ I - A) 0, norm_zero]
      exact ht
    rw [this, measureReal_empty]
    positivity
  set X : Fin ℓ → (Fin ℓ → Fin m → Fin L) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    fun k I ↦ scaledBondComplementWord h E₀ (I k)
  have hind : iIndepFun X (sampleMeasure ℓ m L) :=
    iIndepFun_pi (X := fun _ ↦ scaledBondComplementWord h E₀)
      fun _ ↦ (measurable_of_countable _).aemeasurable
  have heval : ∀ k, IdentDistrib (fun I : Fin ℓ → Fin m → Fin L ↦ I k) (fun I ↦ I 0)
      (sampleMeasure ℓ m L) (sampleMeasure ℓ m L) := fun k ↦
    ⟨(measurable_pi_apply k).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
      rw [sampleMeasure, (measurePreserving_eval _ k).map_eq,
        (measurePreserving_eval _ 0).map_eq]⟩
  have hident : ∀ k, IdentDistrib (X k) (X 0) (sampleMeasure ℓ m L) (sampleMeasure ℓ m L) :=
    fun k ↦ (heval k).comp (measurable_of_countable (scaledBondComplementWord h E₀))
  have hmean : ∀ k, ∫ I, X k I ∂sampleMeasure ℓ m L = A := fun k ↦ by
    rw [sampleMeasure, integral_comp_eval (measurable_of_countable _).aestronglyMeasurable]
    exact integral_scaledBondComplementWord h E₀ m
  have hdev : ∀ k, ∀ᵐ I ∂sampleMeasure ℓ m L, ‖X k I - A‖ ≤ R := fun k ↦
    Filter.Eventually.of_forall fun I ↦
      norm_scaledBondComplementWord_sub_le h h0 h1 hgs hΔ (I k)
  have hbern := Matrix.measureReal_le_norm_average_sub_le hind hident
    (fun k ↦ measurable_of_countable _) hmean hdev ht.le
  have hset : {I : Fin ℓ → Fin m → Fin L | t ≤ ‖sampledProjector h E₀ I - A‖} =
      {I | t ≤ ‖(ℓ : ℝ)⁻¹ • ∑ k, X k I - A‖} := by
    ext I
    simp only [Set.mem_ofPred_eq, X, sampledProjector_eq_average]
  rw [hset]
  refine hbern.trans ?_
  have hcard : (Fintype.card (Fin L → Fin q) : ℝ) = (q : ℝ) ^ L := by simp
  rw [hcard]
  -- the variance terms are at most `R²`
  have hvar : ∀ f : (Fin ℓ → Fin m → Fin L) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (∀ I, ‖f I‖ ≤ R ^ 2) → ‖∫ I, f I ∂sampleMeasure ℓ m L‖ ≤ R ^ 2 := fun f hf ↦ by
    simpa using norm_integral_le_of_norm_le_const (μ := sampleMeasure ℓ m L)
      (Filter.Eventually.of_forall hf)
  have hsq : ∀ I, ‖X 0 I - A‖ ^ 2 ≤ R ^ 2 := fun I ↦
    pow_le_pow_left₀ (norm_nonneg _) (norm_scaledBondComplementWord_sub_le h h0 h1 hgs hΔ _) 2
  have hV₁ := hvar (fun I ↦ (X 0 I - A) * (X 0 I - A)ᴴ) fun I ↦ by
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose, ← sq]
    exact hsq I
  have hV₂ := hvar (fun I ↦ (X 0 I - A)ᴴ * (X 0 I - A)) fun I ↦ by
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose, ← sq]
    exact hsq I
  have hmax := max_le hV₁ hV₂
  gcongr

/-! ### Letter multiplicities -/

/-- The number `Y_j(I)` of occurrences of the letter `j` in the word `I`. Landau, Vazirani and
Vidick, arXiv:1307.5143v1, `algo53.tex`, line 646. -/
def letterCount {m : ℕ} (I : Fin m → Fin L) (j : Fin L) : ℕ :=
  (Finset.univ.filter fun p ↦ I p = j).card

/-- The indicator of the letter `j`, centred at its mean `1/n`. -/
private noncomputable def centredIndicator (L : ℕ) (j x : Fin L) : ℝ :=
  (if x = j then 1 else 0) - (L : ℝ)⁻¹

private theorem measureReal_uniformOn_singleton [NeZero L] (x : Fin L) :
    (uniformOn (Set.univ : Set (Fin L))).real {x} = (L : ℝ)⁻¹ := by
  simp [measureReal_def, uniformOn_univ]

private theorem integral_wordMeasure_eval [NeZero L] {m : ℕ} (p : Fin m)
    (f : Fin L → Matrix (Fin 1) (Fin 1) ℂ) :
    ∫ I, f (I p) ∂wordMeasure m L = ∫ x, f x ∂uniformOn (Set.univ : Set (Fin L)) :=
  integral_comp_eval (measurable_of_countable _).aestronglyMeasurable

private theorem integral_centredIndicator [NeZero L] (j : Fin L) :
    ∫ x, centredIndicator L j x ∂uniformOn (Set.univ : Set (Fin L)) = 0 := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_uniformOn_singleton, centredIndicator, smul_eq_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private theorem integral_centredIndicator_sq_le [NeZero L] (j : Fin L) :
    ∫ x, centredIndicator L j x ^ 2 ∂uniformOn (Set.univ : Set (Fin L)) ≤ (L : ℝ)⁻¹ := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_neZero L)
  have hpt : ∀ x, centredIndicator L j x ^ 2 =
      (if x = j then 1 else 0) * (1 - 2 * (L : ℝ)⁻¹) + (L : ℝ)⁻¹ ^ 2 := fun x ↦ by
    unfold centredIndicator
    split_ifs <;> ring
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_uniformOn_singleton, hpt, smul_eq_mul, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (L : ℝ)⁻¹ * (1 * (1 - 2 * (L : ℝ)⁻¹) + L * (L : ℝ)⁻¹ ^ 2) =
      (L : ℝ)⁻¹ - (L : ℝ)⁻¹ ^ 2 := by
    field_simp
    ring
  rw [this]
  nlinarith [sq_nonneg (L : ℝ)⁻¹]

/-- **The multiplicity tail for one word.** The number `Y_j` of occurrences of a letter `j` in a
uniform word of length `m` has mean `m/n` and variance at most `m/n`, and Bernstein's inequality
gives `P(Y_j ≥ m/n + t) ≤ exp (-(t²/2) / (m/n + t/3))`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 646–649, where the tail is stated as `e^{-Ω(a²)}`. -/
theorem measureReal_le_letterCount_le [NeZero L] (m : ℕ) (j : Fin L) {t : ℝ} (ht : 0 ≤ t) :
    (wordMeasure m L).real {I | (m : ℝ) / L + t ≤ letterCount I j} ≤
      Real.exp (-(t ^ 2 / 2 / ((m : ℝ) / L + t / 3))) := by
  rcases ht.eq_or_lt with rfl | ht0
  · simp
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_neZero L)
  set Y : Fin m → (Fin m → Fin L) → Matrix (Fin 1) (Fin 1) ℂ :=
    fun p I ↦ centredIndicator L j (I p) • (1 : Matrix (Fin 1) (Fin 1) ℂ)
  have hind : iIndepFun Y (wordMeasure m L) :=
    iIndepFun_pi (X := fun _ x ↦ centredIndicator L j x • (1 : Matrix (Fin 1) (Fin 1) ℂ))
      fun _ ↦ (measurable_of_countable _).aemeasurable
  have hY : ∀ p, ∀ᵐ I ∂wordMeasure m L, (Y p I).IsHermitian := fun p ↦
    Filter.Eventually.of_forall fun I ↦ isHermitian_one.smul (IsSelfAdjoint.all _)
  have hmean : ∀ p, ∫ I, Y p I ∂wordMeasure m L = 0 := fun p ↦
    (integral_wordMeasure_eval p fun x ↦ centredIndicator L j x • 1).trans (by
      rw [integral_smul_const, integral_centredIndicator, zero_smul])
  have hbd : ∀ x, |centredIndicator L j x| ≤ 1 := fun x ↦ by
    have h1 : (L : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.pos_of_neZero L))
    have h0 : 0 ≤ (L : ℝ)⁻¹ := inv_nonneg.mpr hL.le
    unfold centredIndicator
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
  have hR : ∀ p, ∀ᵐ I ∂wordMeasure m L, ‖Y p I‖ ≤ 1 := fun p ↦
    Filter.Eventually.of_forall fun I ↦ by
      simp only [Y, norm_smul, norm_one, mul_one, Real.norm_eq_abs]
      exact hbd _
  have hbern := Matrix.measureReal_exists_le_mem_spectrum_sum_le hind
    (fun p ↦ measurable_of_countable _) hY hmean hR ht0.le
  -- the variance parameter is at most `m/n`
  set v := ∫ x, centredIndicator L j x ^ 2 ∂uniformOn (Set.univ : Set (Fin L))
  have hv0 : 0 ≤ v := integral_nonneg fun x ↦ sq_nonneg _
  have hvar : ‖∑ p, ∫ I, Y p I ^ 2 ∂wordMeasure m L‖ ≤ (m : ℝ) / L := by
    have hterm : ∀ p, ∫ I, Y p I ^ 2 ∂wordMeasure m L = v • (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
      fun p ↦ by
        simp only [Y, smul_pow, one_pow]
        exact (integral_wordMeasure_eval p fun x ↦ centredIndicator L j x ^ 2 • 1).trans
          (integral_smul_const _ _)
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, norm_smul, norm_one, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (integral_centredIndicator_sq_le j) (Nat.cast_nonneg m)
  refine le_trans (measureReal_mono ?_) (hbern.trans ?_)
  · intro I hI
    simp only [Set.mem_ofPred_eq] at hI ⊢
    refine ⟨letterCount I j - (m : ℝ) / L, ?_, by linarith⟩
    have hsum : ∑ p, Y p I = algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℂ)
        (letterCount I j - (m : ℝ) / L) := by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [Y, ← Finset.sum_smul, centredIndicator, Finset.sum_sub_distrib,
        Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        letterCount, div_eq_mul_inv]
    rw [hsum, spectrum.scalar_eq]
    exact Set.mem_singleton _
  · simp only [Fintype.card_fin, Nat.cast_one, one_mul]
    gcongr

/-- **The multiplicity tail for the sample.** The probability that some letter occurs at least
`m/n + t` times in one of `ℓ` independent uniform words is at most
`ℓ n exp (-(t²/2) / (m/n + t/3))`, by a union bound over the words and the letters. Landau,
Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 646–649. -/
theorem measureReal_exists_le_letterCount_le [NeZero L] (ℓ m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (sampleMeasure ℓ m L).real {I | ∃ k j, (m : ℝ) / L + t ≤ letterCount (I k) j} ≤
      ℓ * L * Real.exp (-(t ^ 2 / 2 / ((m : ℝ) / L + t / 3))) := by
  have hset : {I : Fin ℓ → Fin m → Fin L | ∃ k j, (m : ℝ) / L + t ≤ letterCount (I k) j} =
      ⋃ k, ⋃ j, (fun I ↦ I k) ⁻¹' {J | (m : ℝ) / L + t ≤ letterCount J j} := by
    ext
    simp
  rw [hset]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc _ ≤ ∑ _k : Fin ℓ, ∑ _j : Fin L, Real.exp (-(t ^ 2 / 2 / ((m : ℝ) / L + t / 3))) :=
        Finset.sum_le_sum fun k _ ↦ (measureReal_iUnion_fintype_le _).trans
          (Finset.sum_le_sum fun j _ ↦ by
            rw [sampleMeasure, (measurePreserving_eval _ k).measureReal_preimage
              (Set.to_countable _).measurableSet.nullMeasurableSet]
            exact measureReal_le_letterCount_le m j ht)
    _ = _ := by simp [mul_assoc]

/-! ### The size of `C^m` -/

/-- `C = (1 - ε₀/n)⁻¹ = 1 + ε₀/(n - ε₀)`. -/
theorem powerNormalization_eq [NeZero L] {E₀ : ℝ} (hE₀L : E₀ < L) :
    powerNormalization L E₀ = 1 + E₀ / (L - E₀) := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hd : (L : ℝ) - E₀ ≠ 0 := sub_ne_zero.mpr hE₀L.ne'
  rw [powerNormalization, one_sub_div hL, inv_div]
  field_simp
  ring

/-- **The normalization grows with the ground energy:** `C^m ≤ exp (ε₀ m / (n - ε₀))`. -/
theorem powerNormalization_pow_le_exp [NeZero L] {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀L : E₀ < L)
    (m : ℕ) : powerNormalization L E₀ ^ m ≤ Real.exp (E₀ * m / (L - E₀)) := by
  have hC : 0 ≤ powerNormalization L E₀ :=
    zero_le_one.trans (one_le_powerNormalization hE₀ hE₀L)
  calc powerNormalization L E₀ ^ m ≤ Real.exp (E₀ / (L - E₀)) ^ m := by
        gcongr
        rw [powerNormalization_eq hE₀L, add_comm]
        exact Real.add_one_le_exp _
    _ = _ := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- **The size of `C^m` at the logarithmic power.** With `0 ≤ ε₀ ≤ n - 1`, `0 < η ≤ 1` and
`m = ⌈((n - ε₀)/Δ) log (1/η)⌉`, `C^m ≤ n (1/η)^{ε₀/Δ}`. Hence `C^m`, and with it the number
`sampledProjectorWordCount` of sampled words, is polynomial in `n` and `1/η` when `ε₀/Δ` is
bounded; for `ε₀` of order `n` it is not. -/
theorem powerNormalization_pow_ceil_le [NeZero L] {E₀ Δ η : ℝ} (hE₀ : 0 ≤ E₀)
    (hE₀L : E₀ + 1 ≤ L) (hΔ : 0 < Δ) (hη : 0 < η) (hη1 : η ≤ 1) :
    powerNormalization L E₀ ^ ⌈((L - E₀) / Δ) * Real.log (1 / η)⌉₊ ≤
      L * (1 / η) ^ (E₀ / Δ) := by
  set x := ((L - E₀) / Δ) * Real.log (1 / η)
  have hd : 1 ≤ (L : ℝ) - E₀ := by linarith
  have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg (one_le_one_div hη hη1)
  have hx : 0 ≤ x := mul_nonneg (div_nonneg (by linarith) hΔ.le) hlog
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hrpow : 1 ≤ (1 / η) ^ (E₀ / Δ) :=
    Real.one_le_rpow (one_le_one_div hη hη1) (div_nonneg hE₀ hΔ.le)
  have hC1 := one_le_powerNormalization hE₀ (by linarith : E₀ < L)
  have hCL : powerNormalization L E₀ ≤ L := by
    rw [powerNormalization_eq (by linarith)]
    have : E₀ / (L - E₀) ≤ E₀ := div_le_self hE₀ hd
    linarith
  rcases Nat.eq_zero_or_pos ⌈x⌉₊ with h0 | hpos
  · rw [h0, pow_zero]
    nlinarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hkx : (k : ℝ) ≤ x := by
    have := Nat.ceil_lt_add_one hx
    rw [hk, Nat.cast_succ] at this
    linarith
  rw [hk, pow_succ']
  gcongr
  calc powerNormalization L E₀ ^ k ≤ Real.exp (E₀ * k / (L - E₀)) :=
        powerNormalization_pow_le_exp hE₀ (by linarith) k
    _ ≤ Real.exp (E₀ * x / (L - E₀)) := by gcongr
    _ = (1 / η) ^ (E₀ / Δ) := by
        rw [Real.rpow_def_of_pos (one_div_pos.mpr hη)]
        congr 1
        simp only [x]
        field_simp

/-! ### Corollary `c:agsp` -/

/-- **Corollary `c:agsp`, probability form.** Let `R = C^m + 1`, and let `ℓ ≥ 1` and `κ`
satisfy `ℓ ≥ (2R² + 2Rη/3) η⁻² log (8 q^n n³)` and `κ ≥ 2m/n + 2 log (4 ℓ n⁴)`. Then with
probability at least `1 - 1/(2n³)`, the sampled projector built from `ℓ` independent uniform
words of length `m` satisfies `‖K - A‖ < η`, and every letter occurs at most `κ` times in every
word. Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 626–649.

The number of words is stated through `C^m`; see the module docstring for the dependence of
`C^m` on the ground energy. -/
theorem one_sub_le_measureReal_sampledProjector [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) (m : ℕ) {η : ℝ} (hη : 0 < η)
    {ℓ κ : ℕ} [NeZero ℓ]
    (hℓ : (2 * (powerNormalization L E₀ ^ m + 1) ^ 2 +
        2 * (powerNormalization L E₀ ^ m + 1) * η / 3) / η ^ 2 *
          Real.log (8 * q ^ L * L ^ 3) ≤ ℓ)
    (hκ : 2 * (m : ℝ) / L + 2 * Real.log (4 * ℓ * L ^ 4) ≤ κ) :
    1 - 1 / (2 * (L : ℝ) ^ 3) ≤ (sampleMeasure ℓ m L).real
      {I | ‖sampledProjector h E₀ I - powerProjector (∑ i, h i) L E₀ m‖ < η ∧
        ∀ k j, letterCount (I k) j ≤ κ} := by
  set μ := sampleMeasure ℓ m L
  set A := powerProjector (∑ i, h i) L E₀ m
  set R := powerNormalization L E₀ ^ m + 1
  set D := 2 * R ^ 2 + 2 * R * η / 3
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_neZero L)
  have hℓ0 : (0 : ℝ) < ℓ := Nat.cast_pos.mpr (Nat.pos_of_neZero ℓ)
  obtain ⟨hE₀, hE₀L⟩ := groundEnergy_nonneg_and_le h h0 h1 hgs
  have hR1 : 1 ≤ R := le_add_of_nonneg_left
    (pow_nonneg (zero_le_one.trans (one_le_powerNormalization hE₀ (by linarith))) m)
  have hD : 0 < D := by positivity
  -- the accuracy failure
  set B₁ := {I : Fin ℓ → Fin m → Fin L | η ≤ ‖sampledProjector h E₀ I - A‖}
  have hB₁ : μ.real B₁ ≤ 1 / (4 * (L : ℝ) ^ 3) := by
    refine (measureReal_le_norm_sampledProjector_sub_le h h0 h1 hgs hΔ ℓ m hη).trans ?_
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [zero_pow (NeZero.ne L)]
    have hqL : (1 : ℝ) ≤ (q : ℝ) ^ L := one_le_pow₀ (Nat.one_le_cast.mpr hq)
    have hpos : (0 : ℝ) < 8 * (q : ℝ) ^ L * (L : ℝ) ^ 3 := by positivity
    have ha : Real.log (8 * (q : ℝ) ^ L * (L : ℝ) ^ 3) ≤ ℓ * η ^ 2 / D := by
      rw [le_div_iff₀ hD]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hℓ
      linarith
    calc 2 * (q : ℝ) ^ L * Real.exp (-(ℓ * η ^ 2 / D))
        ≤ 2 * (q : ℝ) ^ L * Real.exp (-Real.log (8 * (q : ℝ) ^ L * (L : ℝ) ^ 3)) := by
          gcongr
      _ = 1 / (4 * (L : ℝ) ^ 3) := by
          rw [Real.exp_neg, Real.exp_log hpos]
          field_simp
          ring
  -- the multiplicity failure
  set t : ℝ := κ - (m : ℝ) / L
  set a := Real.log (4 * ℓ * (L : ℝ) ^ 4)
  have ha0 : 0 < a := Real.log_pos (by
    have : (1 : ℝ) ≤ ℓ := Nat.one_le_cast.mpr (Nat.pos_of_neZero ℓ)
    have : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ (Nat.one_le_cast.mpr (Nat.pos_of_neZero L))
    nlinarith)
  have hmL : 0 ≤ (m : ℝ) / L := by positivity
  have ht : (m : ℝ) / L + 2 * a ≤ t := by
    simp only [t, a]
    rw [mul_div_assoc] at hκ
    linarith
  have ht0 : 0 < t := by linarith
  set B₂ := {I : Fin ℓ → Fin m → Fin L | ∃ k j, (m : ℝ) / L + t ≤ letterCount (I k) j}
  have hB₂ : μ.real B₂ ≤ 1 / (4 * (L : ℝ) ^ 3) := by
    refine (measureReal_exists_le_letterCount_le ℓ m ht0.le).trans ?_
    have hden : 0 < (m : ℝ) / L + t / 3 := by positivity
    have hexp : a ≤ t ^ 2 / 2 / ((m : ℝ) / L + t / 3) := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc (ℓ : ℝ) * L * Real.exp (-(t ^ 2 / 2 / ((m : ℝ) / L + t / 3)))
        ≤ ℓ * L * Real.exp (-a) := by gcongr
      _ = 1 / (4 * (L : ℝ) ^ 3) := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
  -- the good event contains the complement of the two failures
  have hsub : (B₁ ∪ B₂)ᶜ ⊆ {I | ‖sampledProjector h E₀ I - A‖ < η ∧
      ∀ k j, letterCount (I k) j ≤ κ} := by
    intro I hI
    simp only [Set.mem_compl_iff, Set.mem_union, not_or, B₁, B₂, Set.mem_ofPred_eq, not_le,
      not_exists] at hI
    refine ⟨hI.1, fun k j ↦ ?_⟩
    have := hI.2 k j
    simp only [t, add_sub_cancel] at this
    exact_mod_cast this.le
  have hmeas : MeasurableSet (B₁ ∪ B₂) := (Set.to_countable _).measurableSet
  calc 1 - 1 / (2 * (L : ℝ) ^ 3) ≤ 1 - (μ.real B₁ + μ.real B₂) := by
        have : 1 / (2 * (L : ℝ) ^ 3) = 1 / (4 * (L : ℝ) ^ 3) + 1 / (4 * (L : ℝ) ^ 3) := by
          field_simp
          ring
        linarith
    _ ≤ 1 - μ.real (B₁ ∪ B₂) := by linarith [measureReal_union_le (μ := μ) B₁ B₂]
    _ = μ.real (B₁ ∪ B₂)ᶜ := (probReal_compl_eq_one_sub hmeas).symm
    _ ≤ _ := measureReal_mono hsub

/-- The source's form of the success probability, `1 - 1/n³`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 626–649. -/
theorem one_sub_inv_pow_three_le_measureReal_sampledProjector [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) (m : ℕ) {η : ℝ} (hη : 0 < η)
    {ℓ κ : ℕ} [NeZero ℓ]
    (hℓ : (2 * (powerNormalization L E₀ ^ m + 1) ^ 2 +
        2 * (powerNormalization L E₀ ^ m + 1) * η / 3) / η ^ 2 *
          Real.log (8 * q ^ L * L ^ 3) ≤ ℓ)
    (hκ : 2 * (m : ℝ) / L + 2 * Real.log (4 * ℓ * L ^ 4) ≤ κ) :
    1 - 1 / (L : ℝ) ^ 3 ≤ (sampleMeasure ℓ m L).real
      {I | ‖sampledProjector h E₀ I - powerProjector (∑ i, h i) L E₀ m‖ < η ∧
        ∀ k j, letterCount (I k) j ≤ κ} := by
  refine le_trans ?_ (one_sub_le_measureReal_sampledProjector h h0 h1 hgs hΔ m hη hℓ hκ)
  have : (0 : ℝ) < (L : ℝ) ^ 3 := by have := Nat.pos_of_neZero L; positivity
  gcongr 1 - ?_
  rw [div_le_div_iff_of_pos_left one_pos (by positivity) this]
  linarith

/-- The explicit number of sampled words,
`ℓ = ⌈(2R² + 2Rη/3) η⁻² log (8 q^n n³)⌉ + 1` with `R = C^m + 1`. -/
noncomputable def sampledProjectorWordCount (q L : ℕ) (E₀ η : ℝ) (m : ℕ) : ℕ :=
  ⌈(2 * (powerNormalization L E₀ ^ m + 1) ^ 2 + 2 * (powerNormalization L E₀ ^ m + 1) * η / 3) /
    η ^ 2 * Real.log (8 * q ^ L * L ^ 3)⌉₊ + 1

instance (q L : ℕ) (E₀ η : ℝ) (m : ℕ) : NeZero (sampledProjectorWordCount q L E₀ η m) :=
  ⟨Nat.succ_ne_zero _⟩

/-- The explicit multiplicity bound `κ = ⌈2m/n + 2 log (4 ℓ n⁴)⌉`. -/
noncomputable def sampledProjectorLetterBound (L ℓ m : ℕ) : ℕ :=
  ⌈2 * (m : ℝ) / L + 2 * Real.log (4 * ℓ * L ^ 4)⌉₊

/-- **Corollary `c:agsp`, existence form.** For every power `m` with
`m ≥ ((n - ε₀)/Δ) log (1/η)` there are `ℓ = sampledProjectorWordCount q n ε₀ η m` words of
length `m` such that `‖A - |Γ⟩⟨Γ|‖ ≤ η`, `‖K - A‖ < η`, every letter occurs at most
`κ = sampledProjectorLetterBound n ℓ m` times in every word, and hence every word `P_{I_k}` has
operator Schmidt rank at most `q^{2κ}` across every cut. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 584–588, 602–603 and 626–649. -/
theorem exists_sampledProjector [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) {η : ℝ} (hη : 0 < η) (m : ℕ)
    (hm : ((L - E₀) / Δ) * Real.log (1 / η) ≤ m) :
    ∃ I : Fin (sampledProjectorWordCount q L E₀ η m) → Fin m → Fin L,
      ‖powerProjector (∑ i, h i) L E₀ m - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
        η ∧
      ‖sampledProjector h E₀ I - powerProjector (∑ i, h i) L E₀ m‖ < η ∧
      (∀ k j, letterCount (I k) j ≤
        sampledProjectorLetterBound L (sampledProjectorWordCount q L E₀ η m) m) ∧
      ∀ k (b : Fin (L - 1)), Matrix.operatorSchmidtRank (Entropy.cutOperator
        (n := fun _ : Fin L ↦ q) (leftBlock L (b + 1)) (bondComplementWord h (I k))) ≤
        q ^ (2 * sampledProjectorLetterBound L (sampledProjectorWordCount q L E₀ η m) m) := by
  set ℓ := sampledProjectorWordCount q L E₀ η m
  set κ := sampledProjectorLetterBound L ℓ m
  have hprob := one_sub_le_measureReal_sampledProjector h h0 h1 hgs hΔ m hη (ℓ := ℓ) (κ := κ)
    ((Nat.le_ceil _).trans (by simp [ℓ, sampledProjectorWordCount]))
    (Nat.le_ceil _)
  have hpos : 0 < (sampleMeasure ℓ m L).real
      {I | ‖sampledProjector h E₀ I - powerProjector (∑ i, h i) L E₀ m‖ < η ∧
        ∀ k j, letterCount (I k) j ≤ κ} := by
    refine lt_of_lt_of_le ?_ hprob
    have : (1 : ℝ) ≤ (L : ℝ) ^ 3 :=
      one_le_pow₀ (Nat.one_le_cast.mpr (Nat.pos_of_neZero L))
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  obtain ⟨I, hK, hcount⟩ := nonempty_of_measureReal_ne_zero hpos.ne'
  refine ⟨I, norm_powerProjector_sub_le (Nat.pos_of_neZero L) h h0 h1 hgs hΔ hη m hm, hK,
    hcount, fun k b ↦ operatorSchmidtRank_cutOperator_bondComplementWord_le h hs b (I k) ?_⟩
  have hb : b.val < L := by omega
  refine le_of_eq_of_le ?_ (hcount k ⟨b, hb⟩)
  unfold letterCount
  congr 1

end TNLean.MPS.AreaLaw
