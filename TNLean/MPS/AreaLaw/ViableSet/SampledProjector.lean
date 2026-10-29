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

Draft.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-! ### The probability space of sampled words -/

/-- The uniform law of a word of length `m` in the letters `Fin L`: its letters are independent
and uniform. -/
noncomputable def wordMeasure (m L : ℕ) : Measure (Fin m → Fin L) :=
  Measure.pi fun _ ↦ uniformOn Set.univ

/-- The law of `ℓ` independent uniform words of length `m`. -/
noncomputable def sampleMeasure (ℓ m L : ℕ) : Measure (Fin ℓ → Fin m → Fin L) :=
  Measure.pi fun _ ↦ wordMeasure m L

instance (m L : ℕ) [NeZero L] : IsProbabilityMeasure (wordMeasure m L) := by
  unfold wordMeasure
  infer_instance

instance (ℓ m L : ℕ) [NeZero L] : IsProbabilityMeasure (sampleMeasure ℓ m L) := by
  unfold sampleMeasure
  infer_instance

theorem measureReal_wordMeasure_singleton (m L : ℕ) [NeZero L] (I : Fin m → Fin L) :
    (wordMeasure m L).real {I} = ((L : ℝ) ^ m)⁻¹ := by
  have hI : ({I} : Set (Fin m → Fin L)) = Set.univ.pi fun p ↦ {I p} := by
    ext J
    simp [funext_iff]
  rw [measureReal_def, hI, wordMeasure, Measure.pi_pi]
  simp [uniformOn_univ]


/-! ### The sampled projector -/

/-- The normalization `C = (1 - ε₀/n)⁻¹` of the power projector. -/
noncomputable def powerNormalization (L : ℕ) (E₀ : ℝ) : ℝ :=
  (1 - E₀ / L)⁻¹

/-- One sampled term `C^m P_I`. -/
noncomputable def scaledBondComplementWord
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {m : ℕ}
    (I : Fin m → Fin L) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  powerNormalization L E₀ ^ m • bondComplementWord h I

/-- The sampled projector `K = C^m ℓ⁻¹ ∑_j P_{I_j}`. -/
noncomputable def sampledProjector
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  powerNormalization L E₀ ^ m • ((ℓ : ℝ)⁻¹ • ∑ k, bondComplementWord h (I k))

theorem sampledProjector_eq_average
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) :
    sampledProjector h E₀ I = (ℓ : ℝ)⁻¹ • ∑ k, scaledBondComplementWord h E₀ (I k) := by
  simp only [sampledProjector, scaledBondComplementWord, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- The ground energy lies between `0` and `n - 1`. -/
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

/-- A letter `P_i = 1 - H_i` is a contraction. -/
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

/-- A word `P_I` in the letters is a contraction. -/
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

/-- With `0 ≤ ε₀ < n`, the normalization `C` is at least one. -/
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

end TNLean.MPS.AreaLaw
