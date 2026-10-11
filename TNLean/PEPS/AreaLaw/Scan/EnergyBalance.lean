/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.EntropyBalance

/-!
# Energy at the selected charge point

At the selected point the energy estimate of Proposition 7.4 is bounded leaf by leaf: old good
leaves by Hölder's inequality against the charge defect, old bad leaves by the tail of
Lemma 9.1(4), and new leaves by their total weight `p ≤ ε`. The coefficient
`a² (D/m) KnD = W² n D²/(mK) ≤ C W² n^ℓ D²` contains no total-volume factor.

**Scope restriction (inputs as hypotheses):** the results of this module stated over `ScanData`
are proved from its fields, which record the conclusions of Lemma 9.1, Propositions 7.4
and 8.1, and Lemmas 2.1 and 2.3 for one scan rather than deriving them. Documented in
`docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.integral_rpow_le_of_holder`: Hölder for `η^{1/8}` against a finite
  measure.
* `TNLean.PEPS.AreaLaw.Scan.ScanData.energySum_le`: the leaf accounting.
* `TNLean.PEPS.AreaLaw.Scan.exists_defectEnergy_le`: `scanner:energy-output` from the selected
  density.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`, lines 492–528.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open MeasureTheory Set

/-- Hölder's inequality for the eighth root against a finite measure:
`∫ η^{1/8} dν ≤ ν(univ)^{7/8} (∫ η dν)^{1/8}` for bounded measurable `η ≥ 0`
(lines 497–501). -/
theorem integral_rpow_le_of_holder {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {η : Ω → ℝ} (hη : Measurable η) (hη0 : ∀ x, 0 ≤ η x) {B : ℝ}
    (hηB : ∀ x, η x ≤ B) :
    ∫ x, η x ^ (1 / 8 : ℝ) ∂ν ≤ ν.real univ ^ (7 / 8 : ℝ) * (∫ x, η x ∂ν) ^ (1 / 8 : ℝ) := by
  have hpq : (8 / 7 : ℝ).HolderConjugate 8 := by
    rw [Real.holderConjugate_iff]; exact ⟨by norm_num, by norm_num⟩
  have hgb : ∀ x, ‖η x ^ (1 / 8 : ℝ)‖ ≤ B ^ (1 / 8 : ℝ) := fun x ↦ by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hη0 x) _)]
    exact Real.rpow_le_rpow (hη0 x) (hηB x) (by norm_num)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) hpq (f := fun _ ↦ (1 : ℝ))
    (g := fun x ↦ η x ^ (1 / 8 : ℝ)) (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (Filter.Eventually.of_forall fun x ↦ Real.rpow_nonneg (hη0 x) _) (memLp_const 1)
    (MemLp.of_bound (hη.pow_const _).aestronglyMeasurable _ (Filter.Eventually.of_forall hgb))
  have hcongr : ∫ x, (η x ^ (1 / 8 : ℝ)) ^ (8 : ℝ) ∂ν = ∫ x, η x ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [← Real.rpow_mul (hη0 x)]
    norm_num
  simp only [one_mul, Real.one_rpow, integral_const, smul_eq_mul, mul_one, hcongr] at h
  convert h using 2; norm_num

/-- The eighth-root integral of a function bounded by `E` against a measure of mass `1/2`. -/
lemma integral_rpow_le_half {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] (hν : ν.real univ = 1 / 2) {η : Ω → ℝ} (hη0 : ∀ x, 0 ≤ η x) {E : ℝ}
    (hηE : ∀ x, η x ≤ E) :
    ∫ x, η x ^ (1 / 8 : ℝ) ∂ν ≤ E ^ (1 / 8 : ℝ) / 2 := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x ↦ η x ^ (1 / 8 : ℝ))
    (C := E ^ (1 / 8 : ℝ)) (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hη0 x) _)]
      exact Real.rpow_le_rpow (hη0 x) (hηE x) (by norm_num))
  rw [hν] at h
  linarith [le_abs_self (∫ x, η x ^ (1 / 8 : ℝ) ∂ν), Real.norm_eq_abs (∫ x, η x ^ (1 / 8 : ℝ) ∂ν)]

/-- Pulling a common factor out of a filtered sum. -/
lemma sum_ite_mul_eq {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] (a : ℝ)
    (f : ι → ℝ) :
    ∑ i, (if P i then a * f i else 0) = a * ∑ i, (if P i then f i else 0) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp

/-- A filtered sum of terms `a f i` with `f ≤ b` on at most `N` indices. -/
lemma sum_ite_mul_le {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] {a : ℝ}
    (ha : 0 ≤ a) (f : ι → ℝ) {b N : ℝ} (hb : 0 ≤ b) (hf : ∀ i, P i → f i ≤ b)
    (hcard : ((Finset.univ.filter P).card : ℝ) ≤ N) :
    ∑ i, (if P i then a * f i else 0) ≤ a * (N * b) := by
  rw [sum_ite_mul_eq]
  refine mul_le_mul_of_nonneg_left ?_ ha
  rw [← Finset.sum_filter]
  calc ∑ i ∈ Finset.univ.filter P, f i ≤ ∑ _i ∈ Finset.univ.filter P, b :=
        Finset.sum_le_sum fun i hi ↦ hf i (Finset.mem_filter.1 hi).2
    _ = (Finset.univ.filter P).card * b := by simp
    _ ≤ N * b := mul_le_mul_of_nonneg_right hcard hb

namespace ScanData

variable {X : ScannerExponents} {κ : ScanConstants} {n : ℕ} (S : ScanData X κ n)

/-- Old-leaf eighth-root integrals are nonnegative. -/
lemma integral_etaOld_rpow_nonneg (r : Fin (X.rounds n)) (k : ℕ) (p : ℝ) (i : S.ι)
    (h : (S.round r).H) :
    0 ≤ ∫ θ, (S.round r).etaOld i h θ ^ (1 / 8 : ℝ) ∂((S.round r).μOld k p h) :=
  integral_nonneg fun θ ↦ Real.rpow_nonneg (S.etaOld_nonneg r i h θ) _

/-- New-leaf eighth-root integrals are nonnegative. -/
lemma integral_etaNew_rpow_nonneg (r : Fin (X.rounds n)) (k : ℕ) (p : ℝ) (i : S.ι)
    (h : (S.round r).H) (c : (S.round r).Ch h) :
    0 ≤ ∫ θ, (S.round r).etaNew i h c θ ^ (1 / 8 : ℝ) ∂((S.round r).μNew k p h c) :=
  integral_nonneg fun θ ↦ Real.rpow_nonneg (S.etaNew_nonneg r i h c θ) _

open Classical in
/-- The leaf sum of one term is nonnegative for `p ∈ (0, 1)`. -/
lemma termEnergy_nonneg (r : Fin (X.rounds n)) (k : ℕ) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (i : S.ι) : 0 ≤ (S.round r).termEnergy k p i := by
  unfold ScanRound.termEnergy
  refine add_nonneg (Finset.sum_nonneg fun h _ ↦ ?_)
    (Finset.sum_nonneg fun h _ ↦ Finset.sum_nonneg fun c _ ↦ ?_)
  · split_ifs
    · exact mul_nonneg (mul_nonneg (by linarith [hp.2]) (S.w_nonneg r h))
        (S.integral_etaOld_rpow_nonneg r k p i h)
    · exact le_rfl
  · split_ifs
    · exact mul_nonneg (mul_nonneg (mul_nonneg hp.1.le (S.w_nonneg r h)) (S.q_nonneg r h c))
        (S.integral_etaNew_rpow_nonneg r k p i h c)
    · exact le_rfl

open Classical in
/-- Old good leaves: Hölder's inequality over histories, split terms and `θ` at an interior
interpolation parameter (`08-scanner.tex`, lines 495–501). -/
lemma goodOld_le (r : Fin (X.rounds n)) (k : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {N : ℝ} (hN : 0 < N)
    (hcard : ∀ h, ((Finset.univ.filter fun i ↦ (S.round r).splitOld i h).card : ℝ) ≤ N) :
    (∑ h, if (S.round r).good h then (S.round r).w h * ∑ i,
        (if (S.round r).splitOld i h then
          ∫ θ, (S.round r).etaOld i h θ ^ (1 / 8 : ℝ) ∂((S.round r).μOld k p h) else 0)
      else 0) ≤ N * ((S.round r).chargeDefect k p / N) ^ (1 / 8 : ℝ) := by
  set R := S.round r
  have := S.isFiniteMeasure_μOld r k p
  let J : R.H × S.ι → ℝ := fun x ↦ ∫ θ, R.etaOld x.2 x.1 θ ^ (1 / 8 : ℝ) ∂(R.μOld k p x.1)
  let I : R.H × S.ι → ℝ := fun x ↦ ∫ θ, R.etaOld x.2 x.1 θ ∂(R.μOld k p x.1)
  let c : R.H × S.ι → ℝ := fun x ↦ if R.good x.1 ∧ R.splitOld x.2 x.1 then R.w x.1 else 0
  have hc0 : ∀ x, 0 ≤ c x := fun x ↦ by
    simp only [c]; split_ifs
    · exact S.w_nonneg r x.1
    · exact le_rfl
  have hJ0 : ∀ x, 0 ≤ J x := fun x ↦ S.integral_etaOld_rpow_nonneg r k p x.2 x.1
  have hI0 : ∀ x, 0 ≤ I x := fun x ↦ integral_nonneg fun θ ↦ S.etaOld_nonneg r x.2 x.1 θ
  -- Each `J ≤ I^{1/8}`, by Hölder against the mass `1/2`.
  have hJI : ∀ x, J x ≤ I x ^ (1 / 8 : ℝ) := fun x ↦ by
    have h := integral_rpow_le_of_holder (R.μOld k p x.1) (S.measurable_etaOld r x.2 x.1)
      (S.etaOld_nonneg r x.2 x.1) (S.etaOld_le r x.2 x.1)
    rw [S.μOld_real_univ r k p hp x.1] at h
    have h1 : (1 / 2 : ℝ) ^ (7 / 8 : ℝ) ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num)
      (by norm_num)
    calc J x ≤ _ := h
      _ ≤ 1 * I x ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hI0 x) _)
      _ = _ := one_mul _
  have hJ8 : ∀ x, J x ^ (8 : ℝ) ≤ I x := fun x ↦ by
    calc J x ^ (8 : ℝ) ≤ (I x ^ (1 / 8 : ℝ)) ^ (8 : ℝ) :=
          Real.rpow_le_rpow (hJ0 x) (hJI x) (by norm_num)
      _ = I x := by rw [← Real.rpow_mul (hI0 x)]; norm_num
  have hH := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ (p := 8) (by norm_num) c J hc0
    hJ0
  -- Identify the three sums.
  have hsplit : ∀ f : R.H × S.ι → ℝ, ∑ x, c x * f x =
      ∑ h, if R.good h then R.w h * ∑ i, (if R.splitOld i h then f (h, i) else 0) else 0 := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    by_cases hg : R.good h
    · simp only [hg, ↓reduceIte, true_and, c, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp
    · simp [hg, c]
  have hsumc : ∑ x, c x ≤ N := by
    have := hsplit fun _ ↦ 1
    simp only [mul_one] at this
    rw [this]
    calc (∑ h, if R.good h then R.w h * ∑ i, (if R.splitOld i h then (1 : ℝ) else 0) else 0)
        ≤ ∑ h, R.w h * N := Finset.sum_le_sum fun h _ ↦ by
          split_ifs
          · refine mul_le_mul_of_nonneg_left ?_ (S.w_nonneg r h)
            rw [Finset.sum_boole]; exact hcard h
          · exact mul_nonneg (S.w_nonneg r h) hN.le
      _ = N := by rw [← Finset.sum_mul, S.sum_w r, one_mul]
  have hQ : ∑ x, c x * J x ^ (8 : ℝ) ≤ R.chargeDefect k p := by
    calc ∑ x, c x * J x ^ (8 : ℝ) ≤ ∑ x, c x * I x :=
          Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hJ8 x) (hc0 x)
      _ = R.chargeDefect k p := by rw [hsplit]; rfl
  have hQ0 := S.chargeDefect_nonneg r k p
  have hlhs := hsplit J
  rw [hlhs] at hH
  refine hH.trans ?_
  have e1 : (1 - (8 : ℝ)⁻¹) = 7 / 8 := by norm_num
  have e2 : ((8 : ℝ)⁻¹) = 1 / 8 := by norm_num
  rw [e1, e2]
  have hsc0 : 0 ≤ ∑ x, c x := Finset.sum_nonneg fun x _ ↦ hc0 x
  have hcJ0 : 0 ≤ ∑ x, c x * J x ^ (8 : ℝ) :=
    Finset.sum_nonneg fun x _ ↦ mul_nonneg (hc0 x) (Real.rpow_nonneg (hJ0 x) _)
  calc (∑ x, c x) ^ (7 / 8 : ℝ) * (∑ x, c x * J x ^ (8 : ℝ)) ^ (1 / 8 : ℝ)
      ≤ N ^ (7 / 8 : ℝ) * (R.chargeDefect k p) ^ (1 / 8 : ℝ) :=
        mul_le_mul (Real.rpow_le_rpow hsc0 hsumc (by norm_num))
          (Real.rpow_le_rpow hcJ0 hQ (by norm_num)) (Real.rpow_nonneg hcJ0 _)
          (Real.rpow_nonneg hN.le _)
    _ = N * (R.chargeDefect k p / N) ^ (1 / 8 : ℝ) := by
      rw [Real.div_rpow hQ0 hN.le]
      have hN8 : 0 < N ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hN _
      have : N = N ^ (7 / 8 : ℝ) * N ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_add hN]; norm_num
      calc N ^ (7 / 8 : ℝ) * R.chargeDefect k p ^ (1 / 8 : ℝ)
          = N ^ (7 / 8 : ℝ) * N ^ (1 / 8 : ℝ) *
              (R.chargeDefect k p ^ (1 / 8 : ℝ) / N ^ (1 / 8 : ℝ)) := by
            field_simp
        _ = _ := by rw [← this]

open Classical in
/-- Leaf accounting for the energy sum of Proposition 7.4 (lines 492–507): with `N = CKnD`
split occurrences per leaf, split weights `≤ CD/m`, move entropies `≤ η_max = C (log n)^{C_l}`,
bad weight `≤ n^{-200}` and new-leaf weight `p`,
`energySum ≤ (CD/m) N ((𝒬/N)^{1/8} + η_max^{1/8} (n^{-200} + p))`. -/
theorem energySum_le {C₁ : ℝ} (hn : ScaleFacts X n C₁) (r : Fin (X.rounds n)) (k : ℕ)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    (S.round r).energySum k p ≤
      κ.C * X.D n / X.m n * (κ.C * X.K n * n * X.D n) *
        (((S.round r).chargeDefect k p / (κ.C * X.K n * n * X.D n)) ^ (1 / 8 : ℝ) +
          (κ.C * Real.log n ^ κ.Cl) ^ (1 / 8 : ℝ) * ((n : ℝ) ^ (-200 : ℝ) + p)) := by
  set R := S.round r
  set N : ℝ := κ.C * X.K n * n * X.D n with hNdef
  set E : ℝ := κ.C * Real.log n ^ κ.Cl with hEdef
  have hC : (1 : ℝ) ≤ κ.C := κ.one_le_C
  have hK : (1 : ℝ) ≤ X.K n := by exact_mod_cast hn.one_le_K
  have hD : (1 : ℝ) ≤ X.D n := by exact_mod_cast hn.one_le_D
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le_n
  have hN : 0 < N := by positivity
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := mul_nonneg (by linarith) (Real.rpow_nonneg hlog _)
  have hE8 : 0 ≤ E ^ (1 / 8 : ℝ) := Real.rpow_nonneg hE0 _
  have hb : 0 ≤ E ^ (1 / 8 : ℝ) / 2 := by positivity
  have hm : (0 : ℝ) < X.m n := by exact_mod_cast hn.one_le_m
  have hW0 : 0 ≤ κ.C * X.D n / X.m n := by positivity
  -- Split weights.
  have step1 : R.energySum k p ≤ κ.C * X.D n / X.m n * ∑ i, R.termEnergy k p i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right
      (S.splitWeight_le r p hp i) (S.termEnergy_nonneg r k hp i)
  refine step1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hW0
  unfold ScanRound.termEnergy
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  -- New leaves.
  have hnew : (∑ i, ∑ h, ∑ c, if R.splitNew i h c then
      p * R.w h * R.q h c *
        ∫ θ, R.etaNew i h c θ ^ (1 / 8 : ℝ) ∂(R.μNew k p h c) else 0) ≤
      p * (N * (E ^ (1 / 8 : ℝ) / 2)) := by
    rw [Finset.sum_comm]
    calc _ = ∑ h, ∑ c, ∑ i, (if R.splitNew i h c then
          p * R.w h * R.q h c *
            ∫ θ, R.etaNew i h c θ ^ (1 / 8 : ℝ) ∂(R.μNew k p h c) else 0) :=
          Finset.sum_congr rfl fun h _ ↦ Finset.sum_comm
      _ ≤ ∑ h, ∑ c, p * R.w h * R.q h c * (N * (E ^ (1 / 8 : ℝ) / 2)) :=
          Finset.sum_le_sum fun h _ ↦ Finset.sum_le_sum fun c _ ↦ by
            have := S.isFiniteMeasure_μNew r k p h c
            exact sum_ite_mul_le _ (mul_nonneg (mul_nonneg hp.1.le (S.w_nonneg r h))
              (S.q_nonneg r h c)) _ hb
              (fun i _ ↦ integral_rpow_le_half _ (S.μNew_real_univ r k p hp h c)
                (S.etaNew_nonneg r i h c) (S.etaNew_le r i h c))
              (S.card_splitNew_le r h c)
      _ = ∑ h, p * (N * (E ^ (1 / 8 : ℝ) / 2)) * R.w h * ∑ c, R.q h c :=
          Finset.sum_congr rfl fun h _ ↦ by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ ↦ by ring
      _ = ∑ h, p * (N * (E ^ (1 / 8 : ℝ) / 2)) * R.w h :=
          Finset.sum_congr rfl fun h _ ↦ by rw [S.sum_q r h, mul_one]
      _ = p * (N * (E ^ (1 / 8 : ℝ) / 2)) := by rw [← Finset.mul_sum, S.sum_w r, mul_one]
  -- Old leaves, history by history.
  have hold : ∀ h, (∑ i, if R.splitOld i h then
      (1 - p) * R.w h * ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) else 0) ≤
      (if R.good h then R.w h * ∑ i,
        (if R.splitOld i h then ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) else 0)
        else 0) + (if R.good h then 0 else R.w h * (N * (E ^ (1 / 8 : ℝ) / 2))) := by
    intro h
    have := S.isFiniteMeasure_μOld r k p h
    have hw := S.w_nonneg r h
    by_cases hg : R.good h
    · simp only [hg, ↓reduceIte, add_zero]
      rw [sum_ite_mul_eq]
      have hX : 0 ≤ ∑ i, (if R.splitOld i h then
          ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) else 0) :=
        Finset.sum_nonneg fun i _ ↦ by
          split_ifs
          · exact S.integral_etaOld_rpow_nonneg r k p i h
          · exact le_rfl
      exact mul_le_mul_of_nonneg_right (by nlinarith [hp.1]) hX
    · simp only [hg, ↓reduceIte, zero_add]
      calc _ ≤ (1 - p) * R.w h * (N * (E ^ (1 / 8 : ℝ) / 2)) :=
            sum_ite_mul_le _ (mul_nonneg (by linarith [hp.2]) hw) _ hb
              (fun i _ ↦ integral_rpow_le_half _ (S.μOld_real_univ r k p hp h)
                (S.etaOld_nonneg r i h) (S.etaOld_le r i h))
              (S.card_splitOld_le r h)
        _ ≤ R.w h * (N * (E ^ (1 / 8 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hp.1]) (by positivity)
  have hgood := S.goodOld_le r k p hp hN (S.card_splitOld_le r)
  have hbad : (∑ h, if R.good h then (0 : ℝ) else R.w h * (N * (E ^ (1 / 8 : ℝ) / 2))) ≤
      (n : ℝ) ^ (-200 : ℝ) * (N * (E ^ (1 / 8 : ℝ) / 2)) := by
    have : (∑ h, if R.good h then (0 : ℝ) else R.w h * (N * (E ^ (1 / 8 : ℝ) / 2))) =
        R.badWeight * (N * (E ^ (1 / 8 : ℝ) / 2)) := by
      unfold ScanRound.badWeight
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun h _ ↦ by split_ifs <;> simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (S.badWeight_le r) (by positivity)
  have holdsum := Finset.sum_le_sum fun h (_ : h ∈ Finset.univ) ↦ hold h
  rw [Finset.sum_add_distrib] at holdsum
  have hp0 := hp.1.le
  have hn0 : 0 ≤ (n : ℝ) ^ (-200 : ℝ) := Real.rpow_nonneg (by linarith) _
  nlinarith [mul_nonneg hn0 (mul_nonneg hN.le hE8), mul_nonneg hp0 (mul_nonneg hN.le hE8)]

end ScanData

/-- The defect-energy bound `scanner:energy-output` at a point satisfying the selected density
bound (lines 492–533). For fixed constants, uniformly in the scan data at every sufficiently
large `n`, a point `p ∈ [ε/2, ε]` with `𝒬(p)/(KnD) ≤ δ_n + ρ` has
`E_def ≤ C n^ℓ D² W² (log n)^{C_l} (δ_n^{1/8} + ε + n^{-100}) + C n^{-1000} + Λ (rem_k + ρ^{1/8})`
with `Λ` depending on the fixed data only. -/
theorem exists_defectEnergy_le (X : ScannerExponents) (κ : ScanConstants) (C₁ Cδ : ℝ)
    (hCδ : 0 ≤ Cδ) :
    ∃ C Cl : ℝ, ∀ᶠ n in Filter.atTop, ScaleFacts X n C₁ → ∀ S : ScanData X κ n,
      ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (r : Fin (X.rounds n)) (k : ℕ) (p ρ : ℝ),
        p ∈ Icc (X.eps n / 2) (X.eps n) → 0 ≤ ρ →
        (S.round r).chargeDefect k p / (X.K n * n * X.D n) ≤ X.delta S.W Cδ κ.Cl n + ρ →
        S.defectEnergy r k p ≤
          C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * S.W ^ 2 * Real.log n ^ Cl *
              (X.delta S.W Cδ κ.Cl n ^ (1 / 8 : ℝ) + X.eps n + (n : ℝ) ^ (-100 : ℝ)) +
            C * (n : ℝ) ^ (-1000 : ℝ) + Λ * (S.rem k + ρ ^ (1 / 8 : ℝ)) := by
  refine ⟨2 / κ.g * (κ.C ^ 4 * C₁ + 1), κ.Cl + κ.Cl / 8, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn3 hS S
  have hC : (1 : ℝ) ≤ κ.C := κ.one_le_C
  have hCl := κ.Cl_nonneg
  have hC₁ := hS.one_le_C₁
  have hK : (1 : ℝ) ≤ X.K n := by exact_mod_cast hS.one_le_K
  have hD : (1 : ℝ) ≤ X.D n := by exact_mod_cast hS.one_le_D
  have hm : (1 : ℝ) ≤ X.m n := by exact_mod_cast hS.one_le_m
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hg := κ.g_pos
  have hgap : κ.g / 2 ≤ S.gap := S.half_g_le_gap
  have hgap0 : 0 < S.gap := by linarith
  have hε := hS.eps_pos
  have hε1 := hS.eps_lt_one
  have ha0 : 0 ≤ X.a S.W n := div_nonneg (by linarith [S.one_le_W]) (by linarith)
  have hδ : 0 ≤ X.delta S.W Cδ κ.Cl n := by
    unfold ScannerExponents.delta
    have : 0 ≤ Real.log n ^ κ.Cl := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ X.a S.W n ^ (1 / 4 : ℝ) := Real.rpow_nonneg ha0 _
    have : 0 ≤ (n : ℝ) ^ (X.e - X.mu) := Real.rpow_nonneg (by linarith) _
    positivity
  set N : ℝ := κ.C * X.K n * n * X.D n with hNdef
  have hN : 0 < N := by positivity
  set L0 : ℝ := Real.log n ^ κ.Cl with hL0def
  have hL0 : 0 ≤ L0 := Real.rpow_nonneg (by linarith) _
  set coef : ℝ := κ.C * X.a S.W n ^ 2 * L0 * (κ.C * X.D n / X.m n * N) with hcoef
  have hcoef0 : 0 ≤ coef := by positivity
  refine ⟨(coef + 1) / S.gap, by positivity, ?_⟩
  intro r k p ρ hp hρ hQ
  have hp' : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hsum := S.energySum_le hS r k hp'
  have hen := S.energy r k p hp'
  set δ := X.delta S.W Cδ κ.Cl n with hδdef
  set Q := (S.round r).chargeDefect k p with hQdef
  have hQ0 : 0 ≤ Q := S.chargeDefect_nonneg r k p
  -- The selected density at the scale `N = CKnD`.
  have hQN : Q / N ≤ δ + ρ := by
    have e : Q / N = Q / (X.K n * n * X.D n) / κ.C := by
      rw [hNdef, div_div]; ring_nf
    rw [e]
    exact (div_le_self (by positivity) hC).trans hQ
  have h8 : (Q / N) ^ (1 / 8 : ℝ) ≤ δ ^ (1 / 8 : ℝ) + ρ ^ (1 / 8 : ℝ) :=
    (Real.rpow_le_rpow (div_nonneg hQ0 hN.le) hQN (by norm_num)).trans
      (Real.rpow_add_le_add_rpow hδ hρ (by norm_num) (by norm_num))
  set E8 : ℝ := (κ.C * L0) ^ (1 / 8 : ℝ) with hE8def
  have hE8 : 0 ≤ E8 := Real.rpow_nonneg (by positivity) _
  set M : ℝ := δ ^ (1 / 8 : ℝ) + E8 * ((n : ℝ) ^ (-200 : ℝ) + p) with hMdef
  have hn200 : 0 ≤ (n : ℝ) ^ (-200 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hδ8 : 0 ≤ δ ^ (1 / 8 : ℝ) := Real.rpow_nonneg hδ _
  have hρ8 : 0 ≤ ρ ^ (1 / 8 : ℝ) := Real.rpow_nonneg hρ _
  have hM0 : 0 ≤ M := add_nonneg hδ8 (mul_nonneg hE8 (add_nonneg hn200 hp'.1.le))
  -- The energy estimate at the selected point.
  have hkey : (S.round r).meanEnergy k p - S.E0 ≤
      S.E0 + coef * M + (coef * ρ ^ (1 / 8 : ℝ) + S.rem k) := by
    have h1 : κ.C * X.a S.W n ^ 2 * L0 * (S.round r).energySum k p ≤
        κ.C * X.a S.W n ^ 2 * L0 * (κ.C * X.D n / X.m n * N * (M + ρ ^ (1 / 8 : ℝ))) := by
      refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hMdef]; linarith
    have h2 : κ.C * X.a S.W n ^ 2 * L0 * (κ.C * X.D n / X.m n * N * (M + ρ ^ (1 / 8 : ℝ))) =
        coef * M + coef * ρ ^ (1 / 8 : ℝ) := by rw [hcoef]; ring
    linarith
  -- The coefficient carries no total-volume factor (lines 516–520).
  set P : ℝ := (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * S.W ^ 2 with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hcoefle : coef ≤ κ.C ^ 3 * C₁ * P * L0 := by
    have e : coef = κ.C ^ 3 * L0 * (S.W ^ 2 * (n * (X.D n : ℝ) ^ 2 / (X.m n * X.K n))) := by
      rw [hcoef, hNdef]
      unfold ScannerExponents.a
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hS.coefficient_le (sq_nonneg S.W)
    calc κ.C ^ 3 * L0 * (S.W ^ 2 * (n * (X.D n : ℝ) ^ 2 / (X.m n * X.K n)))
        ≤ κ.C ^ 3 * L0 * (S.W ^ 2 * (C₁ * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = κ.C ^ 3 * C₁ * P * L0 := by rw [hPdef]; ring
  -- The logarithmic factors.
  set Lc : ℝ := Real.log n ^ (κ.Cl + κ.Cl / 8) with hLcdef
  have hLc0 : 0 ≤ Lc := Real.rpow_nonneg (by linarith) _
  have hL0Lc : L0 ≤ Lc := Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
  have hL0E8 : L0 * E8 = κ.C ^ (1 / 8 : ℝ) * Lc := by
    rw [hE8def, Real.mul_rpow (by linarith) hL0, hL0def, ← Real.rpow_mul (by linarith), hLcdef,
      Real.rpow_add (by linarith)]
    ring_nf
  have hC8 : κ.C ^ (1 / 8 : ℝ) ≤ κ.C := by
    simpa using Real.rpow_le_rpow_of_exponent_le hC (show (1 / 8 : ℝ) ≤ 1 by norm_num)
  have hn1 : (n : ℝ) ^ (-200 : ℝ) ≤ (n : ℝ) ^ (-100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  set T : ℝ := δ ^ (1 / 8 : ℝ) + X.eps n + (n : ℝ) ^ (-100 : ℝ) with hTdef
  have hn100 : 0 ≤ (n : ℝ) ^ (-100 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hLM : L0 * M ≤ κ.C * Lc * T := by
    have hpe : (n : ℝ) ^ (-200 : ℝ) + p ≤ (n : ℝ) ^ (-100 : ℝ) + X.eps n := by
      linarith [hp.2]
    have e : L0 * M = L0 * δ ^ (1 / 8 : ℝ) +
        κ.C ^ (1 / 8 : ℝ) * Lc * ((n : ℝ) ^ (-200 : ℝ) + p) := by
      rw [hMdef, ← hL0E8]; ring
    rw [e, hTdef]
    have t1 : L0 * δ ^ (1 / 8 : ℝ) ≤ κ.C * Lc * δ ^ (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right (hL0Lc.trans (le_mul_of_one_le_left hLc0 hC)) hδ8
    have t2 : κ.C ^ (1 / 8 : ℝ) * Lc * ((n : ℝ) ^ (-200 : ℝ) + p) ≤
        κ.C * Lc * ((n : ℝ) ^ (-100 : ℝ) + X.eps n) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hC8 hLc0) hpe (add_nonneg hn200 hp'.1.le)
        (mul_nonneg (by linarith) hLc0)
    linarith
  have hcoefM : coef * M ≤ κ.C ^ 4 * C₁ * (P * Lc * T) := by
    calc coef * M ≤ κ.C ^ 3 * C₁ * P * L0 * M := mul_le_mul_of_nonneg_right hcoefle hM0
      _ = κ.C ^ 3 * C₁ * P * (L0 * M) := by ring
      _ ≤ κ.C ^ 3 * C₁ * P * (κ.C * Lc * T) :=
          mul_le_mul_of_nonneg_left hLM (by positivity)
      _ = κ.C ^ 4 * C₁ * (P * Lc * T) := by ring
  -- Divide by the gap.
  have hT0 : 0 ≤ T := by positivity
  have hPLT : 0 ≤ P * Lc * T := by positivity
  have hX : κ.C ^ 4 * C₁ + 1 ≤ 2 / κ.g * (κ.C ^ 4 * C₁ + 1) * S.gap := by
    have hX0 : 0 ≤ κ.C ^ 4 * C₁ + 1 := by positivity
    calc κ.C ^ 4 * C₁ + 1 = 2 / κ.g * (κ.C ^ 4 * C₁ + 1) * (κ.g / 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
  unfold ScanData.defectEnergy
  rw [div_le_iff₀ hgap0]
  have hE0 := S.E0_le
  have hrem := S.rem_nonneg k
  have hΛ : (coef + 1) / S.gap * (S.rem k + ρ ^ (1 / 8 : ℝ)) * S.gap =
      (coef + 1) * (S.rem k + ρ ^ (1 / 8 : ℝ)) := by field_simp
  have hn1000 : 0 ≤ (n : ℝ) ^ (-1000 : ℝ) := Real.rpow_nonneg (by linarith) _
  have e1 : 2 / κ.g * (κ.C ^ 4 * C₁ + 1) * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * S.W ^ 2 * Lc * T
      = 2 / κ.g * (κ.C ^ 4 * C₁ + 1) * (P * Lc * T) := by rw [hPdef]; ring
  rw [e1, add_mul, add_mul, hΛ]
  have hC4 : 0 ≤ κ.C ^ 4 * C₁ := by positivity
  linarith [mul_le_mul_of_nonneg_right hX hPLT, mul_le_mul_of_nonneg_right hX hn1000,
    mul_nonneg hcoef0 hrem, mul_nonneg hC4 hPLT, mul_nonneg hC4 hn1000]

end TNLean.PEPS.AreaLaw.Scan
