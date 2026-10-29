/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledPowerRank
import TNLean.MPS.AreaLaw.ViableSet.CutDecomposition
import TNLean.MPS.AreaLaw.ViableSet.ErrorReduction
import QICLean.Analysis.PowerSamplingNormalization

/-!
# Scalar-free normalized-power sampling from a known energy interval

Fix a known bracket `[a, a + 1]` with `0 ≤ a ≤ n - 1`. The word length
`m = ⌈(n - a) / Δ * log Q⌉₊` and the explicit sample count are chosen from
this bracket, before every actual ground energy and ground vector. The
normalization estimate uses `Emax = min (a + 1) (n - 1)` and
`Cmax = (1 - Emax / n)⁻¹`, with cost at most
`n² * exp (4 * (a + 1) * log Q / Δ)`.

The operator actually constructed is the unscaled mean of sampled complement
words. Its approximation to the actual unscaled power, letter counts and
all-cut operator Schmidt ranks are proved first. For every later choice of a
unit ground vector at energy `E0 ∈ [a, a + 1]` with the original lower gap,
put `β = (1 - E0 / n)^m`. Then `β > 0` and the same operator obeys the relative
projection estimate `‖T - β P‖ < β * (η + 1 / Q)`.

At each cut, the product factors of `T` are chosen before all such ground data
and all viable input families. When `η + 1 / Q < 1/2`, their actual images
have viability error `4 * (η + 1 / Q)`, with the derived cardinality and MPS
bond bounds. The proof reuses the checked QICLean power, ordered-word and
concentration theorems and the chain rank estimates.

**Scope restriction (known energy interval):** this theorem takes a width-one
bracket as data. It does not choose that bracket, implement trial-energy
selection, instantiate the source's high success probability, or prove an
energy-independent polynomial running time. The
source boundary is recorded in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`.

Source: LVV, arXiv:1307.5143v1, `algo53.tex`, lines 599--614, and the published
Methods, Proposition 1 and the unknown-normalization remark, author PDF p. 6:
https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf. Scalar normalization
is unnecessary for normalized output vectors; the word and sample budgets
still require the bracket assumed here.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

namespace TNLean.MPS.AreaLaw

/-- A scalar-free sample with parameters chosen from a known width-one energy bracket.
The sample and its cut factors precede all bracketed ground energies and vectors.
LVV, published Methods, Proposition 1, p. 6, and its unknown-normalization remark. -/
theorem exists_interval_sampled_nn_power
    {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (h i) (interval L i.val (i.val + 2)))
    (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {a Δ Q η : ℝ} (ha : 0 ≤ a) (haN : a ≤ Fintype.card (Fin (L - 1)))
    (hΔ : 0 < Δ) (hQ : 1 ≤ Q) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) (hpD : 2 * (q : ℝ) ^ L < (4 : ℝ) ^ p) :
    let n := Fintype.card (Fin (L - 1)) + 1
    let Emax := min (a + 1) ((n : ℝ) - 1)
    let Cmax := (1 - Emax / n)⁻¹
    let m := ⌈((n : ℝ) - a) / Δ * Real.log Q⌉₊
    let S := (n : ℝ) ^ 2 * Real.exp (4 * (a + 1) * Real.log Q / Δ)
    let ℓ := ⌈16 * (p : ℝ) ^ 2 * S / η ^ 2⌉₊ + 1
    let u := ⌈((m : ℝ) / n + Real.log (2 * (n : ℝ) * ℓ)) / Real.log 2⌉₊
    let r := ℓ * q ^ (2 * u)
    0 < ℓ ∧ ∃ σ : Fin ℓ → Fin m → Option (Fin (L - 1)),
      let T := (ℓ : ℂ)⁻¹ • ∑ b, (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod
      ‖T - (1 - (Fintype.card (Fin (L - 1)) + 1 : ℂ)⁻¹ • ∑ i, h i) ^ m‖ < η / Cmax ^ m ∧
      (∀ b c, WordMultiplicity.countsFinsupp (σ b) c < u) ∧
      (∀ k : ℕ, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) T) ≤ r) ∧
      (∀ (E0 : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)), a ≤ E0 → E0 ≤ a + 1 →
        ‖Ω‖ = 1 → (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω →
        ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
          (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
        let β := (1 - E0 / n) ^ m
        0 < β ∧ ‖T - (β : ℂ) • vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ <
          β * (η + 1 / Q)) ∧
      ∀ i : ℕ, i ≤ L → ∃ (t : ℕ) (A : Fin t → LeftBlockMatrix L q i)
        (B : Fin t → RightBlockMatrix L q i),
        t ≤ r ∧ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) T =
          ∑ j, A j ⊗ₖ B j ∧
        (∀ j k, 0 < k → k < i → operatorSchmidtRank
          (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
            ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ r) ∧
        ∀ (E0 : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)), a ≤ E0 → E0 ≤ a + 1 →
          ‖Ω‖ = 1 → (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω →
          ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
            (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
          η + 1 / Q < 1 / 2 → ∀ (s b : ℕ) (V : Finset (LeftBlockVector L q i)),
          IsViableMPS Ω s b (1 / 2) V →
          IsViableMPS Ω (t * s) (r * max 1 b) (4 * (η + 1 / Q))
            (errorReductionSet Finset.univ A V) := by
  classical
  intro n Emax Cmax m S ℓ u r
  let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, by omega⟩⟩
  have hn : (0 : ℝ) < n := by dsimp only [n]; positivity
  have haN' : a ≤ (n : ℝ) - 1 := by
    simpa only [n, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using haN
  obtain ⟨hC1, _, hCost⟩ := Real.power_sampling_interval_normalization_pow_ceil_le ha haN' hΔ hQ
  change 1 ≤ Cmax at hC1
  change Cmax ^ (2 * m) ≤ S at hCost
  have hmaxN : Emax ≤ (n : ℝ) - 1 := min_le_right _ _
  have hbmax0 : 0 ≤ 1 - Emax / n :=
    sub_nonneg.mpr ((div_le_one hn).mpr (by linarith only [hmaxN]))
  have hCp : 0 < Cmax := lt_of_lt_of_le zero_lt_one hC1
  have htol : 0 < η / Cmax ^ m := div_pos hη (pow_pos hCp m)
  have hℓ : 0 < ℓ := Nat.succ_pos _
  let : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hη2 : 0 < η ^ 2 := sq_pos_of_pos hη
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hlarge : 16 * (p : ℝ) ^ 2 * S ≤ (ℓ : ℝ) * η ^ 2 := by
    apply (div_le_iff₀ hη2).mp
    calc
      _ ≤ (⌈16 * (p : ℝ) ^ 2 * S / η ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (ℓ : ℝ) := by dsimp only [ℓ]; push_cast; linarith
  have hbase : 4 * (p : ℝ) ^ 2 * S / ((ℓ : ℝ) * η ^ 2) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos hℓR hη2)).mpr
    nlinarith only [hlarge]
  have hcoef : 4 * (p : ℝ) ^ 2 / ((ℓ : ℝ) * (η / Cmax ^ m) ^ 2) =
      4 * (p : ℝ) ^ 2 * Cmax ^ (2 * m) / ((ℓ : ℝ) * η ^ 2) := by
    rw [div_pow, ← mul_div_assoc, div_div_eq_mul_div, ← pow_mul, Nat.mul_comm m 2]
  have hrawbase : 4 * (p : ℝ) ^ 2 / ((ℓ : ℝ) * (η / Cmax ^ m) ^ 2) ≤ 1 / 4 := by
    rw [hcoef]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCost (by positivity)) (by positivity)).trans hbase
  have hM : (q : ℝ) ^ L *
      (4 * (p : ℝ) ^ 2 / ((ℓ : ℝ) * (η / Cmax ^ m) ^ 2)) ^ p < 1 / 2 := by
    calc
      _ ≤ (q : ℝ) ^ L * (1 / 4 : ℝ) ^ p := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hrawbase p) (by positivity)
      _ = (q : ℝ) ^ L / (4 : ℝ) ^ p := by simp only [div_eq_mul_inv, one_mul, inv_pow]
      _ < 1 / 2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 ^ p)).mpr (by nlinarith only [hpD])
  have huLog : (m : ℝ) / n + Real.log (2 * (n : ℝ) * ℓ) ≤ u * Real.log 2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp (Nat.le_ceil _)
  have hF : (n : ℝ) * ℓ * Real.exp ((m : ℝ) / n - u * Real.log 2) ≤ 1 / 2 := by
    calc
      _ ≤ (n : ℝ) * ℓ * Real.exp (-Real.log (2 * (n : ℝ) * ℓ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (by linarith only [huLog])
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 2 * (n : ℝ) * ℓ)]
        field_simp
  have hcard : Fintype.card (Fin ℓ) = ℓ := Fintype.card_fin _
  have hdim : Fintype.card (Fin L → Fin q) = q ^ L := by simp
  obtain ⟨σ, hsample, hcounts⟩ :=
    Matrix.exists_sampled_complement_power_approximation_and_word_counts
    (β := Fin ℓ) h hpos hu (c := 1) zero_le_one htol m hp u (by
      simpa only [hcard, hdim, Nat.cast_pow, one_pow, mul_one, n, Nat.cast_add, Nat.cast_one] using
        (show (q : ℝ) ^ L * (4 * (p : ℝ) ^ 2 /
            ((ℓ : ℝ) * (η / Cmax ^ m) ^ 2)) ^ p +
          (n : ℝ) * ℓ * Real.exp ((m : ℝ) / n - u * Real.log 2) < 1 from by linarith only [hM, hF]))
  let T := (ℓ : ℂ)⁻¹ • ∑ b, (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod
  let M := (1 - (Fintype.card (Fin (L - 1)) + 1 : ℂ)⁻¹ • ∑ i, h i) ^ m
  have hTM : ‖T - M‖ < η / Cmax ^ m := by
    rw [hcard] at hsample
    simpa only [Complex.ofReal_one, one_pow, one_smul] using hsample
  have hrank (k : ℕ) : operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) T) ≤ r := by
    have hb := operatorSchmidtRank_sampled_nn_complements_le
      (m := m) (u := u) (β := Fin ℓ) hq h hs σ (fun b c ↦ (hcounts b c).le) 1 (ℓ : ℂ)⁻¹ k
    have hb' : operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) T) ≤
          Fintype.card (Fin ℓ) * q ^ (2 * u) := by simpa only [one_smul] using hb
    exact hb'.trans_eq (congrArg (fun t ↦ t * q ^ (2 * u)) hcard)
  have hHnorm : ‖∑ i, h i‖ ≤ (Fintype.card (Fin (L - 1)) : ℝ) := by
    calc
      _ ≤ ∑ i, ‖h i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin (L - 1), (1 : ℝ) := Finset.sum_le_sum fun i _ ↦
        (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hpos i).nonneg).mpr (hu i)
      _ = _ := by simp
  have hApprox (E0 : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q))
      (haE : a ≤ E0) (hEa : E0 ≤ a + 1) (hΩ : ‖Ω‖ = 1)
      (heig : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
      (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef) :
      let β := (1 - E0 / n) ^ m
      0 < β ∧ ‖T - (β : ℂ) • vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ <
        β * (η + 1 / Q) := by
    intro β
    have hlin : toEuclideanLin (∑ i, h i) Ω = (E0 : ℂ) • Ω := by
      change WithLp.toLp 2 ((∑ i, h i) *ᵥ WithLp.ofLp Ω) = _
      rw [heig]
      rfl
    have hEnorm := Entropy.norm_toEuclideanLin_le (∑ i, h i) Ω
    rw [hlin, norm_smul, hΩ, mul_one, Complex.norm_real, Real.norm_eq_abs] at hEnorm
    simp only [mul_one] at hEnorm
    have hEN : E0 ≤ (n : ℝ) - 1 := by
      have he := (le_abs_self E0).trans (hEnorm.trans hHnorm)
      simpa only [n, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using he
    have hEmax : E0 ≤ Emax := le_min hEa hEN
    have hb : 0 < 1 - E0 / n := sub_pos.mpr ((div_lt_one hn).mpr (by linarith only [hEN]))
    have hβ : 0 < β := pow_pos hb m
    have htolβ : η / Cmax ^ m ≤ β * η := by
      calc
        _ = η * (1 - Emax / n) ^ m := by simp only [Cmax, div_eq_mul_inv, inv_pow, inv_inv]
        _ ≤ η * (1 - E0 / n) ^ m := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hbmax0
            (by have := div_le_div_of_nonneg_right hEmax hn.le; linarith) m) hη.le
        _ = _ := by dsimp only [β]; ring
    have hm : (((n : ℝ) - E0) / Δ) * Real.log (1 / (1 / Q)) ≤ (m : ℝ) := by
      simp only [one_div, inv_inv]
      exact (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (sub_le_sub_left haE (n : ℝ)) hΔ.le)
        (Real.log_nonneg hQ)).trans (Nat.le_ceil (((n : ℝ) - a) / Δ * Real.log Q))
    have hpower := Matrix.norm_power_filter_sub_ground_le_of_lower_gap_log_threshold
      h hpos hu hΩ heig hgap hΔ (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hQ)) m hm
    let C0 := (1 - E0 / (n : ℝ))⁻¹
    let A0 := ((C0 : ℂ) • (1 - (Fintype.card (Fin (L - 1)) + 1 : ℂ)⁻¹ • ∑ i, h i)) ^ m
    have hpower' : ‖A0 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ 1 / Q := by
      simpa only [A0, C0, n, Nat.cast_add, Nat.cast_one, ← Complex.coe_smul,
        Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
        using hpower
    have hcancel : (β : ℂ) * (C0 : ℂ) ^ m = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
      dsimp only [β, C0]
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hb), one_pow, Complex.ofReal_one]
    have hscale : (β : ℂ) • (A0 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) =
        M - (β : ℂ) • vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) := by
      simp only [smul_sub, A0, smul_pow, smul_smul, hcancel, one_smul, M]
    have hMP : ‖M - (β : ℂ) • vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ β / Q := by
      rw [← hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hpower' hβ.le
    refine ⟨hβ, ?_⟩
    calc
      _ ≤ ‖T - M‖ + ‖M - (β : ℂ) • vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < β * η + β / Q := add_lt_add_of_lt_of_le (hTM.trans_le htolβ) hMP
      _ = _ := by ring
  refine ⟨hℓ, σ, hTM, hcounts, hrank, hApprox, fun i hi ↦ ?_⟩
  obtain ⟨t, A, B, ht, hdec, hleft⟩ := exists_cutDecomposition_of_operatorSchmidtRank_le hi T hrank
  refine ⟨t, A, B, ht, hdec, hleft, fun E0 Ω haE hEa hΩ heig hgap hsmall s b V hV ↦ ?_⟩
  obtain ⟨hβ, hTP⟩ := hApprox E0 Ω haE hEa hΩ heig hgap
  have hred := hV.errorReduction_of_norm_sub_smul_groundProjection_le
    (J := Finset.univ) hi hΩ hdec (fun j _ k hk hki ↦ hleft j k hk hki) hβ hTP.le
    (by exact (mul_lt_mul_of_pos_left hsmall hβ).trans_eq (by ring))
  have hcardt : (Finset.univ : Finset (Fin t)).card = t := by simp
  have herr : 4 * ((1 - E0 / n) ^ m * (η + 1 / Q)) / (1 - E0 / n) ^ m =
      4 * (η + 1 / Q) := by
    apply (div_eq_iff (ne_of_gt hβ)).mpr
    ring
  simpa only [hcardt, herr] using hred

end TNLean.MPS.AreaLaw
