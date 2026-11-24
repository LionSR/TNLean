/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChebyshevAGSP.LowSpectrumGap
import TNLean.MPS.AreaLaw.ChebyshevAGSP.ApproximateGroundVector
import QICLean.Spectral.Gap.CodimensionOneGap

/-!
# Robustness of the ground vector and gap under two-sided truncation

AKLV, arXiv:1301.1162v1, Theorem 6.1, for the normalized chain of
Section 6.1. The explicit cutoff `32768 (e+g)/g²` yields a gap of at
least `g/2` and a phase-aligned squared distance at most `exp(-t/16)`.
The boundary, tail, mass and residual estimates are all derived from
the original chain terms and its three positive disconnected blocks.
-/

open ManyBody (interval)

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- Polynomial gap prefactors in the residual estimate are absorbed by
the cutoff in AKLV, Theorem 6.1. No numerical exponential approximation
is needed for these explicit universal constants. -/
theorem phase_budget_le_exp (g t : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (htg : 32768 ≤ t * g) :
    2 * (10 * Real.exp (-(t - 40) / 16) / (g / 2) +
      2 * Real.exp (-(t - 40) / 16)) ^ 2 ≤ Real.exp (-t / 16) := by
  let η := Real.exp (-(t - 40) / 16)
  have hη : 0 ≤ η := (Real.exp_pos _).le
  have hbound : 10 * η / (g / 2) + 2 * η ≤ 22 * η / g := by
    apply (le_div_iff₀ hg).mpr
    rw [add_mul]
    have hc : (10 * η / (g / 2)) * g = 20 * η := by field_simp; ring
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_left hg1 hη]
  have hsquare : 2 * (10 * η / (g / 2) + 2 * η) ^ 2 ≤
      (968 / g ^ 2) * Real.exp (-(t - 40) / 8) := by
    have h := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hbound 2) (by norm_num : (0 : ℝ) ≤ 2)
    refine h.trans_eq ?_
    rw [div_pow]
    have hexp : η ^ 2 = Real.exp (-(t - 40) / 8) := by
      rw [show η ^ 2 = η * η from pow_two η, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, hexp]
    field_simp
    norm_num
  have hlog : Real.log 968 - 2 * Real.log g - (t - 40) / 8 ≤ -t / 16 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 968)
    have hi := Real.one_sub_inv_le_log_of_pos hg
    have hl' := mul_le_mul_of_nonneg_left hl hg.le
    have hi' := mul_le_mul_of_nonneg_left hi hg.le
    rw [mul_sub, mul_inv_cancel₀ hg.ne', mul_one] at hi'
    apply le_of_mul_le_mul_left (a := g) _ hg
    nlinarith
  have hpositive : 0 < (968 / g ^ 2) * Real.exp (-(t - 40) / 8) := by positivity
  have hfinal : (968 / g ^ 2) * Real.exp (-(t - 40) / 8) ≤ Real.exp (-t / 16) := by
    apply (Real.log_le_iff_le_exp hpositive).mp
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_div (by norm_num) (pow_ne_zero _ hg.ne'), Real.log_pow, Real.log_exp]
    nlinarith only [hlog]
  exact hsquare.trans hfinal

/-- Assembly of AKLV, arXiv:1301.1162v1, Theorem 6.1 from a clipped ground
vector with the orthogonal energy bound `e+g/2`. The residual and tail
estimates of the original chain give the gap `g/2` and the phase-aligned
squared distance `exp(-t/16)` once `32768 ≤ t g`; this step is shared by
every cutoff that produces the orthogonal bound. -/
theorem robust_ground_of_clipped_ground_gap {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (a b : Fin (L - 1)) (z e g t : ℝ)
    (X N Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hX : X.PosSemidef) (hN : N.PosSemidef) (hY : Y.PosSemidef)
    (hXN : Commute X N) (hXY : Commute X Y) (hNY : Commute N Y)
    (hB : X + N + Y = Φ.partialHamiltonian I - (z : ℂ) • 1)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1) (htg : 32768 ≤ t * g)
    (heig : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (X + N + Y + (Φ.term a + Φ.term b)) Ω = (e : ℂ) • Ω)
    (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)) (hφ : ‖φ‖ = 1)
    (hφeig : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (Matrix.twoSidedEnergyTruncation X (N + (Φ.term a + Φ.term b)) Y t) φ = (e' : ℂ) • φ)
    (he'e : e' ≤ e)
    (hstrong : ∀ v : EuclideanSpace ℂ (Fin L → Fin q),
      (e + g / 2 - e') * (‖v‖ ^ 2 - ‖⟪φ, v⟫_ℂ‖ ^ 2) ≤
        (⟪v, Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          (Matrix.twoSidedEnergyTruncation X (N + (Φ.term a + Φ.term b)) Y t) v⟫_ℂ).re -
        e' * ‖v‖ ^ 2)
    (horth : ∀ v : EuclideanSpace ℂ (Fin L → Fin q), ⟪φ, v⟫_ℂ = 0 →
      (e + g / 2) * ‖v‖ ^ 2 ≤ (⟪v, Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (Matrix.twoSidedEnergyTruncation X (N + (Φ.term a + Φ.term b)) Y t) v⟫_ℂ).re) :
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let K := Matrix.twoSidedEnergyTruncation X (N + (Φ.term a + Φ.term b)) Y t
    (∀ v : EuclideanSpace ℂ (Fin L → Fin q),
      (g / 2) * (‖v‖ ^ 2 - ‖⟪φ, v⟫_ℂ‖ ^ 2) ≤ (⟪v, ι K v⟫_ℂ).re - e' * ‖v‖ ^ 2) ∧
      ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  intro ι K
  let A := Φ.term a + Φ.term b
  let B := X + N + Y
  let P := 1 - Matrix.spectralProjectionGE B t
  let η := Real.exp (-(t - 40) / 16)
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (add_nonneg (h0 a) (h0 b))
  have ht0 : 0 < t := by nlinarith
  have hpositive : (ι K).IsPositive :=
    (twoSidedEnergyTruncation_posSemidef_le X (N + A) Y hX (hN.add hA) hY t ht0.le).1
      |>.isPositive_toEuclideanCLM
  have hweak (v : EuclideanSpace ℂ (Fin L → Fin q)) :
      (g / 2) * (‖v‖ ^ 2 - ‖⟪φ, v⟫_ℂ‖ ^ 2) ≤ (⟪v, ι K v⟫_ℂ).re - e' * ‖v‖ ^ 2 := by
    have hv : ‖⟪φ, v⟫_ℂ‖ ≤ ‖v‖ := by
      simpa only [hφ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) φ v
    have hdef : 0 ≤ ‖v‖ ^ 2 - ‖⟪φ, v⟫_ℂ‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hv 2]
    exact (mul_le_mul_of_nonneg_right (by linarith : g / 2 ≤ e + g / 2 - e') hdef).trans
      (hstrong v)
  have hres : ‖ι K (ι P Ω) - (e : ℂ) • ι P Ω‖ ≤ 10 * η :=
    norm_clipped_lowProjection_residual_le_exp I Φ h0 h1 a b z e t ht0.le
      X N Y hX hN hY hXN hXY hNY hB Ω hΩ he0 he6 heig
  have htail : ‖Ω - ι P Ω‖ ≤ 2 * η := by
    have htail' := ManyBody.BondInteraction.norm_groundState_highProjection_le_exp I Φ h0 h1 a b z e t Ω
      he0 he6 (by simpa only [← hB] using heig)
    have hid : Ω - ι P Ω = ι (Matrix.spectralProjectionGE B t) Ω := by
      simp only [P, map_sub, map_one, _root_.sub_apply, one_apply_eq_self, sub_sub_cancel]
    rw [hid]
    have hdecay : 2 * Real.exp (-(t - 20) / 8) ≤ 2 * η :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    apply le_trans ?_ hdecay
    simpa only [← hB, hΩ, mul_one] using htail'
  obtain ⟨θ, hθ⟩ := ContinuousLinearMap.exists_phase_sq_distance_le_residual (ι K)
    hpositive.isSymmetric φ Ω hφ hΩ e' e (e + g / 2) hφeig (by linarith) horth (ι P Ω)
  have hden : e + g / 2 - e = g / 2 := by ring
  rw [hden] at hθ
  have hsmall : ‖ι K (ι P Ω) - (e : ℂ) • ι P Ω‖ / (g / 2) + ‖Ω - ι P Ω‖ ≤
      10 * η / (g / 2) + 2 * η :=
    add_le_add (div_le_div_of_nonneg_right hres (by positivity)) htail
  refine ⟨hweak, θ, ?_⟩
  exact hθ.trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hsmall 2) (by norm_num : (0 : ℝ) ≤ 2)).trans
      (phase_budget_le_exp g t hg hg1 htg))

/-- **AKLV robustness for a normalized chain with its disconnected
regional blocks.** The local positive contractions imply both the
constant-fraction gap and exponentially small phase-aligned ground-vector
squared distance for the actual separate exterior clipping.
AKLV, arXiv:1301.1162v1, Theorem 6.1 and Sections 6.1, 6.3.
The block commutations and decomposition are the algebraic data coming
from their disjoint supports; no tail, residual or new gap is assumed. -/
theorem exists_robust_ground_twoSidedEnergyTruncation {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (a b : Fin (L - 1)) (z e g t : ℝ)
    (X N Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hX : X.PosSemidef) (hN : N.PosSemidef) (hY : Y.PosSemidef)
    (hXN : Commute X N) (hXY : Commute X Y) (hNY : Commute N Y)
    (hB : X + N + Y = Φ.partialHamiltonian I - (z : ℂ) • 1)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 32768 * (e + g) / g ^ 2 ≤ t)
    (heig : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (X + N + Y + (Φ.term a + Φ.term b)) Ω = (e : ℂ) • Ω)
    (hgap : ∀ v : EuclideanSpace ℂ (Fin L → Fin q),
      g * (‖v‖ ^ 2 - ‖⟪Ω, v⟫_ℂ‖ ^ 2) ≤
        (⟪v, Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          (X + N + Y + (Φ.term a + Φ.term b)) v⟫_ℂ).re - e * ‖v‖ ^ 2) :
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let K := Matrix.twoSidedEnergyTruncation X (N + (Φ.term a + Φ.term b)) Y t
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
      ‖φ‖ = 1 ∧ ι K φ = (e' : ℂ) • φ ∧ 0 ≤ e' ∧ e' ≤ e ∧
      (∀ v : EuclideanSpace ℂ (Fin L → Fin q),
        (g / 2) * (‖v‖ ^ 2 - ‖⟪φ, v⟫_ℂ‖ ^ 2) ≤
          (⟪v, ι K v⟫_ℂ).re - e' * ‖v‖ ^ 2) ∧
      ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  intro ι K
  let A := Φ.term a + Φ.term b
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (add_nonneg (h0 a) (h0 b))
  have hAcap : A ≤ (2 : ℂ) • 1 := by
    simpa only [two_smul] using add_le_add (h1 a) (h1 b)
  have hcut : 32768 * (e + g) ≤ t * g ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hg)).mp ht
  have ht0 : 0 < t := by nlinarith [sq_pos_of_pos hg]
  have hcut' : 1024 * (e + g) ≤ t * g ^ 2 := by nlinarith
  have hH : X + (N + A) + Y = X + N + Y + A := by abel
  obtain ⟨e', φ, hφ, hφeig, he'0, he'e, hstrong, horth⟩ :=
    exists_ground_gap_twoSidedEnergyTruncation X N Y A hX hN hY hA hXN hXY hNY hAcap
      Ω hΩ e g t he0 he6 hg hg1 ht0 hcut' (by simpa only [hH] using heig)
      (by simpa only [hH] using hgap)
  have htg : 32768 ≤ t * g := by
    have h : (32768 : ℝ) * g ≤ (t * g) * g := by nlinarith
    exact le_of_mul_le_mul_right h hg
  obtain ⟨hweak, θ, hθ⟩ := robust_ground_of_clipped_ground_gap I Φ h0 h1 a b z e g t
    X N Y hX hN hY hXN hXY hNY hB Ω hΩ he0 he6 hg hg1 htg heig e' φ hφ hφeig he'e
    hstrong horth
  exact ⟨e', φ, hφ, hφeig, he'0, he'e, hweak, θ, hθ⟩

end TNLean.MPS.AreaLaw.AKLV
