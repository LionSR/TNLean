/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.ProjectionEnergy
import TNLean.MPS.AreaLaw.AKLV.CodimensionOneGap

/-!
# The low-spectrum gap under two-sided energy truncation

For the normalization in AKLV, arXiv:1301.1162v1, Section 6.1, the
threshold `t ≥ 1024 (e+g)/g²` suffices for a gap of at least `g/2`.
The projected energy, high-energy mass, and all compatibility identities
are derived from the original regional operators.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- The cutoff condition makes every sufficiently low-energy vector's
high-energy norm at most `g/32`. Auxiliary scalar estimate for AKLV,
Theorem 6.1(a). -/
private theorem high_norm_le_gap_div_thirtyTwo (e g t q E : ℝ)
    (he : 0 ≤ e) (hg : 0 < g) (hq : 0 ≤ q)
    (hcut : 1024 * (e + g) ≤ t * g ^ 2)
    (hmass : t * q ^ 2 ≤ E) (hE : E ≤ e + g / 2) : q ≤ g / 32 := by
  have hep : 0 < e + g := by linarith
  have h1 := mul_le_mul_of_nonneg_right hcut (sq_nonneg q)
  have h2 := mul_le_mul_of_nonneg_right (hmass.trans hE) (sq_nonneg g)
  have hsq : (e + g) * (1024 * q ^ 2) ≤ (e + g) * g ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg g) hg.le]
  have hsq' := le_of_mul_le_mul_left hsq hep
  nlinarith

/-- Every vector orthogonal to the original ground vector has clipped
energy at least `e+g/2` times its squared norm. This is the variational
step in AKLV, arXiv:1301.1162v1, Theorem 6.1(a). -/
theorem orthogonal_clipped_energy_ge
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1)
    (e g t : ℝ) (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 0 < t) (hcut : 1024 * (e + g) ≤ t * g ^ 2)
    (hgap : ∀ y : EuclideanSpace ℂ n,
      g * (‖y‖ ^ 2 - ‖⟪Ω, y⟫_ℂ‖ ^ 2) ≤
        (⟪y, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (L + (N + A) + R) y⟫_ℂ).re -
          e * ‖y‖ ^ 2) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let K := twoSidedEnergyTruncation L (N + A) R t
    ∀ x : EuclideanSpace ℂ n, ⟪Ω, x⟫_ℂ = 0 →
      (e + g / 2) * ‖x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re := by
  intro ι K
  apply re_inner_lower_of_unit_orthogonal_lower (ι K) Ω (e + g / 2)
  intro x hx horth
  let Q := Matrix.spectralProjectionGE (L + N + R) t
  let P := 1 - Q
  let q := ‖ι Q x‖
  let E := (⟪x, ι K x⟫_ℂ).re
  by_contra hnot
  have hE : E ≤ e + g / 2 := (not_le.mp hnot).le
  have hmass := cutoff_mul_sq_norm_highProjection_le_energy
    L N R A hL hN hR hA hLN hLR hNR t ht.le x
  have hq : q ≤ g / 32 := high_norm_le_gap_div_thirtyTwo e g t q E
    he0 hg (norm_nonneg _) hcut hmass hE
  have hQ : IsStarProjection (ι Q) :=
    (((hL.isHermitian.add hN.isHermitian).add hR.isHermitian)
      |>.isStarProjection_spectralProjectionGE t).map ι
  have hPx : ι P x = x - ι Q x := by
    rw [map_sub, map_one]
    rfl
  have hPnorm : ‖ι P x‖ ^ 2 = 1 - q ^ 2 := by
    have h := ContinuousLinearMap.IsStarProjection.norm_sq_eq hQ x
    rw [hx, one_pow, ← hPx] at h
    change 1 = q ^ 2 + ‖ι P x‖ ^ 2 at h
    linarith
  have hinner : ⟪Ω, ι P x⟫_ℂ = -⟪Ω, ι Q x⟫_ℂ := by
    rw [hPx, inner_sub_right, horth, zero_sub]
  have hover : ‖⟪Ω, ι P x⟫_ℂ‖ ≤ q := by
    rw [hinner, norm_neg]
    simpa only [hΩ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) Ω (ι Q x)
  have hover2 : ‖⟪Ω, ι P x⟫_ℂ‖ ^ 2 ≤ q ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hover 2
  have hG := hgap (ι P x)
  rw [hPnorm] at hG
  have hproj := projected_energy_le_clipped_energy_add_tail
    L N R A hL hN hR hA hLN hLR hNR hAcap t ht x hx
  have hmul := mul_le_mul_of_nonneg_left hover2 hg.le
  have hnecessary : g ≤ g / 2 + 4 * q + (e + 2 * g) * q ^ 2 := by
    nlinarith
  have hcoef : (e + 2 * g) * q ^ 2 ≤ 8 * q ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg q)
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq2 : q ^ 2 ≤ g / 1024 := by
    nlinarith [sq_nonneg (g / 32 - q)]
  nlinarith

/-- The actual clipped Hamiltonian has a unit ground vector, and all
directions orthogonal to it have energy at least `e+g/2`.
AKLV, arXiv:1301.1162v1, Theorem 6.1(a), with explicit cutoff constants.
The gap is therefore at least `g/2`, since its ground energy is at most `e`. -/
theorem exists_ground_gap_twoSidedEnergyTruncation
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1)
    (e g t : ℝ) (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 0 < t) (hcut : 1024 * (e + g) ≤ t * g ^ 2)
    (heig : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (L + (N + A) + R) Ω = (e : ℂ) • Ω)
    (hgap : ∀ y : EuclideanSpace ℂ n,
      g * (‖y‖ ^ 2 - ‖⟪Ω, y⟫_ℂ‖ ^ 2) ≤
        (⟪y, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (L + (N + A) + R) y⟫_ℂ).re -
          e * ‖y‖ ^ 2) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let K := twoSidedEnergyTruncation L (N + A) R t
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧ ι K φ = (e' : ℂ) • φ ∧
      0 ≤ e' ∧ e' ≤ e ∧
      (∀ x : EuclideanSpace ℂ n,
        (e + g / 2 - e') * (‖x‖ ^ 2 - ‖⟪φ, x⟫_ℂ‖ ^ 2) ≤
          (⟪x, ι K x⟫_ℂ).re - e' * ‖x‖ ^ 2) ∧
      (∀ x : EuclideanSpace ℂ n, ⟪φ, x⟫_ℂ = 0 →
        (e + g / 2) * ‖x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re) := by
  intro ι K
  obtain ⟨hKpos, hKle⟩ :=
    twoSidedEnergyTruncation_posSemidef_le L (N + A) R hL (hN.add hA) hR t ht.le
  have hpositive : (ι K).IsPositive := hKpos.isPositive_toEuclideanCLM
  have htest : (⟪Ω, ι K Ω⟫_ℂ).re ≤ e := by
    have h := (Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp hKle))
      |>.re_inner_nonneg_right Ω
    change 0 ≤ (⟪Ω, ι (L + (N + A) + R - K) Ω⟫_ℂ).re at h
    rw [map_sub] at h
    change 0 ≤ (⟪Ω, ι (L + (N + A) + R) Ω - ι K Ω⟫_ℂ).re at h
    rw [inner_sub_right, Complex.sub_re, heig, inner_smul_right,
      Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K, hΩ] at h
    norm_num at h
    exact h
  exact exists_ground_gap_of_orthogonal_lower (ι K) hpositive Ω hΩ e (e + g / 2)
    (by linarith) htest
    (orthogonal_clipped_energy_ge L N R A hL hN hR hA hLN hLR hNR hAcap
      Ω hΩ e g t he0 he6 hg hg1 ht hcut hgap)

end TNLean.MPS.AreaLaw.AKLV
