/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.NormalizedChain

/-!
# Robustness with an inverse-gap cutoff

A refinement of AKLV, arXiv:1301.1162v1, Theorem 6.1 and Section 6.3.
Keeping the positive high-energy diagonal in the two-block comparison
improves the gap cutoff from order `(e+g)/g²` to `e + 3g/2 + 8/g`.
For the normalized chain, the full robustness conclusion holds at
`t ≥ 32768/g`. The energy normalization remains `0 ≤ e ≤ 6`;
no global shift to zero ground energy is made.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- Completing the square absorbs the boundary cross term while retaining
the high-energy diagonal. Refinement of AKLV, Lemma 6.5(2). -/
private theorem boundary_cross_le (g p q : ℝ) (hg : 0 < g) :
    4 * p * q ≤ (g / 2) * p ^ 2 + (8 / g) * q ^ 2 := by
  apply le_of_mul_le_mul_left (a := 2 * g) _ (by positivity)
  have hcancel : (2 * g) * ((g / 2) * p ^ 2 + (8 / g) * q ^ 2) =
      g ^ 2 * p ^ 2 + 16 * q ^ 2 := by field_simp; ring
  rw [hcancel]
  nlinarith [sq_nonneg (g * p - 4 * q)]

/-- Retaining the high-energy diagonal gives the excited-energy threshold
`e+g/2` at cutoff `e+3g/2+8/g`. This refines the variational step in
AKLV, arXiv:1301.1162v1, Theorem 6.1(a), without changing the truncation.
All assumptions concern the original regional operators and ground line. -/
theorem orthogonal_clipped_energy_ge_of_inverse_gap_cutoff
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1)
    (e g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t)
    (hcut : e + 3 * g / 2 + 8 / g ≤ t)
    (hgap : ∀ y : EuclideanSpace ℂ n,
      g * (‖y‖ ^ 2 - ‖⟪Ω, y⟫_ℂ‖ ^ 2) ≤
        (⟪y, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (L + (N + A) + R) y⟫_ℂ).re -
          e * ‖y‖ ^ 2) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let K := twoSidedEnergyTruncation L (N + A) R t
    ∀ x : EuclideanSpace ℂ n, ⟪Ω, x⟫_ℂ = 0 →
      (e + g / 2) * ‖x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re := by
  intro ι K x horth
  let Q := Matrix.spectralProjectionGE (L + N + R) t
  let P := 1 - Q
  let p := ι P x
  let q := ι Q x
  have hQ : IsStarProjection (ι Q) :=
    (((hL.isHermitian.add hN.isHermitian).add hR.isHermitian)
      |>.isStarProjection_spectralProjectionGE t).map ι
  have hP : IsStarProjection (ι P) := by
    simpa only [P, map_sub, map_one] using hQ.one_sub
  have hsplit : p + q = x := by
    dsimp only [p, q, P]
    rw [← _root_.add_apply, ← map_add, sub_add_cancel, map_one, one_apply_eq_self]
  have hnorm : ‖x‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    have h := ContinuousLinearMap.IsStarProjection.norm_sq_eq hQ x
    have hPx : x - ι Q x = p := by
      simp only [p, P, map_sub, map_one, _root_.sub_apply, one_apply_eq_self]
    rw [hPx] at h
    change ‖x‖ ^ 2 = ‖q‖ ^ 2 + ‖p‖ ^ 2 at h
    linarith
  have hinner : ⟪Ω, p⟫_ℂ = -⟪Ω, q⟫_ℂ := by
    have h := congrArg (fun y ↦ ⟪Ω, y⟫_ℂ) hsplit
    rw [inner_add_right, horth] at h
    exact eq_neg_of_add_eq_zero_left h
  have hover : ‖⟪Ω, p⟫_ℂ‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [hinner, norm_neg]
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [hΩ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) Ω q
  have hlow : ι (L + (N + A) + R) p = ι K p := by
    dsimp only [p]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
    exact congrArg (fun M : Matrix n n ℂ ↦ ι M x)
      (twoSidedEnergyTruncation_mul_lowProjection_eq_of_commuting
        L N R A hL hN hR hLN hLR hNR t).symm
  have hlowenergy : (e + g) * ‖p‖ ^ 2 - g * ‖q‖ ^ 2 ≤ (⟪p, ι K p⟫_ℂ).re := by
    have h := hgap p
    rw [hlow] at h
    have hmul := mul_le_mul_of_nonneg_left hover hg.le
    nlinarith
  have hhighenergy : t * ‖q‖ ^ 2 ≤ (⟪q, ι K q⟫_ℂ).re := by
    have h := cutoff_mul_sq_norm_highProjection_le_energy
      L N R A hL hN hR hA hLN hLR hNR t ht q
    have hQq : ι Q q = q := by
      dsimp only [q]
      exact congrArg (fun f : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n ↦ f x)
        hQ.isIdempotentElem.eq
    change t * ‖ι Q q‖ ^ 2 ≤ (⟪q, ι K q⟫_ℂ).re at h
    rw [hQq] at h
    exact h
  have hcross : ⟪p, ι K q⟫_ℂ = ⟪p, ι A q⟫_ℂ := by
    dsimp only [p, q]
    rw [ContinuousLinearMap.IsStarProjection.inner_apply_left hP,
      ContinuousLinearMap.IsStarProjection.inner_apply_left hP]
    simp only [← mul_apply_eq_comp, ← map_mul]
    rw [← Matrix.mul_assoc, lowProjection_mul_clipped_mul_highProjection_eq
      L N R A hL.isHermitian hN.isHermitian hR.isHermitian hLN hLR hNR t]
    simp only [Matrix.mul_assoc]
    rfl
  have hnormA : ‖A‖ ≤ 2 := hA.norm_le_of_le_smul_one (by norm_num) (by simpa using hAcap)
  have hbound : ‖⟪p, ι K q⟫_ℂ‖ ≤ 2 * ‖p‖ * ‖q‖ := by
    rw [hcross]
    calc
      _ ≤ ‖p‖ * ‖ι A q‖ := norm_inner_le_norm _ _
      _ ≤ ‖p‖ * (2 * ‖q‖) := mul_le_mul_of_nonneg_left
        (((ι A).le_opNorm q).trans
          (mul_le_mul_of_nonneg_right hnormA (norm_nonneg q))) (norm_nonneg p)
      _ = _ := by ring
  have hKpos : (ι K).IsPositive :=
    (twoSidedEnergyTruncation_posSemidef_le L (N + A) R hL (hN.add hA) hR t ht).1
      |>.isPositive_toEuclideanCLM
  have hsym : (⟪q, ι K p⟫_ℂ).re = (⟪p, ι K q⟫_ℂ).re := by
    calc
      _ = (⟪ι K p, q⟫_ℂ).re := by
        simpa only [RCLike.re_to_complex] using inner_re_symm (𝕜 := ℂ) q (ι K p)
      _ = _ := congrArg Complex.re (hKpos.isSymmetric p q)
  have henergy : (⟪x, ι K x⟫_ℂ).re =
      (⟪p, ι K p⟫_ℂ).re + (⟪q, ι K q⟫_ℂ).re +
        2 * (⟪p, ι K q⟫_ℂ).re := by
    conv_lhs => rw [← hsplit]
    simp only [map_add, inner_add_left, inner_add_right, Complex.add_re, hsym]
    ring
  have hnegative : -‖⟪p, ι K q⟫_ℂ‖ ≤ (⟪p, ι K q⟫_ℂ).re :=
    (neg_le_neg (Complex.abs_re_le_norm _)).trans (neg_abs_le _)
  have hcrossbudget := boundary_cross_le g ‖p‖ ‖q‖ hg
  have hcutbudget := mul_le_mul_of_nonneg_right hcut (sq_nonneg ‖q‖)
  rw [hnorm, henergy]
  nlinarith

/-- The actual clipped Hamiltonian has a unit ground vector, and all
directions orthogonal to it have energy at least `e+g/2`.
Refinement of AKLV, arXiv:1301.1162v1, Theorem 6.1(a), at
cutoff `e+3g/2+8/g`.
The gap is therefore at least `g/2`, since its ground energy is at most `e`. -/
theorem exists_ground_gap_twoSidedEnergyTruncation_of_inverse_gap_cutoff
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1)
    (e g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t)
    (hcut : e + 3 * g / 2 + 8 / g ≤ t)
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
        (e + g / 2) * ‖x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re) :=
  exists_ground_gap_twoSidedEnergyTruncation_of_orthogonal L N R A hL hN hR hA Ω hΩ e g t hg ht
    heig (orthogonal_clipped_energy_ge_of_inverse_gap_cutoff L N R A hL hN hR hA hLN hLR hNR
      hAcap Ω hΩ e g t hg ht hcut hgap)

/-- The normalized energy and gap bounds turn the refined cutoff into
an inverse-gap bound. Auxiliary to the refinement of AKLV, Theorem 6.1. -/
private theorem refined_cutoff_le (e g t : ℝ) (he6 : e ≤ 6)
    (hg : 0 < g) (hg1 : g ≤ 1) (htg : 16 ≤ t * g) :
    e + 3 * g / 2 + 8 / g ≤ t := by
  apply le_of_mul_le_mul_right (a := g) _ hg
  rw [add_mul, add_mul, div_mul_cancel₀ _ hg.ne']
  have heg := mul_le_mul_of_nonneg_right he6 hg.le
  have hg2 : g ^ 2 ≤ 1 := by nlinarith
  nlinarith

/-- **Refined AKLV robustness for a normalized chain with its disconnected
regional blocks.** The local positive contractions imply both the
constant-fraction gap and exponentially small phase-aligned ground-vector
squared distance for the actual separate exterior clipping at `t ≥ 32768/g`.
AKLV, arXiv:1301.1162v1, Theorem 6.1 and Sections 6.1, 6.3.
The block commutations and decomposition are the algebraic data coming
from their disjoint supports; no tail, residual or new gap is assumed. -/
theorem exists_robust_ground_twoSidedEnergyTruncation_of_inverse_gap_cutoff {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (z e g t : ℝ)
    (X N Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hX : X.PosSemidef) (hN : N.PosSemidef) (hY : Y.PosSemidef)
    (hXN : Commute X N) (hXY : Commute X Y) (hNY : Commute N Y)
    (hB : X + N + Y = (∑ i ∈ I, h i) - (z : ℂ) • 1)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 32768 / g ≤ t)
    (heig : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (X + N + Y + (h a + h b)) Ω = (e : ℂ) • Ω)
    (hgap : ∀ v : EuclideanSpace ℂ (Fin L → Fin q),
      g * (‖v‖ ^ 2 - ‖⟪Ω, v⟫_ℂ‖ ^ 2) ≤
        (⟪v, Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          (X + N + Y + (h a + h b)) v⟫_ℂ).re - e * ‖v‖ ^ 2) :
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let K := twoSidedEnergyTruncation X (N + (h a + h b)) Y t
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
      ‖φ‖ = 1 ∧ ι K φ = (e' : ℂ) • φ ∧ 0 ≤ e' ∧ e' ≤ e ∧
      (∀ v : EuclideanSpace ℂ (Fin L → Fin q),
        (g / 2) * (‖v‖ ^ 2 - ‖⟪φ, v⟫_ℂ‖ ^ 2) ≤
          (⟪v, ι K v⟫_ℂ).re - e' * ‖v‖ ^ 2) ∧
      ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  intro ι K
  let A := h a + h b
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (add_nonneg (h0 a) (h0 b))
  have hAcap : A ≤ (2 : ℂ) • 1 := by
    simpa only [two_smul] using add_le_add (h1 a) (h1 b)
  have htg : 32768 ≤ t * g := (div_le_iff₀ hg).mp ht
  have ht0 : 0 < t := by nlinarith
  have hcut : e + 3 * g / 2 + 8 / g ≤ t :=
    refined_cutoff_le e g t he6 hg hg1 (by linarith)
  have hH : X + (N + A) + Y = X + N + Y + A := by abel
  obtain ⟨e', φ, hφ, hφeig, he'0, he'e, hstrong, horth⟩ :=
    exists_ground_gap_twoSidedEnergyTruncation_of_inverse_gap_cutoff
      X N Y A hX hN hY hA hXN hXY hNY hAcap
      Ω hΩ e g t hg ht0.le hcut (by simpa only [hH] using heig)
      (by simpa only [hH] using hgap)
  obtain ⟨hweak, θ, hθ⟩ := robust_ground_of_clipped_ground_gap I h hs h0 h1 a b z e g t
    X N Y hX hN hY hXN hXY hNY hB Ω hΩ he0 he6 hg hg1 htg heig e' φ hφ hφeig he'e
    hstrong horth
  exact ⟨e', φ, hφ, hφeig, he'0, he'e, hweak, θ, hθ⟩

/-- **Refinement of AKLV Theorem 6.1 on the normalized nearest-neighbour chain.**
For `t ≥ 32768/g`, separate clipping of the exterior blocks has
an actual unit ground vector, gap at least `g/2`, and phase-aligned
squared distance at most `exp(-t/16)` from the original ground vector.
The regional positivity and `0 ≤ e ≤ 6` are precisely the normalization
of Section 6.1; commutations, decompositions and all analytic estimates
are derived. Source: arXiv:1301.1162v1, Theorem 6.1 and Section 6.3. -/
theorem normalized_chain_robustness_of_inverse_gap_cutoff {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (x m y e g t : ℝ)
    (hX : (leftCutBlock h a x).PosSemidef)
    (hN : (middleCutBlock h a b m).PosSemidef)
    (hY : (rightCutBlock h b y).PosSemidef)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 32768 / g ≤ t) :
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let X := leftCutBlock h a x
    let N := middleCutBlock h a b m
    let Y := rightCutBlock h b y
    let H := (∑ i, h i) - ((x + m + y : ℝ) : ℂ) • 1
    let K := twoSidedEnergyTruncation X (N + (h a + h b)) Y t
    ι H Ω = (e : ℂ) • Ω →
    (H - (e : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
      ‖φ‖ = 1 ∧ ι K φ = (e' : ℂ) • φ ∧ 0 ≤ e' ∧ e' ≤ e ∧
      (K - (e' : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
        (1 - Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
      ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  intro ι X N Y H K heig hgap
  obtain ⟨I, hB⟩ := exists_normalizedCutBlock_eq_sum_sub h a b hab x m y
  obtain ⟨hXN, hXY, hNY⟩ := normalizedCutBlock_commutations h hs a b hab x m y
  have hH : X + N + Y + (h a + h b) = H := normalizedCutBlock_sum h a b hab x m y
  obtain ⟨e', φ, hφ, hφeig, he'0, he'e, hquad, θ, hθ⟩ :=
    exists_robust_ground_twoSidedEnergyTruncation_of_inverse_gap_cutoff
      I h hs h0 h1 a b (x + m + y) e g t
    X N Y hX hN hY hXN hXY hNY hB Ω hΩ he0 he6 hg hg1 ht
    (by simpa only [hH] using heig) (by
      intro v
      have hv := hgap.gap_le v
      rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin H] at hv
      change g * (‖v‖ ^ 2 - ‖⟪Ω, v⟫_ℂ‖ ^ 2) ≤ (⟪v, ι H v⟫_ℂ).re - e * ‖v‖ ^ 2 at hv
      simpa only [hH] using hv)
  refine ⟨e', φ, hφ, hφeig, he'0, he'e, ?_, θ, hθ⟩
  have hAHerm : (h a + h b).IsHermitian := IsSelfAdjoint.of_nonneg
    (add_nonneg (h0 a) (h0 b))
  have hKHerm : K.IsHermitian :=
    ((Matrix.isHermitian_energyTruncation X t).add (hN.isHermitian.add hAHerm)).add
      (Matrix.isHermitian_energyTruncation Y t)
  apply (hKHerm.posSemidef_gap_iff e' (g / 2) φ).mpr
  intro v
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin K]
  exact hquad v

end TNLean.MPS.AreaLaw.AKLV
