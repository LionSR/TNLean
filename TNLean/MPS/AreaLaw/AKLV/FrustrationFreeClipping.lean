/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.NormalizedChain

/-!
# Exact ground-vector preservation for frustration-free clipping

The actual separate exterior clipping of a positive nearest-neighbour chain
preserves its original zero-energy unit ground vector exactly. At cutoff
`t ≥ 1024/g`, the same vector has projector gap at least `g/2` for the clipped
Hamiltonian. Regional positivity, commutation, reconstruction and the clipped
order comparison are derived from the original supported positive contractions.

Source: AKLV, arXiv:1301.1162v1, Section 4, frustration-free clipping preceding
Theorem 4.3 (`t:ent`), `1dfrustrated34.tex`, lines 810–818. The inverse-gap cutoff
uses the accepted Theorem 6.1(a) estimate at original energy zero. This result
asserts no final entropy rate, parameter optimization, or detectability argument.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- Separate exterior clipping preserves the original frustration-free ground
vector and gives a gap of at least half the original gap at cutoff `1024/g`.
The boundary bonds `a < b` are retained, the bonds strictly before `a` and
strictly after `b` form the clipped exteriors, and the intervening bonds are
unchanged. All three existing cut blocks have zero regional shift.

Source: AKLV, arXiv:1301.1162v1, Section 4, lines 810–818, and Theorem 6.1(a).
The source's unique-ground-vector setting is expressed by the original
projector-gap hypothesis; no gap or comparison for the clipped operator is supplied. -/
lemma frustrationFree_twoSidedEnergyTruncation_ground_gap {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (g t : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) (ht : 1024 / g ≤ t)
    (hzero : (∑ i, h i) *ᵥ WithLp.ofLp Ω = 0)
    (hgap : ((∑ i, h i) - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef) :
    let X := leftCutBlock h a 0
    let N := middleCutBlock h a b 0
    let Y := rightCutBlock h b 0
    let K := twoSidedEnergyTruncation X (N + (h a + h b)) Y t
    K.PosSemidef ∧ K ≤ ∑ i, h i ∧ K *ᵥ WithLp.ofLp Ω = 0 ∧
      (K - ((g / 2 : ℝ) : ℂ) •
        (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
  intro X N Y K
  classical
  let H := ∑ i, h i
  let A := h a + h b
  let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
  have hsumpos (S : Finset (Fin (L - 1))) : (∑ i ∈ S, h i).PosSemidef :=
    Matrix.posSemidef_sum S fun i _ ↦ Matrix.nonneg_iff_posSemidef.mp (h0 i)
  have hX : X.PosSemidef := by
    simpa only [X, leftCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      hsumpos (Finset.univ.filter fun i ↦ i.val < a.val)
  have hN : N.PosSemidef := by
    simpa only [N, middleCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      hsumpos (Finset.univ.filter fun i ↦ a.val < i.val ∧ i.val < b.val)
  have hY : Y.PosSemidef := by
    simpa only [Y, rightCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      hsumpos (Finset.univ.filter fun i ↦ b.val < i.val)
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (add_nonneg (h0 a) (h0 b))
  have hAcap : A ≤ (2 : ℂ) • 1 := by
    simpa only [A, two_smul] using add_le_add (h1 a) (h1 b)
  obtain ⟨hXN, hXY, hNY⟩ := normalizedCutBlock_commutations h hs a b hab 0 0 0
  have hsum : X + N + Y + A = H := by
    simpa only [H, X, N, Y, A, zero_add, Complex.ofReal_zero, zero_smul, sub_zero] using
      normalizedCutBlock_sum h a b hab 0 0 0
  have hH : X + (N + A) + Y = H := by rw [← hsum]; abel
  have ht0 : 0 < t := (div_pos (by norm_num : (0 : ℝ) < 1024) hg).trans_le ht
  obtain ⟨hK, hKle⟩ := twoSidedEnergyTruncation_posSemidef_le X (N + A) Y
    hX (hN.add hA) hY t ht0.le
  rw [hH] at hKle
  have hKzero : K *ᵥ WithLp.ofLp Ω = 0 := by
    have hz := Matrix.mulVec_eq_smul_of_order_sandwich H K 0 (WithLp.ofLp Ω)
      (by simpa only [Complex.ofReal_zero, zero_smul] using hK.nonneg) hKle
      (by simpa only [H, Complex.ofReal_zero, zero_smul] using hzero)
    simpa only [Complex.ofReal_zero, zero_smul] using hz
  have hgap0 : (H - (0 : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    simpa only [H, zero_smul, sub_zero] using hgap
  have hcut : 1024 * (0 + g) ≤ t * g ^ 2 := by
    have htg := (div_le_iff₀ hg).mp ht
    have hmul := mul_le_mul_of_nonneg_right htg hg.le
    nlinarith
  have horth := orthogonal_clipped_energy_ge X N Y A hX hN hY hA hXN hXY hNY hAcap
    Ω hΩ 0 g t (by norm_num) (by norm_num) hg hg1 ht0 hcut
    (by
      intro v
      simpa only [hH, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
        ContinuousLinearMap.coe_coe] using hgap0.gap_le v)
  have hKΩ : ι K Ω = (0 : ℂ) • Ω := by
    change WithLp.toLp 2 (K *ᵥ WithLp.ofLp Ω) = _
    rw [hKzero]
    simp
  refine ⟨hK, hKle, hKzero, ?_⟩
  suffices hfull : (K - (0 : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef by
    simpa only [zero_smul, sub_zero] using hfull
  apply (hK.isHermitian.posSemidef_gap_iff 0 (g / 2) Ω).2
  intro v
  let α := ⟪Ω, v⟫_ℂ
  let w := v - α • Ω
  have hself : ⟪Ω, Ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  have hw : ⟪Ω, w⟫_ℂ = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, hself, mul_one, α, sub_self]
  have hv : v = α • Ω + w := by dsimp only [w]; module
  have hn : ‖v‖ ^ 2 = ‖α‖ ^ 2 + ‖w‖ ^ 2 := by
    have hi : ⟪α • Ω, w⟫_ℂ = 0 := by rw [inner_smul_left, hw, mul_zero]
    conv_lhs => rw [hv]
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi, norm_smul, hΩ]
    ring
  have he : (⟪v, ι K v⟫_ℂ).re = (⟪w, ι K w⟫_ℂ).re := by
    conv_lhs => rw [hv]
    simpa only [mul_zero, zero_add] using
      re_inner_smul_add_eigenvector hK.isPositive_toEuclideanCLM.isSymmetric hΩ hKΩ hw α
  have hlower := horth w hw
  change (g / 2) * (‖v‖ ^ 2 - ‖α‖ ^ 2) ≤ (⟪v, ι K v⟫_ℂ).re - 0 * ‖v‖ ^ 2
  rw [hn, he]
  simpa only [zero_add, add_sub_cancel_left, zero_mul, sub_zero] using hlower

end TNLean.MPS.AreaLaw.AKLV
