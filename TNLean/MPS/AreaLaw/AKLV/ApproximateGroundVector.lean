/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.ProjectionEnergy

/-!
# Projected approximate ground vectors

The projected original ground vector is an approximate eigenvector of the
actual two-sided clipping. AKLV, arXiv:1301.1162v1, Section 6.3, uses this
observation to conclude Theorem 6.1(b). The residual is controlled entirely
by the boundary interaction and the already proved energy tails.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The low spectral projection of an eigenvector is an approximate
eigenvector for any operator agreeing with the original Hamiltonian on
that low subspace. The bound uses the actual cross-block norm and tails
at two cutoffs. Auxiliary to AKLV, Theorem 6.1(b). -/
theorem IsHermitian.norm_lowProjection_residual_le
    {B : Matrix n n ℂ} (hB : B.IsHermitian) (A K : Matrix n n ℂ)
    (hA : ‖A‖ ≤ 2) (Ω : EuclideanSpace ℂ n) (e t u δ : ℝ) (hut : u ≤ t)
    (heig : toEuclideanCLM (n := n) (𝕜 := ℂ) (B + A) Ω = (e : ℂ) • Ω)
    (hagree : K * (1 - spectralProjectionGE B t) =
      (B + A) * (1 - spectralProjectionGE B t))
    (hoff : ‖spectralProjectionGE B t * A * (1 - spectralProjectionGE B u)‖ ≤ δ) :
    let ι := toEuclideanCLM (n := n) (𝕜 := ℂ)
    let Pt := 1 - spectralProjectionGE B t
    ‖ι K (ι Pt Ω) - (e : ℂ) • ι Pt Ω‖ ≤
      δ * ‖Ω‖ + 2 * ‖ι (spectralProjectionGE B u) Ω‖ +
        2 * ‖ι (spectralProjectionGE B t) Ω‖ := by
  intro ι Pt
  let Qt := spectralProjectionGE B t
  let Pu := 1 - spectralProjectionGE B u
  let Qu := spectralProjectionGE B u
  have hQnorm : ‖Qt‖ ≤ 1 := (hB.isStarProjection_spectralProjectionGE t).norm_le _
  have hPnorm : ‖Pt‖ ≤ 1 := (hB.isStarProjection_spectralProjectionGE t).one_sub.norm_le _
  have hPA : ‖Pt * A‖ ≤ 2 := by
    simpa only [one_mul] using norm_mul_le_of_le hPnorm hA
  have hQAP : ‖Qt * A * Pt‖ ≤ 2 := by
    simpa only [one_mul, mul_one] using
      norm_mul_le_of_le (norm_mul_le_of_le hQnorm hA) hPnorm
  have hPtPu : Pt * Pu = Pu := by
    change (1 - Qt) * Pu = Pu
    rw [sub_mul, one_mul, hB.spectralProjectionGE_mul_one_sub_eq_zero hut, sub_zero]
  have hPt : Pt = Pu + Pt * Qu := by
    calc
      Pt = Pt * (Pu + Qu) := by simp only [Pu, Qu, sub_add_cancel, mul_one]
      _ = _ := by rw [mul_add, hPtPu]
  have hblock : Qt * A * Pt = Qt * A * Pu + (Qt * A * Pt) * Qu := by
    conv_lhs => rhs; rw [hPt]
    noncomm_ring
  have hfirst : ‖ι (Qt * A * Pt) Ω‖ ≤ δ * ‖Ω‖ + 2 * ‖ι Qu Ω‖ := by
    rw [hblock, map_add, _root_.add_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact ((ι (Qt * A * Pu)).le_opNorm Ω).trans
        (mul_le_mul_of_nonneg_right hoff (norm_nonneg _))
    · rw [map_mul, mul_apply_eq_comp]
      exact ((ι (Qt * A * Pt)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hQAP (norm_nonneg _))
  have hsecond : ‖ι (Pt * A * Qt) Ω‖ ≤ 2 * ‖ι Qt Ω‖ := by
    rw [map_mul, mul_apply_eq_comp]
    exact ((ι (Pt * A)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hPA (norm_nonneg _))
  have hcomm : Commute B Pt :=
    (Commute.one_right B).sub_right (hB.commute_spectralProjectionGE t)
  have hmatrix : K * Pt - Pt * (B + A) = Qt * A * Pt - Pt * A * Qt := by
    rw [hagree]
    calc
      (B + A) * Pt - Pt * (B + A) = (B * Pt - Pt * B) + (A * Pt - Pt * A) := by
        noncomm_ring
      _ = A * Pt - Pt * A := by rw [hcomm.eq, sub_self, zero_add]
      _ = _ := by dsimp [Pt]; noncomm_ring
  have hres : ι K (ι Pt Ω) - (e : ℂ) • ι Pt Ω =
      ι (Qt * A * Pt - Pt * A * Qt) Ω := by
    calc
      _ = ι (K * Pt) Ω - ι (Pt * (B + A)) Ω := by
        rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, heig, map_smul]
      _ = ι (K * Pt - Pt * (B + A)) Ω := by rw [map_sub]; rfl
      _ = _ := congrArg (fun M : Matrix n n ℂ ↦ ι M Ω) hmatrix
  rw [hres, map_sub]
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

end Matrix

namespace TNLean.MPS.AreaLaw.AKLV

/-- The actual clipped Hamiltonian has an exponentially accurate
approximate ground vector, with residual at most `10 exp(-(t-40)/16)`.
AKLV, arXiv:1301.1162v1, the approximate-eigenvector argument in Section 6.3.
All tail estimates are derived from the original chain interactions. -/
theorem norm_clipped_lowProjection_residual_le_exp {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (z e t : ℝ) (ht : 0 ≤ t)
    (X N Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hX : X.PosSemidef) (hN : N.PosSemidef) (hY : Y.PosSemidef)
    (hXN : Commute X N) (hXY : Commute X Y) (hNY : Commute N Y)
    (hB : X + N + Y = (∑ i ∈ I, h i) - (z : ℂ) • 1)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6)
    (heig : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (X + N + Y + (h a + h b)) Ω = (e : ℂ) • Ω) :
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let P := 1 - Matrix.spectralProjectionGE (X + N + Y) t
    let K := twoSidedEnergyTruncation X (N + (h a + h b)) Y t
    ‖ι K (ι P Ω) - (e : ℂ) • ι P Ω‖ ≤ 10 * Real.exp (-(t - 40) / 16) := by
  intro ι P K
  let B := X + N + Y
  let A := h a + h b
  have hnorm (i : Fin (L - 1)) : ‖h i‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (h i) (h0 i)).mpr (h1 i)
  have hA : ‖A‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hnorm a, hnorm b])
  have hherm : B.IsHermitian := (hX.isHermitian.add hN.isHermitian).add hY.isHermitian
  have hagree : K * P = (B + A) * P := by
    have h := twoSidedEnergyTruncation_mul_lowProjection_eq_of_commuting
      X N Y A hX hN hY hXN hXY hNY t
    have hsum : X + (N + A) + Y = B + A := by dsimp [B]; abel
    simpa only [hsum] using h
  have hoff : ‖Matrix.spectralProjectionGE B t * A *
      (1 - Matrix.spectralProjectionGE B (t / 2))‖ ≤
        2 * Real.exp (-(t - t / 2) / 8) := by
    rw [show B = (∑ i ∈ I, h i) - (z : ℂ) • 1 from hB]
    exact norm_two_boundary_spectral_offDiagonal_le I h hs h0 h1 a b z t (t / 2)
      (by linarith)
  have htail (s : ℝ) : ‖ι (Matrix.spectralProjectionGE B s) Ω‖ ≤
      2 * Real.exp (-(s - 20) / 8) := by
    have heig' : ι (((∑ i ∈ I, h i) - (z : ℂ) • 1) + A) Ω = (e : ℂ) • Ω := by
      rw [← hB]
      exact heig
    have h := norm_groundState_highProjection_le_exp I h hs h0 h1 a b z e s Ω
      he0 he6 heig'
    simpa only [← hB, hΩ, mul_one] using h
  have hres := hherm.norm_lowProjection_residual_le A K hA Ω e t (t / 2)
    (2 * Real.exp (-(t - t / 2) / 8)) (by linarith) heig hagree hoff
  have htailt : ‖ι (Matrix.spectralProjectionGE B t) Ω‖ ≤
      2 * Real.exp (-(t - 40) / 16) := (htail t).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  have htailu : ‖ι (Matrix.spectralProjectionGE B (t / 2)) Ω‖ ≤
      2 * Real.exp (-(t - 40) / 16) := by
    simpa only [show -(t / 2 - 20) / 8 = -(t - 40) / 16 by ring] using htail (t / 2)
  have hdecay : 2 * Real.exp (-(t - t / 2) / 8) ≤
      2 * Real.exp (-(t - 40) / 16) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  rw [hΩ, mul_one] at hres
  exact hres.trans (by linarith)

end TNLean.MPS.AreaLaw.AKLV
