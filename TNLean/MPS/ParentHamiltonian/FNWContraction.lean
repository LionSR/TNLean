/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.C3CorrectionBounds
import TNLean.MPS.ParentHamiltonian.CenteredOverlapFactor
import TNLean.MPS.ParentHamiltonian.Martingale.OpenChain

/-!
# A geometric C3 projector-defect bound

This file assembles the exact limiting-metric telescope, the centered overlap
estimate, and the three finite-Gram corrections into a common-ambient
open-chain projector bound uniform in the spectator length.

**Scope restriction (Nachtergaele C3 coefficient):** The coefficient proved here is a
reconstructed substitute sufficient for condition C3, not the optimized rational numerator
quoted from Fannes--Nachtergaele--Werner in Nachtergaele, equation (6.1). See
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`.

## Main results

* `MPSTensor.IsPrimitiveMPS.openChain_groundProjection_defect_le_geometric`
-/

open scoped ComplexOrder Matrix Matrix.Norms.Frobenius

/-- If two real numbers are bounded by the same nonnegative number, the product of
their square roots is bounded by that number. -/
private theorem sqrt_mul_sqrt_le_of_le {a b B : ℝ} (hB : 0 ≤ B)
    (haB : a ≤ B) (hbB : b ≤ B) :
    Real.sqrt a * Real.sqrt b ≤ B := by
  calc
    Real.sqrt a * Real.sqrt b ≤ Real.sqrt B * Real.sqrt B := by
      exact mul_le_mul (Real.sqrt_le_sqrt haB) (Real.sqrt_le_sqrt hbB)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = B := Real.mul_self_sqrt hB

/-- A moving geometric denominator is bounded by the denominator at the base
length. -/
private theorem inverse_one_sub_geometric_le_base {c r : ℝ} (hc : 0 < c)
    (hr_pos : 0 < r) (hr_lt_one : r < 1) {l n : ℕ} (hln : l ≤ n)
    (hsmall : c * r ^ l < 1) :
    (1 - c * r ^ n)⁻¹ ≤ (1 - c * r ^ l)⁻¹ := by
  have hpow : r ^ n ≤ r ^ l :=
    pow_le_pow_of_le_one hr_pos.le hr_lt_one.le hln
  have hden : 1 - c * r ^ l ≤ 1 - c * r ^ n := by
    linarith [mul_le_mul_of_nonneg_left hpow hc.le]
  exact inv_anti₀ (sub_pos.mpr hsmall) hden

namespace MPSTensor

variable {d D : ℕ}

/-- The physical sandwich containing the centered virtual C3 residual. -/
noncomputable def c3CenteredProjectorResidualES [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l))) :
    EuclideanSpace ℂ (Cfg d (K + l + 1)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (K + l + 1)) :=
  let Itail := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (l + 1)) hLocalTail
  let Ileft := ContinuousLinearMap.inverseGram
    (groundSpaceMapES A (K + l)) hLocalLeft
  (tailBoundaryMapES A K (l + 1)).comp
    ((boundaryFiberwiseMap (D := D) (Cfg d K) Itail).comp
      ((c3CenteredVirtualResidualES A K l ρ hρ).comp
        ((boundaryFiberwiseMap (D := D) (Cfg d 1) Ileft).comp
          (leftBoundaryMapES A (K + l) 1).adjoint)))

/-- Exact assembly of the projector defect into the centered physical sandwich
and the three finite-Gram correction sandwiches. -/
theorem c3_injectiveRangeProjector_residual_eq_centered_sub_corrections [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l)))
    (hFull : Function.Injective (groundSpaceMapES A (K + l + 1))) :
    let hTail := tailBoundaryMapES_injective_of_groundSpaceMapES_injective
      A K (l + 1) hLocalTail
    let hLeft := leftBoundaryMapES_injective_of_groundSpaceMapES_injective
      A (K + l) 1 hLocalLeft
    (ContinuousLinearMap.injectiveRangeProjector
        (tailBoundaryMapES A K (l + 1)) hTail).comp
        (ContinuousLinearMap.injectiveRangeProjector
          (leftBoundaryMapES A (K + l) 1) hLeft) -
      ContinuousLinearMap.injectiveRangeProjector
        (groundSpaceMapES A (K + l + 1)) hFull =
      c3CenteredProjectorResidualES A K l ρ hρ hLocalTail hLocalLeft -
        c3TailFiniteGramCorrectionES A K l ρ hρ
          hLocalTail hLocalLeft hFull -
        c3FullInverseGramCorrectionES A K l ρ hρ
          hLocalTail hLocalLeft hFull -
        c3LeftFiniteGramCorrectionES A K l ρ hρ hLocalTail hLocalLeft := by
  dsimp only
  rw [c3_injectiveRangeProjector_residual_eq_centered_sub_gramErrors
    A K l ρ hρ hLocalTail hLocalLeft hFull]
  ext x
  simp only [c3CenteredProjectorResidualES, c3CenteredVirtualResidualES,
    c3TailFiniteGramCorrectionES, c3FullInverseGramCorrectionES,
    c3LeftFiniteGramCorrectionES, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_apply,
    sub_apply]

/-- Norm bound for the centered physical sandwich. -/
theorem c3CenteredProjectorResidualES_norm_le [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (l + 1)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + l))) :
    let Itail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (l + 1)) hLocalTail
    let Ileft := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l)) hLocalLeft
    ‖c3CenteredProjectorResidualES A K l ρ hρ hLocalTail hLocalLeft‖ ≤
      Real.sqrt ‖Itail‖ * ‖c3CenteredVirtualResidualES A K l ρ hρ‖ *
        Real.sqrt ‖Ileft‖ := by
  dsimp only
  simp only [c3CenteredProjectorResidualES]
  let Ptail := (tailBoundaryMapES A K (l + 1)).comp
    (ContinuousLinearMap.inverseGram (tailBoundaryMapES A K (l + 1))
      (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
        A K (l + 1) hLocalTail))
  let R := c3CenteredVirtualResidualES A K l ρ hρ
  let Pleft := (ContinuousLinearMap.inverseGram
    (leftBoundaryMapES A (K + l) 1)
      (leftBoundaryMapES_injective_of_groundSpaceMapES_injective
        A (K + l) 1 hLocalLeft)).comp
          (leftBoundaryMapES A (K + l) 1).adjoint
  rw [← inverseGram_tailBoundaryMapES_eq_fiberwise_inverseGram
    A K (l + 1) hLocalTail]
  rw [← inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram
    A (K + l) 1 hLocalLeft]
  change ‖Ptail.comp (R.comp Pleft)‖ ≤ _
  calc
    ‖Ptail.comp (R.comp Pleft)‖ ≤ ‖Ptail‖ * ‖R.comp Pleft‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖R‖ * ‖Pleft‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (l + 1)) hLocalTail‖ * (‖R‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + l)) hLocalLeft‖) := by
      have hPtail : ‖Ptail‖ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (l + 1)) hLocalTail‖ := by
        dsimp only [Ptail]
        exact norm_tailBoundaryMapES_comp_inverseGram_le_sqrt
          A K (l + 1) hLocalTail
      have hPleft : ‖Pleft‖ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + l)) hLocalLeft‖ := by
        dsimp only [Pleft]
        exact norm_inverseGram_comp_leftBoundaryMapES_adjoint_le_sqrt
          A (K + l) 1 hLocalLeft
      exact mul_le_mul hPtail
        (mul_le_mul_of_nonneg_left hPleft (norm_nonneg R))
        (mul_nonneg (norm_nonneg R) (norm_nonneg Pleft))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Norm bound for the whole-increment centered physical sandwich. -/
theorem wholeIncrementCenteredProjectorResidualES_norm_le [NeZero D]
    (A : MPSTensor d D) (K L Q : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hLocalTail : Function.Injective (groundSpaceMapES A (L + Q)))
    (hLocalLeft : Function.Injective (groundSpaceMapES A (K + L))) :
    let Itail := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (L + Q)) hLocalTail
    let Ileft := ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + L)) hLocalLeft
    ‖wholeIncrementCenteredProjectorResidualES A K L Q ρ hρ
        hLocalTail hLocalLeft‖ ≤
      Real.sqrt ‖Itail‖ *
        ‖wholeIncrementCenteredResidualES A K L Q ρ
          (ne_of_gt hρ.trace_pos)‖ * Real.sqrt ‖Ileft‖ := by
  dsimp only
  let Ptail := (reassocTailBoundaryMapES A K L Q).comp
    (ContinuousLinearMap.inverseGram (reassocTailBoundaryMapES A K L Q)
      ((physicalReassocES (d := d) K L Q).injective.comp
        (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
          A K (L + Q) hLocalTail)))
  let R := wholeIncrementCenteredResidualES A K L Q ρ
    (ne_of_gt hρ.trace_pos)
  let Pleft := (ContinuousLinearMap.inverseGram
    (leftBoundaryMapES A (K + L) Q)
      (leftBoundaryMapES_injective_of_groundSpaceMapES_injective
        A (K + L) Q hLocalLeft)).comp
          (leftBoundaryMapES A (K + L) Q).adjoint
  simp only [wholeIncrementCenteredProjectorResidualES]
  rw [← inverseGram_reassocTailBoundaryMapES_eq_fiberwise_inverseGram
    A K L Q hLocalTail]
  rw [← inverseGram_leftBoundaryMapES_eq_fiberwise_inverseGram
    A (K + L) Q hLocalLeft]
  change ‖Ptail.comp (R.comp Pleft)‖ ≤ _
  calc
    ‖Ptail.comp (R.comp Pleft)‖ ≤ ‖Ptail‖ * ‖R.comp Pleft‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Ptail‖ * (‖R‖ * ‖Pleft‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail‖ * (‖R‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + L)) hLocalLeft‖) := by
      have hPtail : ‖Ptail‖ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail‖ := by
        dsimp only [Ptail]
        exact norm_reassocTailBoundaryMapES_comp_inverseGram_le_sqrt
          A K L Q hLocalTail
      have hPleft : ‖Pleft‖ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + L)) hLocalLeft‖ := by
        dsimp only [Pleft]
        exact norm_inverseGram_comp_leftBoundaryMapES_adjoint_le_sqrt
          A (K + L) Q hLocalLeft
      exact mul_le_mul hPtail
        (mul_le_mul_of_nonneg_left hPleft (norm_nonneg R))
        (mul_nonneg (norm_nonneg R) (norm_nonneg Pleft))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
-- The four-term operator-norm assembly requires extra elaboration budget.
/-- A geometric-over-denominator estimate for a whole suffix increment.
The decay is controlled by the overlap length `L`; the constants are uniform in
both the prefix length `K` and suffix increment `Q`. -/
theorem IsPrimitiveMPS.wholeIncrement_groundProjection_defect_le_geometric
    [NeZero D] {A : MPSTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ C c r : ℝ,
      0 < C ∧ 0 < c ∧ 0 < r ∧ r < 1 ∧
      ∀ K L Q : ℕ, 1 ≤ L → c * r ^ L < 1 →
        ‖(reassocTailBoundaryMapES A K L Q).range.starProjection ∘L
              (leftBoundaryMapES A (K + L) Q).range.starProjection -
            (groundSpaceES A (K + L + Q)).starProjection‖ ≤
          (1 - c * r ^ L)⁻¹ * (C * r ^ L) := by
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  obtain ⟨g, c, r, hg, hc, hr_pos, hr_lt_one, hc_eq, hGramInv⟩ :=
    hP.groundSpaceMapES_geometric_inverseGram_bounds hρ
  obtain ⟨C_T, hC_T, hTail⟩ := hP.tailVirtualMapES_norm_uniform
  have hKinfUnit : IsUnit Kinf := by
    simpa only [Kinf] using Matrix.gramReshuffle_fixedPointProj_isUnit hρ
  have hIinfUnit : IsUnit Iinf := by
    simpa only [Iinf] using hKinfUnit.ringInverse
  have hIinf_pos : 0 < ‖Iinf‖ := norm_pos_iff.mpr hIinfUnit.ne_zero
  let M := ‖Kinf‖ * ‖Iinf‖
  let C := 4 * (‖Iinf‖ * C_T * g * (M + 1))
  have hC : 0 < C := by
    dsimp only [C, M]
    positivity
  refine ⟨C, c, r, hC, hc, hr_pos, hr_lt_one, ?_⟩
  intro K L Q hL hsmall
  have hsmall_of_le {n : ℕ} (hLn : L ≤ n) : c * r ^ n < 1 := by
    have hpow : r ^ n ≤ r ^ L :=
      pow_le_pow_of_le_one hr_pos.le hr_lt_one.le hLn
    exact (mul_le_mul_of_nonneg_left hpow hc.le).trans_lt hsmall
  obtain ⟨hGramL, -⟩ := hGramInv L hL
  obtain ⟨hGramTail, hTailPoint⟩ := hGramInv (L + Q) (by omega)
  obtain ⟨hLocalTail, -, hInvTailRaw, -⟩ :=
    hTailPoint (hsmall_of_le (by omega))
  obtain ⟨hGramLeft, hLeftPoint⟩ := hGramInv (K + L) (by omega)
  obtain ⟨hLocalLeft, -, hInvLeftRaw, -⟩ :=
    hLeftPoint (hsmall_of_le (by omega))
  obtain ⟨hGramFull, hFullPoint⟩ := hGramInv (K + L + Q) (by omega)
  obtain ⟨hFull, -, hInvFullRaw, -⟩ :=
    hFullPoint (hsmall_of_le (by omega))
  let q := (1 - c * r ^ L)⁻¹
  let B := q * ‖Iinf‖
  have hq_pos : 0 < q := by
    dsimp only [q]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hInvTail : ‖ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (L + Q)) hLocalTail‖ ≤ B := by
    calc
      _ ≤ (1 - c * r ^ (L + Q))⁻¹ * ‖Iinf‖ := hInvTailRaw
      _ ≤ q * ‖Iinf‖ := by
        gcongr
        exact inverse_one_sub_geometric_le_base hc hr_pos hr_lt_one
          (by omega) hsmall
      _ = B := rfl
  have hInvLeft : ‖ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + L)) hLocalLeft‖ ≤ B := by
    calc
      _ ≤ (1 - c * r ^ (K + L))⁻¹ * ‖Iinf‖ := hInvLeftRaw
      _ ≤ q * ‖Iinf‖ := by
        gcongr
        exact inverse_one_sub_geometric_le_base hc hr_pos hr_lt_one
          (by omega) hsmall
      _ = B := rfl
  have hInvFull : ‖ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + L + Q)) hFull‖ ≤ B := by
    calc
      _ ≤ (1 - c * r ^ (K + L + Q))⁻¹ * ‖Iinf‖ := hInvFullRaw
      _ ≤ q * ‖Iinf‖ := by
        gcongr
        exact inverse_one_sub_geometric_le_base hc hr_pos hr_lt_one
          (by omega) hsmall
      _ = B := rfl
  have hSqrtTailLeft :
      Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + L)) hLocalLeft‖ ≤ B :=
    sqrt_mul_sqrt_le_of_le hB_nonneg hInvTail hInvLeft
  have hSqrtTailFull :
      Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (L + Q)) hLocalTail‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + L + Q)) hFull‖ ≤ B :=
    sqrt_mul_sqrt_le_of_le hB_nonneg hInvTail hInvFull
  have hpow {n : ℕ} (hLn : L ≤ n) : r ^ n ≤ r ^ L :=
    pow_le_pow_of_le_one hr_pos.le hr_lt_one.le hLn
  have hGramTailBase : ‖groundSpaceGram A (L + Q) - Kinf‖ ≤ g * r ^ L :=
    hGramTail.trans (mul_le_mul_of_nonneg_left (hpow (by omega)) hg.le)
  have hGramLeftBase : ‖groundSpaceGram A (K + L) - Kinf‖ ≤ g * r ^ L :=
    hGramLeft.trans (mul_le_mul_of_nonneg_left (hpow (by omega)) hg.le)
  have hGramFullBase : ‖groundSpaceGram A (K + L + Q) - Kinf‖ ≤ g * r ^ L :=
    hGramFull.trans (mul_le_mul_of_nonneg_left (hpow (by omega)) hg.le)
  have hCenterVirtual :
      ‖wholeIncrementCenteredResidualES A K L Q ρ
        (ne_of_gt hρ.trace_pos)‖ ≤ g * r ^ L * C_T := by
    calc
      _ ≤ ‖groundSpaceGram A L - Kinf‖ * ‖tailVirtualMapES A K‖ := by
        simpa only [Kinf] using
          hP.wholeIncrementCenteredResidualES_norm_le hρ K L Q
      _ ≤ (g * r ^ L) * C_T :=
        mul_le_mul hGramL (hTail K) (norm_nonneg _)
          (mul_nonneg hg.le (pow_nonneg hr_pos.le _))
  let base := ‖Iinf‖ * C_T * g * (M + 1)
  have hbase_nonneg : 0 ≤ base := by
    dsimp only [base, M]
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hFactorBounds : 1 ≤ M + 1 ∧ M ≤ M + 1 := by
    constructor <;> linarith
  obtain ⟨hOne_le, hM_le⟩ := hFactorBounds
  have hTerm (x : ℝ) (hx : x ≤ M + 1) :
      q * ((‖Iinf‖ * C_T * g * x) * r ^ L) ≤ q * (base * r ^ L) := by
    apply mul_le_mul_of_nonneg_left _ hq_pos.le
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr_pos.le _)
    dsimp only [base]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hx
      (mul_nonneg (mul_nonneg (norm_nonneg Iinf) hC_T.le) hg.le)
  have hCenter : ‖wholeIncrementCenteredProjectorResidualES A K L Q ρ hρ
      hLocalTail hLocalLeft‖ ≤ q * (base * r ^ L) := by
    calc
      _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (L + Q)) hLocalTail‖ *
          ‖wholeIncrementCenteredResidualES A K L Q ρ
            (ne_of_gt hρ.trace_pos)‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + L)) hLocalLeft‖ :=
        wholeIncrementCenteredProjectorResidualES_norm_le A K L Q ρ hρ
          hLocalTail hLocalLeft
      _ = (Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (L + Q)) hLocalTail‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + L)) hLocalLeft‖) *
          ‖wholeIncrementCenteredResidualES A K L Q ρ
            (ne_of_gt hρ.trace_pos)‖ := by ring
      _ ≤ B * ((g * r ^ L) * C_T) :=
        mul_le_mul hSqrtTailLeft hCenterVirtual (norm_nonneg _) hB_nonneg
      _ ≤ q * (base * r ^ L) := by
        dsimp only [B, base]
        calc
          q * ‖Iinf‖ * (g * r ^ L * C_T) =
              q * ((‖Iinf‖ * C_T * g) * r ^ L) := by ring
          _ ≤ q * (base * r ^ L) := by
            simpa only [mul_one] using hTerm 1 hOne_le
  have hQTail : ‖wholeIncrementTailFiniteGramCorrectionES A K L Q ρ hρ
      hLocalTail hFull‖ ≤ q * (base * r ^ L) := by
    calc
      _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (L + Q)) hLocalTail‖ *
          ‖groundSpaceGram A (L + Q) - Kinf‖ * ‖tailVirtualMapES A K‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + L + Q)) hFull‖ := by
        simpa only [Kinf] using wholeIncrementTailFiniteGramCorrectionES_norm_le
          A K L Q ρ hρ hLocalTail hFull
      _ = (Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (L + Q)) hLocalTail‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + L + Q)) hFull‖) *
          (‖groundSpaceGram A (L + Q) - Kinf‖ * ‖tailVirtualMapES A K‖) := by ring
      _ ≤ B * ((g * r ^ L) * C_T) := by
        apply mul_le_mul hSqrtTailFull
        · exact mul_le_mul hGramTailBase (hTail K) (norm_nonneg _)
            (mul_nonneg hg.le (pow_nonneg hr_pos.le _))
        · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
        · exact hB_nonneg
      _ ≤ q * (base * r ^ L) := by
        dsimp only [B, base]
        calc
          q * ‖Iinf‖ * (g * r ^ L * C_T) =
              q * ((‖Iinf‖ * C_T * g) * r ^ L) := by ring
          _ ≤ q * (base * r ^ L) := by
            simpa only [mul_one] using hTerm 1 hOne_le
  have hQFull : ‖wholeIncrementFullInverseGramCorrectionES A K L Q ρ hρ
      hLocalTail hFull‖ ≤ q * (base * r ^ L) := by
    calc
      _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (L + Q)) hLocalTail‖ * ‖Kinf‖ *
          ‖tailVirtualMapES A K‖ * ‖Iinf‖ *
          ‖groundSpaceGram A (K + L + Q) - Kinf‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + L + Q)) hFull‖ := by
        simpa only [Kinf, Iinf] using wholeIncrementFullInverseGramCorrectionES_norm_le
          A K L Q ρ hρ hLocalTail hFull
      _ = (Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (L + Q)) hLocalTail‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + L + Q)) hFull‖) *
          (M * ‖tailVirtualMapES A K‖ *
            ‖groundSpaceGram A (K + L + Q) - Kinf‖) := by
        dsimp only [M]
        ring
      _ ≤ B * (M * C_T * (g * r ^ L)) := by
        have hInner : M * ‖tailVirtualMapES A K‖ *
            ‖groundSpaceGram A (K + L + Q) - Kinf‖ ≤
            M * C_T * (g * r ^ L) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hTail K) hM_nonneg) hGramFullBase
            (norm_nonneg _) (mul_nonneg hM_nonneg hC_T.le)
        exact mul_le_mul hSqrtTailFull hInner
          (mul_nonneg (mul_nonneg hM_nonneg (norm_nonneg _)) (norm_nonneg _))
          hB_nonneg
      _ ≤ q * (base * r ^ L) := by
        dsimp only [B, base]
        calc
          q * ‖Iinf‖ * (M * C_T * (g * r ^ L)) =
              q * ((‖Iinf‖ * C_T * g * M) * r ^ L) := by ring
          _ ≤ q * (base * r ^ L) := hTerm M hM_le
  have hLeftVirtual : ‖leftVirtualMapES A Q‖ ≤ 1 :=
    leftVirtualMapES_norm_le_one_of_leftCanonical A Q hP.norm
  have hQLeft : ‖wholeIncrementLeftFiniteGramCorrectionES A K L Q ρ hρ
      hLocalTail hLocalLeft‖ ≤ q * (base * r ^ L) := by
    calc
      _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (L + Q)) hLocalTail‖ * ‖Kinf‖ *
          ‖tailVirtualMapES A K‖ * ‖Iinf‖ * ‖leftVirtualMapES A Q‖ *
          ‖groundSpaceGram A (K + L) - Kinf‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + L)) hLocalLeft‖ := by
        simpa only [Kinf, Iinf] using wholeIncrementLeftFiniteGramCorrectionES_norm_le
          A K L Q ρ hρ hLocalTail hLocalLeft
      _ = (Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (L + Q)) hLocalTail‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + L)) hLocalLeft‖) *
          (M * ‖tailVirtualMapES A K‖ * ‖leftVirtualMapES A Q‖ *
            ‖groundSpaceGram A (K + L) - Kinf‖) := by
        dsimp only [M]
        ring
      _ ≤ B * (M * C_T * 1 * (g * r ^ L)) := by
        have hPrefix : M * ‖tailVirtualMapES A K‖ * ‖leftVirtualMapES A Q‖ ≤
            M * C_T * 1 := by
          calc
            M * ‖tailVirtualMapES A K‖ * ‖leftVirtualMapES A Q‖ ≤
                M * C_T * ‖leftVirtualMapES A Q‖ := by
              gcongr
              exact hTail K
            _ ≤ M * C_T * 1 := by
              gcongr
        have hInner : M * ‖tailVirtualMapES A K‖ * ‖leftVirtualMapES A Q‖ *
            ‖groundSpaceGram A (K + L) - Kinf‖ ≤
            M * C_T * 1 * (g * r ^ L) :=
          mul_le_mul hPrefix hGramLeftBase (norm_nonneg _)
            (mul_nonneg (mul_nonneg hM_nonneg hC_T.le) zero_le_one)
        exact mul_le_mul hSqrtTailLeft hInner
          (mul_nonneg
            (mul_nonneg (mul_nonneg hM_nonneg (norm_nonneg _)) (norm_nonneg _))
            (norm_nonneg _)) hB_nonneg
      _ ≤ q * (base * r ^ L) := by
        dsimp only [B, base]
        calc
          q * ‖Iinf‖ * (M * C_T * 1 * (g * r ^ L)) =
              q * ((‖Iinf‖ * C_T * g * M) * r ^ L) := by ring
          _ ≤ q * (base * r ^ L) := hTerm M hM_le
  have hInjectiveDefect :
      ‖(ContinuousLinearMap.injectiveRangeProjector
          (reassocTailBoundaryMapES A K L Q)
            ((physicalReassocES (d := d) K L Q).injective.comp
              (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
                A K (L + Q) hLocalTail))).comp
          (ContinuousLinearMap.injectiveRangeProjector
            (leftBoundaryMapES A (K + L) Q)
              (leftBoundaryMapES_injective_of_groundSpaceMapES_injective
                A (K + L) Q hLocalLeft)) -
        ContinuousLinearMap.injectiveRangeProjector
          (groundSpaceMapES A (K + L + Q)) hFull‖ ≤
        q * (C * r ^ L) := by
    rw [wholeIncrement_injectiveRangeProjector_residual_eq_centered_sub_corrections
      A K L Q ρ hρ hLocalTail hLocalLeft hFull]
    calc
      _ ≤ ‖wholeIncrementCenteredProjectorResidualES A K L Q ρ hρ
              hLocalTail hLocalLeft‖ +
          ‖wholeIncrementTailFiniteGramCorrectionES A K L Q ρ hρ
            hLocalTail hFull‖ +
          ‖wholeIncrementFullInverseGramCorrectionES A K L Q ρ hρ
            hLocalTail hFull‖ +
          ‖wholeIncrementLeftFiniteGramCorrectionES A K L Q ρ hρ
            hLocalTail hLocalLeft‖ := by
        calc
          _ ≤ ‖wholeIncrementCenteredProjectorResidualES A K L Q ρ hρ
                hLocalTail hLocalLeft -
              wholeIncrementTailFiniteGramCorrectionES A K L Q ρ hρ
                hLocalTail hFull -
              wholeIncrementFullInverseGramCorrectionES A K L Q ρ hρ
                hLocalTail hFull‖ +
              ‖wholeIncrementLeftFiniteGramCorrectionES A K L Q ρ hρ
                hLocalTail hLocalLeft‖ := norm_sub_le _ _
          _ ≤ (‖wholeIncrementCenteredProjectorResidualES A K L Q ρ hρ
                hLocalTail hLocalLeft -
              wholeIncrementTailFiniteGramCorrectionES A K L Q ρ hρ
                hLocalTail hFull‖ +
              ‖wholeIncrementFullInverseGramCorrectionES A K L Q ρ hρ
                hLocalTail hFull‖) +
              ‖wholeIncrementLeftFiniteGramCorrectionES A K L Q ρ hρ
                hLocalTail hLocalLeft‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ ((‖wholeIncrementCenteredProjectorResidualES A K L Q ρ hρ
                hLocalTail hLocalLeft‖ +
              ‖wholeIncrementTailFiniteGramCorrectionES A K L Q ρ hρ
                hLocalTail hFull‖) +
              ‖wholeIncrementFullInverseGramCorrectionES A K L Q ρ hρ
                hLocalTail hFull‖) +
              ‖wholeIncrementLeftFiniteGramCorrectionES A K L Q ρ hρ
                hLocalTail hLocalLeft‖ := by
            gcongr
            exact norm_sub_le _ _
          _ = _ := by ring
      _ ≤ q * (base * r ^ L) + q * (base * r ^ L) +
          q * (base * r ^ L) + q * (base * r ^ L) := by gcongr
      _ = q * (C * r ^ L) := by
        dsimp only [C, base]
        ring
  simpa only [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection,
    range_groundSpaceMapES, q] using hInjectiveDefect

/-- A spectator-uniform geometric-over-denominator estimate for the open-chain
C3 projector defect. The constants are reconstructed from the limiting Gram
metric, geometric Gram convergence, and uniform virtual-word bounds. -/
theorem IsPrimitiveMPS.openChain_groundProjection_defect_le_geometric
    [NeZero D] {A : MPSTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ C c r : ℝ,
      0 < C ∧ 0 < c ∧ 0 < r ∧ r < 1 ∧
      ∀ K l : ℕ, 1 ≤ l → c * r ^ l < 1 →
        ‖openChainTailGroundProjectionES A K (l + 1) ∘L
              openChainLeftGroundProjectionES A (K + l) -
            (groundSpaceES A (K + l + 1)).starProjection‖ ≤
          (1 - c * r ^ l)⁻¹ * (C * r ^ l) := by
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Iinf := Ring.inverse Kinf
  obtain ⟨g, c, r, hg, hc, hr_pos, hr_lt_one, hc_eq, hGramInv⟩ :=
    hP.groundSpaceMapES_geometric_inverseGram_bounds hρ
  obtain ⟨C_T, hC_T, hTail⟩ := hP.tailVirtualMapES_norm_uniform
  have hKinfUnit : IsUnit Kinf := by
    simpa only [Kinf] using Matrix.gramReshuffle_fixedPointProj_isUnit hρ
  have hIinfUnit : IsUnit Iinf := by
    simpa only [Iinf] using hKinfUnit.ringInverse
  have hIinf_pos : 0 < ‖Iinf‖ := norm_pos_iff.mpr hIinfUnit.ne_zero
  let J := ‖leftVirtualMapES A 1‖
  let M := ‖Kinf‖ * ‖Iinf‖
  let C := 4 * (‖Iinf‖ * C_T * g * (J + 1) * (M + 1))
  have hC : 0 < C := by
    dsimp only [C, J, M]
    positivity
  refine ⟨C, c, r, hC, hc, hr_pos, hr_lt_one, ?_⟩
  intro K l hl hsmall
  obtain ⟨hsmallTail, hsmallLeft, hsmallFull⟩ :=
    geometric_smallness_at_c3_lengths hc hr_pos hr_lt_one hsmall K
  obtain ⟨hGramL, -⟩ := hGramInv l hl
  obtain ⟨hGramTail, hTailPoint⟩ := hGramInv (l + 1) (by omega)
  obtain ⟨hLocalTail, -, hInvTailRaw, -⟩ := hTailPoint hsmallTail
  obtain ⟨hGramLeft, hLeftPoint⟩ := hGramInv (K + l) (by omega)
  obtain ⟨hLocalLeft, -, hInvLeftRaw, -⟩ := hLeftPoint hsmallLeft
  obtain ⟨hGramFull, hFullPoint⟩ := hGramInv (K + l + 1) (by omega)
  obtain ⟨hFull, -, hInvFullRaw, -⟩ := hFullPoint hsmallFull
  let q := (1 - c * r ^ l)⁻¹
  let B := q * ‖Iinf‖
  have hq_pos : 0 < q := by
    dsimp only [q]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hInvTail : ‖ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (l + 1)) hLocalTail‖ ≤ B := by
    calc
      _ ≤ (1 - c * r ^ (l + 1))⁻¹ * ‖Iinf‖ := hInvTailRaw
      _ ≤ q * ‖Iinf‖ := by
        gcongr
        exact inverse_one_sub_geometric_le_base hc hr_pos hr_lt_one
          (by omega) hsmall
      _ = B := rfl
  have hInvLeft : ‖ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l)) hLocalLeft‖ ≤ B := by
    calc
      _ ≤ (1 - c * r ^ (K + l))⁻¹ * ‖Iinf‖ := hInvLeftRaw
      _ ≤ q * ‖Iinf‖ := by
        gcongr
        exact inverse_one_sub_geometric_le_base hc hr_pos hr_lt_one
          (by omega) hsmall
      _ = B := rfl
  have hInvFull : ‖ContinuousLinearMap.inverseGram
      (groundSpaceMapES A (K + l + 1)) hFull‖ ≤ B := by
    calc
      _ ≤ (1 - c * r ^ (K + l + 1))⁻¹ * ‖Iinf‖ := hInvFullRaw
      _ ≤ q * ‖Iinf‖ := by
        gcongr
        exact inverse_one_sub_geometric_le_base hc hr_pos hr_lt_one
          (by omega) hsmall
      _ = B := rfl
  have hSqrtTailLeft :
      Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (l + 1)) hLocalTail‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + l)) hLocalLeft‖ ≤ B :=
    sqrt_mul_sqrt_le_of_le hB_nonneg hInvTail hInvLeft
  have hSqrtTailFull :
      Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (l + 1)) hLocalTail‖ *
        Real.sqrt ‖ContinuousLinearMap.inverseGram
          (groundSpaceMapES A (K + l + 1)) hFull‖ ≤ B :=
    sqrt_mul_sqrt_le_of_le hB_nonneg hInvTail hInvFull
  have hpow {n : ℕ} (hln : l ≤ n) : r ^ n ≤ r ^ l :=
    pow_le_pow_of_le_one hr_pos.le hr_lt_one.le hln
  have hGramTailBase : ‖groundSpaceGram A (l + 1) - Kinf‖ ≤ g * r ^ l :=
    hGramTail.trans (mul_le_mul_of_nonneg_left (hpow (by omega)) hg.le)
  have hGramLeftBase : ‖groundSpaceGram A (K + l) - Kinf‖ ≤ g * r ^ l :=
    hGramLeft.trans (mul_le_mul_of_nonneg_left (hpow (by omega)) hg.le)
  have hGramFullBase : ‖groundSpaceGram A (K + l + 1) - Kinf‖ ≤ g * r ^ l :=
    hGramFull.trans (mul_le_mul_of_nonneg_left (hpow (by omega)) hg.le)
  have hCenterVirtual : ‖c3CenteredVirtualResidualES A K l ρ hρ‖ ≤
      J * (g * r ^ l) * C_T := by
    calc
      _ ≤ ‖leftVirtualMapES A 1‖ *
          ‖groundSpaceGram A l - Kinf‖ * ‖tailVirtualMapES A K‖ := by
        simpa only [Kinf] using c3_centeredVirtualResidualES_norm_le A K l ρ hρ
      _ ≤ J * (g * r ^ l) * C_T := by
        dsimp only [J]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hGramL (norm_nonneg _)
        · exact hTail K
        · exact norm_nonneg _
        · exact mul_nonneg (norm_nonneg _)
            (mul_nonneg hg.le (pow_nonneg hr_pos.le _))
  let base := ‖Iinf‖ * C_T * g * (J + 1) * (M + 1)
  have hbase_nonneg : 0 ≤ base := by
    dsimp only [base, J, M]
    positivity
  have hJ_nonneg : 0 ≤ J := by
    dsimp only [J]
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hFactorBounds :
      J ≤ (J + 1) * (M + 1) ∧
      1 ≤ (J + 1) * (M + 1) ∧
      M ≤ (J + 1) * (M + 1) ∧
      J * M ≤ (J + 1) * (M + 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hJ_nonneg, hM_nonneg, mul_nonneg hJ_nonneg hM_nonneg]
  obtain ⟨hJ_le, hOne_le, hM_le, hJM_le⟩ := hFactorBounds
  have hTerm (x : ℝ) (hx : x ≤ (J + 1) * (M + 1)) :
      q * ((‖Iinf‖ * C_T * g * x) * r ^ l) ≤ q * (base * r ^ l) := by
    apply mul_le_mul_of_nonneg_left _ hq_pos.le
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr_pos.le _)
    dsimp only [base]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hx
      (mul_nonneg (mul_nonneg (norm_nonneg Iinf) hC_T.le) hg.le)
  have hCenter : ‖c3CenteredProjectorResidualES A K l ρ hρ
      hLocalTail hLocalLeft‖ ≤ q * (base * r ^ l) := by
    calc
      _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (l + 1)) hLocalTail‖ *
          ‖c3CenteredVirtualResidualES A K l ρ hρ‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + l)) hLocalLeft‖ :=
        c3CenteredProjectorResidualES_norm_le A K l ρ hρ
          hLocalTail hLocalLeft
      _ = (Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (l + 1)) hLocalTail‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + l)) hLocalLeft‖) *
          ‖c3CenteredVirtualResidualES A K l ρ hρ‖ := by ring
      _ ≤ B * (J * (g * r ^ l) * C_T) :=
        mul_le_mul hSqrtTailLeft hCenterVirtual (norm_nonneg _) hB_nonneg
      _ ≤ q * (base * r ^ l) := by
        dsimp only [B, base]
        calc
          q * ‖Iinf‖ * (J * (g * r ^ l) * C_T) =
              q * ((‖Iinf‖ * C_T * g * J) * r ^ l) := by ring
          _ ≤ q * (base * r ^ l) := hTerm J hJ_le
  have hQTail : ‖c3TailFiniteGramCorrectionES A K l ρ hρ
      hLocalTail hLocalLeft hFull‖ ≤ q * (base * r ^ l) := by
    calc
      _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (l + 1)) hLocalTail‖ *
          ‖groundSpaceGram A (l + 1) - Kinf‖ * ‖tailVirtualMapES A K‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + l + 1)) hFull‖ := by
        simpa only [Kinf] using c3TailFiniteGramCorrectionES_norm_le
          A K l ρ hρ hLocalTail hLocalLeft hFull
      _ = (Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (l + 1)) hLocalTail‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + l + 1)) hFull‖) *
          (‖groundSpaceGram A (l + 1) - Kinf‖ * ‖tailVirtualMapES A K‖) := by ring
      _ ≤ B * ((g * r ^ l) * C_T) := by
        apply mul_le_mul hSqrtTailFull
        · exact mul_le_mul hGramTailBase (hTail K) (norm_nonneg _)
            (mul_nonneg hg.le (pow_nonneg hr_pos.le _))
        · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
        · exact hB_nonneg
      _ ≤ q * (base * r ^ l) := by
        dsimp only [B, base]
        calc
          q * ‖Iinf‖ * (g * r ^ l * C_T) =
              q * ((‖Iinf‖ * C_T * g) * r ^ l) := by ring
          _ ≤ q * (base * r ^ l) := by
            simpa only [mul_one] using hTerm 1 hOne_le
  have hQFull : ‖c3FullInverseGramCorrectionES A K l ρ hρ
      hLocalTail hLocalLeft hFull‖ ≤ q * (base * r ^ l) := by
    calc
      _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (l + 1)) hLocalTail‖ * ‖Kinf‖ *
          ‖tailVirtualMapES A K‖ * ‖Iinf‖ *
          ‖groundSpaceGram A (K + l + 1) - Kinf‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + l + 1)) hFull‖ := by
        simpa only [Kinf, Iinf] using c3FullInverseGramCorrectionES_norm_le
          A K l ρ hρ hLocalTail hLocalLeft hFull
      _ = (Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (l + 1)) hLocalTail‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + l + 1)) hFull‖) *
          (‖Kinf‖ * ‖Iinf‖ * ‖tailVirtualMapES A K‖ *
            ‖groundSpaceGram A (K + l + 1) - Kinf‖) := by ring
      _ ≤ B * (M * C_T * (g * r ^ l)) := by
        have hInner : M * ‖tailVirtualMapES A K‖ *
            ‖groundSpaceGram A (K + l + 1) - Kinf‖ ≤
            M * C_T * (g * r ^ l) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hTail K) hM_nonneg) hGramFullBase
            (norm_nonneg _) (mul_nonneg hM_nonneg hC_T.le)
        exact mul_le_mul hSqrtTailFull hInner
          (mul_nonneg (mul_nonneg hM_nonneg (norm_nonneg _)) (norm_nonneg _))
          hB_nonneg
      _ ≤ q * (base * r ^ l) := by
        dsimp only [B, base]
        calc
          q * ‖Iinf‖ * (M * C_T * (g * r ^ l)) =
              q * ((‖Iinf‖ * C_T * g * M) * r ^ l) := by ring
          _ ≤ q * (base * r ^ l) := hTerm M hM_le
  have hQLeft : ‖c3LeftFiniteGramCorrectionES A K l ρ hρ
      hLocalTail hLocalLeft‖ ≤ q * (base * r ^ l) := by
    calc
      _ ≤ Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (l + 1)) hLocalTail‖ * ‖Kinf‖ *
          ‖tailVirtualMapES A K‖ * ‖Iinf‖ * ‖leftVirtualMapES A 1‖ *
          ‖groundSpaceGram A (K + l) - Kinf‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + l)) hLocalLeft‖ := by
        simpa only [Kinf, Iinf] using c3LeftFiniteGramCorrectionES_norm_le
          A K l ρ hρ hLocalTail hLocalLeft
      _ = (Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (l + 1)) hLocalTail‖ *
          Real.sqrt ‖ContinuousLinearMap.inverseGram
            (groundSpaceMapES A (K + l)) hLocalLeft‖) *
          (M * ‖tailVirtualMapES A K‖ * J *
            ‖groundSpaceGram A (K + l) - Kinf‖) := by
        dsimp only [M, J]
        ring
      _ ≤ B * (M * C_T * J * (g * r ^ l)) := by
        have hInner : M * ‖tailVirtualMapES A K‖ * J *
            ‖groundSpaceGram A (K + l) - Kinf‖ ≤
            M * C_T * J * (g * r ^ l) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hTail K) hM_nonneg) hJ_nonneg)
            hGramLeftBase (norm_nonneg _)
            (mul_nonneg (mul_nonneg hM_nonneg hC_T.le) hJ_nonneg)
        exact mul_le_mul hSqrtTailLeft hInner
          (mul_nonneg
            (mul_nonneg (mul_nonneg hM_nonneg (norm_nonneg _)) hJ_nonneg)
            (norm_nonneg _)) hB_nonneg
      _ ≤ q * (base * r ^ l) := by
        dsimp only [B, base]
        calc
          q * ‖Iinf‖ * (M * C_T * J * (g * r ^ l)) =
              q * ((‖Iinf‖ * C_T * g * J * M) * r ^ l) := by ring
          _ ≤ q * (base * r ^ l) := by
            simpa only [mul_assoc] using hTerm (J * M) hJM_le
  have hInjectiveDefect :
      ‖(ContinuousLinearMap.injectiveRangeProjector
          (tailBoundaryMapES A K (l + 1))
            (tailBoundaryMapES_injective_of_groundSpaceMapES_injective
              A K (l + 1) hLocalTail)).comp
          (ContinuousLinearMap.injectiveRangeProjector
            (leftBoundaryMapES A (K + l) 1)
              (leftBoundaryMapES_injective_of_groundSpaceMapES_injective
                A (K + l) 1 hLocalLeft)) -
        ContinuousLinearMap.injectiveRangeProjector
          (groundSpaceMapES A (K + l + 1)) hFull‖ ≤
        q * (C * r ^ l) := by
    rw [c3_injectiveRangeProjector_residual_eq_centered_sub_corrections
      A K l ρ hρ hLocalTail hLocalLeft hFull]
    calc
      _ ≤ ‖c3CenteredProjectorResidualES A K l ρ hρ hLocalTail hLocalLeft‖ +
          ‖c3TailFiniteGramCorrectionES A K l ρ hρ
            hLocalTail hLocalLeft hFull‖ +
          ‖c3FullInverseGramCorrectionES A K l ρ hρ
            hLocalTail hLocalLeft hFull‖ +
          ‖c3LeftFiniteGramCorrectionES A K l ρ hρ hLocalTail hLocalLeft‖ := by
        calc
          _ ≤ ‖c3CenteredProjectorResidualES A K l ρ hρ
                hLocalTail hLocalLeft -
              c3TailFiniteGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft hFull -
              c3FullInverseGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft hFull‖ +
              ‖c3LeftFiniteGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft‖ := norm_sub_le _ _
          _ ≤ (‖c3CenteredProjectorResidualES A K l ρ hρ
                hLocalTail hLocalLeft -
              c3TailFiniteGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft hFull‖ +
              ‖c3FullInverseGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft hFull‖) +
              ‖c3LeftFiniteGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ ((‖c3CenteredProjectorResidualES A K l ρ hρ
                hLocalTail hLocalLeft‖ +
              ‖c3TailFiniteGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft hFull‖) +
              ‖c3FullInverseGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft hFull‖) +
              ‖c3LeftFiniteGramCorrectionES A K l ρ hρ
                hLocalTail hLocalLeft‖ := by
            gcongr
            exact norm_sub_le _ _
          _ = _ := by ring
      _ ≤ q * (base * r ^ l) + q * (base * r ^ l) +
          q * (base * r ^ l) + q * (base * r ^ l) := by gcongr
      _ = q * (C * r ^ l) := by
        dsimp only [C, base]
        ring
  simpa only [openChainTailGroundProjectionES, openChainLeftGroundProjectionES,
    ContinuousLinearMap.injectiveRangeProjector_eq_starProjection,
    range_tailBoundaryMapES, range_leftBoundaryMapES_one,
    range_groundSpaceMapES, q] using hInjectiveDefect

end MPSTensor
