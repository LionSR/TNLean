/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.HighEnergyMass

/-!
# Energy after projection onto the disconnected low spectrum

The normalized chain assumptions imply the projected-energy comparison
used in AKLV, arXiv:1301.1162v1, Lemma 6.5(2). The cross term is taken
with its unsquared modulus, as corrected in the accompanying paper-gap note.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

/-- Dropping the positive energy of one summand costs at most twice the
modulus of the cross term. Auxiliary to AKLV, Lemma 6.5(2). -/
theorem re_inner_left_le_energy_add_cross {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : E →L[ℂ] E) (hK : K.IsPositive) (p q : E) :
    (⟪p, K p⟫_ℂ).re ≤ (⟪p + q, K (p + q)⟫_ℂ).re + 2 * ‖⟪p, K q⟫_ℂ‖ := by
  have hcross : (⟪q, K p⟫_ℂ).re = (⟪p, K q⟫_ℂ).re := by
    calc
      _ = (⟪K p, q⟫_ℂ).re := by
        simpa only [RCLike.re_to_complex] using inner_re_symm (𝕜 := ℂ) q (K p)
      _ = _ := congrArg Complex.re (hK.isSymmetric p q)
  have hsplit : (⟪p + q, K (p + q)⟫_ℂ).re =
      (⟪p, K p⟫_ℂ).re + (⟪q, K q⟫_ℂ).re + 2 * (⟪p, K q⟫_ℂ).re := by
    simp only [map_add, inner_add_left, inner_add_right, Complex.add_re, hcross]
    ring
  have hnonneg := hK.re_inner_nonneg_right q
  change 0 ≤ (⟪q, K q⟫_ℂ).re at hnonneg
  have habs := Complex.abs_re_le_norm (⟪p, K q⟫_ℂ)
  have hneg := neg_abs_le (⟪p, K q⟫_ℂ).re
  rw [hsplit]
  linarith

end ContinuousLinearMap

namespace TNLean.MPS.AreaLaw.AKLV

/-- Positivity and domination by the original Hamiltonian require no
budget for the middle term. Auxiliary to AKLV, Sections 6.1 and 6.3. -/
theorem twoSidedEnergyTruncation_posSemidef_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (L M R : Matrix n n ℂ) (hL : L.PosSemidef) (hM : M.PosSemidef)
    (hR : R.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    (twoSidedEnergyTruncation L M R t).PosSemidef ∧
      twoSidedEnergyTruncation L M R t ≤ L + M + R := by
  have hcap : M ≤ (‖M‖ : ℂ) • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using
      IsSelfAdjoint.le_algebraMap_norm_self M hM.isHermitian.isSelfAdjoint
  obtain ⟨hpos, hle, _⟩ := twoSidedEnergyTruncation_bounds L M R hL hM hR t ‖M‖ ht hcap
  exact ⟨hpos, hle⟩

/-- The original regional commutations imply commutation of the clipped
disconnected Hamiltonian with the original disconnected sum.
Auxiliary to AKLV, arXiv:1301.1162v1, Section 6.3. -/
theorem commute_twoSidedEnergyTruncation_disconnected
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R : Matrix n n ℂ) (hLN : Commute L N) (hLR : Commute L R)
    (hNR : Commute N R) (t : ℝ) :
    Commute (twoSidedEnergyTruncation L N R t) (L + N + R) := by
  have hLB := ((Commute.refl L).add_right hLN).add_right hLR
  have hNB := (hLN.symm.add_right (Commute.refl N)).add_right hNR
  have hRB := (hLR.symm.add_right hNR.symm).add_right (Commute.refl R)
  exact ((hLB.cfc_real (fun x : ℝ ↦ min x t)).add_left hNB).add_left
    (hRB.cfc_real (fun x : ℝ ↦ min x t))

/-- The actual clipping agrees with the original operator below the
cutoff of the disconnected sum. All reducing-subspace and order
conditions are derived from the original positive regional blocks.
AKLV, arXiv:1301.1162v1, equation (8). -/
theorem twoSidedEnergyTruncation_mul_lowProjection_eq_of_commuting
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hLN : Commute L N) (hLR : Commute L R)
    (hNR : Commute N R) (t : ℝ) :
    twoSidedEnergyTruncation L (N + A) R t *
        (1 - Matrix.spectralProjectionGE (L + N + R) t) =
      (L + (N + A) + R) * (1 - Matrix.spectralProjectionGE (L + N + R) t) := by
  have hLB := ((Commute.refl L).add_right hLN).add_right hLR
  have hRB := (hLR.symm.add_right hNR.symm).add_right (Commute.refl R)
  apply twoSidedEnergyTruncation_mul_lowProjection_eq L (N + A) R (L + N + R)
    hL.isHermitian hR.isHermitian ((hL.isHermitian.add hN.isHermitian).add hR.isHermitian)
    hLB hRB
  · exact (le_add_of_nonneg_right hN.nonneg).trans (le_add_of_nonneg_right hR.nonneg)
  · exact le_add_of_nonneg_left (add_nonneg hL.nonneg hN.nonneg)

/-- Only the boundary coupling contributes to the low-high cross block
of the actual clipped Hamiltonian. AKLV, Lemma 6.5(2). -/
theorem lowProjection_mul_clipped_mul_highProjection_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.IsHermitian) (hN : N.IsHermitian)
    (hR : R.IsHermitian) (hLN : Commute L N) (hLR : Commute L R)
    (hNR : Commute N R) (t : ℝ) :
    let Q := Matrix.spectralProjectionGE (L + N + R) t
    (1 - Q) * twoSidedEnergyTruncation L (N + A) R t * Q = (1 - Q) * A * Q := by
  intro Q
  let K₀ := twoSidedEnergyTruncation L N R t
  have hK : twoSidedEnergyTruncation L (N + A) R t = K₀ + A := by
    dsimp [K₀, twoSidedEnergyTruncation]
    abel
  have hcomm : Commute K₀ Q :=
    ((commute_twoSidedEnergyTruncation_disconnected L N R hLN hLR hNR t).symm.cfc_real
      (fun x : ℝ ↦ if t ≤ x then 1 else 0)).symm
  have hQQ := ((hL.add hN).add hR).isStarProjection_spectralProjectionGE t
  have hPQ : (1 - Q) * Q = 0 := by
    rw [sub_mul, one_mul, hQQ.isIdempotentElem.eq, sub_self]
  rw [hK, mul_add, add_mul, mul_assoc, hcomm.eq, ← mul_assoc, hPQ, zero_mul, zero_add]

/-- The projected energy of the original Hamiltonian is bounded by the
actual clipped energy plus four times the high-energy norm. This is the explicit corrected
version of AKLV, arXiv:1301.1162v1, Lemma 6.5(2), for unit vectors.
No projection norm estimate or compatibility identity is assumed. -/
theorem projected_energy_le_clipped_energy_add_tail
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let P := 1 - Matrix.spectralProjectionGE (L + N + R) t
    let H := L + (N + A) + R
    let K := twoSidedEnergyTruncation L (N + A) R t
    (⟪ι P x, ι H (ι P x)⟫_ℂ).re ≤ (⟪x, ι K x⟫_ℂ).re +
      4 * ‖ι (Matrix.spectralProjectionGE (L + N + R) t) x‖ := by
  intro ι P H K
  let Q := Matrix.spectralProjectionGE (L + N + R) t
  have hP : IsStarProjection (ι P) :=
    (((hL.isHermitian.add hN.isHermitian).add hR.isHermitian)
      |>.isStarProjection_spectralProjectionGE t).one_sub.map ι
  have hpos : (ι K).IsPositive :=
    (twoSidedEnergyTruncation_posSemidef_le L (N + A) R hL (hN.add hA) hR t ht.le).1
      |>.isPositive_toEuclideanCLM
  have hsplit : ι P x + ι Q x = x := by
    rw [← _root_.add_apply, ← map_add, sub_add_cancel, map_one, one_apply_eq_self]
  have hlow : ι H (ι P x) = ι K (ι P x) := by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
    exact congrArg (fun M : Matrix n n ℂ ↦ ι M x)
      (twoSidedEnergyTruncation_mul_lowProjection_eq_of_commuting
        L N R A hL hN hR hLN hLR hNR t).symm
  have hcross : ⟪ι P x, ι K (ι Q x)⟫_ℂ = ⟪ι P x, ι A (ι Q x)⟫_ℂ := by
    rw [ContinuousLinearMap.IsStarProjection.inner_apply_left hP,
      ContinuousLinearMap.IsStarProjection.inner_apply_left hP]
    simp only [← mul_apply_eq_comp, ← map_mul]
    rw [← Matrix.mul_assoc, lowProjection_mul_clipped_mul_highProjection_eq
      L N R A hL.isHermitian hN.isHermitian hR.isHermitian hLN hLR hNR t]
    simp only [Matrix.mul_assoc]
    rfl
  have henergy := ContinuousLinearMap.re_inner_left_le_energy_add_cross
    (ι K) hpos (ι P x) (ι Q x)
  rw [hsplit, hcross] at henergy
  have hnormA : ‖A‖ ≤ 2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap A (by norm_num) hA.nonneg).mpr
    simpa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using hAcap
  have hnormP : ‖ι P x‖ ≤ 1 := by
    simpa only [hx] using ContinuousLinearMap.IsStarProjection.norm_apply_le hP x
  have hbound : ‖⟪ι P x, ι A (ι Q x)⟫_ℂ‖ ≤ 2 * ‖ι Q x‖ := by
    calc
      _ ≤ ‖ι P x‖ * ‖ι A (ι Q x)‖ := norm_inner_le_norm _ _
      _ ≤ 1 * (2 * ‖ι Q x‖) :=
        mul_le_mul hnormP (((ι A).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hnormA (norm_nonneg _)))
          (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [hlow]
  linarith

/-- The square-root form of AKLV, Lemma 6.5(2), with explicit constant four. -/
theorem projected_energy_le_clipped_energy_add_sqrt
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let P := 1 - Matrix.spectralProjectionGE (L + N + R) t
    let H := L + (N + A) + R
    let K := twoSidedEnergyTruncation L (N + A) R t
    (⟪ι P x, ι H (ι P x)⟫_ℂ).re ≤ (⟪x, ι K x⟫_ℂ).re +
      4 * Real.sqrt ((⟪x, ι K x⟫_ℂ).re / t) := by
  intro ι P H K
  have he := projected_energy_le_clipped_energy_add_tail
    L N R A hL hN hR hA hLN hLR hNR hAcap t ht x hx
  have ht := norm_highProjection_le_sqrt_clipped_energy
    L N R A hL hN hR hA hLN hLR hNR t ht x
  exact he.trans (by linarith)

end TNLean.MPS.AreaLaw.AKLV
