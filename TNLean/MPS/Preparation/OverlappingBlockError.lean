/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockOverlap

/-!
# Overlaps after the partial isometry, and the final estimate of Lemma 1'(ii)

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound
the error of the approximating state `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of eq. (S7) for a tensor that is not
normal. This file collects the steps of that proof that do not depend on how the blocks of the
tensor overlap: after `V^{⊗M}` the overlap of the approximating state with the target is a
combination of the overlaps `⟨φ_M(P_{σ'_j})|φ_M(P)⟩` of the positive part `P` of the whole
blocked tensor with fixed-point tensors (`sum_star_nonNormalApproxVector_mul_mpv`); `V^{⊗M}` does
not increase norms, so normalizing the approximating state can only increase the overlap
(`inv_mul_norm_le_norm_of_sum_norm_sq_le_one`); and two elementary estimates combine the overlaps
of the blocks with the norm of the target. The error bounds themselves are
`MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum` and its corollaries in
`TNLean.MPS.Preparation.BlockSumError`.

## Main declarations

* `MPSTensor.sum_star_tensorPower_polarIso_mulVec_mul_mpv`,
  `MPSTensor.sum_star_nonNormalApproxVector_mul_mpv` — the unnormalized overlap after `V^{⊗M}`.
* `MPSTensor.inv_mul_norm_le_norm_of_sum_norm_sq_le_one` — normalizing a vector of norm at most
  one does not decrease an overlap.
* `MPSTensor.one_sub_norm_div_le_of_norm_sub_le`, `MPSTensor.one_sub_le_mul_mul_exp_div_of_one_le`,
  `MPSTensor.one_sub_le_mul_mul_exp_div_of_sum_le` — the elementary estimates combining the errors.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S12) and Lemma 1'(ii)
  (`eq:fid_err_gen_non_normal`).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix

namespace MPSTensor

variable {d D b : ℕ}

/-! ### The overlap after the partial isometry -/

/-- **The overlap after `V^{⊗M}`.** For any tensor `A` and any vector `F` on the bond pairs of
`M` sites, `V^{⊗M} F` has overlap `⟨F|φ_M(P)⟩` with the periodic state of `A` on `N = qM`
sites, where `V P` is the polar decomposition of the `q`-site blocked tensor and `φ_M(P)` is the
periodic state of the positive part read as a tensor. The source uses `V†V = Π` and `Π P = P`
(arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors"); no injectivity is needed. -/
theorem sum_star_tensorPower_polarIso_mulVec_mul_mpv (A : MPSTensor d D) (q M : ℕ)
    (F : (Fin M → Fin D × Fin D) → ℂ) :
    ∑ τ, star ((tensorPower M (Matrix.polarIso (physicalMatrix (blockTensor A q))) *ᵥ F) τ) *
        mpv A (blockedConfigEquiv d M q τ) =
      ∑ c, star (F c) *
        mpv (polarPosTensor (blockTensor A q)) fun k => (virtualPairEquiv D).symm (c k) := by
  set Bq := blockTensor A q
  set V := Matrix.polarIso (physicalMatrix Bq)
  set e : (Fin M → Fin (D * D)) ≃ (Fin M → Fin D × Fin D) :=
    Equiv.piCongrRight fun _ => virtualPairEquiv D
  set m : (Fin M → Fin D × Fin D) → ℂ := fun c => mpv (polarPosTensor Bq) (e.symm c)
  have hT : ∀ τ, mpv A (blockedConfigEquiv d M q τ) = (tensorPower M V *ᵥ m) τ := by
    intro τ
    rw [mpv_blockedConfigEquiv_eq_sum_polar]
    simp only [mulVec, dotProduct, tensorPower, of_apply, m]
    exact Fintype.sum_equiv e _ _ fun τ' => by
      simp [e, polarIsoMatrix, V, Bq]
  have hfixP : tensorPower M (Vᴴ * V) *ᵥ m = m := by
    funext c
    have h : mpv (rotatePhysical (polarSupportMatrix Bq) (polarPosTensor Bq)) (e.symm c) =
        mpv (polarPosTensor Bq) (e.symm c) := by rw [rotatePhysical_polarSupportMatrix]
    rw [mpv_rotatePhysical] at h
    change _ = mpv (polarPosTensor Bq) (e.symm c)
    rw [← h, Matrix.conjTranspose_polarIso_mul_polarIso]
    simp only [mulVec, dotProduct, tensorPower, of_apply, m]
    refine (Fintype.sum_equiv e.symm _ _ fun c' => ?_)
    simp [e, polarSupportMatrix, Bq]
  simp only [hT]
  rw [sum_star_tensorPower_mulVec_mul, hfixP]
  rfl

/-- **The overlap after `V^{⊗M}`.** For any tensor `A` and pairs `ω_j` of matrices `σ'_j`, the
unnormalized approximating state `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of arXiv:2307.01696, Supplemental
Material, eq. (S7), has overlap `∑ⱼ conj(αⱼ) ⟨φ_M(P_{σ'_j})|φ_M(P)⟩` with the periodic state of `A`
on `N = qM` sites, where `P` is the positive part of the `q`-site blocked tensor and `P_{σ'_j}`
the fixed-point tensor of `σ'_j` (`sum_star_tensorPower_polarIso_mulVec_mul_mpv`). -/
theorem sum_star_nonNormalApproxVector_mul_mpv (A : MPSTensor d D) (q M : ℕ) [NeZero M]
    (α : Fin b → ℂ) (σ' : Fin b → Matrix (Fin D) (Fin D) ℂ) :
    ∑ τ, star (nonNormalApproxVector A q M α (fun j => fixedPointPair (σ' j)) τ) *
        mpv A (blockedConfigEquiv d M q τ) =
      ∑ j, star (α j) *
        mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor (σ' j)) M := by
  set Bq := blockTensor A q
  set e : (Fin M → Fin (D * D)) ≃ (Fin M → Fin D × Fin D) :=
    Equiv.piCongrRight fun _ => virtualPairEquiv D
  set m : (Fin M → Fin D × Fin D) → ℂ := fun c => mpv (polarPosTensor Bq) (e.symm c)
  have hpair : ∀ j, ∑ c, star (pairProductState (fixedPointPair (σ' j)) c) * m c =
      mpvOverlap (polarPosTensor Bq) (fixedPointTensor (σ' j)) M := fun j => by
    rw [mpvOverlap]
    refine (Fintype.sum_equiv e.symm _ _ fun c => ?_)
    rw [mpv_fixedPointTensor, mul_comm]
    simp [e, m, virtualPairEquiv]
  rw [nonNormalApproxVector, sum_star_tensorPower_polarIso_mulVec_mul_mpv]
  change ∑ c, star (nonNormalFixedPointState α (fun j => fixedPointPair (σ' j)) c) * m c = _
  calc ∑ c, star (nonNormalFixedPointState α (fun j => fixedPointPair (σ' j)) c) * m c
      = ∑ j, star (α j) * ∑ c, star (pairProductState (fixedPointPair (σ' j)) c) * m c := by
        simp only [nonNormalFixedPointState, star_sum, star_mul', Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring
    _ = _ := by simp only [hpair]

/-- **Normalizing a short vector does not decrease an overlap.** If `∑_τ |v_τ|² ≤ 1` and `t ≥ 0`,
then `t⁻¹ |⟨v|w⟩| ≤ |(‖v‖⁻¹ t⁻¹) ⟨v|w⟩|`: the approximating vector `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` has norm at
most one because `V^{⊗M}` does not increase norms, so normalizing it can only increase its
overlap with the target (arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii)). -/
theorem inv_mul_norm_le_norm_of_sum_norm_sq_le_one {ι : Type*} [Fintype ι] (v w : ι → ℂ)
    (hv : ∑ τ, ‖v τ‖ ^ 2 ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    t⁻¹ * ‖∑ τ, star (v τ) * w τ‖ ≤
      ‖((Real.sqrt (∑ τ, ‖v τ‖ ^ 2) : ℂ)⁻¹ * (t : ℂ)⁻¹) * ∑ τ, star (v τ) * w τ‖ := by
  set num := ∑ τ, star (v τ) * w τ
  rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg ht]
  rcases (Real.sqrt_nonneg (∑ τ, ‖v τ‖ ^ 2)).lt_or_eq with hpos' | hzero
  · have hle : Real.sqrt (∑ τ, ‖v τ‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hv
    have h1 : 1 ≤ (Real.sqrt (∑ τ, ‖v τ‖ ^ 2))⁻¹ := one_le_inv₀ hpos' |>.2 hle
    have h2 : 0 ≤ t⁻¹ * ‖num‖ := by positivity
    nlinarith
  · have hv0 : ∀ τ, v τ = 0 := by
      have hsum : ∑ τ, ‖v τ‖ ^ 2 = 0 := by
        have := Real.sqrt_eq_zero'.1 hzero.symm
        linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => sq_nonneg ‖v τ‖]
      intro τ
      have := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => sq_nonneg ‖v τ‖).1 hsum τ
        (Finset.mem_univ τ)
      simpa using this
    have : num = 0 := Finset.sum_eq_zero fun τ _ => by rw [hv0 τ, star_zero, zero_mul]
    rw [this, norm_zero, mul_zero]
    positivity

/-! ### An elementary estimate -/

/-- If `‖S - 1‖ ≤ δ` and `|t² - 1| ≤ η` with `t ≥ 0`, then `1 - ‖S‖ / t ≤ δ + η`. This combines
the normalized overlap `S` and the normalized norm `t` in the triangle inequality of
arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii). -/
theorem one_sub_norm_div_le_of_norm_sub_le {S : ℂ} {t δ η : ℝ} (ht : 0 ≤ t)
    (hS : ‖S - 1‖ ≤ δ) (hT : |t ^ 2 - 1| ≤ η) : 1 - ‖S‖ / t ≤ δ + η := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hS
  have hη : 0 ≤ η := (abs_nonneg _).trans hT
  have hnn : 0 ≤ ‖S‖ / t := by positivity
  rcases le_or_gt 1 (δ + η) with h | h
  · linarith
  have ht2 := abs_le.1 hT
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at ht2; nlinarith [ht2.1]
  have hS' : 1 - δ ≤ ‖S‖ := by
    have := norm_sub_norm_le (1 : ℂ) S
    rw [norm_sub_rev, norm_one] at this
    linarith
  have hw2 : 2 * t ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (1 - t)]
  have hwle : t ≤ 1 + η / 2 := by linarith [ht2.2]
  have : 1 - δ - η ≤ ‖S‖ / t := by
    rw [le_div_iff₀ htpos]
    nlinarith [mul_le_mul_of_nonneg_right hwle (by linarith : (0 : ℝ) ≤ 1 - δ - η)]
  linarith

/-- **The trivial range of the error bound.** If `0 ≤ r`, `C ≥ 1`, `u ≥ 1` and `0 < s ≤ 1`, then
`1 - r ≤ C u e^{C u} / s`. -/
theorem one_sub_le_mul_mul_exp_div_of_one_le {r C u s : ℝ} (hr : 0 ≤ r) (hC : 1 ≤ C) (hu : 1 ≤ u)
    (hs : 0 < s) (hs1 : s ≤ 1) : 1 - r ≤ C * u * Real.exp (C * u) / s := by
  have h1 : 1 ≤ C * u := by nlinarith
  have h2 : 1 ≤ Real.exp (C * u) := Real.one_le_exp (by linarith)
  have h3 : 1 ≤ C * u * Real.exp (C * u) / s := by rw [le_div_iff₀ hs]; nlinarith
  linarith

/-- **The final estimate of the approximation error.** Let `0 ≤ x ≤ 1`, `M ≥ 1`, `u = M x^q`,
`K ≥ 0`, `0 < s ≤ 1`, and let `e_j ≤ C_j u e^{C_j u}` with `C_j ≥ 0`. If
`1 - r ≤ (∑ⱼ e_j) / s + K x^{Mq}`, then `1 - r ≤ C u e^{C u} / s` with `C = ∑ⱼ C_j + K + 1`.
This collects the overlaps of the blocks and the norm of the target in the proof of
arXiv:2307.01696, Supplemental Material, Lemma 1'(ii). -/
theorem one_sub_le_mul_mul_exp_div_of_sum_le {ι : Type*} [Fintype ι] {Cz e : ι → ℝ}
    {K x s r : ℝ} {M q : ℕ} (hCz : ∀ j, 0 ≤ Cz j)
    (he : ∀ j, e j ≤ Cz j * (M * x ^ q) * Real.exp (Cz j * (M * x ^ q))) (hK : 0 ≤ K)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hM : M ≠ 0) (hs : 0 < s) (hs1 : s ≤ 1)
    (h : 1 - r ≤ (∑ j, e j) / s + K * x ^ (M * q)) :
    1 - r ≤ (∑ j, Cz j + K + 1) * (M * x ^ q) *
      Real.exp ((∑ j, Cz j + K + 1) * (M * x ^ q)) / s := by
  set u : ℝ := M * x ^ q
  set S := ∑ j, Cz j
  have hu : 0 ≤ u := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hCz j
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hM
  have hδ : ∑ j, e j ≤ S * u * Real.exp (S * u) := by
    have h' : ∀ j, e j ≤ Cz j * u * Real.exp (S * u) := fun j => by
      refine (he j).trans ?_
      have hCS : Cz j ≤ S :=
        Finset.single_le_sum (f := Cz) (fun j _ => hCz j) (Finset.mem_univ j)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hCS hu))
        (mul_nonneg (hCz j) hu)
    refine (Finset.sum_le_sum fun j _ => h' j).trans_eq ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hη : K * x ^ (M * q) ≤ K * u / s := by
    have h1 : x ^ (M * q) ≤ u := by
      calc x ^ (M * q) ≤ x ^ q :=
            pow_le_pow_of_le_one hx0 hx1 (Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero hM))
        _ ≤ u := le_mul_of_one_le_left (by positivity) hM1
    calc K * x ^ (M * q) ≤ K * u := mul_le_mul_of_nonneg_left h1 hK
      _ ≤ K * u / s := le_div_self (by positivity) hs hs1
  have hexp : 1 ≤ Real.exp ((S + K + 1) * u) := Real.one_le_exp (by positivity)
  have he' : Real.exp (S * u) ≤ Real.exp ((S + K + 1) * u) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hu)
  have hfin : S * u * Real.exp (S * u) + K * u ≤ (S + K + 1) * u * Real.exp ((S + K + 1) * u) := by
    have h1 : S * u * Real.exp (S * u) ≤ S * u * Real.exp ((S + K + 1) * u) :=
      mul_le_mul_of_nonneg_left he' (mul_nonneg hS hu)
    have h2 : K * u ≤ K * u * Real.exp ((S + K + 1) * u) :=
      le_mul_of_one_le_right (mul_nonneg hK hu) hexp
    have h3 : 0 ≤ u * Real.exp ((S + K + 1) * u) := by positivity
    nlinarith
  calc 1 - r ≤ (∑ j, e j) / s + K * x ^ (M * q) := h
    _ ≤ S * u * Real.exp (S * u) / s + K * u / s :=
        add_le_add (div_le_div_of_nonneg_right hδ hs.le) hη
    _ = (S * u * Real.exp (S * u) + K * u) / s := by rw [add_div]
    _ ≤ _ := by gcongr

end MPSTensor
