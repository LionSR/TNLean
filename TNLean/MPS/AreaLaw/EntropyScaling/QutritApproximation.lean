/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.OptimizedPureStateTraceError
import TNLean.MPS.AreaLaw.MPSApproximation
import TNLean.MPS.AreaLaw.CopyErrorAmplification
import TNLean.MPS.AreaLaw.EntropyScaling.QutritCopies
import TNLean.MPS.AreaLaw.EntropyScaling.QutritMiddleTail

/-!
# Bond dimension bounds for the repeated qutrit family

The middle-cut Schmidt tail bounds the scalar optimized trace error of any
normalized MPS. Applying the amplification estimate to the repeated family
then gives an exponential lower bound on its approximating bond dimension.

Source: arXiv:0705.0292v2, `paper_v2.tex`, lines 471–479.

**Local fix (constant):** The bond-dimension bounds of this module have the
constant two where the source prints `D ≥ 2^N(1 - 8T) + 1`, and they use the
amplification `√(K/4) T(f) ≤ T(f^K)` under product error below one in place
of the printed `√(K/8)` estimate with its single-copy smallness hypothesis.
The printed bound follows. Documented in
`docs/paper-gaps/swvc08_qutrit_copy_constant.tex`.
-/

namespace TNLean.MPS.AreaLaw.EntropyScaling
open Matrix
open scoped ComplexOrder

/-- The optimized scalar error dominates the lost squared fidelity. -/
private theorem one_sub_le_error {f : ℝ} (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) :
    1 - f ≤ Real.optimizedPureTraceError f := by
  by_cases hf : 1 / 2 ≤ f
  · have hs := Real.optimizedPureTraceError_sq hf hf₁
    have hn := Real.optimizedPureTraceError_nonneg f
    nlinarith [mul_nonneg (sub_nonneg.mpr hf₁) (by linarith : 0 ≤ 5 * f - 1)]
  · rw [Real.optimizedPureTraceError, ite_eq_right hf]
    linarith

/-- Relabelling a middle cut gives the coefficient matrix in numbered half-chain
coordinates, for every vector on the chain. -/
private theorem middleMatrix_reindex (N : ℕ)
    (φ : EuclideanSpace ℂ (Fin (N + N) → Fin 3)) :
    (cutMatrix φ N).reindex (qutritLeftConfigurationEquiv N) (qutritRightConfigurationEquiv N) =
      schmidtCoeffMatrix (WithLp.ofLp
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (qutritHalves N) φ)) := by
  ext a b
  change φ ((Entropy.cutEquiv (fun _ : Fin (N + N) ↦ 3) (leftBlock (N + N) N)).symm
    ((qutritLeftConfigurationEquiv N).symm a, (qutritRightConfigurationEquiv N).symm b)) =
      φ ((qutritHalves N).symm (a, b))
  apply congrArg φ
  apply (qutritHalves N).injective
  rw [← qutritConfigurations_cutEquiv, Equiv.apply_symm_apply]
  simp

/-- The squared overlap of an actual MPS with the qutrit state is bounded by the
mass of its largest D middle-cut Schmidt coefficients. -/
theorem normSq_overlap_qutritFamily_le_kyFan {N D : ℕ} (hN : 0 < N)
    (φ : EuclideanSpace ℂ (Fin (N + N) → Fin 3)) (hφ : ‖φ‖ = 1)
    (hmps : IsOpenMPS (N + N) 3 D (fun x ↦ φ x)) :
    ‖inner ℂ (qutritFamily N) φ‖ ^ 2 ≤
      (qutritMiddleMarginal_posSemidef N (N : ℝ)⁻¹).isHermitian.kyFanNorm D := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (qutritHalves N)
  let Φ := e φ
  have hn : ‖Φ‖ = 1 := (e.norm_map φ).trans hφ
  have hr : (schmidtCoeffMatrix (WithLp.ofLp Φ)).rank ≤ D := by
    rw [← middleMatrix_reindex, Matrix.rank_reindex]
    exact hmps.rank_cutMatrix_le hN (by omega)
  have h := normSq_inner_le_kyFanNorm (qutritMiddleVector N (N : ℝ)⁻¹) Φ hn D hr
  have hi : inner ℂ (qutritMiddleVector N (N : ℝ)⁻¹) Φ =
      inner ℂ (qutritFamily N) φ := e.inner_map_map _ _
  rw [hi] at h
  simpa only [qutritMiddleMarginal, partialTraceRight_vecMulVec_eq] using h

/-- The single-copy obstruction in scalar optimized trace error, with the actual
MPS rank bound. Source: arXiv:0705.0292v2, lines 475–479. -/
theorem qutritFamily_scalar_error_lower_bound {N D : ℕ} (hN : 2 ≤ N)
    (φ : EuclideanSpace ℂ (Fin (N + N) → Fin 3)) (hφ : ‖φ‖ = 1)
    (hmps : IsOpenMPS (N + N) 3 D (fun x ↦ φ x)) :
    ((2 : ℝ) ^ N - ((D : ℝ) - 1)) * (N : ℝ)⁻¹ / (2 : ℝ) ^ N ≤
      Real.optimizedPureTraceError (‖inner ℂ (qutritFamily N) φ‖ ^ 2) := by
  have ho := normSq_overlap_qutritFamily_le_kyFan (by omega) φ hφ hmps
  have hinner : ‖inner ℂ (qutritFamily N) φ‖ ≤ 1 := by
    simpa only [norm_qutritFamily (N := N) (by omega), hφ, one_mul] using
      norm_inner_le_norm (𝕜 := ℂ) (qutritFamily N) φ
  have hf : ‖inner ℂ (qutritFamily N) φ‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hinner 2
  exact (one_sub_kyFanNorm_qutritFamily_ge hN D).trans
    ((sub_le_sub_left ho 1).trans (one_sub_le_error (sq_nonneg _) hf))

/-- Combining the one-copy tail and the square-root amplification bound. -/
private theorem bond_bound_of_amplification {N D : ℕ} (hN : 0 < N) {s δ : ℝ}
    (ht : ((2 : ℝ) ^ N - ((D : ℝ) - 1)) * (N : ℝ)⁻¹ / (2 : ℝ) ^ N ≤ s)
    (ha : Real.sqrt (((N ^ 2 : ℕ) : ℝ) / 4) * s ≤ δ) :
    (2 : ℝ) ^ N * (1 - 2 * δ) + 1 ≤ D := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hsqrt : Real.sqrt (((N ^ 2 : ℕ) : ℝ) / 4) = (N : ℝ) / 2 := by
    rw [Nat.cast_pow, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hn.le]
    norm_num
  rw [hsqrt] at ha
  have ht' := (div_le_iff₀ he).mp ht
  have ht'' := mul_le_mul_of_nonneg_left ht' hn.le
  field_simp at ht''
  nlinarith [mul_le_mul_of_nonneg_left ha he.le]

/-- The normalized repeated family forces exponential bond dimension whenever
its optimized scalar error is less than one. Source: arXiv:0705.0292v2,
lines 471–479; the constant two strengthens the printed constant eight. -/
theorem bondDimension_qutritCopies_ge_of_scalar_error_lt_one {N D : ℕ} (hN : 2 ≤ N)
    (φ : EuclideanSpace ℂ (Fin (N ^ 2 * (N + N)) → Fin 3)) (hφ : ‖φ‖ = 1)
    (hmps : IsOpenMPS (N ^ 2 * (N + N)) 3 D (fun x ↦ φ x))
    (hsmall : Real.optimizedPureTraceError (‖inner ℂ (qutritCopies N) φ‖ ^ 2) < 1) :
    (2 : ℝ) ^ N * (1 - 2 * Real.optimizedPureTraceError
      (‖inner ℂ (qutritCopies N) φ‖ ^ 2)) + 1 ≤ D := by
  obtain ⟨θ, hm, hn, _, ha⟩ := hmps.exists_copy_error_amplification hφ
    (norm_qutritFamily (by omega)) (by nlinarith : 1 ≤ N ^ 2) hsmall
  exact bond_bound_of_amplification (by omega)
    (qutritFamily_scalar_error_lower_bound hN θ hn hm) ha

/-- The optimized scalar error is bounded by the actual full density error,
with only the target vector assumed to be a unit vector. -/
private theorem optimizedError_le_actualError
    {n : Type*} [Fintype n] [DecidableEq n] (η ψ : EuclideanSpace ℂ n)
    (hη : ‖η‖ = 1) (hψ : ψ ≠ 0) :
    Real.optimizedPureTraceError (‖inner ℂ η ((‖ψ‖⁻¹ : ℂ) • ψ)‖ ^ 2) ≤
      Matrix.rectangularTraceNorm
        (Matrix.euclideanOuterProduct η η - Matrix.euclideanOuterProduct ψ ψ) := by
  have hη0 : η ≠ 0 := norm_ne_zero_iff.mp (by
    simpa only [hη] using (one_ne_zero : (1 : ℝ) ≠ 0))
  have hmin := (Matrix.isLeast_optimizedPureTraceError η ψ hη0 hψ).2 ⟨1, rfl⟩
  simp only [one_smul, Matrix.rectangularTraceNorm_euclideanOuterProduct_self,
    hη, one_pow, one_mul, div_one] at hmin
  simpa only [inner_smul_right, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg ψ), mul_pow, inv_pow,
    div_eq_mul_inv, mul_comm] using hmin

/-- An error below one from a unit target excludes the zero approximant. -/
private theorem approximant_ne_zero_of_actualError_lt_one
    {n : Type*} [Fintype n] [DecidableEq n] (η ψ : EuclideanSpace ℂ n)
    (hη : ‖η‖ = 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct η η - Matrix.euclideanOuterProduct ψ ψ) < 1) :
    ψ ≠ 0 := by
  intro hψ
  have hzero : Matrix.euclideanOuterProduct ψ ψ = 0 := by
    simp [hψ, Matrix.euclideanOuterProduct]
  have hone : Matrix.rectangularTraceNorm (Matrix.euclideanOuterProduct η η) = 1 := by
    simp only [Matrix.rectangularTraceNorm_euclideanOuterProduct_self, hη, one_pow]
  simp only [hzero, sub_zero, hone, lt_self_iff_false] at herror

/-- The full trace error of an arbitrary MPS approximation forces exponential
bond dimension. Source: arXiv:0705.0292v2, lines 421–479. The constant two
strengthens the printed constant eight, and the approximant need not be normalized. -/
theorem bondDimension_qutritCopies_ge {N D : ℕ} (hN : 2 ≤ N)
    (φ : EuclideanSpace ℂ (Fin (N ^ 2 * (N + N)) → Fin 3))
    (hmps : IsOpenMPS (N ^ 2 * (N + N)) 3 D (fun x ↦ φ x)) :
    (2 : ℝ) ^ N * (1 - 2 * Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct (qutritCopies N) (qutritCopies N) -
        Matrix.euclideanOuterProduct φ φ)) + 1 ≤ D := by
  let δ := Matrix.rectangularTraceNorm
    (Matrix.euclideanOuterProduct (qutritCopies N) (qutritCopies N) -
      Matrix.euclideanOuterProduct φ φ)
  change (2 : ℝ) ^ N * (1 - 2 * δ) + 1 ≤ D
  by_cases hδ : δ < 1
  · have hφ0 := approximant_ne_zero_of_actualError_lt_one
      (qutritCopies N) φ (norm_qutritCopies (by omega)) hδ
    have hn : ‖(‖φ‖⁻¹ : ℂ) • φ‖ = 1 := by
      simp [norm_smul, norm_ne_zero_iff.mpr hφ0]
    refine le_trans ?_ (bondDimension_qutritCopies_ge_of_scalar_error_lt_one hN
      ((‖φ‖⁻¹ : ℂ) • φ) hn
      (by simpa only [PiLp.smul_apply, smul_eq_mul] using hmps.smul (‖φ‖⁻¹ : ℂ))
      ((optimizedError_le_actualError (qutritCopies N) φ
        (norm_qutritCopies (by omega)) hφ0).trans_lt hδ))
    simpa only [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (mul_le_mul_of_nonneg_left
        (optimizedError_le_actualError (qutritCopies N) φ
          (norm_qutritCopies (by omega)) hφ0) (by norm_num : (0 : ℝ) ≤ 2)) 1)
      (by positivity : 0 ≤ (2 : ℝ) ^ N)) 1
  · have hp : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    have hd : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hδ' : 1 ≤ δ := le_of_not_gt hδ
    nlinarith [mul_le_mul_of_nonneg_left hδ' (by positivity : 0 ≤ (2 : ℝ) ^ N)]

end TNLean.MPS.AreaLaw.EntropyScaling
