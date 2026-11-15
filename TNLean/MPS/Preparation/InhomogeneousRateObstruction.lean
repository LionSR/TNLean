/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.RingSeparation
import TNLean.Circuit.WeightedGHZ
import TNLean.MPS.Preparation.StateApproximationError

/-!
# Accuracy-dependent preparation of weighted GHZ vectors

A unit vector prepared by a depth-`T` nearest-neighbour circuit has zero connected
correlation beyond distance `2T`. Stability of expectations therefore bounds the
overlap error with a weighted GHZ vector from below by
`(2 / 9) (|a|² |b|²)²` whenever `N > 4T + 4`.

This estimate is the circuit obstruction needed for the source-rate question in
arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS". In particular,
a vanishing GHZ branch can be invisible at one convergent error schedule while
remaining detectable at a smaller requested accuracy. The tensor and positive-part
identifications of that example are recorded separately in
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.
-/

open Matrix QuantumCircuit
open scoped InnerProductSpace

namespace MPSPreparation

variable {N : ℕ} [NeZero N]

/-- A distant connected correlation in a target unit vector has squared modulus
at most `72` times its overlap error with any unit vector prepared in depth `T`.
The supports must be separated by more than `2T` in the ring geometry.

This uses the light-cone argument of arXiv:2307.01696, Supplemental Material,
proof of Theorem 1, with the overlap error of main-text eq. (7). -/
theorem norm_covariance_sq_le_overlap_error_of_isPreparedInDepth {T : ℕ}
    {ψ φ : (Fin N → Fin 2) → ℂ} (hprep : IsPreparedInDepth T ψ)
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1)
    (hφ : ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1)
    {X Y : Set (Fin N)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hA : A ∈ supportedOperators 2 X) (hB : B ∈ supportedOperators 2 Y)
    (hAu : A ∈ unitary _) (hBu : B ∈ unitary _) :
    ‖expect φ (A * B) - expect φ A * expect φ B‖ ^ 2 ≤
      72 * (1 - ‖⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin N → Fin 2)),
        WithLp.toLp 2 φ⟫_ℂ‖) := by
  have hnorm : star ψ ⬝ᵥ ψ = 1 := by
    rw [← expect_one, expect_eq_inner, one_mulVec, inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have hfactor := expect_mul_eq_of_isPreparedInDepth hprep hnorm hXY hA hB
  obtain ⟨c, hc, heq⟩ := exists_norm_sub_smul_sq_eq hψ hφ
  have hcφ : ‖(WithLp.toLp 2 (c • φ) : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1 := by
    change ‖c • (WithLp.toLp 2 φ : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1
    rw [norm_smul, hc, hφ, mul_one]
  have hdiff := norm_covariance_sub_le hψ hcφ hAu hBu
  simp only [expect_smul_state hc, hfactor, sub_self, zero_sub, norm_neg] at hdiff
  have hsquare := (sq_le_sq₀
    (norm_nonneg (expect φ (A * B) - expect φ A * expect φ B))
    (by positivity)).mpr hdiff
  nlinarith

/-- On a ring with `N > 4T + 4`, approximation of a normalized weighted GHZ vector
`a|0ᴺ⟩ + b|1ᴺ⟩` by a unit vector prepared in depth `T` has overlap error at least
`(2 / 9) (|a|² |b|²)²`. The amplitudes may depend on `N`.

This is a quantitative obstruction to an accuracy-uniform conclusion from the
qualitative convergence assumption in arXiv:2307.01696's inhomogeneous paragraph;
it does not assume normality of a fixed translation-invariant tensor. -/
theorem weightedGHZ_infidelity_lower_bound_of_isPreparedInDepth {T : ℕ}
    {ψ : (Fin N → Fin 2) → ℂ} (hprep : IsPreparedInDepth T ψ)
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1)
    (hN : 4 * T + 4 < N) {a b : ℂ} (hab : star a * a + star b * b = 1) :
    (2 : ℝ) / 9 * (‖a‖ ^ 2 * ‖b‖ ^ 2) ^ 2 ≤
      1 - ‖⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin N → Fin 2)),
        WithLp.toLp 2 (ghzState (M := N) ![a, b])⟫_ℂ‖ := by
  obtain ⟨i, j, _, hsep, _⟩ := exists_separated_singletons_notMem_neighbourhood hN
  let Z (l : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
    diagonal (fun σ => if σ l = 0 then 1 else -1)
  have hZu (l : Fin N) : Z l ∈ unitary _ := by
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
    simp only [Z, diagonal_conjTranspose, diagonal_mul_diagonal]
    convert (diagonal_one : diagonal (fun _ : Fin N → Fin 2 => (1 : ℂ)) = 1) using 1
    congr 1
    funext σ
    split_ifs with h <;> simp [h]
  have hZs (l : Fin N) : Z l ∈ supportedOperators 2 {l} :=
    diagonal_comp_eval_mem_supportedOperators l (fun x => if x = 0 then 1 else -1)
  have hZφ (l : Fin N) :
      expect (ghzState (M := N) ![a, b]) (Z l) = star a * a - star b * b := by
    change expect (ghzState (M := N) ![a, b]) (diagonal _) = _
    rw [expect_ghzState_two_diagonal]
    simp [sub_eq_add_neg]
  have hZZφ : expect (ghzState (M := N) ![a, b]) (Z i * Z j) = 1 := by
    change expect (ghzState (M := N) ![a, b]) (diagonal _ * diagonal _) = _
    rw [diagonal_mul_diagonal, expect_ghzState_two_diagonal]
    simpa using hab
  have hstar (z : ℂ) : star z * z = (‖z‖ ^ 2 : ℝ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  have hcov : expect (ghzState (M := N) ![a, b]) (Z i * Z j) -
      expect (ghzState (M := N) ![a, b]) (Z i) *
        expect (ghzState (M := N) ![a, b]) (Z j) =
      ((4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hZZφ, hZφ, hZφ]
    calc
      _ = 4 * (star a * a) * (star b * b) := by
        linear_combination -(star a * a + star b * b + 1) * hab
      _ = _ := by rw [hstar, hstar]; push_cast; ring
  have hbound := norm_covariance_sq_le_overlap_error_of_isPreparedInDepth hprep hψ
    (norm_ghzState_two hab) hsep (hZs i) (hZs j) (hZu i) (hZu j)
  rw [hcov, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2)] at hbound
  nlinarith

end MPSPreparation
