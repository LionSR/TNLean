/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.Circuit.RingSeparation
import TNLean.Circuit.WeightedGHZ
import TNLean.MPS.Preparation.StateApproximationError

/-!
# A circuit obstruction to changing GHZ sector weights

A nearest-neighbour unitary circuit of depth `T` on a ring of `N > 4T + 4` qubits
cannot convert `(2|0ᴺ⟩ + |1ᴺ⟩)/√5` to the balanced GHZ vector with overlap error
below `9/5000`. The error is `1 - |⟨ψ|φ⟩|`, as in arXiv:2307.01696v2, eq. (7).

This is a quantitative qualification of the discussion and outlook's informal
same-phase conversion remark: a common degenerate parent groundspace alone does
not determine the selected-vector conversion problem. It imposes no claim about
phase definitions that include coherent sector-weight compatibility, and concerns
unitary circuits without measurements or uncounted gates.
-/

open Matrix QuantumCircuit
open scoped InnerProductSpace

namespace MPSPreparation

variable {N : ℕ} [NeZero N]


/-- A depth-`T` nearest-neighbour unitary cannot change the sector probabilities `(4/5,1/5)`
to `(1/2,1/2)` on a ring with `N > 4T + 4` at overlap error smaller than `9/5000`.
The observable obstruction concerns selected vectors, rather than their common groundspace. -/
theorem ghz_sector_weight_infidelity_lower_bound {T : ℕ}
    {U : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hU : IsLocalCircuitOfDepth U T) (hN : 4 * T + 4 < N) :
    (9 : ℝ) / 5000 ≤ 1 - ‖⟪
      (WithLp.toLp 2 (U *ᵥ ghzState (M := N)
        ![2 / (Real.sqrt 5 : ℂ), 1 / (Real.sqrt 5 : ℂ)]) :
          EuclideanSpace ℂ (Fin N → Fin 2)),
      WithLp.toLp 2 (ghzState (M := N) ![Complex.invSqrtTwo, Complex.invSqrtTwo])⟫_ℂ‖ := by
  let a : ℂ := 2 / (Real.sqrt 5 : ℂ)
  let b : ℂ := 1 / (Real.sqrt 5 : ℂ)
  let ψ := U *ᵥ ghzState (M := N) ![a, b]
  let φ := ghzState (M := N) ![Complex.invSqrtTwo, Complex.invSqrtTwo]
  have ha : ‖a‖ ^ 2 = (4 : ℝ) / 5 := by
    norm_num [a, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt]
  have hb : ‖b‖ ^ 2 = (1 : ℝ) / 5 := by
    norm_num [b, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt]
  have hstar (z : ℂ) : star z * z = (‖z‖ ^ 2 : ℝ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  have hab : star a * a + star b * b = 1 := by rw [hstar, hstar, ha, hb]; norm_num
  have hbal : star Complex.invSqrtTwo * Complex.invSqrtTwo +
      star Complex.invSqrtTwo * Complex.invSqrtTwo = 1 := by
    simp only [Complex.star_invSqrtTwo, Complex.invSqrtTwo_mul_self]
    norm_num
  have hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1 :=
    (Matrix.norm_eq_of_mulVec_eq hU.mem_unitary rfl).trans (norm_ghzState_two hab)
  have hφ : ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1 :=
    norm_ghzState_two hbal
  obtain ⟨i, j, k, hsep, hk⟩ := exists_separated_singletons_notMem_neighbourhood hN
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
  have hcov := norm_covariance_mulVec_ghzState_two_le hU hsep ⟨k, hk⟩
    (hZs i) (hZs j) (hZu i) (hZu j) hab
  rw [ha, hb] at hcov
  have hcov' : ‖expect ψ (Z i * Z j) - expect ψ (Z i) * expect ψ (Z j)‖ ≤ 16 / 25 := by
    convert hcov using 1; norm_num
  have hZφ (l : Fin N) : expect φ (Z l) = 0 := by
    rw [show φ = ghzState (M := N) ![Complex.invSqrtTwo, Complex.invSqrtTwo] from rfl,
      show Z l = diagonal (fun σ => if σ l = 0 then 1 else -1) from rfl,
      expect_ghzState_two_diagonal]
    simp [Complex.invSqrtTwo_mul_self]
  have hZZφ : expect φ (Z i * Z j) = 1 := by
    change expect (ghzState (M := N) ![Complex.invSqrtTwo, Complex.invSqrtTwo])
      (diagonal _ * diagonal _) = 1
    rw [diagonal_mul_diagonal, expect_ghzState_two_diagonal]
    norm_num [Complex.invSqrtTwo_mul_self]
  obtain ⟨c, hc, heq⟩ := exists_norm_sub_smul_sq_eq hψ hφ
  have hcφ : ‖(WithLp.toLp 2 (c • φ) : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1 := by
    change ‖c • (WithLp.toLp 2 φ : EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1
    rw [norm_smul, hc, hφ, mul_one]
  let η := ‖(WithLp.toLp 2 ψ - c • WithLp.toLp 2 φ :
    EuclideanSpace ℂ (Fin N → Fin 2))‖
  have hdiff := norm_covariance_sub_le hψ hcφ (hZu i) (hZu j)
  simp only [expect_smul_state hc, hZφ, hZZφ, mul_zero, sub_zero] at hdiff
  have htri : (1 : ℝ) ≤ 16 / 25 + 6 * η := by
    calc
      1 = ‖(expect ψ (Z i * Z j) - expect ψ (Z i) * expect ψ (Z j)) -
          ((expect ψ (Z i * Z j) - expect ψ (Z i) * expect ψ (Z j)) - 1)‖ := by
        ring_nf
        simp
      _ ≤ ‖expect ψ (Z i * Z j) - expect ψ (Z i) * expect ψ (Z j)‖ +
          ‖(expect ψ (Z i * Z j) - expect ψ (Z i) * expect ψ (Z j)) - 1‖ :=
        norm_sub_le _ _
      _ ≤ 16 / 25 + 6 * η := add_le_add hcov' hdiff
  have hη : (3 : ℝ) / 50 ≤ η := by linarith
  have hηsq : (9 : ℝ) / 2500 ≤ η ^ 2 := by nlinarith [sq_nonneg (η - 3 / 50)]
  change (9 : ℝ) / 5000 ≤ 1 - ‖⟪WithLp.toLp 2 ψ, WithLp.toLp 2 φ⟫_ℂ‖
  change η ^ 2 = _ at heq
  linarith

end MPSPreparation
