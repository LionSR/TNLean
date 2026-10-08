/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExactTreeRepresentation
import TNLean.PEPS.Approximation.SquareLatticeConnectivity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact square-grid PEPS and the finite-size prefactor

The exact spanning-tree construction on a positive square grid has bond dimension
at most `q ^ (L * L)`. A single bound `q ^ (L₀ * L₀)` covers every smaller positive
size. For a unit input vector the native contraction is itself unit, so normalizing
it introduces no error and the phase can be chosen to be one.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `07-assembly.tex`, lines 203–214, at immutable manuscript
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.ExactTreeRepresentation

/-- Every vector on a nonempty open square grid is a literal native PEPS
contraction with positive bonds bounded by the physical Hilbert-space dimension. -/
theorem exists_exact_square_tensor {q L : ℕ} (hq : 0 < q) (hL : 0 < L)
    (ψ : (SquareLatticeVertex L L → Fin q) → ℂ) :
    ∃ A : Tensor (squareLatticeGraph L L) q, (∀ e, 0 < A.bondDim e) ∧
      (∀ e, A.bondDim e ≤ q ^ (L * L)) ∧ stateCoeff A = ψ := by
  simpa only [SquareLatticeVertex, Fintype.card_prod, Fintype.card_fin] using
    exists_exact_tensor q (squareLatticeGraph_connected hL hL) hq ψ

open Classical in
/-- The exact square-grid tensor is supported on a spanning tree: every tree
edge has bond dimension `q ^ (L * L)`, and every non-tree edge has dimension one. -/
theorem exists_exact_square_tree_tensor {q L : ℕ} (hq : 0 < q) (hL : 2 ≤ L)
    (ψ : (SquareLatticeVertex L L → Fin q) → ℂ) :
    ∃ (T : SimpleGraph (SquareLatticeVertex L L))
      (A : Tensor (squareLatticeGraph L L) q),
      T ≤ squareLatticeGraph L L ∧ T.IsTree ∧
      (∀ e, A.bondDim e = if T.Adj e.1.1 e.1.2 then q ^ (L * L) else 1) ∧
      (∀ e, 0 < A.bondDim e) ∧ (∀ e, A.bondDim e ≤ q ^ (L * L)) ∧
      stateCoeff A = ψ := by
  classical
  let := squareLatticeVertex_nontrivial hL
  have hpos : 0 < L := by omega
  simpa only [SquareLatticeVertex, Fintype.card_prod, Fintype.card_fin] using
    exists_exact_tree_tensor q (squareLatticeGraph_connected hpos hpos) hq ψ

/-- Exact contraction gives equality in the physical Hilbert space, unit norm,
and zero error after normalization, with the unit phase chosen to be one. -/
theorem exists_exact_unit_square_tensor {q L : ℕ} (hq : 0 < q) (hL : 0 < L)
    (ψ : EuclideanSpace ℂ (SquareLatticeVertex L L → Fin q)) (hψ : ‖ψ‖ = 1) :
    ∃ A : Tensor (squareLatticeGraph L L) q,
      (∀ e, 0 < A.bondDim e) ∧ (∀ e, A.bondDim e ≤ q ^ (L * L)) ∧
      WithLp.toLp 2 (stateCoeff A) = ψ ∧
      ‖WithLp.toLp 2 (stateCoeff A)‖ = 1 ∧
      ‖(‖WithLp.toLp 2 (stateCoeff A)‖⁻¹ : ℝ) •
          WithLp.toLp 2 (stateCoeff A) - (1 : ℂ) • ψ‖ = 0 := by
  obtain ⟨A, hpos, hbound, hstate⟩ := exists_exact_square_tensor hq hL (WithLp.ofLp ψ)
  have hv : WithLp.toLp 2 (stateCoeff A) = ψ := by rw [hstate, WithLp.toLp_ofLp]
  refine ⟨A, hpos, hbound, hv, ?_, ?_⟩
  · simpa only [hv] using hψ
  · simp [hv, hψ]

/-- The exact representations for all smaller positive square sizes admit one
finite prefactor independent of the vector and its Hamiltonian. Source:
manuscript, assembly, lines 203–214. -/
theorem exists_exact_square_tensor_bounded {q L L₀ : ℕ} (hq : 0 < q)
    (hL : 0 < L) (hsmall : L ≤ L₀)
    (ψ : (SquareLatticeVertex L L → Fin q) → ℂ) :
    ∃ A : Tensor (squareLatticeGraph L L) q, (∀ e, 0 < A.bondDim e) ∧
      (∀ e, A.bondDim e ≤ q ^ (L₀ * L₀)) ∧ stateCoeff A = ψ := by
  obtain ⟨A, hpos, hbound, hstate⟩ := exists_exact_square_tensor hq hL ψ
  refine ⟨A, hpos, fun e => (hbound e).trans ?_, hstate⟩
  exact pow_le_pow_right' hq (Nat.mul_le_mul hsmall hsmall)

/-- Enlarging any existing prefactor to the maximum with the finite-size bound
preserves every nonnegative polynomial exponent and covers all smaller sizes.
Source: manuscript, assembly, lines 170–172 and 203–214. -/
theorem exists_exact_square_tensor_polynomial {q L L₀ : ℕ} (hq : 0 < q)
    (hL : 0 < L) (hsmall : L ≤ L₀) (C r : ℝ) (hr : 0 ≤ r)
    (ψ : (SquareLatticeVertex L L → Fin q) → ℂ) :
    ∃ A : Tensor (squareLatticeGraph L L) q, (∀ e, 0 < A.bondDim e) ∧
      (∀ e, (A.bondDim e : ℝ) ≤
        max C (q ^ (L₀ * L₀) : ℕ) * (L : ℝ) ^ r) ∧ stateCoeff A = ψ := by
  obtain ⟨A, hpos, hbound, hstate⟩ := exists_exact_square_tensor_bounded hq hL hsmall ψ
  refine ⟨A, hpos, ?_, hstate⟩
  intro e
  have hb : (A.bondDim e : ℝ) ≤ (q ^ (L₀ * L₀) : ℕ) := by exact_mod_cast hbound e
  have hpow : 1 ≤ (L : ℝ) ^ r := Real.one_le_rpow (by exact_mod_cast hL) hr
  have hC : 0 ≤ max C (q ^ (L₀ * L₀) : ℕ) :=
    (Nat.cast_nonneg _).trans (le_max_right _ _)
  exact hb.trans ((le_max_right _ _).trans (le_mul_of_one_le_right hC hpow))

/-- A positive real outer exponent can be preserved by enlarging the prefactor
by the corresponding root of the uniform finite-size bound. Source: manuscript,
assembly, lines 168–172 and 203–214. -/
theorem exists_exact_square_tensor_outer_power {q L L₀ : ℕ} (hq : 0 < q)
    (hL : 0 < L) (hsmall : L ≤ L₀) (C r χ : ℝ) (hr : 0 ≤ r) (hχ : 0 < χ)
    (ψ : (SquareLatticeVertex L L → Fin q) → ℂ) :
    ∃ A : Tensor (squareLatticeGraph L L) q, (∀ e, 0 < A.bondDim e) ∧
      (∀ e, (A.bondDim e : ℝ) ≤
        (max C (((q ^ (L₀ * L₀) : ℕ) : ℝ) ^ χ⁻¹) * (L : ℝ) ^ r) ^ χ) ∧
      stateCoeff A = ψ := by
  obtain ⟨A, hpos, hbound, hstate⟩ := exists_exact_square_tensor_bounded hq hL hsmall ψ
  refine ⟨A, hpos, ?_, hstate⟩
  intro e
  have hb : (A.bondDim e : ℝ) ≤ (q ^ (L₀ * L₀) : ℕ) := by exact_mod_cast hbound e
  have hroot : 0 ≤ ((q ^ (L₀ * L₀) : ℕ) : ℝ) ^ χ⁻¹ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpow : 1 ≤ (L : ℝ) ^ r := Real.one_le_rpow (by exact_mod_cast hL) hr
  have hC : 0 ≤ max C (((q ^ (L₀ * L₀) : ℕ) : ℝ) ^ χ⁻¹) :=
    hroot.trans (le_max_right _ _)
  have hbase : ((q ^ (L₀ * L₀) : ℕ) : ℝ) ^ χ⁻¹ ≤
      max C (((q ^ (L₀ * L₀) : ℕ) : ℝ) ^ χ⁻¹) * (L : ℝ) ^ r :=
    (le_max_right _ _).trans (le_mul_of_one_le_right hC hpow)
  exact hb.trans (by
    simpa only [Real.rpow_inv_rpow (Nat.cast_nonneg _) hχ.ne'] using
      Real.rpow_le_rpow hroot hbase hχ.le)

end TNLean.PEPS.ExactTreeRepresentation
