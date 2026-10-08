/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExactSquareRepresentation

/-!
# Exact PEPS representation regressions

The cases below check the empty-product obstruction, one-site coefficients,
zero input, a one-dimensional physical alphabet, nonzero contraction, exact
entangled coefficients, and uniform finite-size bounds.
-/

noncomputable section

namespace TNLean.PEPS.ExactTreeRepresentation

example (A : Tensor (⊥ : SimpleGraph (Fin 0)) 2) (σ : Fin 0 → Fin 2) :
    stateCoeff A σ = 1 :=
  stateCoeff_of_isEmpty 2 A σ

example : ¬ ∃ A : Tensor (⊥ : SimpleGraph (Fin 0)) 2, stateCoeff A = 0 := by
  rintro ⟨A, hA⟩
  have h := congrFun hA (fun v => Fin.elim0 v)
  simp only [stateCoeff_of_isEmpty, Pi.zero_apply, one_ne_zero] at h

example (ψ : (Fin 1 → Fin 3) → ℂ) (σ : Fin 1 → Fin 3) :
    stateCoeff (singletonTensor (G := (⊥ : SimpleGraph (Fin 1))) 3 ψ) σ = ψ σ :=
  stateCoeff_singletonTensor 3 0 ψ σ

example : ∃ A : Tensor (squareLatticeGraph 2 2) 1,
    (∀ e, A.bondDim e = 1) ∧ stateCoeff A = 0 := by
  obtain ⟨A, hpos, hbound, hstate⟩ :=
    exists_exact_square_tensor (q := 1) (L := 2) (by decide) (by decide) 0
  refine ⟨A, ?_, hstate⟩
  intro e
  have hp := hpos e
  have hb := hbound e
  simp only [one_pow] at hb
  omega

example (ψ : (SquareLatticeVertex 2 2 → Fin 2) → ℂ) (hψ : ψ ≠ 0) :
    ∃ A : Tensor (squareLatticeGraph 2 2) 2,
      (∀ e, 0 < A.bondDim e) ∧ (∀ e, A.bondDim e ≤ 16) ∧
      stateCoeff A = ψ ∧ stateCoeff A ≠ 0 := by
  obtain ⟨A, hpos, hbound, hstate⟩ :=
    exists_exact_square_tensor (q := 2) (L := 2) (by decide) (by decide) ψ
  exact ⟨A, hpos, hbound, hstate, by simpa only [hstate] using hψ⟩

open Classical in
example : ∃ A : Tensor (squareLatticeGraph 2 2) 2,
    ∀ σ, stateCoeff A σ =
      if σ (0, 0) = σ (1, 1) then (1 : ℂ) else 0 := by
  obtain ⟨A, _, _, hA⟩ := exists_exact_square_tensor (q := 2) (L := 2)
    (by decide) (by decide) (fun σ => if σ (0, 0) = σ (1, 1) then (1 : ℂ) else 0)
  exact ⟨A, fun σ => congrFun hA σ⟩

example {L : ℕ} (hL : 2 ≤ L) (hsmall : L < 5)
    (ψ : (SquareLatticeVertex L L → Fin 2) → ℂ) :
    ∃ A : Tensor (squareLatticeGraph L L) 2,
      (∀ e, 0 < A.bondDim e) ∧ (∀ e, A.bondDim e ≤ 2 ^ 25) ∧
      stateCoeff A = ψ :=
  exists_exact_square_tensor_bounded (by decide) (by omega) hsmall.le ψ

example {q L : ℕ} (hq : 0 < q) (hL : 0 < L)
    (ψ : EuclideanSpace ℂ (SquareLatticeVertex L L → Fin q)) (hψ : ‖ψ‖ = 1) :
    ∃ A : Tensor (squareLatticeGraph L L) q,
      WithLp.toLp 2 (stateCoeff A) = ψ ∧
      ‖(‖WithLp.toLp 2 (stateCoeff A)‖⁻¹ : ℝ) •
          WithLp.toLp 2 (stateCoeff A) - (1 : ℂ) • ψ‖ = 0 := by
  obtain ⟨A, _, _, hA, _, herror⟩ := exists_exact_unit_square_tensor hq hL ψ hψ
  exact ⟨A, hA, herror⟩

end TNLean.PEPS.ExactTreeRepresentation
