/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin

/-!
# Coboundaries on a finite cycle

This module records the elementary multiplicative fact that a product-one
family of scalars around a finite cycle is a coboundary.  It is the algebraic
form of the phase telescoping used in arXiv:1708.00029, Appendix A, lines
1093--1102: from phases whose product is one, choose vertex phases so that
each edge phase is the ratio of consecutive vertex phases.
-/

open scoped BigOperators

namespace TNLean.Algebra

variable {G : Type*} [CommGroup G]

/-- The total product around the cycle is the product of the first `n` edges,
multiplied by the last edge. -/
lemma prod_univ_eq_prod_castSucc_last {n : ℕ} (κ : Fin (n + 1) → G) :
    (∏ v : Fin (n + 1), κ v) =
      (∏ v : Fin n, κ v.castSucc) * κ (Fin.last n) := by
  rw [Fin.prod_univ_castSucc]

private lemma prod_eq_partialProd_last {n : ℕ} (ψ : Fin n → G) :
    (∏ v : Fin n, ψ v) = Fin.partialProd ψ (Fin.last n) := by
  rw [← Fin.prod_ofFn]
  rw [Fin.partialProd]
  rw [List.take_of_length_le]
  simp

/-- A product-one family on a finite cycle is a multiplicative coboundary.

This is the group-valued version of the phase choice in arXiv:1708.00029,
Appendix A, lines 1093--1102.  The witness is
φ(k) = (κ₀ ··· κ_{k-1})⁻¹; hence κ_k = φ(k) · φ(k+1)⁻¹ for each
interior edge, and the hypothesis ∏ κ = 1 supplies the closing equation
κ(n) = φ(n) · φ(0)⁻¹ at the last vertex. -/
lemma exists_fin_succ_coboundary_of_prod_eq_one {n : ℕ}
    (κ : Fin (n + 1) → G) (hprod : ∏ v : Fin (n + 1), κ v = 1) :
    ∃ φ : Fin (n + 1) → G,
      (∀ v : Fin n, κ v.castSucc = φ v.castSucc * (φ v.succ)⁻¹) ∧
      κ (Fin.last n) = φ (Fin.last n) * (φ 0)⁻¹ := by
  let ψ : Fin n → G := fun v => κ v.castSucc
  let φ : Fin (n + 1) → G := fun v => (Fin.partialProd ψ v)⁻¹
  refine ⟨φ, ?_, ?_⟩
  · intro v
    have hquot : (Fin.partialProd ψ v.castSucc)⁻¹ * Fin.partialProd ψ v.succ = ψ v :=
      Fin.partialProd_right_inv ψ v
    simpa [φ, ψ] using hquot.symm
  · have hsplit : (∏ v : Fin n, κ v.castSucc) * κ (Fin.last n) = 1 := by
      simpa [prod_univ_eq_prod_castSucc_last κ] using hprod
    have hpartial : (∏ v : Fin n, κ v.castSucc) =
        Fin.partialProd ψ (Fin.last n) := by
      simpa [ψ] using prod_eq_partialProd_last ψ
    have hlast : Fin.partialProd ψ (Fin.last n) * κ (Fin.last n) = 1 := by
      simpa [hpartial] using hsplit
    have hlast' : (Fin.partialProd ψ (Fin.last n))⁻¹ = κ (Fin.last n) := by
      calc
        (Fin.partialProd ψ (Fin.last n))⁻¹ =
            (Fin.partialProd ψ (Fin.last n))⁻¹ * 1 := by simp
        _ = (Fin.partialProd ψ (Fin.last n))⁻¹ *
            (Fin.partialProd ψ (Fin.last n) * κ (Fin.last n)) := by rw [hlast]
        _ = κ (Fin.last n) := by simp
    simp [φ, hlast']

end TNLean.Algebra
