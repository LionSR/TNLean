/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Ordered `Fin` products and configuration sums

Domain-free identities used by the sequential-generation schemes of
arXiv:quant-ph/0608197, Section 5: peeling off the last factor of the ordered
product `Fin.prod`, commuting a fixed matrix through an ordered product of
alternating factors, norm preservation by a unitary, and splitting a sum over
configurations of `m + 1` sites into the first site and the rest.

## Main results

* `Fin.prod_succ'`: `x₀ ⋯ x_m = (x₀ ⋯ x_{m-1}) x_m`.
* `Fin.prod_mul_mul_eq`: `(E R₀)(E R₁) ⋯ (E R_{m-1}) E = E (R₀ E) ⋯ (R_{m-1} E)`.
* `Matrix.star_mulVec_dotProduct_of_mem_unitaryGroup`: `‖W v‖² = ‖v‖²`.
* `Fintype.sum_fin_succ_pi`: splitting a configuration sum at the first site.
-/

namespace Fin

/-- Peeling off the last factor of an ordered product. -/
theorem prod_succ' {α : Type*} [Monoid α] {m : ℕ} (x : Fin (m + 1) → α) :
    Fin.prod x = Fin.prod (fun p => x p.castSucc) * x (Fin.last m) := by
  simp only [Fin.prod_eq_prod_map_finRange, ← List.ofFn_eq_map, List.ofFn_succ',
    List.prod_concat]

/-- An ordered product of factors `E R_p` followed by `E` is `E` followed by the
ordered product of the factors `R_p E`. -/
theorem prod_mul_mul_eq {ι κ R : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] [CommSemiring R] (E : Matrix ι κ R) :
    ∀ {m : ℕ} (F : Fin m → Matrix κ ι R),
      Fin.prod (fun p => E * F p) * E = E * Fin.prod (fun p => F p * E)
  | 0, _ => by simp
  | m + 1, F => by
    rw [Fin.prod_succ, Fin.prod_succ, Matrix.mul_assoc, prod_mul_mul_eq E (fun p => F p.succ),
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc E]

end Fin

namespace Matrix

/-- A unitary preserves the squared norm. -/
theorem star_mulVec_dotProduct_of_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    star (W *ᵥ v) ⬝ᵥ (W *ᵥ v) = star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hW, Matrix.vecMul_one]

end Matrix

namespace Fintype

/-- Splitting a sum over configurations `τ : Fin (m + 1) → α` into the value at
the first site and the configuration of the remaining sites. -/
theorem sum_fin_succ_pi {α M : Type*} [Fintype α] [AddCommMonoid M] {m : ℕ}
    (f : α → (Fin m → α) → M) :
    ∑ τ : Fin (m + 1) → α, f (τ 0) (fun p => τ p.succ) = ∑ τ', ∑ j, f j τ' := by
  classical
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => α).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  simp [Fin.consEquiv_apply]

end Fintype
