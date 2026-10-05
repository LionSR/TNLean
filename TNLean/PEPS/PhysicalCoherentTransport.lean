/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusPhysicalCoherentMap
import TNLean.PEPS.SemiRegularBondProductIsometry

/-!
# Transport of coherent products and supported physical vectors

A single-factor identity determines the action on a coherent sum of product
vectors. Two physical matrices which agree after a bond inclusion also agree
on the product of the included bond spaces. These elementary identities apply
to arbitrary finite families of physical bonds.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {Site Q In Out : Type*} [Fintype Site] [DecidableEq Site]
variable [Fintype Q] [Fintype In]

/-- Single-factor transport extends to every coherent product sum.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem physicalProductMap_sum_prod_eq (F : Matrix Out In ℂ) (w : Q → ℂ)
    (x : Site → Q → In → ℂ) (y : Site → Q → Out → ℂ)
    (h : ∀ e q, F *ᵥ x e q = y e q) :
    physicalProductMap Site F (fun σ => ∑ q, w q * ∏ e, x e q (σ e)) =
      fun τ => ∑ q, w q * ∏ e, y e q (τ e) := by
  rw [physicalProductMap_sum_prod]
  simp only [h]

omit [Fintype Q] in
/-- Agreement on one included bond space gives agreement on its product space.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem physicalProductMap_eq_on_inclusion_range
    {K : Type*} [Fintype K] (T F : Matrix Out In ℂ) (E : Matrix In K ℂ)
    (hTE : T * E = F * E) (ψ : (Site → In) → ℂ)
    (hψ : ψ ∈ LinearMap.range (physicalProductMap Site E)) :
    physicalProductMap Site T ψ = physicalProductMap Site F ψ := by
  obtain ⟨χ, rfl⟩ := hψ
  simp only [physicalProductMap, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, physicalProductMatrix_mul, hTE,
    ← physicalProductMatrix_mul, ← Matrix.mulVec_mulVec]
end TNLean.PEPS
