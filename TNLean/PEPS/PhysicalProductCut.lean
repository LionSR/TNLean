/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusPhysicalMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Prod

/-!
# Physical product maps across a finite partition

A product of physical linear maps factors into a map on each side of a partition.
Consequently the coefficient matrix across the partition changes by multiplication
on its two sides. Its rank cannot increase; if a reverse product map recovers the
original vector, the rank is unchanged.

This is the Schmidt-rank argument used in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Corollary 6.10, `Papers/1001.3807/paper_v3.tex`, lines 2074–2090.
The statements here concern arbitrary finite physical vectors and rectangular
physical maps. They do not assume that a PEPS has the rank asserted in the source.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {Site Phys Out : Type*} [Fintype Site]
variable (p : Site → Prop) [DecidablePred p]

/-- The coefficient matrix of a physical vector across a vertex partition.
Its rank is the Schmidt rank. Source: SCP10, Corollary 6.10, lines 2074–2090. -/
def physicalCutMatrix (ψ : (Site → Phys) → ℂ) :
    Matrix ({v : Site // p v} → Phys) ({v : Site // ¬ p v} → Phys) ℂ :=
  fun σ τ => ψ ((Equiv.piEquivPiSubtypeProd p (fun _ => Phys)).symm (σ, τ))

/-- A physical product matrix factors over the two sides of a partition.
Source: SCP10, the local-map Schmidt-rank argument of Corollary 6.10. -/
theorem physicalProductMatrix_split (F : Matrix Out Phys ℂ)
    (τ : {v : Site // p v} → Out) (ν : {v : Site // ¬ p v} → Out)
    (σ : {v : Site // p v} → Phys) (μ : {v : Site // ¬ p v} → Phys) :
    physicalProductMatrix Site F
        ((Equiv.piEquivPiSubtypeProd p (fun _ => Out)).symm (τ, ν))
        ((Equiv.piEquivPiSubtypeProd p (fun _ => Phys)).symm (σ, μ)) =
      physicalProductMatrix {v : Site // p v} F τ σ *
        physicalProductMatrix {v : Site // ¬ p v} F ν μ := by
  unfold physicalProductMatrix
  rw [← Fintype.prod_subtype_mul_prod_subtype p]
  congr 1
  all_goals
    apply Finset.prod_congr rfl
    intro v _
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply, v.property, dite_true, dite_false]

/-- Across a cut, a product of physical maps multiplies the coefficient matrix
on the left and by the ordinary transpose on the right.
Source: SCP10, the Schmidt-rank argument of Corollary 6.10, lines 2074–2090. -/
theorem physicalCutMatrix_physicalProductMap [DecidableEq Site] [Fintype Phys]
    (F : Matrix Out Phys ℂ) (ψ : (Site → Phys) → ℂ) :
    physicalCutMatrix p (physicalProductMap Site F ψ) =
      physicalProductMatrix {v : Site // p v} F * physicalCutMatrix p ψ *
        (physicalProductMatrix {v : Site // ¬ p v} F).transpose := by
  ext τ ν
  change (∑ σ, physicalProductMatrix Site F
      ((Equiv.piEquivPiSubtypeProd p (fun _ => Out)).symm (τ, ν)) σ * ψ σ) = _
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p (fun _ => Phys)).symm,
    Fintype.sum_prod_type]
  simp only [physicalProductMatrix_split, Matrix.mul_apply, Matrix.transpose_apply,
    physicalCutMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_right_comm]

/-- Local physical maps cannot increase the Schmidt rank of a finite vector.
Source: SCP10, the rank-preservation argument of Corollary 6.10, lines 2074–2090. -/
theorem rank_physicalCutMatrix_physicalProductMap_le [DecidableEq Site]
    [Fintype Phys] [Fintype Out] (F : Matrix Out Phys ℂ) (ψ : (Site → Phys) → ℂ) :
    (physicalCutMatrix p (physicalProductMap Site F ψ)).rank ≤
      (physicalCutMatrix p ψ).rank := by
  rw [physicalCutMatrix_physicalProductMap]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- If rectangular physical product maps carry two vectors to one another, their
Schmidt ranks agree across every partition. No global inverse of either map is required.
Source: SCP10, the local deformation argument of Corollary 6.10, lines 2074–2090. -/
theorem rank_physicalCutMatrix_eq_of_physicalProductMaps [DecidableEq Site]
    [Fintype Phys] [Fintype Out] (F : Matrix Out Phys ℂ) (L : Matrix Phys Out ℂ)
    (ψ : (Site → Phys) → ℂ) (φ : (Site → Out) → ℂ)
    (hF : physicalProductMap Site F ψ = φ) (hL : physicalProductMap Site L φ = ψ) :
    (physicalCutMatrix p φ).rank = (physicalCutMatrix p ψ).rank := by
  apply le_antisymm
  · rw [← hF]
    exact rank_physicalCutMatrix_physicalProductMap_le p F ψ
  · rw [← hL]
    exact rank_physicalCutMatrix_physicalProductMap_le p L φ

end TNLean.PEPS
