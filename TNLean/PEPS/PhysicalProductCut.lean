/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusPhysicalMap
import QICLean.ManyBody.Sites.CutMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Prod

/-!
# Physical product maps across a finite partition

A product of physical linear maps factors into a map on each side of a partition.
Consequently the coefficient matrix across the partition changes by multiplication
on its two sides. Its rank cannot increase; if a reverse product map recovers the
original vector, the rank is unchanged.

The coefficient matrix across a region `R` is the cut matrix `ManyBody.cutMatrix R` of
QICLean, and the factorization is its lemma
`ManyBody.cutMatrix_mulVec_of_cutOperator_eq_kronecker` for the product matrix.

This is the Schmidt-rank argument used in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Corollary 6.10, `Papers/1001.3807/paper_v3.tex`, lines 2074–2090.
The statements here concern arbitrary finite physical vectors and rectangular
physical maps. They do not assume that a PEPS has the rank asserted in the source.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix Kronecker

namespace TNLean.PEPS

variable {Site Phys Out : Type*} [Fintype Site]

section Split

variable (p : Site → Prop) [DecidablePred p]

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

end Split

variable [DecidableEq Site] (R : Finset Site)

/-- In the coordinates of the cut along a region `R`, a physical product matrix is the
Kronecker product of the product matrices on `R` and outside `R`.
Source: SCP10, the local-map Schmidt-rank argument of Corollary 6.10. -/
theorem reindex_cutEquiv_physicalProductMatrix (F : Matrix Out Phys ℂ) :
    Matrix.reindex (ManyBody.cutEquiv (fun _ : Site => Out) R)
        (ManyBody.cutEquiv (fun _ : Site => Phys) R) (physicalProductMatrix Site F) =
      physicalProductMatrix {v : Site // v ∈ R} F ⊗ₖ
        physicalProductMatrix {v : Site // v ∉ R} F := by
  ext ⟨τ, ν⟩ ⟨σ, μ⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  convert physicalProductMatrix_split (· ∈ R) F τ ν σ μ using 3

/-- Across a cut, a product of physical maps multiplies the coefficient matrix
on the left and by the ordinary transpose on the right.
Source: SCP10, the Schmidt-rank argument of Corollary 6.10, lines 2074–2090. -/
theorem cutMatrix_physicalProductMap [Fintype Phys]
    (F : Matrix Out Phys ℂ) (ψ : (Site → Phys) → ℂ) :
    ManyBody.cutMatrix R (physicalProductMap Site F ψ) =
      physicalProductMatrix {v : Site // v ∈ R} F * ManyBody.cutMatrix R ψ *
        (physicalProductMatrix {v : Site // v ∉ R} F).transpose :=
  ManyBody.cutMatrix_mulVec_of_cutOperator_eq_kronecker
    (reindex_cutEquiv_physicalProductMatrix R F) ψ

/-- Local physical maps cannot increase the Schmidt rank of a finite vector.
Source: SCP10, the rank-preservation argument of Corollary 6.10, lines 2074–2090. -/
theorem rank_cutMatrix_physicalProductMap_le
    [Fintype Phys] [Fintype Out] (F : Matrix Out Phys ℂ) (ψ : (Site → Phys) → ℂ) :
    (ManyBody.cutMatrix R (physicalProductMap Site F ψ)).rank ≤
      (ManyBody.cutMatrix R ψ).rank :=
  ManyBody.cutRank_mulVec_le_of_cutOperator_eq_kronecker
    (reindex_cutEquiv_physicalProductMatrix R F) ψ

/-- If rectangular physical product maps carry two vectors to one another, their
Schmidt ranks agree across every region. No global inverse of either map is required.
Source: SCP10, the local deformation argument of Corollary 6.10, lines 2074–2090. -/
theorem rank_cutMatrix_eq_of_physicalProductMaps
    [Fintype Phys] [Fintype Out] (F : Matrix Out Phys ℂ) (L : Matrix Phys Out ℂ)
    (ψ : (Site → Phys) → ℂ) (φ : (Site → Out) → ℂ)
    (hF : physicalProductMap Site F ψ = φ) (hL : physicalProductMap Site L φ = ψ) :
    (ManyBody.cutMatrix R φ).rank = (ManyBody.cutMatrix R ψ).rank := by
  apply le_antisymm
  · rw [← hF]
    exact rank_cutMatrix_physicalProductMap_le R F ψ
  · rw [← hL]
    exact rank_cutMatrix_physicalProductMap_le R L φ

end TNLean.PEPS
