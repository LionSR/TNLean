/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.BondCoordinateTransport
import TNLean.PEPS.PhysicalCoherentTransport
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Returning the torus bond state to the original representation coordinates

An isometric change of virtual coordinates induces a physical change on each
pair of bond endpoints. The product of these maps carries the actual torus
averaging state to the actual averaging state in the new coordinates. The
coefficient identity is derived from the two contractions.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2938–3019.
-/

open scoped Matrix BigOperators
namespace TNLean.PEPS

variable {G In Out : Type*} [Group G] [Fintype G]
variable [Fintype In] [DecidableEq In] [Fintype Out] [DecidableEq Out]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Coordinate transport of the actual regrouped torus averaging state.
Source: SCP10, Section 7, lines 2938–3019. The representation intertwining
condition is the ordinary change-of-basis identity, not a supplied state identity. -/
theorem physicalProductMap_bondCoordinateMatrix_averagingSite
    (Q : Matrix Out In ℂ) (U : G →* Matrix In In ℂ) (U' : G →* Matrix Out Out ℂ)
    (hU : ∀ g, U' g = Q * U g * Q.conjTranspose) :
    physicalProductMap (TorusVertex width height × Bool) (bondCoordinateMatrix Q)
      (torusBondRegrouping (fun σ => torusBondNetwork
        (fun v t => averagingSite U t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1)) =
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v t => averagingSite U' t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1) := by
  rw [torusBondRegrouping_averagingSite_coherent U,
    torusBondRegrouping_averagingSite_coherent U']
  apply physicalProductMap_sum_prod_eq
    (bondCoordinateMatrix Q)
    (fun _ : TorusVertex width height → G =>
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height))
    (fun (e : TorusVertex width height × Bool) (q : TorusVertex width height → G)
      (a : In × In) => U (torusBondRelativeElement q e) a.1 a.2)
    (fun (e : TorusVertex width height × Bool) (q : TorusVertex width height → G)
      (a : Out × Out) => U' (torusBondRelativeElement q e) a.1 a.2)
  intro e q
  rw [bondCoordinateMatrix_mulVec, ← hU]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Collecting a representation in another orthonormal basis induces an isometric
physical bond map between its actual torus averaging states.
Source: SCP10, the unitary irreducible decomposition in Section 7, lines 2938–3019. -/
theorem physicalProductMap_bondCoordinateMatrix_orthonormalBasis
    (ρ : Representation ℂ G H) (b : OrthonormalBasis In ℂ H)
    (c : OrthonormalBasis Out ℂ H) :
    Matrix.IsIsometry (bondCoordinateMatrix (c.toBasis.toMatrix b)) ∧
    physicalProductMap (TorusVertex width height × Bool)
      (bondCoordinateMatrix (c.toBasis.toMatrix b))
      (torusBondRegrouping (fun σ => torusBondNetwork
        (fun v t => averagingSite ((LinearMap.toMatrixAlgEquiv b.toBasis).toMonoidHom.comp ρ)
          t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1)) =
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v t => averagingSite ((LinearMap.toMatrixAlgEquiv c.toBasis).toMonoidHom.comp ρ)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1) := by
  refine ⟨bondCoordinateMatrix_isIsometry _
    (c.toMatrix_orthonormalBasis_conjTranspose_mul_self b), ?_⟩
  apply physicalProductMap_bondCoordinateMatrix_averagingSite
  intro g
  change LinearMap.toMatrix c.toBasis c.toBasis (ρ g) =
    c.toBasis.toMatrix b * LinearMap.toMatrix b.toBasis b.toBasis (ρ g) *
      (c.toBasis.toMatrix b).conjTranspose
  have hBC : b.toBasis.toMatrix c * c.toBasis.toMatrix b = 1 :=
    Module.Basis.toMatrix_mul_toMatrix_flip b.toBasis c.toBasis
  have hInv : (c.toBasis.toMatrix b).conjTranspose = b.toBasis.toMatrix c := by
    calc
      _ = (b.toBasis.toMatrix c * c.toBasis.toMatrix b) *
          (c.toBasis.toMatrix b).conjTranspose := by
        rw [hBC, Matrix.one_mul]
      _ = _ := by
        rw [Matrix.mul_assoc, c.toMatrix_orthonormalBasis_self_mul_conjTranspose b,
          Matrix.mul_one]
  rw [hInv]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    c.toBasis b.toBasis c.toBasis b.toBasis (ρ g)).symm

end TNLean.PEPS
