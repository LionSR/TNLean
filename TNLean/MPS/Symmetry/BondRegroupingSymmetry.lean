/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondRegroupingLocality
import TNLean.MPS.Symmetry.SPTFixedPoint
import TNLean.Algebra.FinKronecker

/-!
# Physical symmetry in incoming-bond coordinates

Regrouping the registers exchanges the order of their two actions: an on-site
left-right action `L ⊗ R` becomes the bond action `R ⊗ L`. This is the
coordinate identity underlying the symmetric independent-bond Hamiltonian in
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
equation `eq:1d-sym:jointsym`.
-/

open scoped Matrix Kronecker

namespace MPSTensor

/-- The on-site left-right action becomes the right-left action on incoming
bonds. Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem incomingBondPerm_conj_registerAction (D N : ℕ)
    (L R : Matrix (Fin D) (Fin D) ℂ) :
    (incomingBondPerm D N).permMatrix ℂ *
      Matrix.finKronecker (fun _ : Fin N =>
        Matrix.reindex finProdFinEquiv finProdFinEquiv (R ⊗ₖ L)) *
      ((incomingBondPerm D N).permMatrix ℂ).conjTranspose =
    Matrix.finKronecker (fun _ : Fin N =>
      Matrix.reindex finProdFinEquiv finProdFinEquiv (L ⊗ₖ R)) := by
  classical
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def,
    permMatrix_conj_eq_submatrix]
  ext s t
  simp only [Matrix.submatrix_apply, Matrix.finKronecker_apply,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply]
  simp only [incomingBondPerm, Equiv.trans_apply, Equiv.piCongrRight_apply,
    Pi.map_apply, Equiv.symm_apply_apply]
  change (∏ n, R (finProdFinEquiv.symm (s ((finRotate N).symm n))).2
      (finProdFinEquiv.symm (t ((finRotate N).symm n))).2 *
      L (finProdFinEquiv.symm (s n)).1 (finProdFinEquiv.symm (t n)).1) = _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [Equiv.prod_comp (finRotate N).symm
    (fun n => R (finProdFinEquiv.symm (s n)).2 (finProdFinEquiv.symm (t n)).2),
    mul_comm]

/-- The physical action `U(g) = W_gᵀ ⊗ W_g⁻¹` of the fixed-point tensor, with
`W_g = ρ(g⁻¹)`, is the right-left virtual action `W_g⁻¹ ⊗ W_gᵀ` in incoming-bond
coordinates. Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem incomingBondPerm_conj_sptFixedPointAction {G : Type} [Group G]
    {D : ℕ} {ω : TNLean.Algebra.ScalarCocycle G}
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω) (g : G) (N : ℕ) :
    (incomingBondPerm D N).permMatrix ℂ *
      Matrix.finKronecker (fun _ : Fin N =>
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          ((((sptGauge ρ g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
            (sptGauge ρ g : Matrix (Fin D) (Fin D) ℂ)ᵀ)) *
      ((incomingBondPerm D N).permMatrix ℂ).conjTranspose =
    Matrix.finKronecker (fun _ : Fin N => sptFixedPointAction ρ 1 g) := by
  simp only [sptFixedPointAction, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply,
    one_smul, Matrix.coe_reindexAlgEquiv, sptKron]
  exact incomingBondPerm_conj_registerAction D N _ _

end MPSTensor
