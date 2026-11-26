/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import Mathlib.Logic.Equiv.Fin.Rotate
import TNLean.MPS.Operator.Interaction.PhysicalGibbsEmbedding
import TNLean.MPS.FundamentalTheorem.Sectors.FundamentalCoord
import TNLean.MPS.Symmetry.FixedPoint.SPTFixedPoint
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct

/-!
# Regrouping physical registers into neighboring bonds

A physical site has a left and a right virtual register. The incoming bond
at site `i` consists of the right register at its cyclic predecessor and
the left register at `i`. This is a permutation of the entire configuration
basis. It is the change of coordinates used for the independent-bond parent
Hamiltonian in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2,
figure `fig:iso-injective` and equation `eq:phase-nosym:iso-hamiltonian`.

No assertion about the depth of a circuit on whole physical sites is made.

## Locality of the incoming-bond Hamiltonian

Regrouping incoming bonds places each one-bond interaction on the right
register of the preceding physical site and the left register of the current
site. The entry formula below includes identities on all other registers.
Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2,
figure `fig:iso-injective` and equation `eq:phase-nosym:iso-hamiltonian`.

It also contains the following results.

* `MPSTensor.incomingBondPerm_conj_registerAction`,
  `MPSTensor.incomingBondPerm_conj_sptFixedPointAction`: physical symmetry in incoming-bond
  coordinates.
-/

section BondRegrouping

section

namespace MPSTensor

/-- Read the incoming bond registers `(R_{i-1}, L_i)` from physical sites
`(L_i, R_i)`. The cyclic permutation also defines this equivalence for an
empty chain. Source: arXiv:1010.3732, Section II.D.2, figure `fig:iso-injective`. -/
def incomingBondEquiv (D N : ℕ) :
    (Fin N → Fin (D * D)) ≃ (Fin N → Fin D × Fin D) where
  toFun s i := ((finProdFinEquiv.symm (s ((finRotate N).symm i))).2,
    (finProdFinEquiv.symm (s i)).1)
  invFun b i := finProdFinEquiv ((b i).2, (b (finRotate N i)).1)
  left_inv s := by
    funext i
    simp only [Equiv.symm_apply_apply, Prod.eta, Equiv.apply_symm_apply]
  right_inv b := by
    funext i
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.eta]

/-- The incoming-bond change of coordinates with each bond pair encoded
by the same physical alphabet of size `D²`. Source: arXiv:1010.3732,
Section II.D.2, figure `fig:iso-injective`. -/
def incomingBondPerm (D N : ℕ) : Equiv.Perm (Fin N → Fin (D * D)) :=
  (incomingBondEquiv D N).trans (Equiv.piCongrRight fun _ => finProdFinEquiv)

/-- The permutation of physical registers into incoming bonds is unitary
on the whole chain Hilbert space. Source: arXiv:1010.3732, Section II.D.2,
figure `fig:iso-injective`. -/
theorem incomingBondPerm_mem_unitaryGroup (D N : ℕ) :
    (incomingBondPerm D N).permMatrix ℂ ∈
      Matrix.unitaryGroup (Fin N → Fin (D * D)) ℂ :=
  (incomingBondPerm D N).permMatrix_mem_unitaryGroup

end MPSTensor

end

section

namespace MPSTensor

/-- In physical coordinates a one-bond operator acts on precisely the registers
`(R_{i-1}, L_i)`, with identity factors on all remaining registers.
Source: arXiv:1010.3732, Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem incomingBondPerm_conj_local_apply {D N : ℕ} (hN : 1 ≤ N) (i : Fin N)
    (K : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
    (s t : Fin N → Fin (D * D)) :
    ((incomingBondPerm D N).permMatrix ℂ *
      ManyBody.placeAlong (X := fun _ ↦ Fin (D * D)) (ManyBody.ringWindow hN i)
        (MPOTensor.oneSiteOperator K) *
      ((incomingBondPerm D N).permMatrix ℂ).conjTranspose) s t =
      ∏ j, if j = i then
        K (finProdFinEquiv (incomingBondEquiv D N s j))
          (finProdFinEquiv (incomingBondEquiv D N t j))
      else if incomingBondEquiv D N s j = incomingBondEquiv D N t j then 1 else 0 := by
  classical
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def, permMatrix_conj_eq_submatrix,
    ← MPOTensor.piKronecker_mulSingle]
  change (∏ j, (Pi.mulSingle
    (M := fun _ : Fin N => Matrix (Fin (D * D)) (Fin (D * D)) ℂ) i K) j
    (incomingBondPerm D N s j) (incomingBondPerm D N t j)) = _
  apply Finset.prod_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [incomingBondPerm]
  · simp [hji, Matrix.one_apply, incomingBondPerm]

end MPSTensor

end

end BondRegrouping

section BondRegroupingSymmetry

/-!
## Physical symmetry in incoming-bond coordinates

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
      Matrix.piKronecker (fun _ : Fin N =>
        Matrix.reindex finProdFinEquiv finProdFinEquiv (R ⊗ₖ L)) *
      ((incomingBondPerm D N).permMatrix ℂ).conjTranspose =
    Matrix.piKronecker (fun _ : Fin N =>
      Matrix.reindex finProdFinEquiv finProdFinEquiv (L ⊗ₖ R)) := by
  classical
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def,
    permMatrix_conj_eq_submatrix]
  ext s t
  simp only [Matrix.submatrix_apply, Matrix.piKronecker_apply,
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
    {D : ℕ} {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω) (g : G) (N : ℕ) :
    (incomingBondPerm D N).permMatrix ℂ *
      Matrix.piKronecker (fun _ : Fin N =>
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          ((((sptGauge ρ g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
            (sptGauge ρ g : Matrix (Fin D) (Fin D) ℂ)ᵀ)) *
      ((incomingBondPerm D N).permMatrix ℂ).conjTranspose =
    Matrix.piKronecker (fun _ : Fin N => sptFixedPointAction ρ 1 g) := by
  simp only [sptFixedPointAction, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply,
    one_smul, Matrix.coe_reindexAlgEquiv, sptKron]
  exact incomingBondPerm_conj_registerAction D N _ _

end MPSTensor

end BondRegroupingSymmetry
