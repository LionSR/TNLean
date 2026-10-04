/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ConjugateProjectiveRepresentation
import TNLean.Algebra.MonomialMatrix
import QICLean.Algebra.MatrixReindexUnitary

/-!
# Regular realization of conjugate-projective factor systems

For any finite group and any unit-modulus twisted two-cocycle, the matrices
`L(g)[x,y] = ω(g,y)` when `x = g*y`, and zero otherwise, form a unitary
conjugate-projective representation with exactly that factor system.
The proof uses the twisted cocycle identity directly, and requires neither
normalization at the identity nor a change of cocycle representative.

This is the semilinear regular construction for the virtual multiplication
law of arXiv:2011.12127, Section III.A, `TN-Review-main.tex` lines 1123–1129.
It supplies the prescribed virtual factor system for the finite-group fixed
point construction discussed in lines 1147–1157. The left-regular matrices
used here are a supporting construction, not the right-regular gauge formula
printed at lines 1151–1155.
-/

open scoped Matrix

namespace TNLean.Algebra

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- The matrix part of the semilinear left regular action, with prescribed
factor system. No normalization of the cochain is assumed.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
def conjugateLeftRegular (ω : ScalarCocycle G) (g : G) : Matrix G G ℂ :=
  Matrix.monomial (Equiv.mulLeft g) fun h => (ω g h : ℂ)

omit [Fintype G] in
/-- The regular matrix sends the basis vector at `y` to `ω(g,y)` times the
basis vector at `g*y`.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
theorem conjugateLeftRegular_apply (ω : ScalarCocycle G) (g x y : G) :
    conjugateLeftRegular ω g x y = if x = g * y then (ω g y : ℂ) else 0 := rfl

/-- Conjugation of a monomial matrix conjugates its phases.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
private theorem parityConjMatrix_monomial {ι : Type*} [DecidableEq ι] (p : SymmetryParity)
    (σ : Equiv.Perm ι) (φ : ι → ℂ) :
    parityConjMatrix p (Matrix.monomial σ φ) =
      Matrix.monomial σ (fun i => parityConj p (φ i)) := by
  ext i j
  simp only [parityConjMatrix_apply, Matrix.monomial_apply]
  split <;> simp_all

/-- The twisted cocycle equation is exactly the multiplication law of the
semilinear regular matrices.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
theorem conjugateLeftRegular_mul (α : G →* SymmetryParity) (ω : ScalarCocycle G)
    (hω : letI := parityUnitsAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω)) (g h : G) :
    conjugateLeftRegular ω g * parityConjMatrix (α g) (conjugateLeftRegular ω h) =
      (ω g h : ℂ) • conjugateLeftRegular ω (g * h) := by
  simp only [conjugateLeftRegular, parityConjMatrix_monomial,
    Matrix.monomial_mul_monomial, Matrix.smul_monomial]
  have hperm : Equiv.mulLeft g * Equiv.mulLeft h = Equiv.mulLeft (g * h) := by
    ext k
    exact (mul_assoc g h k).symm
  rw [hperm]
  congr 1
  funext k
  have hk := congrArg (fun z : Units ℂ => (z : ℂ)) (hω g h k)
  change (ω (g * h) k : ℂ) * (ω g h : ℂ) =
    parityConj (α g) (ω h k : ℂ) * (ω g (h * k) : ℂ) at hk
  simpa only [Equiv.coe_mulLeft, Pi.smul_apply, smul_eq_mul, mul_comm] using hk.symm

/-- Unit-modulus phases make every regular matrix unitary.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
theorem conjugateLeftRegular_mem_unitaryGroup (ω : ScalarCocycle G)
    (hunit : ∀ g h, star (ω g h : ℂ) * (ω g h : ℂ) = 1) (g : G) :
    conjugateLeftRegular ω g ∈ Matrix.unitaryGroup G ℂ :=
  Matrix.monomial_mem_unitaryGroup _ _ (hunit g)

/-- A regular matrix as an invertible matrix, with its adjoint as inverse.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
noncomputable def conjugateLeftRegularGL (ω : ScalarCocycle G)
    (hunit : ∀ g h, star (ω g h : ℂ) * (ω g h : ℂ) = 1) (g : G) : GL G ℂ :=
  Unitary.toUnits ⟨conjugateLeftRegular ω g, conjugateLeftRegular_mem_unitaryGroup ω hunit g⟩

/-- The invertible regular matrix has the original regular entries.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
@[simp] theorem conjugateLeftRegularGL_coe (ω : ScalarCocycle G)
    (hunit : ∀ g h, star (ω g h : ℂ) * (ω g h : ℂ) = 1) (g : G) :
    (conjugateLeftRegularGL ω hunit g : Matrix G G ℂ) = conjugateLeftRegular ω g := rfl

/-- Every unit-modulus twisted cocycle of a finite group is realized by a
unitary conjugate-projective representation of dimension `|G|`, with the
prescribed cocycle itself rather than only a cohomologous representative.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
noncomputable def conjugateRegularRepresentation (α : G →* SymmetryParity)
    (ω : ScalarCocycle G)
    (hω : letI := parityUnitsAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω))
    (hunit : ∀ g h, star (ω g h : ℂ) * (ω g h : ℂ) = 1) :
    ConjugateProjectiveRepresentation α ω (D := Fintype.card G) where
  X g := Units.map (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin G)).toMonoidHom
    (conjugateLeftRegularGL ω hunit g)
  unitary g := by
    change Matrix.reindex (Fintype.equivFin G) (Fintype.equivFin G)
      (conjugateLeftRegular ω g) ∈ _
    exact Matrix.reindex_mem_unitaryGroup _ _ (conjugateLeftRegular_mem_unitaryGroup ω hunit g)
  map_mul' g h := by
    let e := Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin G)
    change e (conjugateLeftRegular ω g) *
      parityConjMatrix (α g) (e (conjugateLeftRegular ω h)) =
      (ω g h : ℂ) • e (conjugateLeftRegular ω (g * h))
    have he : parityConjMatrix (α g) (e (conjugateLeftRegular ω h)) =
        e (parityConjMatrix (α g) (conjugateLeftRegular ω h)) := rfl
    rw [he, ← map_mul, conjugateLeftRegular_mul α ω hω, map_smul]

/-- Every prescribed genuine U(1)-valued twisted factor system has a regular
unitary realization, without any normalization or representative change.
Supporting regular construction for the virtual law and fixed-point existence in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1124–1129 and 1147. -/
noncomputable def conjugateRegularUnitaryRepresentation (α : G →* SymmetryParity)
    (ω : G → G → unitary ℂ)
    (hω : letI := parityUnitaryAction α;
      groupCohomology.IsMulCocycle₂ (Function.uncurry ω)) :
    ConjugateProjectiveRepresentation α (fun g h => Unitary.toUnits (ω g h))
      (D := Fintype.card G) :=
  conjugateRegularRepresentation α (fun g h => Unitary.toUnits (ω g h))
    (isMulCocycle₂_toUnits α ω hω) (fun g h => Unitary.coe_star_mul_self (ω g h))

end TNLean.Algebra
