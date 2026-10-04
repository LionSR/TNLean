/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SemiRegularEquiv
import TNLean.PEPS.RegularTorusSite

/-!
# The regular matrix representation in group-algebra coordinates

The native left-regular permutation matrices are the matrices of Mathlib's regular
representation in the group basis. The basis coordinate equivalence is therefore an
equivalence of representations. Transporting semi-regularity along this equivalence
shows that the native regular matrix representation is semi-regular.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 4.5,
`Papers/1001.3807/paper_v3.tex`, lines 1010–1013, and the regular-representation
specialization of Theorem 5.9, lines 1582–1621.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The group basis identifies the group-algebra regular representation with the
native regular permutation matrices. Source: SCP10, Definition 4.5 and Theorem 5.9. -/
noncomputable def leftRegularMatrixEquiv :
    (Representation.leftRegular ℂ G).Equiv
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (leftRegularMatrix G)) :=
  Representation.Equiv.mk (MonoidAlgebra.basis G ℂ).equivFun fun g => by
    apply LinearMap.ext
    intro x
    funext i
    change (MonoidAlgebra.basis G ℂ).equivFun (Representation.leftRegular ℂ G g x) i =
      (leftRegularMatrix G g *ᵥ (MonoidAlgebra.basis G ℂ).equivFun x) i
    simpa only [Module.Basis.equivFun_apply, toMatrix_leftRegular_eq_leftRegularMatrix] using
      congrFun (LinearMap.toMatrix_mulVec_repr (MonoidAlgebra.basis G ℂ)
        (MonoidAlgebra.basis G ℂ) (Representation.leftRegular ℂ G g) x).symm i

/-- The native regular permutation-matrix representation is semi-regular.
Source: SCP10, Definition 4.5, lines 1010–1013. -/
theorem isSemiRegular_leftRegularMatrix :
    Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (leftRegularMatrix G)) :=
  Representation.isSemiRegular_leftRegular.of_equiv leftRegularMatrixEquiv

end TNLean.PEPS
