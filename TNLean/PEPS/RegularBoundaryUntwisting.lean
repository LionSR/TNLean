/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import Mathlib.Algebra.Group.Action.Prod

/-!
# A controlled permutation removing a regular boundary twist

Suppose two accessible labels satisfy `c = t * b`. Their relative label `c * b⁻¹`
determines the twist `t`. Controlled multiplication of a third label by this relative
label is a permutation; its inverse removes `t` from a twisted boundary label.
The complex permutation matrices are unitary. On a bipartite vector with a twisted
pair and an accessible reference pair, the inverse operation leaves an untwisted
pair and places all dependence on `t` in the reference pair on the first side.

This is the local group-coordinate operation of Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, equation `eq:iso:tweezer-duplicate-operation`, source lines 1956–1969.
Both directions are specified, since the source uses ket and bra orientations.
Identification of these accessible labels with an actual torus contraction, and
the simultaneous removal of its two closures, are separate statements. No full
physical entropy theorem is asserted here.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G]

/-- The controlled coordinate permutation in SCP10,
`eq:iso:tweezer-duplicate-operation`, lines 1961–1966, with the labels ordered `a,b,c`. -/
def regularTweezerEquiv : Equiv.Perm (G × G × G) where
  toFun p := (p.2.2 * p.2.1⁻¹ * p.1, p.2.1, p.2.2)
  invFun p := (p.2.1 * p.2.2⁻¹ * p.1, p.2.1, p.2.2)
  left_inv p := by simp [mul_assoc]
  right_inv p := by simp [mul_assoc]

@[simp]
theorem regularTweezerEquiv_apply (a b c : G) :
    regularTweezerEquiv (a, b, c) = (c * b⁻¹ * a, b, c) := rfl

@[simp]
theorem regularTweezerEquiv_symm_apply (a b c : G) :
    regularTweezerEquiv.symm (a, b, c) = (b * c⁻¹ * a, b, c) := rfl

/-- The reference pair determines the conjugated closure element.
Source: SCP10, lines 1958–1960. -/
theorem regularTweezer_relative_label (g x b : G) :
    (x⁻¹ * g * x * b) * b⁻¹ = x⁻¹ * g * x := by
  simp [mul_assoc]

/-- The inverse controlled operation removes a common twist from the first label,
while retaining its reference pair on the same side of the cut.
Source: SCP10, `eq:iso:tweezer-duplicate-operation`, lines 1956–1969. -/
theorem regularTweezerEquiv_symm_apply_twisted (t a b : G) :
    regularTweezerEquiv.symm (t * a, b, t * b) = (a, b, t * b) := by
  simp

/-- In particular, the accessible conjugated torus closure can be removed locally.
This is the group-coordinate cancellation of SCP10, lines 1958–1969. -/
theorem regularTweezerEquiv_symm_apply_conjugated (g x a b : G) :
    regularTweezerEquiv.symm (x⁻¹ * g * x * a, b, x⁻¹ * g * x * b) =
      (a, b, x⁻¹ * g * x * b) :=
  regularTweezerEquiv_symm_apply_twisted (x⁻¹ * g * x) a b

variable [Fintype G] [DecidableEq G]

/-- The unitary matrix of the source's controlled basis permutation. -/
def regularTweezerMatrix : Matrix (G × G × G) (G × G × G) ℂ :=
  Matrix.permMatrixHom (R := ℂ) regularTweezerEquiv

/-- The controlled operation is unitary in the regular group basis.
Source: SCP10, lines 1961–1966. -/
theorem regularTweezerMatrix_mem_unitaryGroup :
    regularTweezerMatrix (G := G) ∈ Matrix.unitaryGroup (G × G × G) ℂ :=
  (regularTweezerEquiv⁻¹).permMatrix_mem_unitaryGroup

/-- A twisted boundary pair together with an accessible reference pair, all reference
labels being on the first side of the cut. Source: SCP10, lines 1956–1969. -/
def regularTweezerState (t : G) : ((G × G × G) × G) → ℂ :=
  fun p => if p.1.1 = t * p.2 ∧ p.1.2.2 = t * p.1.2.1 then 1 else 0

omit [Fintype G] in
/-- Applying the inverse controlled operation to the first side produces an
untwisted pair and a reference pair containing the twist. This is the local
coefficient factorization used in SCP10, lines 1967–1990; it does not assert the
factorization of an actual torus PEPS. -/
theorem regularTweezerState_factorization (t a b c d : G) :
    regularTweezerState t (regularTweezerEquiv (a, b, c), d) =
      (if a = d then (1 : ℂ) else 0) * (if c = t * b then 1 else 0) := by
  by_cases hc : c = t * b
  · subst c
    simp [regularTweezerState, mul_assoc]
  · simp [regularTweezerState, hc]

/-- The same factorization as a matrix action: the inverse permutation acts only
on the three accessible labels, leaving the second side unchanged.
Source: SCP10, `eq:iso:tweezer-duplicate-operation`, lines 1956–1969. -/
theorem regularTweezerState_mulVec (t : G) :
    Matrix.permMatrixHom (R := ℂ)
        (Equiv.prodCongr regularTweezerEquiv.symm (Equiv.refl G)) *ᵥ
      regularTweezerState t =
      fun p => (if p.1.1 = p.2 then (1 : ℂ) else 0) *
        (if p.1.2.2 = t * p.1.2.1 then 1 else 0) := by
  funext p
  rcases p with ⟨⟨a, b, c⟩, d⟩
  rw [Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  exact regularTweezerState_factorization t a b c d

end TNLean.PEPS
