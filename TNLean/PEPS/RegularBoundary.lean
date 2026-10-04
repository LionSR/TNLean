/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis

/-!
# Invariant regular boundary vectors

For a finite group `G`, simultaneous left multiplication on `n + 1` group labels has
`|G| ^ n` orbits. Choosing the first label as a reference identifies the orbit labels with
`n` relative group elements. Accordingly, the invariant boundary vectors form a space of
dimension `|G| ^ n`.

This is the virtual boundary dimension entering Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Theorem 6.9 (`Papers/1001.3807/paper_v3.tex`, lines 2027–2072).
The identification of these vectors with the support of a reduced density operator requires
the separate tensor-contraction and isometry arguments of that theorem.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module Representation

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G]

/-- Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2043–2076. The virtual boundary
representation is the simultaneous left-regular action on all `b` group labels. -/
noncomputable def regularBoundaryRepresentation (b : ℕ) :
    Representation ℂ G ((Fin b → G) → ℂ) :=
  (((MonoidAlgebra.basis (Fin b → G) ℂ).equivFun.conjAlgEquiv ℂ).toMonoidHom).comp
    (Representation.diagonal ℂ G b)

@[simp]
theorem regularBoundaryRepresentation_apply (b : ℕ) (g : G)
    (x : (Fin b → G) → ℂ) (a : Fin b → G) :
    regularBoundaryRepresentation b g x a = x (g⁻¹ • a) := by
  classical
  simp [regularBoundaryRepresentation, LinearEquiv.conjAlgEquiv_apply,
    Basis.equivFun, MonoidAlgebra.basis]

/-- Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2054–2076. The first boundary
label is a reference; the remaining labels are measured relative to it. -/
def regularBoundaryRelativeEquiv (n : ℕ) : (Fin (n + 1) → G) ≃ G × (Fin n → G) where
  toFun a := (a 0, fun i => (a 0)⁻¹ * a i.succ)
  invFun p := Fin.cons p.1 (fun i => p.1 * p.2 i)
  left_inv a := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · simp
    · funext i
      simp

omit [Fintype G] in
@[simp]
theorem regularBoundaryRelativeEquiv_smul (n : ℕ) (g : G) (a : Fin (n + 1) → G) :
    regularBoundaryRelativeEquiv n (g • a) =
      (g * a 0, (regularBoundaryRelativeEquiv n a).2) := by
  apply Prod.ext
  · rfl
  · funext i
    simp [regularBoundaryRelativeEquiv, mul_assoc]

/-- Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2054–2076. An invariant
boundary vector is specified by its values on configurations whose reference label is `1`. -/
noncomputable def regularBoundaryInvariantsEquiv (n : ℕ) :
    (regularBoundaryRepresentation (G := G) (n + 1)).invariants ≃ₗ[ℂ] ((Fin n → G) → ℂ) where
  toFun x r := x.1 (Fin.cons 1 r)
  invFun f := ⟨fun a => f (regularBoundaryRelativeEquiv n a).2, by
    intro g
    funext a
    simp⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    have h : (a 0)⁻¹ • a = Fin.cons 1 (regularBoundaryRelativeEquiv n a).2 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [regularBoundaryRelativeEquiv]
    change x.1 (Fin.cons 1 (regularBoundaryRelativeEquiv n a).2) = x.1 a
    rw [← h]
    simpa only [regularBoundaryRepresentation_apply] using congrFun (x.2 (a 0)) a
  right_inv f := by
    funext r
    simp [regularBoundaryRelativeEquiv]
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Source: arXiv:1001.3807, Theorem 6.9, lines 2027–2037. The invariant virtual
boundary space for `n + 1` regular legs has dimension `|G| ^ n`. -/
theorem finrank_regularBoundaryInvariants_succ (n : ℕ) :
    Module.finrank ℂ (regularBoundaryRepresentation (G := G) (n + 1)).invariants =
      Fintype.card G ^ n := by
  rw [(regularBoundaryInvariantsEquiv n).finrank_eq, Module.finrank_pi]
  simp

/-- Source: arXiv:1001.3807, Theorem 6.9, lines 2027–2037. A nonempty regular
boundary of `b` legs has an invariant space of dimension `|G| ^ (b - 1)`. -/
theorem finrank_regularBoundaryInvariants (b : ℕ) (hb : 0 < b) :
    Module.finrank ℂ (regularBoundaryRepresentation (G := G) b).invariants =
      Fintype.card G ^ (b - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  simpa using finrank_regularBoundaryInvariants_succ (G := G) n

/-- Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2054–2076. Each relative
configuration labels the equal-weight sum over its simultaneous-translation orbit. -/
noncomputable def regularBoundaryOrbitBasis (n : ℕ) :
    Basis (Fin n → G) ℂ (regularBoundaryRepresentation (G := G) (n + 1)).invariants :=
  (Pi.basisFun ℂ (Fin n → G)).map (regularBoundaryInvariantsEquiv n).symm

@[simp]
theorem regularBoundaryOrbitBasis_apply [DecidableEq G] (n : ℕ) (r : Fin n → G)
    (a : Fin (n + 1) → G) :
    (regularBoundaryOrbitBasis n r).1 a =
      if r = (regularBoundaryRelativeEquiv n a).2 then 1 else 0 := by
  classical
  simp [regularBoundaryOrbitBasis, regularBoundaryInvariantsEquiv, Pi.basisFun_apply,
    Pi.single_apply, eq_comm]

/-- The orbit basis vector is the sum of the coordinate vectors on its `|G|` boundary
configurations. Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2054–2076. -/
theorem regularBoundaryOrbitBasis_eq_sum [DecidableEq G] (n : ℕ) (r : Fin n → G) :
    (regularBoundaryOrbitBasis n r).1 =
      ∑ g : G, Pi.single (Fin.cons g (fun i => g * r i)) (1 : ℂ) := by
  classical
  funext a
  have hEq (g : G) : a = Fin.cons g (fun i => g * r i) ↔
      g = a 0 ∧ r = (regularBoundaryRelativeEquiv n a).2 := by
    rw [eq_comm, ← (regularBoundaryRelativeEquiv n).injective.eq_iff]
    simp [regularBoundaryRelativeEquiv, Prod.ext_iff]
  simp only [regularBoundaryOrbitBasis_apply, Finset.sum_apply, Pi.single_apply, hEq]
  by_cases hr : r = (regularBoundaryRelativeEquiv n a).2 <;> simp [hr]

/-- The equal-weight orbit vectors are orthogonal and have squared norm `|G|`.
Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2054–2076. -/
theorem regularBoundaryOrbitBasis_dotProduct [DecidableEq G] (n : ℕ) (r s : Fin n → G) :
    star (regularBoundaryOrbitBasis n r).1 ⬝ᵥ (regularBoundaryOrbitBasis n s).1 =
      if r = s then (Fintype.card G : ℂ) else 0 := by
  rw [regularBoundaryOrbitBasis_eq_sum]
  simp [star_sum, sum_dotProduct, regularBoundaryOrbitBasis_apply,
    regularBoundaryRelativeEquiv, eq_comm]

end TNLean.PEPS
