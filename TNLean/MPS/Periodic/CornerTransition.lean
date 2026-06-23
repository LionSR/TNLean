/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.CyclicSectors.FixedAdjoint

/-!
# Corner-transition tensors for the periodic-overlap Case 3 contraction

This file isolates the *corner-transition tensors* and their *repeated products*
used by the `m`-factor cyclic contraction of arXiv:1708.00029, Appendix A
(lines 1023--1117).  Given cyclic orthogonal projections `P : Fin m → M_D(ℂ)` of
a cyclic sector decomposition, the appendix introduces the one-site corner
letters
$$A_u^i = P_u\, A^i\, P_{u+1}$$
(eq:Auprop) and their repeated products
$$F_u^{\mathbf i} = A_u^{i_1}\, A_{u+1}^{i_2}\cdots A_{u+\ell-1}^{i_\ell}$$
(eq:Fu).  Here `cornerLetter P A u i` is `A_u^i`, and `cornerProd P A u w` is the
product `F_u^{\mathbf i}` along the word `w = [i_1, …, i_\ell]`, with successive
letters carried one sector forward.

The structural fact proved here is purely a projector-idempotency statement and
requires no injectivity or normality input:

* `cornerProd_append` — the **cyclic concatenation law**
  `cornerProd u (w₁ ++ w₂) = cornerProd u w₁ * cornerProd (u + w₁.length • 1) w₂`,
  the algebraic mechanism by which the appendix repeats a single block around the
  cycle to reach an injective length (eq:Fu).  The junction projector
  `P (u + w₁.length • 1)` is absorbed by idempotency.

These are the `A_u^i`/`F_u` building blocks named in the issue's split plan for
Case 3.  The remaining steps of Appendix A — the right-inverse contraction of
`F_u` to the uniform product-tensor identity (feeding
`PiTensorProductPhase.exists_kappa_product_one_of_piTensorProduct_eq_root_smul`)
and the global gauge assembly — are not addressed here; see
`docs/paper-gaps/1708_periodic_overlap_route_alignment.tex`.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A (eq:Auprop, eq:Fu).
-/

open scoped Matrix BigOperators
open Matrix

namespace MPSTensor

variable {d D : ℕ}

section CornerTransition

variable {m : ℕ} [NeZero m]

/-- The **corner-transition tensor** `A_u^i = P_u A^i P_{u+1}` of
arXiv:1708.00029, Appendix A, eq:Auprop: the one-site compression of the letter
`A^i` between the sector projectors `P_u` and `P_{u+1}`. -/
def cornerLetter (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin m) (i : Fin d) : MatrixAlg D :=
  P u * A i * P (u + 1)

/-- The **repeated corner-transition product** `F_u^{\mathbf i}` of
arXiv:1708.00029, Appendix A, eq:Fu: the product of corner letters
`A_u^{i_1} A_{u+1}^{i_2} ⋯` along the word, with each successive letter carried
one sector forward.  The empty word evaluates to the projector `P u`. -/
def cornerProd (P : Fin m → MatrixAlg D) (A : MPSTensor d D) :
    Fin m → List (Fin d) → MatrixAlg D
  | u, [] => P u
  | u, i :: w => P u * A i * cornerProd P A (u + 1) w

@[simp]
lemma cornerProd_nil (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (u : Fin m) :
    cornerProd P A u [] = P u := rfl

@[simp]
lemma cornerProd_cons (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin m) (i : Fin d) (w : List (Fin d)) :
    cornerProd P A u (i :: w) = P u * A i * cornerProd P A (u + 1) w := rfl

/-- A single-letter corner product is the corner-transition tensor `A_u^i`. -/
lemma cornerProd_single (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin m) (i : Fin d) :
    cornerProd P A u [i] = cornerLetter P A u i := by
  simp [cornerProd, cornerLetter]

/-- The corner product is fixed on the left by its starting projector:
`P u * F_u = F_u` (projector idempotency, applied to either the head letter or
the empty-word projector). -/
lemma corner_mul_cornerProd (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin m) (w : List (Fin d)) (hP : IsOrthogonalProjection (P u)) :
    P u * cornerProd P A u w = cornerProd P A u w := by
  cases w with
  | nil => simpa [cornerProd] using hP.2
  | cons i w => simp only [cornerProd_cons, ← Matrix.mul_assoc, hP.2]

/-- **Cyclic concatenation law** for corner-transition products
(arXiv:1708.00029, Appendix A, eq:Fu).

Splitting a word as `w₁ ++ w₂` factors the repeated product `F_u` at the
junction sector `u + w₁.length • 1`:
`cornerProd u (w₁ ++ w₂) = cornerProd u w₁ * cornerProd (u + w₁.length • 1) w₂`.
The junction projector is removed by idempotency.  This is the algebraic step by
which the appendix repeats a single sector block around the cycle to reach an
injective length. -/
lemma cornerProd_append (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (hP : ∀ k, IsOrthogonalProjection (P k))
    (u : Fin m) (w₁ w₂ : List (Fin d)) :
    cornerProd P A u (w₁ ++ w₂) =
      cornerProd P A u w₁ * cornerProd P A (u + w₁.length • (1 : Fin m)) w₂ := by
  induction w₁ generalizing u with
  | nil =>
    simp only [List.nil_append, cornerProd_nil, List.length_nil, zero_smul, add_zero]
    exact (corner_mul_cornerProd P A u w₂ (hP u)).symm
  | cons i w₁ ih =>
    simp only [List.cons_append, cornerProd_cons, ih (u + 1), List.length_cons,
      Matrix.mul_assoc]
    congr 2
    -- Realign the running sector index `(u + 1) + w₁.length • 1 = u + (w₁.length + 1) • 1`.
    congr 1
    rw [add_smul, one_smul, add_assoc, add_comm (1 : Fin m)]

end CornerTransition

end MPSTensor
