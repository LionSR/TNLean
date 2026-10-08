/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import Mathlib.Data.ZMod.Basic

/-!
# Word spans in cyclic matrix degrees

Let the virtual projections satisfy \(P_u A_i=A_iP_{u+1}\).
A word of length \(n\) then lies in the matrix space of cyclic degree
\(n\). Suppose that words of one length \(q\) span the whole space of
that degree. Under the left-canonical normalization, this equality persists
at every length \(q+r\). Indeed, a matrix \(X\) of degree \(q+r\)
satisfies
\[
  X=\sum_{|w|=r}(XA_w^\dagger)A_w,
\]
and every coefficient \(XA_w^\dagger\) has degree \(q\).

This is an algebraic step in the original-chain intersection argument.
The initial spanning equality is a hypothesis here; its derivation from
primitive blocked sectors is separate. In particular, the cyclic matrix
space need not be the full matrix algebra.

Sources: arXiv:1708.00029, Lemma bdcf, for the cyclic sectors;
arXiv:quant-ph/0608197, canonical-form normalization, for the adjoint-word
resolution; Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.11)
and Lemma existenceinteraction, for the intersection argument.
-/

open scoped Matrix BigOperators
namespace MPSTensor
variable {d D m : ℕ}

/-- Matrices of cyclic degree \(n\) satisfy \(P_uX=XP_{u+n}\).
Source: arXiv:1708.00029, Lemma bdcf. The definition itself only requires
an indexed matrix family. -/
def cyclicMatrixSubspace (P : ZMod m → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) where
  carrier := {X | ∀ u, P u * X = X * P (u + (n : ZMod m))}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY u
    simp only [Matrix.mul_add, Matrix.add_mul, hX u, hY u]
  smul_mem' := by
    intro c X hX u
    simp only [Matrix.mul_smul, Matrix.smul_mul, hX u]

/-- A word has its length as cyclic degree.
Source: arXiv:1708.00029, Lemma bdcf. -/
theorem evalWord_mem_cyclicMatrixSubspace
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1)) (w : List (Fin d)) :
    Kraus.evalWord A w ∈ cyclicMatrixSubspace P w.length := by
  induction w with
  | nil => simp [cyclicMatrixSubspace]
  | cons i w ih =>
    intro u
    rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, hshift u i, Matrix.mul_assoc,
      ih (u + 1), ← Matrix.mul_assoc]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
      add_comm (1 : ZMod m) (w.length : ZMod m)]

/-- Every word of fixed length belongs to the corresponding cyclic degree.
Source: arXiv:1708.00029, Lemma bdcf. -/
theorem wordSpan_le_cyclicMatrixSubspace
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1)) (N : ℕ) :
    Kraus.wordSpan A N ≤ cyclicMatrixSubspace P N := by
  rw [Kraus.wordSpan, Submodule.span_le]
  rintro _ ⟨σ, rfl⟩
  simpa only [List.length_ofFn, SetLike.mem_coe] using
    evalWord_mem_cyclicMatrixSubspace A P hshift (List.ofFn σ)

/-- Multiplication by an adjoint subtracts its cyclic degree when the
indexed matrices are Hermitian. Source: arXiv:1708.00029, Lemma bdcf,
with the degree convention above. -/
theorem mul_conjTranspose_mem_cyclicMatrixSubspace
    (P : ZMod m → Matrix (Fin D) (Fin D) ℂ) (hP : ∀ u, (P u).IsHermitian)
    {q r : ℕ} {X Y : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ cyclicMatrixSubspace P (q + r))
    (hY : Y ∈ cyclicMatrixSubspace P r) :
    X * Yᴴ ∈ cyclicMatrixSubspace P q := by
  intro u
  have hYstar := congrArg Matrix.conjTranspose (hY (u + (q : ZMod m)))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    (hP (u + (q : ZMod m))).eq,
    (hP (u + (q : ZMod m) + (r : ZMod m))).eq] at hYstar
  rw [← Matrix.mul_assoc, hX u, Matrix.mul_assoc]
  simpa only [Nat.cast_add, ← add_assoc, Matrix.mul_assoc] using
    congrArg (fun Z : Matrix (Fin D) (Fin D) ℂ => X * Z) hYstar.symm

/-- Left-canonical normalization propagates a full cyclic word span to
every later degree. This is the adjoint-word reconstruction used in the
intersection argument of Nachtergaele, arXiv:cond-mat/9410110,
equations (3.10)--(3.11). The initial spanning equality is explicit. -/
theorem wordSpan_eq_cyclicMatrixSubspace_add
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ u, (P u).IsHermitian)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (hLeft : ∑ i, (A i)ᴴ * A i = 1) {q : ℕ}
    (hSpan : Kraus.wordSpan A q = cyclicMatrixSubspace P q) (r : ℕ) :
    Kraus.wordSpan A (q + r) = cyclicMatrixSubspace P (q + r) := by
  apply le_antisymm (wordSpan_le_cyclicMatrixSubspace A P hshift (q + r))
  intro X hX
  rw [Kraus.wordSpan_add]
  have hsum : (∑ σ : Fin r → Fin d,
      (X * (Kraus.evalWord A (List.ofFn σ))ᴴ) * Kraus.evalWord A (List.ofFn σ)) = X := by
    simp only [Matrix.mul_assoc, ← Finset.mul_sum,
      sum_evalWord_conjTranspose_mul_evalWord A hLeft r, Matrix.mul_one]
  rw [← hsum]
  refine Submodule.sum_mem _ (fun σ _ => Submodule.mul_mem_mul ?_ ?_)
  · rw [hSpan]
    exact mul_conjTranspose_mem_cyclicMatrixSubspace P hP hX
      (by simpa only [List.length_ofFn] using
        evalWord_mem_cyclicMatrixSubspace A P hshift (List.ofFn σ))
  · simpa only [List.length_ofFn] using Kraus.evalWord_mem_wordSpan A (List.ofFn σ)
/-- Once one cyclic degree is spanned, all later degrees are spanned.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.11),
using the cyclic-sector coordinates of arXiv:1708.00029, Lemma bdcf. -/
theorem wordSpan_eq_cyclicMatrixSubspace_of_ge
    (A : MPSTensor d D) (P : ZMod m → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ u, (P u).IsHermitian)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (hLeft : ∑ i, (A i)ᴴ * A i = 1) {q : ℕ}
    (hSpan : Kraus.wordSpan A q = cyclicMatrixSubspace P q)
    {N : ℕ} (hqN : q ≤ N) :
    Kraus.wordSpan A N = cyclicMatrixSubspace P N := by
  simpa only [Nat.add_sub_of_le hqN] using
    wordSpan_eq_cyclicMatrixSubspace_add A P hP hshift hLeft hSpan (N - q)
end MPSTensor
