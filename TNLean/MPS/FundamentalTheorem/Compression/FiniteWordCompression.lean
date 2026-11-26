/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic
import QICLean.Kraus.Word
import TNLean.MPS.Tensor
import QICLean.Kraus.WordCompression

/-!
# Finite certificates for word compression

Let `B` be a `Fin n`-indexed family of matrices on `ℂ^D`, and let `A` be the
corresponding `Fin n`-indexed family on `ℂ^d`.
This file proves the finite-dimensional compression principle used in
`Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/boundary_equal_modules.tex`:
if rectangular matrices `V : ℂ^d → ℂ^D` and `W : ℂ^D → ℂ^d` satisfy
`W V = 1` and compress every nonempty word of length at most `D - d + 1`, then
they compress every word.  The proof uses the reachable spaces
`span {B^w Vx : |w| ≤ L}`.  Since the initial reachable space has dimension at
least `d`, the chain must stop by level `D - d`; the stopped space is invariant,
and the short word identities give an intertwining quotient map on it.

The second main result identifies this finite certificate with the intrinsic
condition that `A` occurs as an invariant subquotient of `B`: there is a
`B`-invariant subspace `R ⊆ ℂ^D` and a surjective map `q : R → ℂ^d` intertwining
all generators.  This is deliberately a subquotient statement; no invariant
ambient complement is asserted.

## Main declarations

* `Kraus.reachableSpan`: the span of vectors `B^w Vx` with `|w| ≤ L`.
* `Kraus.allWordCompression_of_finiteWordCompression`: the sharp finite
  certificate, with bound `D - d + 1`.
* `Kraus.HasInvariantSubquotient`: invariant-subquotient occurrence.
* `TNLean.MPS.FundamentalTheorem.finiteWordCompression_iff_hasInvariantSubquotient`: equivalence of
  the
  sharp finite certificate and invariant-subquotient occurrence.
-/

open scoped Matrix

namespace Kraus

variable {n d D : ℕ}

namespace InvariantSubquotient

variable {A : MPSTensor n d} {B : MPSTensor n D} (Q : InvariantSubquotient A B)

lemma _root_.TNLean.MPS.FundamentalTheorem.q_evalWord (w : List (Fin n)) (x : Q.R) :
    Q.q ⟨evalWord B w *ᵥ x, Q.evalWord_mem w x⟩ = evalWord A w *ᵥ Q.q x := by
  induction w with
  | nil =>
      simp [evalWord]
  | cons i w ih =>
      have harg :
          (⟨evalWord B (i :: w) *ᵥ x, Q.evalWord_mem (i :: w) x⟩ : Q.R) =
            ⟨B i *ᵥ (evalWord B w *ᵥ x), Q.invariant i _ (Q.evalWord_mem w x)⟩ := by
        apply Subtype.ext
        simp [evalWord, Matrix.mulVec_mulVec]
      calc
        Q.q ⟨evalWord B (i :: w) *ᵥ x, Q.evalWord_mem (i :: w) x⟩
            = Q.q ⟨B i *ᵥ (evalWord B w *ᵥ x), Q.invariant i _ (Q.evalWord_mem w x)⟩ := by
                rw [harg]
        _ = A i *ᵥ Q.q ⟨evalWord B w *ᵥ x, Q.evalWord_mem w x⟩ := by
                simpa using
                  Q.intertwines i ⟨evalWord B w *ᵥ x, Q.evalWord_mem w x⟩
        _ = evalWord A (i :: w) *ᵥ Q.q x := by
                simp [evalWord, ih, Matrix.mulVec_mulVec]

end InvariantSubquotient

private noncomputable def matrixOf (f : (Fin d → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :
    Matrix (Fin D) (Fin d) ℂ :=
  LinearMap.toMatrix' f

private noncomputable def matrixOf' (f : (Fin D → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    Matrix (Fin d) (Fin D) ℂ :=
  LinearMap.toMatrix' f

/-- An invariant subquotient gives matrices `V,W` compressing every word.  The proof chooses a
linear section of `q` and an arbitrary linear extension of `q` from `R` to the ambient space by
projecting onto a complement of `R`; the complement is not asserted to be invariant. -/
theorem _root_.TNLean.MPS.FundamentalTheorem.exists_allWordCompression_of_hasInvariantSubquotient
    {A : MPSTensor n d} {B : MPSTensor n D}
    (h : HasInvariantSubquotient A B) :
    ∃ (V : Matrix (Fin D) (Fin d) ℂ) (W : Matrix (Fin d) (Fin D) ℂ),
      W * V = 1 ∧ AllWordCompression A B V W := by
  classical
  rcases h with ⟨Q⟩
  obtain ⟨s, hs⟩ := Q.q.exists_rightInverse_of_surjective Q.q_surjective
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Q.R
  let p : (Fin D → ℂ) →ₗ[ℂ] Q.R := Q.R.projectionOnto C hC
  let Vlin : (Fin d → ℂ) →ₗ[ℂ] (Fin D → ℂ) := Q.R.subtype.comp s
  let Wlin : (Fin D → ℂ) →ₗ[ℂ] (Fin d → ℂ) := Q.q.comp p
  let V : Matrix (Fin D) (Fin d) ℂ := matrixOf Vlin
  let W : Matrix (Fin d) (Fin D) ℂ := matrixOf' Wlin
  refine ⟨V, W, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    change Matrix.toLin' (LinearMap.toMatrix' Wlin * LinearMap.toMatrix' Vlin) =
      Matrix.toLin' (1 : Matrix (Fin d) (Fin d) ℂ)
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    apply LinearMap.ext
    intro x
    change Wlin (Vlin x) = x
    have hx := congrArg (fun f : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) => f x) hs
    simpa [Wlin, Vlin, p] using hx
  · intro w
    apply Matrix.toLin'.injective
    change Matrix.toLin'
        ((LinearMap.toMatrix' Wlin * evalWord B w) * LinearMap.toMatrix' Vlin) =
      Matrix.toLin' (evalWord A w)
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
      Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    change Wlin ((Matrix.toLin' (evalWord B w)) (Vlin x)) =
      Matrix.toLin' (evalWord A w) x
    have hmem : evalWord B w *ᵥ (Vlin x) ∈ Q.R := by
      simpa [Vlin, Matrix.toLin'_apply] using Q.evalWord_mem w (s x)
    calc
      Wlin ((Matrix.toLin' (evalWord B w)) (Vlin x))
          = Q.q ⟨evalWord B w *ᵥ (s x), hmem⟩ := by
              have hp : p (evalWord B w *ᵥ (s x : Fin D → ℂ)) =
                  ⟨evalWord B w *ᵥ (s x : Fin D → ℂ), hmem⟩ :=
                Submodule.projectionOnto_apply_of_mem_left hC hmem
              simp [Wlin, Vlin, p, Matrix.toLin'_apply, hp]
      _ = evalWord A w *ᵥ Q.q (s x) := TNLean.MPS.FundamentalTheorem.q_evalWord Q w (s x)
      _ = Matrix.toLin' (evalWord A w) x := by
              have hx := congrArg (fun f : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) => f x) hs
              simpa [Matrix.toLin'_apply] using congrArg (fun y => evalWord A w *ᵥ y) hx

/-- An invariant subquotient gives the sharp finite word-compression certificate. -/
theorem _root_.TNLean.MPS.FundamentalTheorem.hasWordCompressionUpTo_of_hasInvariantSubquotient
    {A : MPSTensor n d} {B : MPSTensor n D} :
    HasInvariantSubquotient A B →
      HasWordCompressionUpTo A B (D - d + 1) := by
  intro h
  rcases TNLean.MPS.FundamentalTheorem.exists_allWordCompression_of_hasInvariantSubquotient (A := A)
      (B := B) h with
    ⟨V, W, hWV, hall⟩
  exact ⟨V, W, hWV, fun w _ _ => hall w⟩

/-- Sharp finite word compression is equivalent to invariant-subquotient occurrence. -/
theorem _root_.TNLean.MPS.FundamentalTheorem.finiteWordCompression_iff_hasInvariantSubquotient
    {A : MPSTensor n d} {B : MPSTensor n D} (hD : d ≤ D) :
    HasWordCompressionUpTo A B (D - d + 1) ↔ HasInvariantSubquotient A B :=
  ⟨hasInvariantSubquotient_of_hasWordCompressionUpTo hD,
    TNLean.MPS.FundamentalTheorem.hasWordCompressionUpTo_of_hasInvariantSubquotient⟩

end Kraus
