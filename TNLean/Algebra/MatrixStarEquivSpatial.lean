/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.SkolemNoetherUnitary
import QICLean.Algebra.MatrixUnitaryBetween
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Spatial implementation between finite full matrix algebras

A star-algebra equivalence between full complex matrix algebras on two
nonempty finite coordinate types is conjugation by a unitary between the
two coordinate spaces. Equality of their dimensions is derived from the
algebra equivalence. The same-index Skolem--Noether theorem is reused
after an explicit coordinate equivalence.

This is the finite spatial step in Schumacher--Werner,
arXiv:quant-ph/0405174, equations bruleU and bruleV, lines 980--1001.
The input is an actual full-matrix equivalence; it supplies no support
algebra, adjacent-generation or local-QCA conclusion independently.
-/

open scoped Matrix

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem reindexed_conjugation (e : m ≃ n) (U : Matrix n n ℂ)
    (A : Matrix m m ℂ) :
    let W := Matrix.reindex (Equiv.refl n) e.symm U
    W * A * Wᴴ = U * Matrix.reindex e e A * Uᴴ := by
  intro W
  let B := Matrix.reindex e e A
  have hA : A = Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm B := by
    ext i j
    simp [B]
  have hstar : Wᴴ = Matrix.reindexLinearEquiv ℂ ℂ e.symm (Equiv.refl n) Uᴴ := by
    simp only [W, Matrix.conjTranspose_reindex]
    rfl
  calc
    W * A * Wᴴ =
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl n) e.symm U *
          Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm B *
            Matrix.reindexLinearEquiv ℂ ℂ e.symm (Equiv.refl n) Uᴴ := by
      rw [hstar, hA]
      rfl
    _ = Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl n) (Equiv.refl n) (U * B * Uᴴ) := by
      rw [Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
        (Equiv.refl n) e.symm e.symm,
        Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
          (Equiv.refl n) e.symm (Equiv.refl n)]
    _ = U * Matrix.reindex e e A * Uᴴ := rfl

/-- Every star-algebra equivalence of two nonzero finite full complex
matrix algebras is implemented by an actual rectangular unitary.
Its coordinate spaces need not have the same index type. Their equal
cardinalities and the implementing unitary are both derived.
Source: Schumacher--Werner, bruleU and bruleV, lines 980--1001;
Skolem--Noether in CPSV16, Appendix C.4. -/
theorem exists_unitary_conj_of_starAlgEquiv_matrix_between [Nonempty m] [Nonempty n]
    (f : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    ∃ U : Matrix n m ℂ, U.IsUnitaryBetween ∧
      ∀ A : Matrix m m ℂ, f A = U * A * Uᴴ := by
  classical
  have hdim : Fintype.card m * Fintype.card m = Fintype.card n * Fintype.card n := by
    simpa only [Module.finrank_matrix, Module.finrank_self, mul_one] using
      f.toAlgEquiv.toLinearEquiv.finrank_eq
  have hcard : Fintype.card m = Fintype.card n := by nlinarith
  let e : m ≃ n := Fintype.equivOfCardEq hcard
  let E := Matrix.matrixReindexStarAlgEquiv e
  let g := E.symm.trans f
  obtain ⟨V, hV⟩ := Matrix.exists_unitary_conj_of_starAlgEquiv_matrix g
  let W : Matrix n m ℂ := Matrix.reindex (Equiv.refl n) e.symm (V : Matrix n n ℂ)
  have hW : W.IsUnitaryBetween :=
    (Matrix.isUnitaryBetween_coe_unitaryGroup V).reindex _ (Equiv.refl n) e.symm
  refine ⟨W, hW, ?_⟩
  intro A
  calc
    f A = g (E A) := by
      change f A = f (E.symm (E A))
      rw [StarAlgEquiv.symm_apply_apply]
    _ = (V : Matrix n n ℂ) * E A * (V : Matrix n n ℂ)ᴴ := hV (E A)
    _ = W * A * Wᴴ := (reindexed_conjugation e (V : Matrix n n ℂ) A).symm

end Matrix
