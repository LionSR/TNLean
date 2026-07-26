/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SkolemNoether

/-!
# Algebra isomorphisms between finite matrix algebras

This file shows that an algebra isomorphism between finite full matrix algebras is inner after
identifying their matrix sizes.
-/

open scoped Matrix

namespace MPSTensor

/-- An algebra isomorphism between full matrix algebras is conjugation by an
invertible matrix after the matrix sizes are identified.

Source: arXiv:1804.04964, Section 3, lines 582--586:
after the insertion correspondence is shown to be an algebra isomorphism
between full matrix algebras, the paper identifies the two matrix sizes and
applies Skolem--Noether to obtain an invertible gauge matrix. -/
theorem matrixAlgEquiv_inner_of_fin {D E : ℕ}
    (φ : Matrix (Fin D) (Fin D) ℂ ≃ₐ[ℂ] Matrix (Fin E) (Fin E) ℂ) :
    ∃ h : D = E, ∃ X : GL (Fin E) ℂ,
      ∀ M : Matrix (Fin D) (Fin D) ℂ,
        φ M = (X : Matrix (Fin E) (Fin E) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) M *
            ((X⁻¹ : GL (Fin E) ℂ) : Matrix (Fin E) (Fin E) ℂ) := by
  classical
  have hDE : D = E := matrixAlgEquiv_fin_eq φ
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₐ[ℂ] Matrix (Fin E) (Fin E) ℂ :=
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr hDE)
  let f : Matrix (Fin E) (Fin E) ℂ ≃ₐ[ℂ] Matrix (Fin E) (Fin E) ℂ :=
    e.symm.trans φ
  obtain ⟨X, hX⟩ := skolemNoether_matrix (f := f)
  refine ⟨hDE, X, ?_⟩
  intro M
  calc φ M
      = f (e M) := by
          change φ (e.symm (e M)) = φ M
          rw [AlgEquiv.symm_apply_apply]
    _ = (X : Matrix (Fin E) (Fin E) ℂ) * e M *
          ((X⁻¹ : GL (Fin E) ℂ) : Matrix (Fin E) (Fin E) ℂ) := hX (e M)
    _ = (X : Matrix (Fin E) (Fin E) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr hDE) M *
          ((X⁻¹ : GL (Fin E) ℂ) : Matrix (Fin E) (Fin E) ℂ) := by rfl

end MPSTensor
