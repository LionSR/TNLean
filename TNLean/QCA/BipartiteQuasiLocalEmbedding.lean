/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.SiteIndexedSupportAlgebra

/-!
# Faithful bipartite matrix embeddings into the quasi-local algebra

The canonical left/right matrix coordinates on two disjoint regions
embed faithfully into the quasi-local algebra. Their full tensor-factor
ranges become exactly the two finite-region observable algebras.

Source: GNVW, arXiv:0910.3675v2, ordered finite local coordinates in
lines 1251--1278; Cirac et al., arXiv:1703.09188, lines 2292--2300.
-/

open scoped Kronecker

namespace SpinChain

variable {d : ℕ} [NeZero d] {Λ Γ : Finset ℤ}

/-- The canonical finite-to-quasi-local embedding after ordered
bipartite coordinates; GNVW, arXiv:0910.3675v2, lines 1251--1278. -/
noncomputable def bipartiteMatrixToQuasiLocalObservable (h : Disjoint Λ Γ) :
    Matrix (Config d Λ × Config d Γ) (Config d Λ × Config d Γ) ℂ →⋆ₐ[ℂ]
      QuasiLocalAlgebra d :=
  (quasiLocalObservable d (Λ ∪ Γ)).comp
    (bipartiteLocalAlgebraEquiv h).symm.toStarAlgHom

/-- Canonical bipartite matrix coordinates embed faithfully;
GNVW, arXiv:0910.3675v2, finite local image in lines 1251--1258. -/
theorem bipartiteMatrixToQuasiLocalObservable_injective (h : Disjoint Λ Γ) :
    Function.Injective (bipartiteMatrixToQuasiLocalObservable (d := d) h) :=
  (quasiLocalObservable_injective d (Λ ∪ Γ)).comp
    (bipartiteLocalAlgebraEquiv h).symm.injective

/-- The left tensor embedding becomes the canonical observable on the
first region; GNVW, arXiv:0910.3675v2, lines 1251--1278. -/
theorem bipartiteMatrixToQuasiLocalObservable_leftKroneckerEmbed
    (h : Disjoint Λ Γ) (A : Matrix (Config d Λ) (Config d Λ) ℂ) :
    bipartiteMatrixToQuasiLocalObservable h (Matrix.leftKroneckerEmbed A) =
      matrixToQuasiLocalObservable d Λ A := by
  have hi := bipartiteLocalAlgebraEquiv_localInclusion_left h (CStarMatrix.ofMatrix A)
  change (bipartiteLocalAlgebraEquiv h)
    (localInclusion _ (CStarMatrix.ofMatrix A)) =
      Matrix.leftKroneckerEmbed A at hi
  change quasiLocalObservable d (Λ ∪ Γ)
    ((bipartiteLocalAlgebraEquiv h).symm (Matrix.leftKroneckerEmbed A)) = _
  rw [← hi, StarAlgEquiv.symm_apply_apply, quasiLocalObservable_localInclusion]
  rfl

/-- The right tensor embedding becomes the canonical observable on the
second region; GNVW, arXiv:0910.3675v2, lines 1251--1278. -/
theorem bipartiteMatrixToQuasiLocalObservable_rightKroneckerEmbed
    (h : Disjoint Λ Γ) (A : Matrix (Config d Γ) (Config d Γ) ℂ) :
    bipartiteMatrixToQuasiLocalObservable h (Matrix.rightKroneckerEmbed A) =
      matrixToQuasiLocalObservable d Γ A := by
  have hi := bipartiteLocalAlgebraEquiv_localInclusion_right h (CStarMatrix.ofMatrix A)
  change (bipartiteLocalAlgebraEquiv h)
    (localInclusion _ (CStarMatrix.ofMatrix A)) =
      Matrix.rightKroneckerEmbed A at hi
  change quasiLocalObservable d (Λ ∪ Γ)
    ((bipartiteLocalAlgebraEquiv h).symm (Matrix.rightKroneckerEmbed A)) = _
  rw [← hi, StarAlgEquiv.symm_apply_apply, quasiLocalObservable_localInclusion]
  rfl

/-- A product of the two finite-region observables is the observable
of their Kronecker product in the existing ordered bipartite coordinates.
Source: the local tensor-product convention in GNVW, arXiv:0910.3675v2,
lines 1251--1278, and CPSV17, Appendix lines 2292--2300. -/
theorem bipartiteMatrixToQuasiLocalObservable_kronecker
    (h : Disjoint Λ Γ) (A : Matrix (Config d Λ) (Config d Λ) ℂ)
    (B : Matrix (Config d Γ) (Config d Γ) ℂ) :
    bipartiteMatrixToQuasiLocalObservable h (A ⊗ₖ B) =
      matrixToQuasiLocalObservable d Λ A * matrixToQuasiLocalObservable d Γ B := by
  have hprod : A ⊗ₖ B = Matrix.leftKroneckerEmbed A * Matrix.rightKroneckerEmbed B := by
    simp only [Matrix.leftKroneckerEmbed_apply, Matrix.rightKroneckerEmbed_apply,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hprod, map_mul, bipartiteMatrixToQuasiLocalObservable_leftKroneckerEmbed,
    bipartiteMatrixToQuasiLocalObservable_rightKroneckerEmbed]

/-- The full left tensor factor has exactly the first region's observable
range after canonical embedding; GNVW, arXiv:0910.3675v2, shift example,
lines 1251--1268. -/
theorem map_range_leftKroneckerEmbed_bipartiteMatrixToQuasiLocalObservable
    (h : Disjoint Λ Γ) :
    (Matrix.leftKroneckerEmbed (m := Config d Λ) (n := Config d Γ)).range.map
      (bipartiteMatrixToQuasiLocalObservable h) = (quasiLocalObservable d Λ).range := by
  ext z
  constructor
  · rintro ⟨X, ⟨A, rfl⟩, rfl⟩
    exact ⟨CStarMatrix.ofMatrixStarAlgEquiv A,
      (bipartiteMatrixToQuasiLocalObservable_leftKroneckerEmbed h A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨Matrix.leftKroneckerEmbed (CStarMatrix.ofMatrixStarAlgEquiv.symm A),
      ⟨_, rfl⟩, ?_⟩
    change bipartiteMatrixToQuasiLocalObservable h
      (Matrix.leftKroneckerEmbed (CStarMatrix.ofMatrixStarAlgEquiv.symm A)) =
        quasiLocalObservable d Λ A
    rw [bipartiteMatrixToQuasiLocalObservable_leftKroneckerEmbed]
    change quasiLocalObservable d Λ
      (CStarMatrix.ofMatrixStarAlgEquiv (CStarMatrix.ofMatrixStarAlgEquiv.symm A)) = _
    rw [StarAlgEquiv.apply_symm_apply]

/-- The full right tensor factor has exactly the second region's
observable range; GNVW, arXiv:0910.3675v2, inverse shift orientation,
lines 1251--1268. -/
theorem map_range_rightKroneckerEmbed_bipartiteMatrixToQuasiLocalObservable
    (h : Disjoint Λ Γ) :
    (Matrix.rightKroneckerEmbed (m := Config d Λ) (n := Config d Γ)).range.map
      (bipartiteMatrixToQuasiLocalObservable h) = (quasiLocalObservable d Γ).range := by
  ext z
  constructor
  · rintro ⟨X, ⟨A, rfl⟩, rfl⟩
    exact ⟨CStarMatrix.ofMatrixStarAlgEquiv A,
      (bipartiteMatrixToQuasiLocalObservable_rightKroneckerEmbed h A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨Matrix.rightKroneckerEmbed (CStarMatrix.ofMatrixStarAlgEquiv.symm A),
      ⟨_, rfl⟩, ?_⟩
    change bipartiteMatrixToQuasiLocalObservable h
      (Matrix.rightKroneckerEmbed (CStarMatrix.ofMatrixStarAlgEquiv.symm A)) =
        quasiLocalObservable d Γ A
    rw [bipartiteMatrixToQuasiLocalObservable_rightKroneckerEmbed]
    change quasiLocalObservable d Γ
      (CStarMatrix.ofMatrixStarAlgEquiv (CStarMatrix.ofMatrixStarAlgEquiv.symm A)) = _
    rw [StarAlgEquiv.apply_symm_apply]

end SpinChain
