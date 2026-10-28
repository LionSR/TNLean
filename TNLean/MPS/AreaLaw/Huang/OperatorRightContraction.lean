/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.OperatorSchmidt
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Operator decompositions whose left factors are right contractions

A basis of the actual right operator-block span gives a minimal product decomposition.
Every left factor is a contraction by a linear functional on right matrices. Such
contractions preserve all earlier operator-Schmidt rank bounds, without an assumed
matrix product representation.

Supporting algebra for Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
Claim `c:errorreduction`, decomposition `e:decomp`, lines 584--591. These generic
finite-dimensional statements belong upstream in QICLean's operator-Schmidt development.
-/

open scoped BigOperators Kronecker

namespace Matrix

/-- Contract the right matrix factor by a linear functional. This supplies the left
factors in LVV13, `algo53.tex`, decomposition `e:decomp`, lines 584--591. -/
def operatorRightContraction {m n : Type*}
    (φ : Matrix n n ℂ →ₗ[ℂ] ℂ) (K : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  fun x y ↦ φ (operatorBlock K x y)

/-- A shortest product decomposition can be chosen with every left factor obtained by
right contraction. Supporting algebra for LVV13, `algo53.tex`, `e:decomp`, lines 584--591. -/
theorem exists_operatorRightContraction_decomposition {m n : Type*}
    [Fintype m] [Finite n] (K : Matrix (m × n) (m × n) ℂ) :
    ∃ (φ : Fin (operatorSchmidtRank K) → Matrix n n ℂ →ₗ[ℂ] ℂ)
      (B : Fin (operatorSchmidtRank K) → Matrix n n ℂ),
      K = ∑ j, operatorRightContraction (φ j) K ⊗ₖ B j := by
  classical
  let S := operatorBlockSpan K
  let b := Module.finBasis ℂ S
  let φ := fun t ↦ (b.coord t).comp S.subtype.leftInverse
  have hblock (x y : m) : operatorBlock K x y ∈ S :=
    Submodule.subset_span ⟨(x, y), rfl⟩
  rw [operatorSchmidtRank_eq_finrank_operatorBlockSpan]
  refine ⟨φ, fun t ↦ (b t : Matrix n n ℂ), ?_⟩
  ext ⟨x, u⟩ ⟨y, v⟩
  have hrec := congrArg (fun X : S ↦ (X : Matrix n n ℂ))
    (b.sum_repr ⟨operatorBlock K x y, hblock x y⟩)
  have hφ (t) : φ t (operatorBlock K x y) = b.repr ⟨_, hblock x y⟩ t := by
    dsimp only [φ, LinearMap.comp_apply]
    change (b.coord t) (S.subtype.leftInverse (S.subtype ⟨_, hblock x y⟩)) = _
    rw [LinearMap.leftInverse_apply_of_inj S.ker_subtype]
    rfl
  have hentry := congrFun (congrFun hrec u) v
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply,
    Matrix.smul_apply, kroneckerMap_apply, operatorRightContraction, hφ, smul_eq_mul,
    operatorBlock_apply] using hentry.symm

/-- Contracting the last factor of a three-factor operator cannot increase its rank at
the first cut. Supporting algebra for LVV13, `algo53.tex`, Claim `c:errorreduction`,
the internal bond bound at line 591. Empty factors and zero ranks are included. -/
theorem operatorSchmidtRank_operatorRightContraction_le {a b c : Type*}
    [Fintype a] [Finite b] [Finite c]
    (φ : Matrix c c ℂ →ₗ[ℂ] ℂ) (K : Matrix ((a × b) × c) ((a × b) × c) ℂ) :
    operatorSchmidtRank (operatorRightContraction φ K) ≤
      operatorSchmidtRank (K.reindex (Equiv.prodAssoc a b c) (Equiv.prodAssoc a b c)) := by
  classical
  let := Fintype.ofFinite b
  obtain ⟨A, Y, hK⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank
    (K.reindex (Equiv.prodAssoc a b c) (Equiv.prodAssoc a b c))
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨A, fun j ↦ operatorRightContraction φ (Y j), ?_⟩
  ext ⟨x, u⟩ ⟨y, v⟩
  have hblock : operatorBlock K (x, u) (y, v) =
      ∑ j, A j x y • operatorBlock (Y j) u v := by
    ext z z'
    simpa only [reindex_apply, submatrix_apply, Equiv.symm_symm,
      Equiv.prodAssoc_symm_apply, Matrix.sum_apply, kroneckerMap_apply,
      Matrix.smul_apply, smul_eq_mul, operatorBlock_apply] using
      congrArg (fun M ↦ M (x, (u, z)) (y, (v, z'))) hK
  change φ (operatorBlock K (x, u) (y, v)) = _
  simp only [hblock, map_sum, map_smul, smul_eq_mul, Matrix.sum_apply,
    kroneckerMap_apply, operatorRightContraction]

end Matrix
