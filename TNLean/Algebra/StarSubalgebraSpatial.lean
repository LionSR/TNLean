/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Orthogonal reducibility for a star-subalgebra of complex matrices

The spatial input to the structure theory of Wolf Ch. 6 (towards Thm 6.14) is the
fact that a star-closed set of operators reduces orthogonally: whenever a subspace
is invariant, its orthogonal complement is invariant as well. This is the feature
distinguishing a star-subalgebra from a general subalgebra; the abstract
Wedderburn-Artin decomposition only produces a direct sum of matrix algebras,
while the star structure forces that direct sum to be orthogonal, hence realizable
by a single unitary change of basis.

## Main results

* `orthogonal_mem_invtSubmodule_of_adjoint` -- for an operator on a
  finite-dimensional inner product space, the orthogonal complement of a submodule
  invariant under the adjoint is invariant under the operator itself.
* `Matrix.orthogonal_mem_invtSubmodule_toEuclideanLin` -- the matrix form: if a
  subspace of Euclidean space is invariant under the conjugate transpose, its
  orthogonal complement is invariant under the matrix.
* `StarSubalgebra.orthogonal_mem_invtSubmodule` -- for a star-subalgebra of complex
  matrices, the orthogonal complement of a subspace invariant under every member is
  again invariant under every member.
* `StarSubalgebra.isCompl_orthogonal_of_invariant` -- an invariant subspace of a
  star-subalgebra has its orthogonal complement as an invariant complement: the two
  subspaces are complementary and both are invariant.

## Remaining gap towards Wolf Thm 6.14

Orthogonal reducibility supplies an invariant orthogonal complement to every
invariant subspace, which is the central ingredient for an orthogonal
decomposition of the representation space into irreducible pieces. The full
theorem additionally asserts that, after grouping the irreducible pieces into
isotypic components, each component carries a tensor identification of the form
"matrix block on the multiplicity space" and that the assembled change of basis is
a single unitary. That tensor identification and the unitary assembly are not
formalized here; they remain the open steps towards Wolf Thm 6.14.
-/

open scoped Matrix
open scoped InnerProductSpace

namespace StarSubalgebraSpatial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The orthogonal complement of a submodule invariant under the adjoint of an
operator is invariant under the operator. If `p` is mapped into itself by the
adjoint of `f`, then for `x` orthogonal to `p` and `y` in `p` one has
`inner y (f x) = inner (adjoint f y) x = 0`, so `f x` is orthogonal to `p`. -/
theorem orthogonal_mem_invtSubmodule_of_adjoint
    {f : Module.End 𝕜 E} {p : Submodule 𝕜 E}
    (hp : p ∈ Module.End.invtSubmodule (LinearMap.adjoint f)) :
    pᗮ ∈ Module.End.invtSubmodule f :=
  fun _ hx y hy ↦ LinearMap.adjoint_inner_left f _ y ▸ hx (LinearMap.adjoint f y) (hp hy)

end StarSubalgebraSpatial

namespace Matrix

open StarSubalgebraSpatial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The orthogonal complement of a subspace invariant under the conjugate transpose
`Aᴴ` is invariant under `A`, viewing matrices as operators on Euclidean space. The
adjoint of the operator of `A` is the operator of `Aᴴ`. -/
theorem orthogonal_mem_invtSubmodule_toEuclideanLin {A : Matrix n n ℂ}
    {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : p ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin Aᴴ)) :
    pᗮ ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A) := by
  refine orthogonal_mem_invtSubmodule_of_adjoint ?_
  rwa [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at hp

end Matrix

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- For a star-subalgebra of complex matrices, the orthogonal complement of a
subspace invariant under every member of the subalgebra is again invariant under
every member. The orthogonal complement of an invariant subspace is invariant for a
single member precisely when the conjugate transpose of that member is also a
member, which holds for every element of a star-subalgebra. Wolf Ch. 6, towards
Thm 6.14. -/
theorem orthogonal_mem_invtSubmodule {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : ∀ A ∈ S, p ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A)) (A : Matrix n n ℂ)
    (hA : A ∈ S) : pᗮ ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A) := by
  refine Matrix.orthogonal_mem_invtSubmodule_toEuclideanLin ?_
  have hAstar : Aᴴ ∈ S := by
    have := star_mem hA
    rwa [Matrix.star_eq_conjTranspose] at this
  exact hp Aᴴ hAstar

/-- An invariant subspace of a star-subalgebra of complex matrices has its
orthogonal complement as an invariant complement: the subspace and its orthogonal
complement are complementary, and both are invariant under every member of the
subalgebra. This is the spatial semisimplicity of the representation: every
invariant subspace splits off orthogonally. Wolf Ch. 6, towards Thm 6.14. -/
theorem isCompl_orthogonal_of_invariant {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : ∀ A ∈ S, p ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A)) :
    IsCompl p pᗮ ∧ ∀ A ∈ S, pᗮ ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A) :=
  ⟨Submodule.isCompl_orthogonal (K := p), S.orthogonal_mem_invtSubmodule hp⟩

end StarSubalgebra
