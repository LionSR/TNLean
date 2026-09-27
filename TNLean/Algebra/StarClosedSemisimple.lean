/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.RingTheory.SimpleModule.Basic
import QICLean.Algebra.StarSubalgebraSpatial

/-!
# A star-closed matrix algebra acts semisimply

A unital algebra of complex square matrices that is closed under conjugate transposition acts
semisimply on the coordinate space: every invariant subspace has an invariant complement, namely
its orthogonal complement for the standard inner product. This is the splitting criterion of the
asymmetric compression theorem
(`Notes/OpenProblemsTN/strategies/final_resolution/p5_local_zipper_hypotheses.tex`, the adjoint
closure hypothesis): a fixed occurrence of a block splits off exactly when the step of the
invariant flag carrying it is a direct summand, and adjoint closure of the generated matrix
algebra is a sufficient condition for that.

## Main results

* `StarSubalgebra.submoduleOfInvariant`: a complex subspace preserved by every member of a
  star-subalgebra, read as a submodule over it.
* `StarSubalgebra.isSemisimpleModule`: a star-subalgebra of complex matrices makes the coordinate
  space a semisimple module.
-/

open scoped Matrix

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complex subspace of the coordinate space preserved by every member of `S`, read as a
submodule over `S`. -/
def submoduleOfInvariant (S : StarSubalgebra ℂ (Matrix n n ℂ)) (W : Submodule ℂ (n → ℂ))
    (hW : ∀ A ∈ S, ∀ v ∈ W, A *ᵥ v ∈ W) : Submodule S.toSubalgebra (n → ℂ) where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' A _ hv := hW A.1 A.2 _ hv

@[simp] theorem mem_submoduleOfInvariant {S : StarSubalgebra ℂ (Matrix n n ℂ)}
    {W : Submodule ℂ (n → ℂ)} {hW : ∀ A ∈ S, ∀ v ∈ W, A *ᵥ v ∈ W} {v : n → ℂ} :
    v ∈ S.submoduleOfInvariant W hW ↔ v ∈ W := Iff.rfl

/-- **Semisimplicity of a star-closed matrix algebra**. A star-subalgebra of complex square
matrices, acting on the coordinate space by matrix-vector multiplication, makes it a semisimple
module: the orthogonal complement of an invariant subspace is invariant, because the conjugate
transposes of the members preserve the subspace itself. -/
theorem isSemisimpleModule (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    IsSemisimpleModule S.toSubalgebra (n → ℂ) := by
  rw [isSemisimpleModule_iff]
  refine ⟨fun K => ?_⟩
  set κ : EuclideanSpace ℂ n ≃ₗ[ℂ] (n → ℂ) := WithLp.linearEquiv 2 ℂ (n → ℂ)
  set p : Submodule ℂ (EuclideanSpace ℂ n) := (K.restrictScalars ℂ).comap (κ : _ →ₗ[ℂ] _) with hp
  have hinv : ∀ A ∈ S, p ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A) :=
    fun A hA x hx => K.smul_mem (⟨A, hA⟩ : S.toSubalgebra) hx
  obtain ⟨hcompl, hperp⟩ := S.isCompl_orthogonal_of_invariant hinv
  refine ⟨S.submoduleOfInvariant (pᗮ.map (κ : _ →ₗ[ℂ] _)) ?_, ?_⟩
  · rintro A hA _ ⟨x, hx, rfl⟩
    exact ⟨Matrix.toEuclideanLin A x, hperp A hA hx, rfl⟩
  rw [← Submodule.isCompl_restrictScalars_iff ℂ]
  have hK : K.restrictScalars ℂ = p.map (κ : _ →ₗ[ℂ] _) := by
    rw [hp, Submodule.map_comap_eq_of_surjective κ.surjective]
  rw [hK]
  exact (Submodule.orderIsoMapComap κ).isCompl hcompl

end StarSubalgebra
