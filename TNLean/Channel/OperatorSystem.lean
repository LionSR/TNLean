/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Basic
import TNLean.Channel.TensorMap

/-!
# Operator systems and complete positivity on operator systems

This file sets up the definitions needed to state Wolf's proposition
"Extending cp maps from operator systems"
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 614–619): a
completely positive map defined only on a subspace of a finite-dimensional
`C^*`-algebra extends to a completely positive map on the whole algebra. The
proposition itself is proved in
`Matrix.exists_cp_extension_of_operatorSystem` (`TNLean/Channel/OperatorSystemExtension.lean`).

## Design notes

Wolf's proposition quantifies over two arbitrary finite-dimensional
`C^*`-algebras `A`, `B`; this file takes both to be full matrix algebras
`A = M_m(ℂ)`, `B = M_n(ℂ)`. The two narrowings are not on the same footing.
Taking `B = M_n(ℂ)` is without loss of generality and matches Wolf's own proof
technique: the proof fixes the ancilla dimension `n` and embeds `B` as a
subalgebra of `M_n(ℂ)`, so working with the full matrix algebra `M_n(ℂ)`
directly reproduces the source argument rather than merely being an ambient
convenience. Taking `A = M_m(ℂ)` is a genuine scope restriction: the source
statement allows `A` to be any direct sum of matrix algebras, and the
one-summand case formalized here is not the full proposition. See
`docs/paper-gaps/wolf_ch01_operator_system_extension_matrix_scope.tex`.

An **operator system** `S ⊆ M_m(ℂ)` (line 614) is a subspace closed under the
adjoint and containing the unit. We define `Matrix.IsOperatorSystem` as a
property of a `Submodule ℂ` rather than as a separate structure, so that
`Submodule` membership lemmas (`comap`, `zero_mem`, …) apply directly without
duplication.

Complete positivity of a map `T : S →ₗ[ℂ] M_n(ℂ)` is stated at every level `k`,
generalizing `IsCPMap`/`IsKrausCP` (`TNLean/Channel/Basic.lean`) from maps
defined on all of `M_m(ℂ)` to maps defined only on `S`. Level `k` inputs are
represented as bipartite matrices `X : M_m(ℂ) ⊗ M_k(ℂ)` (indexed by
`Fin m × Fin k`, following `Matrix.bipartiteSlice`/`Matrix.tensorMapId` from
`TNLean/Channel/TensorMap.lean`) whose blocks all lie in `S`; `T ⊗ id_k`
applies `T` to each block.

## Main definitions

* `Matrix.IsOperatorSystem`: `S` contains the unit and is closed under the
  adjoint.
* `Matrix.tensorSubmodule`: the submodule `S ⊗ M_k(ℂ)` of bipartite matrices
  whose blocks lie in `S`.
* `Matrix.tensorMapIdSub`: `T ⊗ id_k` restricted to `S ⊗ M_k(ℂ)`.
* `Matrix.IsCPOnOperatorSystem`: `T` is completely positive at every level.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace Matrix

variable {m n : ℕ}

/-! ### Operator systems -/

/-- **Operator system** (Wolf Ch. 1,
`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, line 614): a
subspace `S` of `M_m(ℂ)` that is closed under the adjoint and contains the
unit element. -/
def IsOperatorSystem (S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  (1 : Matrix (Fin m) (Fin m) ℂ) ∈ S ∧ ∀ ⦃x⦄, x ∈ S → xᴴ ∈ S

theorem IsOperatorSystem.one_mem {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ S :=
  hS.1

theorem IsOperatorSystem.star_mem {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ S) : xᴴ ∈ S :=
  hS.2 hx

/-! ### The bipartite submodule `S ⊗ M_k` -/

/-- The submodule `S ⊗ M_k(ℂ) ⊆ M_m(ℂ) ⊗ M_k(ℂ)`: bipartite matrices, indexed
by `Fin m × Fin k`, all of whose `Matrix.bipartiteSlice` blocks lie in `S`. -/
def tensorSubmodule (S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)) (k : ℕ) :
    Submodule ℂ (Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) where
  carrier := {X | ∀ i j : Fin k, Matrix.bipartiteSlice X i j ∈ S}
  zero_mem' i j := by rw [Matrix.bipartiteSlice_zero]; exact S.zero_mem
  add_mem' {X Y} hX hY i j := by
    rw [Matrix.bipartiteSlice_add]; exact S.add_mem (hX i j) (hY i j)
  smul_mem' c X hX i j := by
    rw [Matrix.bipartiteSlice_smul]; exact S.smul_mem c (hX i j)

theorem mem_tensorSubmodule_iff {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)} {k : ℕ}
    {X : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ} :
    X ∈ tensorSubmodule S k ↔ ∀ i j : Fin k, Matrix.bipartiteSlice X i j ∈ S :=
  Iff.rfl

/-- `S ⊗ M_k(ℂ)` is closed under the adjoint whenever `S` is an operator
system: each block of `Xᴴ` is the adjoint of a block of `X`
(`Matrix.bipartiteSlice_conjTranspose`), and `S` is star-stable. -/
theorem IsOperatorSystem.conjTranspose_mem_tensorSubmodule
    {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)} (hS : IsOperatorSystem S) {k : ℕ}
    {X : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ} (hX : X ∈ tensorSubmodule S k) :
    Xᴴ ∈ tensorSubmodule S k := by
  intro i j
  rw [Matrix.bipartiteSlice_conjTranspose]
  exact hS.star_mem (mem_tensorSubmodule_iff.mp hX j i)

/-! ### Complete positivity on an operator system -/

/-- `T ⊗ id_k` restricted to `S ⊗ M_k(ℂ)`: applying `T` to each
`Matrix.bipartiteSlice` block, which lies in `S` by hypothesis. -/
noncomputable def tensorMapIdSub {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) {k : ℕ}
    (X : ↥(tensorSubmodule S k)) :
    Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ :=
  fun p q => T ⟨Matrix.bipartiteSlice X.1 p.2 q.2, mem_tensorSubmodule_iff.mp X.2 p.2 q.2⟩ p.1 q.1

theorem tensorMapIdSub_apply {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) {k : ℕ}
    (X : ↥(tensorSubmodule S k))
    (i₁ : Fin n) (i₂ : Fin k) (j₁ : Fin n) (j₂ : Fin k) :
    tensorMapIdSub T X (i₁, i₂) (j₁, j₂) =
      T ⟨Matrix.bipartiteSlice X.1 i₂ j₂, mem_tensorSubmodule_iff.mp X.2 i₂ j₂⟩ i₁ j₁ :=
  rfl

/-- `tensorMapIdSub T` as a linear map on `S ⊗ M_k(ℂ)`. -/
noncomputable def tensorMapIdSubLM {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) {k : ℕ} :
    ↥(tensorSubmodule S k) →ₗ[ℂ] Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ where
  toFun := tensorMapIdSub T
  map_add' X Y := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    have hval : ((X + Y : ↥(tensorSubmodule S k)) : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) =
        (X : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) + Y := rfl
    simp only [tensorMapIdSub_apply, Matrix.add_apply, hval]
    rw [show (⟨Matrix.bipartiteSlice (X.1 + Y.1) i₂ j₂, mem_tensorSubmodule_iff.mp
        (X + Y).2 i₂ j₂⟩ : ↥S) =
        (⟨Matrix.bipartiteSlice X.1 i₂ j₂, mem_tensorSubmodule_iff.mp X.2 i₂ j₂⟩ : ↥S) +
        ⟨Matrix.bipartiteSlice Y.1 i₂ j₂, mem_tensorSubmodule_iff.mp Y.2 i₂ j₂⟩ from
      Subtype.ext (Matrix.bipartiteSlice_add X.1 Y.1 i₂ j₂)]
    exact congrFun (congrFun (T.map_add _ _) i₁) j₁
  map_smul' c X := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    have hval : ((c • X : ↥(tensorSubmodule S k)) : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) =
        c • (X : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) := rfl
    simp only [tensorMapIdSub_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, hval]
    rw [show (⟨Matrix.bipartiteSlice (c • X.1) i₂ j₂, mem_tensorSubmodule_iff.mp
        (c • X).2 i₂ j₂⟩ : ↥S) =
        c • (⟨Matrix.bipartiteSlice X.1 i₂ j₂, mem_tensorSubmodule_iff.mp X.2 i₂ j₂⟩ : ↥S) from
      Subtype.ext (Matrix.bipartiteSlice_smul c X.1 i₂ j₂)]
    exact congrFun (congrFun (T.map_smul c _) i₁) j₁

@[simp] theorem tensorMapIdSubLM_apply {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (X : ↥(tensorSubmodule S k)) :
    tensorMapIdSubLM T X = tensorMapIdSub T X := rfl

/-- `T` is **completely positive at level `k`**: for every PSD bipartite matrix
`X ∈ S ⊗ M_k(ℂ)`, the image `(T ⊗ id_k)(X)` is PSD. -/
def IsCPAtLevel {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : Prop :=
  ∀ X : ↥(tensorSubmodule S k), (X : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ).PosSemidef →
    (tensorMapIdSub T X).PosSemidef

/-- **`T` is completely positive on the operator system `S`** (Wolf Ch. 1, line
622): `T` is positive at every level `k` (Wolf's `T_n = T ⊗ id_n`, generalized
from all of `M_m(ℂ)` to the subspace `S`). -/
def IsCPOnOperatorSystem {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ k : ℕ, IsCPAtLevel T k

end Matrix
