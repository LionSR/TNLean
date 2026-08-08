/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.OperatorSystemExtension
import TNLean.Channel.FixedPoint.DirectSumExtension
import TNLean.Channel.LocalizedKrausCPTP
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Extending completely positive maps from operator systems in a direct sum of matrix algebras

Wolf's proposition "Extending cp maps from operator systems"
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 616--626) quantifies the
domain algebra over an arbitrary finite-dimensional `C^*`-algebra, i.e. a finite direct sum
`⊕_k M_{d_k}(ℂ)` of full matrix algebras.
`Matrix.exists_cp_extension_of_operatorSystem` (`TNLean/Channel/OperatorSystemExtension.lean`)
proves only the one-summand case `A = M_m(ℂ)`; this file removes that scope restriction by
transporting the one-summand theorem along the block-diagonal embedding of `⊕_k M_{d_k}(ℂ)`
into a single ambient algebra `M_M(ℂ)`, `M = Σ_k d_k`, closing
`docs/paper-gaps/wolf_ch01_operator_system_extension_matrix_scope.tex`.

## Direct-sum formulation

The direct-sum algebra `⊕_{k : Fin r} M_{d_k}(ℂ)` is represented as the dependent function type
`∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ`, matching the direct-sum matrix algebra used for
Wolf's Theorem 6.14 block structure (`Matrix.directSumDiagonalEmbedding`,
`TNLean/Channel/FixedPoint/DirectSumExtension.lean`). An **operator system** and **complete
positivity at level `j`** for this domain (`Matrix.IsOperatorSystemDirectSum`,
`Matrix.IsCPOnOperatorSystemDirectSum`, `Matrix.IsCPMapDirectSum`) are defined entrywise, block
by block, mirroring the single-summand predicates in `TNLean/Channel/OperatorSystem.lean`; this
is the direct-sum `C^*`-algebra's canonical order and star structure, in which each block
carries its own adjoint and positivity independently of the others.

## Proof route

Fix the block-diagonal embedding `ψ : (∀ k, M_{d_k}(ℂ)) →ₗ[ℂ] M_M(ℂ)`
(`Matrix.directSumEmbedFin`), the composite of `Matrix.directSumDiagonalEmbedding` with the
canonical reindexing `finSigmaFinEquiv : (Σ k, Fin (d k)) ≃ Fin M`. Given an operator system `S`
in the direct-sum algebra and a map `T` completely positive on `S`, push `S` and `T` forward
along `ψ` to an operator system `S'' ⊆ M_M(ℂ)` and a map `T''` completely positive on `S''`: the
key step is that `ψ` and its level-`j` analogues intertwine the per-block bipartite slices with
the ambient bipartite slices (`Matrix.bipartiteSlice_directSumEmbedFinLevel`), so complete
positivity transports across every tensor level. Apply
`Matrix.exists_cp_extension_of_operatorSystem` to `T''` to obtain a Kraus-form extension to all
of `M_M(ℂ)`, and restrict it back to the direct-sum algebra by precomposition with `ψ`. The
restriction is completely positive on the whole direct-sum algebra by the same level-transport
argument, applied this time with `S = ⊤`.

## Main results

* `Matrix.IsOperatorSystemDirectSum`, `Matrix.IsCPOnOperatorSystemDirectSum`,
  `Matrix.IsCPMapDirectSum`: the direct-sum-domain analogues of `Matrix.IsOperatorSystem` and
  `Matrix.IsCPOnOperatorSystem`, the third being the whole-algebra case: entrywise complete
  positivity at every tensor level `j`.
* `Matrix.exists_cp_extension_of_operatorSystem_directSum`: the proposition itself, for the
  direct-sum domain `⊕_{k : Fin r} M_{d_k}(ℂ)`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace Matrix

variable {r : ℕ} {d : Fin r → ℕ} {p : ℕ}

/-! ### Operator systems and complete positivity in a direct sum of matrix algebras -/

/-- **Operator system in a direct sum of matrix algebras** (Wolf Ch. 1,
`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, line 614, generalized from the
single-summand case `Matrix.IsOperatorSystem` to a finite direct sum `⊕_k M_{d_k}(ℂ)`): a
subspace `S` of `∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ` closed under the entrywise adjoint and
containing the unit. -/
def IsOperatorSystemDirectSum (S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)) :
    Prop :=
  (1 : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) ∈ S ∧ ∀ ⦃x⦄, x ∈ S → (fun k => (x k)ᴴ) ∈ S

theorem IsOperatorSystemDirectSum.one_mem
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (hS : IsOperatorSystemDirectSum S) : (1 : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) ∈ S :=
  hS.1

theorem IsOperatorSystemDirectSum.star_mem
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (hS : IsOperatorSystemDirectSum S) {x : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ} (hx : x ∈ S) :
    (fun k => (x k)ᴴ) ∈ S :=
  hS.2 hx

/-- The submodule `S ⊗ M_j(ℂ)` of a direct sum of matrix algebras: families of bipartite
matrices, one per block, all of whose `Matrix.bipartiteSlice` blocks (at every fixed pair of
`M_j` indices) lie in `S`. -/
def tensorSubmoduleDirectSum
    (S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)) (j : ℕ) :
    Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ) where
  carrier := {X | ∀ i l : Fin j, (fun k => Matrix.bipartiteSlice (X k) i l) ∈ S}
  zero_mem' i l := by
    simp only [Pi.zero_apply]
    have h0 : (fun k : Fin r => Matrix.bipartiteSlice
        (0 : Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ) i l) = 0 := by
      funext k; exact Matrix.bipartiteSlice_zero i l
    rw [h0]; exact S.zero_mem
  add_mem' {X Y} hX hY i l := by
    simp only [Pi.add_apply]
    have hadd : (fun k => Matrix.bipartiteSlice (X k + Y k) i l) =
        (fun k => Matrix.bipartiteSlice (X k) i l) +
          fun k => Matrix.bipartiteSlice (Y k) i l := by
      funext k; exact Matrix.bipartiteSlice_add (X k) (Y k) i l
    rw [hadd]; exact S.add_mem (hX i l) (hY i l)
  smul_mem' c X hX i l := by
    simp only [Pi.smul_apply]
    have hsmul : (fun k => Matrix.bipartiteSlice (c • X k) i l) =
        c • fun k => Matrix.bipartiteSlice (X k) i l := by
      funext k; exact Matrix.bipartiteSlice_smul c (X k) i l
    rw [hsmul]; exact S.smul_mem c (hX i l)

theorem mem_tensorSubmoduleDirectSum_iff
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)} {j : ℕ}
    {X : ∀ k, Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ} :
    X ∈ tensorSubmoduleDirectSum S j ↔
      ∀ i l : Fin j, (fun k => Matrix.bipartiteSlice (X k) i l) ∈ S :=
  Iff.rfl

/-- `T ⊗ id_j` restricted to `S ⊗ M_j(ℂ)`, for `T` defined on an operator system `S` of a
direct sum of matrix algebras. -/
noncomputable def tensorMapIdSubDirectSum
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) {j : ℕ}
    (X : ↥(tensorSubmoduleDirectSum S j)) : Matrix (Fin p × Fin j) (Fin p × Fin j) ℂ :=
  fun p₁ p₂ =>
    T ⟨fun k => Matrix.bipartiteSlice (X.1 k) p₁.2 p₂.2,
      mem_tensorSubmoduleDirectSum_iff.mp X.2 p₁.2 p₂.2⟩ p₁.1 p₂.1

/-- **`T` is completely positive on the operator system `S`** of a direct sum of matrix
algebras (Wolf Ch. 1, line 622, generalized from `Matrix.IsCPOnOperatorSystem`): entrywise
(block-by-block) positive semidefiniteness is preserved at every tensor level `j`. -/
def IsCPOnOperatorSystemDirectSum
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) : Prop :=
  ∀ j : ℕ, ∀ X : ↥(tensorSubmoduleDirectSum S j), (∀ k, (X.1 k).PosSemidef) →
    (tensorMapIdSubDirectSum T X).PosSemidef

/-- `T ⊗ id_j` for a linear map defined on the whole direct sum algebra. -/
noncomputable def tensorMapIdDirectSum
    (T : (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) {j : ℕ}
    (X : ∀ k, Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ) :
    Matrix (Fin p × Fin j) (Fin p × Fin j) ℂ :=
  fun p₁ p₂ => T (fun k => Matrix.bipartiteSlice (X k) p₁.2 p₂.2) p₁.1 p₂.1

/-- **`T` is completely positive on a direct sum of matrix algebras** (Wolf Ch. 1,
lines 616--626, the `T ⊗ id_j` ampliation positivity condition applied to the whole
direct-sum algebra; the whole-algebra case of `Matrix.IsCPOnOperatorSystemDirectSum`):
entrywise positive semidefiniteness is preserved at every tensor level `j`. -/
def IsCPMapDirectSum
    (T : (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) : Prop :=
  ∀ j : ℕ, ∀ X : ∀ k, Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ,
    (∀ k, (X k).PosSemidef) → (tensorMapIdDirectSum T X).PosSemidef

/-! ### The block-diagonal embedding into a single matrix algebra -/

/-- The block-diagonal embedding of the direct-sum algebra `⊕_{k : Fin r} M_{d_k}(ℂ)` into the
single ambient algebra `M_M(ℂ)`, `M = Σ_k d_k`: `Matrix.directSumDiagonalEmbedding` followed by
the canonical reindexing `finSigmaFinEquiv`. This realizes the block-diagonal embedding of a
finite-dimensional `C^*`-algebra into a full matrix algebra used in Wolf's proof route. -/
noncomputable def directSumEmbedFin :
    (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ]
      Matrix (Fin (∑ k, d k)) (Fin (∑ k, d k)) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv).toLinearMap ∘ₗ
    Matrix.directSumDiagonalEmbedding

theorem directSumEmbedFin_apply (A : ∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    directSumEmbedFin A =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv (Matrix.blockDiagonal' A) :=
  rfl

theorem directSumEmbedFin_injective :
    Function.Injective (directSumEmbedFin (r := r) (d := d)) := by
  intro A B hAB
  rw [directSumEmbedFin_apply, directSumEmbedFin_apply] at hAB
  exact Matrix.blockDiagonal'_inj.mp
    ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv).injective hAB)

theorem directSumEmbedFin_one :
    directSumEmbedFin (1 : ∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) = 1 := by
  change (Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv).toLinearMap
    (Matrix.directSumDiagonalEmbedding 1) = 1
  rw [Matrix.directSumDiagonalEmbedding_apply, Matrix.blockDiagonal'_one]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ finSigmaFinEquiv

theorem directSumEmbedFin_conjTranspose (A : ∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    directSumEmbedFin (fun k => (A k)ᴴ) = (directSumEmbedFin A)ᴴ := by
  ext p q
  simp only [directSumEmbedFin_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.conjTranspose_apply, ← Matrix.blockDiagonal'_conjTranspose]

/-! ### Positive semidefiniteness of a block-diagonal family -/

theorem directSumEmbedFin_posSemidef_iff (A : ∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    (directSumEmbedFin A).PosSemidef ↔ ∀ k, (A k).PosSemidef := by
  rw [directSumEmbedFin_apply, Matrix.reindex_apply,
    Matrix.posSemidef_submatrix_equiv finSigmaFinEquiv.symm, blockDiagonal'_posSemidef_iff]

/-! ### The level-`j` embedding and the key transport lemma -/

/-- The reindexing used to embed the level-`j` tensor of the direct-sum algebra into the
level-`j` tensor of the ambient algebra `M_M(ℂ)`: distribute the `M_j` factor across the sigma
type, then reindex the block index via `finSigmaFinEquiv`. -/
def directSumLevelEquiv (j : ℕ) :
    (Σ k : Fin r, Fin (d k) × Fin j) ≃ Fin (∑ k, d k) × Fin j :=
  (Equiv.sigmaProdDistrib (fun k : Fin r => Fin (d k)) (Fin j)).symm.trans
    (finSigmaFinEquiv.prodCongr (Equiv.refl (Fin j)))

theorem directSumLevelEquiv_apply (j : ℕ) (k : Fin r) (a : Fin (d k)) (i : Fin j) :
    directSumLevelEquiv j ⟨k, (a, i)⟩ = (finSigmaFinEquiv ⟨k, a⟩, i) := by
  simp [directSumLevelEquiv, Equiv.sigmaProdDistrib]

theorem directSumLevelEquiv_symm_apply (j : ℕ) (p : Fin (∑ k, d k)) (i : Fin j) :
    (directSumLevelEquiv j).symm (p, i) =
      ⟨(finSigmaFinEquiv.symm p).1, ((finSigmaFinEquiv.symm p).2, i)⟩ := by
  simp [directSumLevelEquiv, Equiv.sigmaProdDistrib]

/-- The level-`j` block-diagonal embedding of the `j`-th tensor power of the direct-sum algebra
into the `j`-th tensor power of the ambient algebra, compatible with `Matrix.directSumEmbedFin`
via `Matrix.bipartiteSlice_directSumEmbedFinLevel`. -/
noncomputable def directSumEmbedFinLevel (j : ℕ) :
    (∀ k : Fin r, Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ) →ₗ[ℂ]
      Matrix (Fin (∑ k, d k) × Fin j) (Fin (∑ k, d k) × Fin j) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ (directSumLevelEquiv j) (directSumLevelEquiv j)).toLinearMap ∘ₗ
    Matrix.directSumDiagonalEmbedding

theorem directSumEmbedFinLevel_apply (j : ℕ)
    (X : ∀ k : Fin r, Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ) :
    directSumEmbedFinLevel j X =
      Matrix.reindex (directSumLevelEquiv j) (directSumLevelEquiv j) (Matrix.blockDiagonal' X) :=
  rfl

theorem directSumEmbedFinLevel_posSemidef_iff (j : ℕ)
    (X : ∀ k : Fin r, Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ) :
    (directSumEmbedFinLevel j X).PosSemidef ↔ ∀ k, (X k).PosSemidef := by
  rw [directSumEmbedFinLevel_apply, Matrix.reindex_apply,
    Matrix.posSemidef_submatrix_equiv (directSumLevelEquiv j).symm, blockDiagonal'_posSemidef_iff]

/-- **Key transport lemma**: slicing the level-`j` ambient embedding at a fixed pair of `M_j`
indices reproduces the level-`0` embedding of the per-block slices. This is the fact that
complete positivity at every tensor level descends through the block-diagonal embedding. -/
theorem bipartiteSlice_directSumEmbedFinLevel (j : ℕ)
    (X : ∀ k : Fin r, Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ) (i l : Fin j) :
    Matrix.bipartiteSlice (directSumEmbedFinLevel j X) i l =
      directSumEmbedFin (fun k => Matrix.bipartiteSlice (X k) i l) := by
  ext p q
  rw [Matrix.bipartiteSlice_apply, directSumEmbedFinLevel_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, directSumEmbedFin_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, directSumLevelEquiv_symm_apply, directSumLevelEquiv_symm_apply]
  rcases hp : finSigmaFinEquiv.symm p with ⟨kp, ap⟩
  rcases hq : finSigmaFinEquiv.symm q with ⟨kq, aq⟩
  by_cases hk : kp = kq
  · subst hk
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq,
      Matrix.bipartiteSlice_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hk, Matrix.blockDiagonal'_apply_ne _ _ _ hk]

/-! ### Compressing back onto a single block -/

/-- Extract the `k`-th block of a matrix on the ambient algebra `M_M(ℂ)`, via the canonical
reindexing `finSigmaFinEquiv`. Left inverse to `Matrix.directSumEmbedFin`. -/
noncomputable def directSumCompressFin (Z : Matrix (Fin (∑ k, d k)) (Fin (∑ k, d k)) ℂ)
    (k : Fin r) : Matrix (Fin (d k)) (Fin (d k)) ℂ :=
  fun a b => Z (finSigmaFinEquiv ⟨k, a⟩) (finSigmaFinEquiv ⟨k, b⟩)

theorem directSumCompressFin_directSumEmbedFin
    (A : ∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    directSumCompressFin (directSumEmbedFin A) = A := by
  funext k a b
  rw [directSumCompressFin, directSumEmbedFin_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp [Matrix.blockDiagonal'_apply_eq]

/-- Extract the `k`-th block of a level-`j` matrix on the ambient algebra, via
`Matrix.directSumLevelEquiv`. -/
noncomputable def directSumCompressFinLevel (j : ℕ)
    (Z : Matrix (Fin (∑ k, d k) × Fin j) (Fin (∑ k, d k) × Fin j) ℂ) (k : Fin r) :
    Matrix (Fin (d k) × Fin j) (Fin (d k) × Fin j) ℂ :=
  fun a b => Z (directSumLevelEquiv j ⟨k, a⟩) (directSumLevelEquiv j ⟨k, b⟩)

theorem bipartiteSlice_directSumCompressFinLevel (j : ℕ)
    (Z : Matrix (Fin (∑ k, d k) × Fin j) (Fin (∑ k, d k) × Fin j) ℂ) (k : Fin r) (i l : Fin j) :
    Matrix.bipartiteSlice (directSumCompressFinLevel j Z k) i l =
      directSumCompressFin (Matrix.bipartiteSlice Z i l) k := by
  ext a b
  rw [Matrix.bipartiteSlice_apply, directSumCompressFinLevel, directSumCompressFin,
    Matrix.bipartiteSlice_apply, directSumLevelEquiv_apply, directSumLevelEquiv_apply]

/-! ### Transport of the operator-system and complete-positivity predicates -/

theorem isOperatorSystem_map_directSumEmbedFin
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (hS : IsOperatorSystemDirectSum S) : IsOperatorSystem (S.map directSumEmbedFin) := by
  constructor
  · rw [← directSumEmbedFin_one]; exact Submodule.mem_map_of_mem hS.one_mem
  · rintro x ⟨y, hy, rfl⟩
    rw [← directSumEmbedFin_conjTranspose]
    exact Submodule.mem_map_of_mem (hS.star_mem hy)

/-- The linear equivalence `↥S ≃ₗ[ℂ] ↥(S.map directSumEmbedFin)` induced by the injectivity of
the block-diagonal embedding `Matrix.directSumEmbedFin`. -/
noncomputable def directSumSubmoduleEquiv
    (S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)) :
    ↥S ≃ₗ[ℂ] ↥(S.map directSumEmbedFin) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (S.map directSumEmbedFin) (directSumEmbedFin ∘ₗ S.subtype)
      fun x => Submodule.mem_map_of_mem x.2)
    ⟨fun x y hxy => Subtype.ext (directSumEmbedFin_injective (congrArg Subtype.val hxy)),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem directSumSubmoduleEquiv_apply_coe
    (S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)) (x : ↥S) :
    ((directSumSubmoduleEquiv S x : ↥(S.map directSumEmbedFin)) :
        Matrix (Fin (∑ k, d k)) (Fin (∑ k, d k)) ℂ) = directSumEmbedFin x.1 :=
  rfl

/-- Complete positivity on the direct-sum operator system transports to complete positivity of
the corresponding map on the image of the block-diagonal embedding. -/
theorem isCPOnOperatorSystem_transport
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    {T : ↥S →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ} (hT : IsCPOnOperatorSystemDirectSum T) :
    IsCPOnOperatorSystem (T ∘ₗ (directSumSubmoduleEquiv S).symm.toLinearMap) := by
  intro j Y hY
  have hmem : ∀ i l : Fin j, (fun k => Matrix.bipartiteSlice
      (directSumCompressFinLevel j Y.1 k) i l) ∈ S ∧
      directSumEmbedFin (fun k => Matrix.bipartiteSlice
        (directSumCompressFinLevel j Y.1 k) i l) = Matrix.bipartiteSlice Y.1 i l := by
    intro i l
    obtain ⟨w, hw, hweq⟩ := Submodule.mem_map.mp (mem_tensorSubmodule_iff.mp Y.2 i l)
    have hcomp : (fun k => Matrix.bipartiteSlice
        (directSumCompressFinLevel j Y.1 k) i l) = w := by
      funext k
      rw [bipartiteSlice_directSumCompressFinLevel, ← hweq, directSumCompressFin_directSumEmbedFin]
    rw [hcomp]; exact ⟨hw, hweq⟩
  set X : ↥(tensorSubmoduleDirectSum S j) :=
    ⟨fun k => directSumCompressFinLevel j Y.1 k, fun i l => (hmem i l).1⟩ with hXdef
  have hXPSD : ∀ k, (X.1 k).PosSemidef := fun k =>
    hY.submatrix (fun a : Fin (d k) × Fin j => directSumLevelEquiv j ⟨k, a⟩)
  have key := hT j X hXPSD
  have heq : ∀ i₂ l₂ : Fin j, (directSumSubmoduleEquiv S).symm
      ⟨Matrix.bipartiteSlice Y.1 i₂ l₂, mem_tensorSubmodule_iff.mp Y.2 i₂ l₂⟩ =
      ⟨fun k => Matrix.bipartiteSlice (X.1 k) i₂ l₂, X.2 i₂ l₂⟩ := by
    intro i₂ l₂
    apply (directSumSubmoduleEquiv S).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [directSumSubmoduleEquiv_apply_coe]
    exact ((hmem i₂ l₂).2).symm
  convert key using 1
  ext ⟨i₁, i₂⟩ ⟨l₁, l₂⟩
  change T ((directSumSubmoduleEquiv S).symm.toLinearMap
      ⟨Matrix.bipartiteSlice Y.1 i₂ l₂, mem_tensorSubmodule_iff.mp Y.2 i₂ l₂⟩) i₁ l₁ =
    T ⟨fun k => Matrix.bipartiteSlice (X.1 k) i₂ l₂, X.2 i₂ l₂⟩ i₁ l₁
  rw [LinearEquiv.coe_toLinearMap, heq i₂ l₂]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem tensorMapId_posSemidef_of_isKrausCP {α β δ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype δ] [DecidableEq δ]
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hS : IsKrausCP S)
    {X : Matrix (α × δ) (α × δ) ℂ} (hX : X.PosSemidef) :
    (Matrix.tensorMapId S X).PosSemidef := by
  have hkraus := (tensorMapIdLM_isKrausCP (δ := δ) hS).map_posSemidef hX
  rwa [Matrix.tensorMapIdLM_apply] at hkraus

/-! ### The extension theorem -/

/-- **Extending cp maps from operator systems, direct-sum domain** (Wolf Ch. 1, lines 616--626,
generalized from the single-summand case `Matrix.exists_cp_extension_of_operatorSystem` to a
finite direct sum `⊕_{k : Fin r} M_{d_k}(ℂ)`): a completely positive linear map
`T : S → M_p(ℂ)` defined on an operator system `S ⊆ ⊕_{k : Fin r} M_{d_k}(ℂ)` extends to a
completely positive map `T' : ⊕_{k : Fin r} M_{d_k}(ℂ) → M_p(ℂ)` agreeing with `T` on `S`.

The dimension hypotheses `[NeZero (∑ k, d k)] [NeZero p]` are the direct-sum analogue of the
`[NeZero m] [NeZero n]` convention already used by
`Matrix.exists_cp_extension_of_operatorSystem`. -/
theorem exists_cp_extension_of_operatorSystem_directSum [NeZero (∑ k, d k)] [NeZero p]
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (hS : IsOperatorSystemDirectSum S) {T : ↥S →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ}
    (hT : IsCPOnOperatorSystemDirectSum T) :
    ∃ T' : (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ,
      IsCPMapDirectSum T' ∧ ∀ x : ↥S, T' x.1 = T x := by
  obtain ⟨T'', hT''cp, hT''eq⟩ := exists_cp_extension_of_operatorSystem
    (isOperatorSystem_map_directSumEmbedFin hS) (isCPOnOperatorSystem_transport hT)
  refine ⟨T'' ∘ₗ directSumEmbedFin, ?_, ?_⟩
  · intro j X hX
    have hcompose : tensorMapIdDirectSum (T'' ∘ₗ directSumEmbedFin) X =
        Matrix.tensorMapId T'' (directSumEmbedFinLevel j X) := by
      ext ⟨i₁, i₂⟩ ⟨l₁, l₂⟩
      rw [tensorMapIdDirectSum, Matrix.tensorMapId_apply, LinearMap.comp_apply,
        bipartiteSlice_directSumEmbedFinLevel]
    rw [hcompose]
    exact tensorMapId_posSemidef_of_isKrausCP hT''cp
      ((directSumEmbedFinLevel_posSemidef_iff j X).mpr hX)
  · intro x
    have key := hT''eq (directSumSubmoduleEquiv S x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
      directSumSubmoduleEquiv_apply_coe] at key
    rw [LinearMap.comp_apply]
    exact key

end Matrix
