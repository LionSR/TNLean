/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Basic
import TNLean.Algebra.WordAlgebra
import TNLean.MPS.Defs

/-!
# The word-algebra module of a tensor

A tensor `B : MPSTensor d D` defines a representation `ρ_B` of the word algebra on `ℂ^D` by
`ρ_B(x_i) = B^i` (`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.4).
This file packages that module structure as `MPSTensor.WordModule B`, identifies the action of a
word with the word evaluation `Kraus.evalWord`, identifies the word traces with the periodic
coefficients, and proves that normal tensors define simple modules (Lemma 7.4 of the note,
`lem:p5-normal-simple`).

## Main definitions

* `MPSTensor.wordRep B`: the free-monoid representation `w ↦ B^w` on `Fin D → ℂ`.
* `MPSTensor.WordModule B`: the word-algebra module `ℂ^D` of the tensor.

## Main results

* `MPSTensor.asModuleEquiv_ofWord_smul`: `ofWord w • v = B^w v`.
* `MPSTensor.traceWord_wordModule`: the word traces of the module are the traces `tr (B^w)`.
* `MPSTensor.isSimpleModule_wordModule_of_isNormal`: a normal tensor of positive bond dimension
  defines a simple module.
-/

namespace MPSTensor

open WordAlgebra Matrix

variable {d D : ℕ}

/-- The representation of the free monoid on words attached to a tensor, sending the word `w`
to the linear map of `B^w = B^{i_1} ⋯ B^{i_N}`. -/
noncomputable def wordRep (B : MPSTensor d D) : Representation ℂ (FreeMonoid (Fin d)) (Fin D → ℂ) :=
  FreeMonoid.lift fun i => Matrix.toLin' (B i)

lemma wordRep_of (B : MPSTensor d D) (i : Fin d) :
    B.wordRep (FreeMonoid.of i) = Matrix.toLin' (B i) :=
  FreeMonoid.lift_eval_of _ _

lemma wordRep_ofList (B : MPSTensor d D) (w : List (Fin d)) :
    B.wordRep (FreeMonoid.ofList w) = Matrix.toLin' (Kraus.evalWord B w) := by
  induction w with
  | nil => simp [FreeMonoid.ofList_nil, Kraus.evalWord, Module.End.one_eq_id]
  | cons i w ih =>
    rw [FreeMonoid.ofList_cons, map_mul, ih, wordRep_of, Kraus.evalWord, Matrix.toLin'_mul,
      Module.End.mul_eq_comp]

/-- The word-algebra module `ℂ^D` of a tensor. -/
abbrev WordModule (B : MPSTensor d D) := B.wordRep.asModule

/-- Identification of the module with the coordinate space. -/
noncomputable abbrev WordModule.toVec (B : MPSTensor d D) : B.WordModule ≃ₗ[ℂ] (Fin D → ℂ) :=
  B.wordRep.asModuleEquiv

lemma asModuleEquiv_ofWord_smul (B : MPSTensor d D) (w : List (Fin d)) (v : B.WordModule) :
    B.wordRep.asModuleEquiv (ofWord w • v) = Kraus.evalWord B w *ᵥ B.wordRep.asModuleEquiv v := by
  rw [Representation.asModuleEquiv_map_smul, ofWord, Representation.asAlgebraHom_of, wordRep_ofList,
    Matrix.toLin'_apply]

/-- The action of the word algebra on `ℂ^D` is conjugate to matrix-vector multiplication. -/
lemma actAlgHom_wordModule_ofWord (B : MPSTensor d D) (w : List (Fin d)) :
    actAlgHom B.WordModule (ofWord w) =
      B.wordRep.asModuleEquiv.symm.conj (Matrix.toLin' (Kraus.evalWord B w)) := by
  ext v
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, actAlgHom_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.eq_symm_apply,
    asModuleEquiv_ofWord_smul, Matrix.toLin'_apply]

/-- The word traces of the module are the periodic coefficients `tr (B^w)`. -/
lemma traceWord_wordModule (B : MPSTensor d D) (w : List (Fin d)) :
    traceWord B.WordModule w = Matrix.trace (Kraus.evalWord B w) := by
  rw [traceWord_def, actAlgHom_wordModule_ofWord, LinearMap.trace_conj',
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin D)), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin']

lemma traceChar_wordModule_ofWord (B : MPSTensor d D) (w : List (Fin d)) :
    traceChar B.WordModule (ofWord w) = Matrix.trace (Kraus.evalWord B w) :=
  traceWord_wordModule B w

/-- Every vector is reached from a nonzero vector by some matrix. -/
lemma exists_matrix_mulVec_eq {v : Fin D → ℂ} (hv : v ≠ 0) (u : Fin D → ℂ) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, X *ᵥ v = u := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    exact hv (funext fun j => not_not.1 (not_exists.1 h j))
  refine ⟨Matrix.of fun a b => if b = j then u a / v j else 0, ?_⟩
  ext a
  simp [Matrix.mulVec, dotProduct, Finset.sum_ite_eq', div_mul_cancel₀ _ hj]

/-- A normal tensor of positive bond dimension defines a simple module: a nonzero invariant
subspace is invariant under every linear combination of length-`L` words, hence under every
matrix, hence is everything (Lemma 7.4 of the P5 note, `lem:p5-normal-simple`). -/
theorem isSimpleModule_wordModule_of_isNormal (B : MPSTensor d D) (hB : Kraus.IsNormal B)
    (hD : 0 < D) : IsSimpleModule (WordAlgebra d) B.WordModule := by
  obtain ⟨L, -, hL⟩ := hB
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have : Nontrivial (Fin D → ℂ) := inferInstance
  have : Nontrivial B.WordModule := B.wordRep.asModuleEquiv.toEquiv.nontrivial
  rw [isSimpleModule_iff]
  refine ⟨fun K => ?_⟩
  by_cases hK : K = ⊥
  · exact Or.inl hK
  right
  obtain ⟨v, hvK, hv0⟩ := (Submodule.ne_bot_iff K).1 hK
  rw [eq_top_iff]
  intro u _
  obtain ⟨X, hX⟩ := exists_matrix_mulVec_eq (v := B.wordRep.asModuleEquiv v) (by simpa using hv0)
    (B.wordRep.asModuleEquiv u)
  have hmem : ∀ Y ∈ Kraus.wordSpan B L,
      B.wordRep.asModuleEquiv.symm (Y *ᵥ B.wordRep.asModuleEquiv v) ∈ K := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨σ, rfl⟩ := hY
      have := K.smul_mem (ofWord (List.ofFn σ)) hvK
      change B.wordRep.asModuleEquiv.symm
        (Kraus.evalWord B (List.ofFn σ) *ᵥ B.wordRep.asModuleEquiv v) ∈ K
      rwa [← asModuleEquiv_ofWord_smul, LinearEquiv.symm_apply_apply]
    | zero => simp
    | add Y Z _ _ hY hZ =>
      rw [Matrix.add_mulVec, map_add]
      exact K.add_mem hY hZ
    | smul c Y _ hY =>
      rw [Matrix.smul_mulVec, map_smul, ← algebraMap_smul (WordAlgebra d) c]
      exact K.smul_mem (algebraMap ℂ (WordAlgebra d) c) hY
  have := hmem X (hL ▸ Submodule.mem_top)
  rwa [hX, LinearEquiv.symm_apply_apply] at this

end MPSTensor
