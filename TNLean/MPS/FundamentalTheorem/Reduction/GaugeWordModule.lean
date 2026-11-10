/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.StarSemisimple
import TNLean.MPS.FundamentalTheorem.Reduction.WordModule
import TNLean.MPS.Symmetry.MPOSymmetry.ZipperUniqueness

/-!
# Gauges give isomorphic word modules

A gauge `X` with `A i * X = X * A' i` is a module isomorphism between the word modules of the
two tensors. Together with the converse (an isomorphism of word modules gives a gauge), this
identifies gauge equivalence with isomorphism of word modules.

## Main results

* `MPSTensor.nonempty_linearEquiv_wordModule_of_isGaugeRelated`: a gauge gives an isomorphism
  of word modules.
* `MPSTensor.IsGaugeRelated.refl`: every tensor is gauge related to itself.
-/

open WordAlgebra

namespace MPSTensor

variable {d : ℕ}

/-- **A gauge is an isomorphism of word modules.** If `A i * X = X * A' i` for every letter with
`X` invertible, then the word modules of `A` and `A'` are isomorphic. -/
theorem nonempty_linearEquiv_wordModule_of_isGaugeRelated {D₁ D₂ : ℕ}
    {A : MPSTensor d D₁} {A' : MPSTensor d D₂} (h : IsGaugeRelated A A') :
    Nonempty (A.WordModule ≃ₗ[WordAlgebra d] A'.WordModule) := by
  obtain ⟨X, Y, hXY, hYX, hint⟩ := h
  have hY : ∀ i, A' i * Y = Y * A i := fun i => by
    calc A' i * Y = Y * X * A' i * Y := by rw [hYX, Matrix.one_mul]
      _ = Y * (A i * X) * Y := by rw [hint, Matrix.mul_assoc Y]
      _ = Y * A i := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hXY, Matrix.mul_one]
  have hw := Kraus.evalWord_intertwine A' A Y hY
  have hcomm : ∀ p : WordAlgebra d,
      (Matrix.toLin' Y).comp (A.wordRep.asAlgebraHom p) =
        (A'.wordRep.asAlgebraHom p).comp (Matrix.toLin' Y) := by
    intro p
    induction p using MonoidAlgebra.induction_on with
    | of g =>
      rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of,
        ← FreeMonoid.ofList_toList g, wordRep_ofList, wordRep_ofList, ← Matrix.toLin'_mul,
        ← Matrix.toLin'_mul, hw]
    | add f g hf hg => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hf, hg]
    | smul r f hf => rw [map_smul, map_smul, LinearMap.comp_smul, LinearMap.smul_comp, hf]
  let g : (Fin D₁ → ℂ) ≃ₗ[ℂ] (Fin D₂ → ℂ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' Y) (Matrix.toLin' X)
      (by rw [← Matrix.toLin'_mul, hYX, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hXY, Matrix.toLin'_one])
  let e : A.WordModule ≃ₗ[ℂ] A'.WordModule :=
    ((A.wordRep.asModuleEquiv).trans g).trans (A'.wordRep.asModuleEquiv).symm
  refine ⟨{ e with map_smul' := fun p v => ?_ }⟩
  change e (p • v) = p • e v
  apply (A'.wordRep.asModuleEquiv).injective
  simp only [e, g, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Representation.asModuleEquiv_map_smul, LinearEquiv.coe_ofLinearMap]
  exact LinearMap.congr_fun (hcomm p) _

/-- Every tensor is gauge related to itself (`X = 1`). -/
theorem IsGaugeRelated.refl {D : ℕ} (A : MPSTensor d D) : IsGaugeRelated A A :=
  ⟨1, 1, Matrix.one_mul 1, Matrix.one_mul 1, fun i => by rw [Matrix.mul_one, Matrix.one_mul]⟩

open WordAlgebra
open scoped Matrix

section GaugeRelatedOfLinearEquiv

variable {d D₁ D₂ : ℕ}

/-- Isomorphic word modules come from gauge related tensors: a word-algebra isomorphism
`A.WordModule ≃ A'.WordModule` is, in coordinates, an invertible matrix intertwining the letters. -/
theorem isGaugeRelated_of_linearEquiv {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    (e : A.WordModule ≃ₗ[WordAlgebra d] A'.WordModule) : IsGaugeRelated A A' := by
  let g : (Fin D₂ → ℂ) ≃ₗ[ℂ] (Fin D₁ → ℂ) :=
    ((WordModule.toVec A').symm.trans (e.symm.restrictScalars ℂ)).trans (WordModule.toVec A)
  have hg : ∀ (i : Fin d) (w : Fin D₂ → ℂ), g (A' i *ᵥ w) = A i *ᵥ g w := by
    intro i w
    obtain ⟨v, rfl⟩ := (WordModule.toVec A').surjective w
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      LinearEquiv.symm_apply_apply]
    rw [← asModuleEquiv_letter_smul, LinearEquiv.symm_apply_apply, map_smul,
      asModuleEquiv_letter_smul]
  refine ⟨LinearMap.toMatrix' (g : (Fin D₂ → ℂ) →ₗ[ℂ] (Fin D₁ → ℂ)),
    LinearMap.toMatrix' (g.symm : (Fin D₁ → ℂ) →ₗ[ℂ] (Fin D₂ → ℂ)), ?_, ?_, fun i => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext w
    simp
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext w
    simp
  · refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec,
      LinearEquiv.coe_coe, hg]

/-- Gauge related tensors have all letters zero together. -/
theorem IsGaugeRelated.forall_eq_zero_iff {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    (h : IsGaugeRelated A A') : (∀ i, A i = 0) ↔ ∀ i, A' i = 0 := by
  obtain ⟨X, Y, hXY, hYX, hint⟩ := h
  refine ⟨fun h0 i => ?_, fun h0 i => ?_⟩
  · calc A' i = Y * (A i * X) := by rw [hint, ← Matrix.mul_assoc, hYX, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.zero_mul, Matrix.mul_zero]
  · calc A i = X * A' i * Y := by rw [← hint, Matrix.mul_assoc, hXY, Matrix.mul_one]
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]

/-- Gauge related tensors have equal bond dimensions. -/
theorem IsGaugeRelated.dim_eq {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    (h : IsGaugeRelated A A') : D₁ = D₂ := by
  obtain ⟨X, Y, hXY, hYX, -⟩ := h
  let e : (Fin D₂ → ℂ) ≃ₗ[ℂ] (Fin D₁ → ℂ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' X) (Matrix.toLin' Y)
      (by rw [← Matrix.toLin'_mul, hXY, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hYX, Matrix.toLin'_one])
  simpa using e.finrank_eq.symm

/-- Gauge relatedness is symmetric. -/
theorem IsGaugeRelated.symm {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    (h : IsGaugeRelated A A') : IsGaugeRelated A' A := by
  obtain ⟨X, Y, hXY, hYX, hint⟩ := h
  refine ⟨Y, X, hYX, hXY, fun i => ?_⟩
  calc A' i * Y = Y * (A i * X) * Y := by
        rw [hint, ← Matrix.mul_assoc, hYX, Matrix.one_mul]
    _ = Y * A i := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hXY, Matrix.mul_one]

/-- Gauge relatedness is transitive. -/
theorem IsGaugeRelated.trans {D₁ D₂ D₃ : ℕ} {A : MPSTensor d D₁} {A' : MPSTensor d D₂}
    {A'' : MPSTensor d D₃} (h : IsGaugeRelated A A') (h' : IsGaugeRelated A' A'') :
    IsGaugeRelated A A'' := by
  obtain ⟨X, Y, hXY, hYX, hint⟩ := h
  obtain ⟨X', Y', hXY', hYX', hint'⟩ := h'
  refine ⟨X * X', Y' * Y, ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc X', hXY', Matrix.one_mul, hXY]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y, hYX, Matrix.one_mul, hYX']
  · rw [← Matrix.mul_assoc, hint, Matrix.mul_assoc, hint', Matrix.mul_assoc]

end GaugeRelatedOfLinearEquiv

end MPSTensor
