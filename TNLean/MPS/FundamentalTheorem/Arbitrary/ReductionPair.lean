/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Order.JordanHolder
import QICLean.Algebra.MatrixFamilyAction
import TNLean.Algebra.Subquotient
import TNLean.Algebra.WordAlgebraNilpotent
import TNLean.MPS.Core.ReductionResidual
import TNLean.MPS.Core.ReductionResidual.Basic
import TNLean.MPS.Core.TracePairing
import TNLean.MPS.FundamentalTheorem.Reduction.AdmissibleBlock
import TNLean.MPS.FundamentalTheorem.Arbitrary.ArbitraryTensor
import TNLean.MPS.FundamentalTheorem.Arbitrary.Basic
import TNLean.MPS.FundamentalTheorem.Arbitrary.FlagExistence
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock
import TNLean.MPS.FundamentalTheorem.Reduction.ReachableSubspace
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessAllReductions
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessFlag

/-!
# Reduction pairs onto arbitrary targets and onto one block

A reduction pair from `B` (bond dimension `D`) to `C` (bond dimension `c`) is a pair of matrices,
the projection `P` (`c × D`) and the embedding `E` (`D × c`), with `P E = 1` and
`P B^w E = C^w` for every word (`IsReduction B C P E`); its remainder is the tensor
`R^i = B^i - E C^i P` (`reductionResidual B C P E`).

This file states the description of all reduction pairs onto an arbitrary target through
subquotients of the word module, the placement of a reduction pair in an
invariant flag and in a multi-block reduction. The theorem on one nonzero
irreducible block is in `TNLean.MPS.FundamentalTheorem.Arbitrary.ReductionPairOneBlock`.

The intertwiners between two word modules differ by the invertible matrices commuting with every
letter of `C`; when `C` is irreducible these are the nonzero scalars by Schur's lemma
`exists_eq_smul_one_of_intertwines`.

## Main definitions

* `MPSTensor.IsSubquotSection`: `E` is a linear section of `q ρ`, for an isomorphism `q` from a
  subquotient `U / K` to the word module of `C` and the quotient map `ρ : U → U / K`.
* `MPSTensor.IsSubquotExtension`: `P` extends `q ρ` from `U` to the whole bond space.

## Main results

* `MPSTensor.exists_isReduction_iff_exists_le_and_nonempty_linearEquiv`,
  `MPSTensor.isReduction_iff_exists_isSubquotSection_and_isSubquotExtension`,
  `MPSTensor.IsSubquotSection.isSubquotSection_iff_forall_sub_mulVec_mem`,
  `MPSTensor.IsSubquotExtension.isSubquotExtension_iff_forall_sub_mulVec_eq_zero`,
  `MPSTensor.exists_isUnit_and_forall_commute_and_forall_asModuleEquiv_eq_mulVec`,
  `MPSTensor.exists_linearEquiv_forall_asModuleEquiv_eq_mulVec`.
* `MPSTensor.IsReduction.exists_compositionSeries_map_eq_reachableKer_and_map_eq_reachable`,
  `MPSTensor.IsReduction.exists_multiBlockCompression_map_flag_eq_and_left_eq_and_right_eq`,
  `IsReduction.exists_multiBlockCompression_map_flag_eq_and_leftRow_inr_eq_and_rightCol_inr_eq`.
-/

open scoped Matrix

namespace MPSTensor

open WordAlgebra

variable {d D c : ℕ} {B : MPSTensor d D} {C : MPSTensor d c}

/-! ### Auxiliary facts -/

/-- Membership in a word-algebra submodule through its image in coordinates. -/
theorem mem_iff_of_map_eq {K : Submodule (WordAlgebra d) B.WordModule}
    {V : Submodule ℂ (Fin D → ℂ)}
    (hK : (K.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap = V)
    {x : B.WordModule} : x ∈ K ↔ B.wordRep.asModuleEquiv x ∈ V := by
  rw [← hK]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [(B.wordRep.asModuleEquiv).injective hyx] at hy

/-- The matrix of a word-algebra endomorphism of the word module of `C`. -/
private noncomputable def endMatrix (φ : C.WordModule ≃ₗ[WordAlgebra d] C.WordModule) :
    Matrix (Fin c) (Fin c) ℂ :=
  LinearMap.toMatrix'
    ((C.wordRep.asModuleEquiv.symm.trans ((φ.restrictScalars ℂ).trans C.wordRep.asModuleEquiv) :
      (Fin c → ℂ) ≃ₗ[ℂ] (Fin c → ℂ)) : (Fin c → ℂ) →ₗ[ℂ] (Fin c → ℂ))

private theorem endMatrix_mulVec (φ : C.WordModule ≃ₗ[WordAlgebra d] C.WordModule)
    (v : Fin c → ℂ) :
    endMatrix φ *ᵥ v = C.wordRep.asModuleEquiv (φ (C.wordRep.asModuleEquiv.symm v)) := by
  rw [endMatrix, LinearMap.toMatrix'_mulVec]
  rfl

private theorem endMatrix_mulVec_asModuleEquiv (φ : C.WordModule ≃ₗ[WordAlgebra d] C.WordModule)
    (y : C.WordModule) :
    endMatrix φ *ᵥ C.wordRep.asModuleEquiv y = C.wordRep.asModuleEquiv (φ y) := by
  rw [endMatrix_mulVec, LinearEquiv.symm_apply_apply]

private theorem isUnit_endMatrix (φ : C.WordModule ≃ₗ[WordAlgebra d] C.WordModule) :
    IsUnit (endMatrix φ) := by
  refine ⟨⟨endMatrix φ, endMatrix φ.symm, ?_, ?_⟩, rfl⟩ <;>
  · refine Matrix.mulVec_injective <| funext fun v => ?_
    simp [← Matrix.mulVec_mulVec, endMatrix_mulVec]

private theorem commute_endMatrix (φ : C.WordModule ≃ₗ[WordAlgebra d] C.WordModule) (i : Fin d) :
    Commute (endMatrix φ) (C i) := by
  refine Matrix.mulVec_injective <| funext fun v => ?_
  obtain ⟨y, rfl⟩ := C.wordRep.asModuleEquiv.surjective v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← asModuleEquiv_letter_smul,
    endMatrix_mulVec_asModuleEquiv, endMatrix_mulVec_asModuleEquiv, map_smul,
    asModuleEquiv_letter_smul]

/-! ### All reduction pairs onto an arbitrary target -/

/-- A section and an extension of `q ρ` through a subquotient form a reduction pair (the converse
half of the classification of reduction pairs). -/
private theorem isReduction_of_section_of_extension
    {K U : Submodule (WordAlgebra d) B.WordModule}
    (q : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule) {P : Matrix (Fin c) (Fin D) ℂ}
    {E : Matrix (Fin D) (Fin c) ℂ}
    (hE : ∀ v : Fin c → ℂ, ∃ u : U, B.wordRep.asModuleEquiv (u : B.WordModule) = E *ᵥ v ∧
      C.wordRep.asModuleEquiv (q (Submodule.Quotient.mk u)) = v)
    (hP : ∀ u : U, P *ᵥ B.wordRep.asModuleEquiv (u : B.WordModule) =
      C.wordRep.asModuleEquiv (q (Submodule.Quotient.mk u))) :
    IsReduction B C P E := by
  refine ⟨Matrix.mulVec_injective <| funext fun v => ?_,
    fun w => Matrix.mulVec_injective <| funext fun v => ?_⟩
  · obtain ⟨u, hu, hqu⟩ := hE v
    rw [← Matrix.mulVec_mulVec, ← hu, hP u, hqu, Matrix.one_mulVec]
  · obtain ⟨u, hu, hqu⟩ := hE v
    have h1 := hP ((ofWord w : WordAlgebra d) • u)
    rw [Submodule.coe_smul, asModuleEquiv_ofWord_smul, hu, Submodule.Quotient.mk_smul, map_smul,
      asModuleEquiv_ofWord_smul, hqu] at h1
    simpa only [← Matrix.mulVec_mulVec] using h1

/-- Every isomorphism `q` from a subquotient to the word module of `C` has a linear section and a
linear extension. -/
private theorem exists_section_and_extension {K U : Submodule (WordAlgebra d) B.WordModule}
    (q : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule) :
    ∃ (P : Matrix (Fin c) (Fin D) ℂ) (E : Matrix (Fin D) (Fin c) ℂ),
      (∀ v : Fin c → ℂ, ∃ u : U, B.wordRep.asModuleEquiv (u : B.WordModule) = E *ᵥ v ∧
        C.wordRep.asModuleEquiv (q (Submodule.Quotient.mk u)) = v) ∧
      ∀ u : U, P *ᵥ B.wordRep.asModuleEquiv (u : B.WordModule) =
        C.wordRep.asModuleEquiv (q (Submodule.Quotient.mk u)) := by
  let p : Submodule ℂ B.WordModule := U.restrictScalars ℂ
  let π : p →ₗ[ℂ] (Fin c → ℂ) :=
    { toFun := fun u => C.wordRep.asModuleEquiv (q (Submodule.Quotient.mk ⟨u.1, u.2⟩))
      map_add' := fun u u' => by
        rw [← map_add, ← map_add, ← Submodule.Quotient.mk_add]
        rfl
      map_smul' := fun a u => by
        have hsm : (⟨(a • u).1, (a • u).2⟩ : U) =
            (algebraMap ℂ (WordAlgebra d) a) • (⟨u.1, u.2⟩ : U) := by
          apply Subtype.ext
          change a • (u : B.WordModule) = (algebraMap ℂ (WordAlgebra d) a) • (u : B.WordModule)
          rw [algebraMap_smul]
        rw [hsm, Submodule.Quotient.mk_smul, map_smul, algebraMap_smul, map_smul,
          RingHom.id_apply] }
  have hπ : Function.Surjective π := by
    intro v
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (q.symm (C.wordRep.asModuleEquiv.symm v))
    refine ⟨⟨u.1, u.2⟩, ?_⟩
    change C.wordRep.asModuleEquiv (q (Submodule.Quotient.mk u)) = v
    rw [hu, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨σ, hσ⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend π
  refine ⟨LinearMap.toMatrix' (g ∘ₗ (B.wordRep.asModuleEquiv.symm : (Fin D → ℂ) →ₗ[ℂ] _)),
    LinearMap.toMatrix' ((B.wordRep.asModuleEquiv : B.WordModule →ₗ[ℂ] (Fin D → ℂ)) ∘ₗ
      p.subtype ∘ₗ σ), fun v => ⟨⟨(σ v).1, (σ v).2⟩, ?_, LinearMap.congr_fun hσ v⟩, fun u => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    rfl
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hg ⟨u.1, u.2⟩

/-- **Existence of reduction pairs**. A
reduction pair from `B` to `C` exists if and only if the word module of `C` is isomorphic to a
subquotient `U / K` of the word module of `B`, for invariant subspaces `K ≤ U`. -/
theorem exists_isReduction_iff_exists_le_and_nonempty_linearEquiv :
    (∃ (P : Matrix (Fin c) (Fin D) ℂ) (E : Matrix (Fin D) (Fin c) ℂ), IsReduction B C P E) ↔
      ∃ K U : Submodule (WordAlgebra d) B.WordModule, K ≤ U ∧
        Nonempty (Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule) := by
  constructor
  · rintro ⟨P, E, h⟩
    obtain ⟨U', K', hKU, -, -, hq⟩ := h.exists_quotient_linearEquiv_wordModule
    exact ⟨K', U', hKU, hq⟩
  · rintro ⟨K, U, -, ⟨q⟩⟩
    obtain ⟨P, E, hE, hP⟩ := exists_section_and_extension q
    exact ⟨P, E, isReduction_of_section_of_extension q hE hP⟩

section Subquotient

variable {K U : Submodule (WordAlgebra d) B.WordModule}

/-- **Linear sections through a subquotient**. For
invariant subspaces `K`, `U` of the word module of `B`, an isomorphism `q` from `U / K` to the word
module of `C` and the quotient map `ρ : U → U / K`, the matrix `E` (`D × c`) is a linear section of
`q ρ`: for every `v ∈ ℂ^c` the vector `E v` lies in `U` and `q (ρ (E v)) = v`. -/
def IsSubquotSection (q : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule)
    (E : Matrix (Fin D) (Fin c) ℂ) : Prop :=
  ∀ v : Fin c → ℂ, ∃ u : U, B.wordRep.asModuleEquiv (u : B.WordModule) = E *ᵥ v ∧
    C.wordRep.asModuleEquiv (q (Submodule.Quotient.mk u)) = v

/-- **Linear extensions through a subquotient**. For
invariant subspaces `K`, `U` of the word module of `B`, an isomorphism `q` from `U / K` to the word
module of `C` and the quotient map `ρ : U → U / K`, the matrix `P` (`c × D`) extends `q ρ` from `U`
to `ℂ^D`: `P u = q (ρ u)` for every `u ∈ U`. -/
def IsSubquotExtension (q : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule)
    (P : Matrix (Fin c) (Fin D) ℂ) : Prop :=
  ∀ u : U, P *ᵥ B.wordRep.asModuleEquiv (u : B.WordModule) =
    C.wordRep.asModuleEquiv (q (Submodule.Quotient.mk u))

end Subquotient

/-- **All reduction pairs**. `(P, E)` is a reduction pair
from `B` to `C` if and only if there are invariant subspaces `K ≤ U` and an isomorphism `q` from
`U / K` to the word module of `C` such that, with `ρ : U → U / K` the quotient map, `E` is a linear
section of `q ρ` and `P` extends `q ρ` from `U` to `ℂ^D`. -/
theorem isReduction_iff_exists_isSubquotSection_and_isSubquotExtension
    {P : Matrix (Fin c) (Fin D) ℂ} {E : Matrix (Fin D) (Fin c) ℂ} :
    IsReduction B C P E ↔
      ∃ (K U : Submodule (WordAlgebra d) B.WordModule) (_ : K ≤ U)
        (q : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule),
        IsSubquotSection q E ∧ IsSubquotExtension q P := by
  constructor
  · intro h
    obtain ⟨U', K', f, hKU, hU, -, hsurj, hker, hf⟩ := h.exists_surjective_wordModule_ker_eq
    let q : Submodule.subquot K' U' ≃ₗ[WordAlgebra d] C.WordModule :=
      (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)
    have hq : ∀ u : U', q (Submodule.Quotient.mk u) = f u := fun u => by
      simp only [q, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
        LinearMap.quotKerEquivOfSurjective_apply_mk]
    refine ⟨K', U', hKU, q, fun v => ?_, fun u => by rw [hq, hf]⟩
    have hmem : (B.wordRep.asModuleEquiv).symm (E *ᵥ v) ∈ U' := by
      rw [mem_iff_of_map_eq hU, LinearEquiv.apply_symm_apply]
      exact mulVec_mem_reachable_self E v
    refine ⟨⟨_, hmem⟩, LinearEquiv.apply_symm_apply _ _, ?_⟩
    rw [hq, hf, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, h.mul_eq_one,
      Matrix.one_mulVec]
  · rintro ⟨K, U, -, q, hE, hP⟩
    exact isReduction_of_section_of_extension q hE hP

section Parametrization

variable {K U : Submodule (WordAlgebra d) B.WordModule}

/-- **The sections differ by maps into `K`**. For fixed
`K ≤ U` and `q`, if `E` is a linear section of `q ρ`, then `E'` is one exactly when `E' - E` maps
`ℂ^c` into `K`. -/
theorem IsSubquotSection.isSubquotSection_iff_forall_sub_mulVec_mem
    {q : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule} {E : Matrix (Fin D) (Fin c) ℂ}
    (hE : IsSubquotSection q E) (hKU : K ≤ U) {E' : Matrix (Fin D) (Fin c) ℂ} :
    IsSubquotSection q E' ↔
      ∀ v : Fin c → ℂ, (B.wordRep.asModuleEquiv).symm ((E' - E) *ᵥ v) ∈ K := by
  constructor
  · intro hE' v
    obtain ⟨u, hu, hqu⟩ := hE v
    obtain ⟨u', hu', hqu'⟩ := hE' v
    have hmk : (Submodule.Quotient.mk u' : Submodule.subquot K U) = Submodule.Quotient.mk u :=
      q.injective (C.wordRep.asModuleEquiv.injective (hqu'.trans hqu.symm))
    have hmem := (Submodule.Quotient.eq _).1 hmk
    rw [Submodule.mem_comap] at hmem
    rw [Matrix.sub_mulVec, ← hu, ← hu', ← map_sub, LinearEquiv.symm_apply_apply]
    simpa using hmem
  · intro hK v
    obtain ⟨u, hu, hqu⟩ := hE v
    have hx := hK v
    refine ⟨u + ⟨_, hKU hx⟩, ?_, ?_⟩
    · rw [Submodule.coe_add, map_add, hu, LinearEquiv.apply_symm_apply, Matrix.sub_mulVec,
        add_sub_cancel]
    · have hz : (Submodule.Quotient.mk (⟨_, hKU hx⟩ : U) : Submodule.subquot K U) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hx
      rw [Submodule.Quotient.mk_add, hz, add_zero, hqu]

/-- **The extensions differ by maps vanishing on `U`**. For
fixed `K ≤ U` and `q`, if `P` extends `q ρ`, then `P'` does exactly when `P' - P` vanishes on
`U`. -/
theorem IsSubquotExtension.isSubquotExtension_iff_forall_sub_mulVec_eq_zero
    {q : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule} {P : Matrix (Fin c) (Fin D) ℂ}
    (hP : IsSubquotExtension q P) {P' : Matrix (Fin c) (Fin D) ℂ} :
    IsSubquotExtension q P' ↔
      ∀ u : U, (P' - P) *ᵥ B.wordRep.asModuleEquiv (u : B.WordModule) = 0 := by
  constructor
  · intro hP' u
    rw [Matrix.sub_mulVec, hP' u, hP u, sub_self]
  · intro h0 u
    rw [← hP u, ← sub_eq_zero, ← Matrix.sub_mulVec]
    exact h0 u

/-- **The intertwiners differ by the commutant**. Two
isomorphisms `q`, `q'` from `U / K` to the word module of `C` differ by an invertible matrix
commuting with every letter of `C`. -/
theorem exists_isUnit_and_forall_commute_and_forall_asModuleEquiv_eq_mulVec
    (q q' : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule) :
    ∃ X : Matrix (Fin c) (Fin c) ℂ, IsUnit X ∧ (∀ i, Commute X (C i)) ∧
      ∀ y, C.wordRep.asModuleEquiv (q' y) = X *ᵥ C.wordRep.asModuleEquiv (q y) := by
  refine ⟨endMatrix (q.symm.trans q'), isUnit_endMatrix _, commute_endMatrix _, fun y => ?_⟩
  rw [endMatrix_mulVec_asModuleEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- **Every element of the commutant changes the intertwiner**. An invertible matrix `X` commuting
with every letter of `C` turns an isomorphism `q` from `U / K` to the word module of `C` into
another one, `X q`. -/
theorem exists_linearEquiv_forall_asModuleEquiv_eq_mulVec
    (q : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule) {X : Matrix (Fin c) (Fin c) ℂ}
    (hX : IsUnit X) (hXC : ∀ i, Commute X (C i)) :
    ∃ q' : Submodule.subquot K U ≃ₗ[WordAlgebra d] C.WordModule,
      ∀ y, C.wordRep.asModuleEquiv (q' y) = X *ᵥ C.wordRep.asModuleEquiv (q y) := by
  let e : C.WordModule ≃ₗ[ℂ] C.WordModule := C.wordRep.asModuleEquiv.trans
    ((Matrix.toLinearEquiv' X hX.invertible).trans C.wordRep.asModuleEquiv.symm)
  have he : ∀ y, C.wordRep.asModuleEquiv (e y) = X *ᵥ C.wordRep.asModuleEquiv y := fun y => by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  let φ : C.WordModule ≃ₗ[WordAlgebra d] C.WordModule :=
    linearEquivOfLetter e fun i y => C.wordRep.asModuleEquiv.injective (by
      rw [he, asModuleEquiv_letter_smul, asModuleEquiv_letter_smul, he, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, (hXC i).eq])
  exact ⟨q.trans φ, fun y => he (q y)⟩

end Parametrization

section PairAux

variable {P : Matrix (Fin c) (Fin D) ℂ} {E : Matrix (Fin D) (Fin c) ℂ}

/-- A subspace invariant under every letter is invariant under every word. -/
private theorem evalWord_mulVec_mem_of_invariant {V : Submodule ℂ (Fin D → ℂ)}
    (hV : ∀ i, ∀ x ∈ V, B i *ᵥ x ∈ V) (w : List (Fin d)) {x : Fin D → ℂ} (hx : x ∈ V) :
    Kraus.evalWord B w *ᵥ x ∈ V := by
  induction w with
  | nil => rwa [Kraus.evalWord_nil, Matrix.one_mulVec]
  | cons i w ih => rw [Kraus.evalWord_cons, ← Matrix.mulVec_mulVec]; exact hV i _ ih

/-- The remainder maps `U` into `K`. -/
theorem reductionResidual_mulVec_mem_reachableKer (h : IsReduction B C P E) (i : Fin d)
    {x : Fin D → ℂ} (hx : x ∈ reachable B E) :
    reductionResidual B C P E i *ᵥ x ∈ reachableKer B P E := by
  have hR : reductionResidual B C P E i *ᵥ x = B i *ᵥ x - E *ᵥ (C i *ᵥ (P *ᵥ x)) := by
    simp only [reductionResidual, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [mem_reachableKer_iff, hR]
  refine ⟨Submodule.sub_mem _ (mulVec_mem_reachable B E i hx) (mulVec_mem_reachable_self E _), ?_⟩
  rw [Matrix.mulVec_sub, h.mulVec_mulVec_of_mem_reachable i hx,
    Matrix.mulVec_mulVec (M := P) (N := E), h.mul_eq_one, Matrix.one_mulVec, sub_self]

/-- On `K` the remainder words are the words of `B`. -/
theorem evalWord_reductionResidual_mulVec_of_mem_reachableKer (h : IsReduction B C P E)
    (w : List (Fin d)) {x : Fin D → ℂ} (hx : x ∈ reachableKer B P E) :
    Kraus.evalWord (reductionResidual B C P E) w *ᵥ x = Kraus.evalWord B w *ᵥ x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hw : Kraus.evalWord B w *ᵥ x ∈ reachableKer B P E :=
      evalWord_mulVec_mem_of_invariant (fun j _ hy => h.mulVec_mem_reachableKer j hy) w hx
    rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ih]
    simp only [reductionResidual, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
      (mem_reachableKer_iff.1 hw).2, Matrix.mulVec_zero, sub_zero]

/-- Modulo `U` the remainder words are the words of `B`. -/
theorem evalWord_reductionResidual_mulVec_sub_mem_reachable (h : IsReduction B C P E)
    (w : List (Fin d)) (y : Fin D → ℂ) :
    Kraus.evalWord (reductionResidual B C P E) w *ᵥ y - Kraus.evalWord B w *ᵥ y ∈
      reachable B E := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hsplit : Kraus.evalWord (reductionResidual B C P E) (i :: w) *ᵥ y -
        Kraus.evalWord B (i :: w) *ᵥ y =
        reductionResidual B C P E i *ᵥ (Kraus.evalWord (reductionResidual B C P E) w *ᵥ y -
          Kraus.evalWord B w *ᵥ y) - E *ᵥ (C i *ᵥ (P *ᵥ (Kraus.evalWord B w *ᵥ y))) := by
      simp only [Kraus.evalWord_cons, ← Matrix.mulVec_mulVec, reductionResidual,
        Matrix.sub_mulVec, Matrix.mulVec_sub]
      abel
    rw [hsplit]
    exact Submodule.sub_mem _
      ((reductionResidual_mulVec_mem_reachableKer h i ih).1) (mulVec_mem_reachable_self E _)

end PairAux

section FlagAux

variable {P : Matrix (Fin c) (Fin D) ℂ} {E : Matrix (Fin D) (Fin c) ℂ}

/-- The subspaces `K ⋖ U` (`reachableKer`, `reachable`) for a pair onto an irreducible `C` of
positive bond dimension: the step `U / K` is the simple word module of `C`. -/
private theorem exists_covBy_and_map_eq (h : IsReduction B C P E)
    (hirr : Matrix.IsIrreducibleAction C) (hc : 0 < c) :
    ∃ K' U' : Submodule (WordAlgebra d) B.WordModule, K' ⋖ U' ∧
      (U'.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap = reachable B E ∧
      (K'.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap = reachableKer B P E ∧
      Nonempty (Submodule.subquot K' U' ≃ₗ[WordAlgebra d] C.WordModule) := by
  obtain ⟨U', K', hKU, hU, hK, ⟨q⟩⟩ := h.exists_quotient_linearEquiv_wordModule
  have : IsSimpleModule (WordAlgebra d) C.WordModule :=
    (isIrreducibleAction_and_pos_iff_isSimpleModule C).1 ⟨hirr, hc⟩
  have hs : IsSimpleModule (WordAlgebra d) (Submodule.subquot K' U') := IsSimpleModule.congr q
  exact ⟨K', U', (covBy_iff_quot_is_simple hKU).2 hs, hU, hK, ⟨q⟩⟩

/-- A step `K ⋖ U` of invariant subspaces is a pair of consecutive members of a composition
series of the word module from `0` to the whole bond space. -/
private theorem exists_compositionSeries_eq_of_covBy
    {K' U' : Submodule (WordAlgebra d) B.WordModule} (hcov : K' ⋖ U') :
    ∃ s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule),
      s.head = ⊥ ∧ s.last = ⊤ ∧ ∃ k : Fin s.length, s k.castSucc = K' ∧ s k.succ = U' := by
  have : IsNoetherian (WordAlgebra d) B.WordModule := isNoetherian_of_tower ℂ inferInstance
  have : IsArtinian (WordAlgebra d) B.WordModule := isArtinian_of_tower ℂ inferInstance
  let s₀ : LTSeries (Submodule (WordAlgebra d) B.WordModule) :=
    { length := 1
      toFun := ![K', U']
      step := fun i => by fin_cases i; exact hcov.lt }
  obtain ⟨t, i, hti, ht0, htl⟩ := LTSeries.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot s₀
  have h0 : t (i 0) = K' := congrFun hti 0
  have h1 : t (i 1) = U' := congrFun hti 1
  let tl : LTSeries (Submodule (WordAlgebra d) B.WordModule) :=
    ⟨t.length, t.toFun, fun j => (t.step j).lt⟩
  have hmono : StrictMono t.toFun := tl.strictMono
  have hlt : i 0 < i 1 := by
    by_contra hle
    have h2 := hmono.monotone (not_lt.1 hle)
    change t (i 1) ≤ t (i 0) at h2
    rw [h0, h1] at h2
    exact (lt_irrefl _ (lt_of_lt_of_le hcov.lt h2)).elim
  have hsucc : ((i 1 : Fin _) : ℕ) = ((i 0 : Fin _) : ℕ) + 1 := by
    by_contra hne
    have hlt' : ((i 0 : Fin _) : ℕ) + 1 < ((i 1 : Fin _) : ℕ) := by
      have := Fin.lt_def.1 hlt
      omega
    let m : Fin (t.length + 1) := ⟨((i 0 : Fin _) : ℕ) + 1, by have := (i 1).isLt; omega⟩
    have hm1 : t (i 0) < t m := hmono (Fin.lt_def.2 (by simp [m]))
    have hm2 : t m < t (i 1) := hmono (Fin.lt_def.2 (by simp only [m]; omega))
    rw [h0] at hm1
    rw [h1] at hm2
    exact hcov.2 hm1 hm2
  refine ⟨t, ht0, htl, ⟨((i 0 : Fin _) : ℕ), by have := (i 1).isLt; omega⟩, ?_, ?_⟩
  · exact (congrArg t.toFun (Fin.ext rfl)).trans h0
  · exact (congrArg t.toFun (Fin.ext (by rw [Fin.val_succ]; exact hsucc.symm))).trans h1

/-- **Changing the coordinates of a reduction to a given pair** (the adapted basis).
Let `Q₀` be a multi-block reduction of `B`, `b₀` a slot of `Q₀`, and `(P, E)` a reduction pair from
`B` to the diagonal block of `b₀` whose subspaces `K`, `U` (`reachableKer`, `reachable`) are the
members of the flag of `Q₀` just below and at the position of `b₀`. If every matrix commuting with
the diagonal block of `b₀` is a scalar, there is a block upper triangular `h` with nonzero scalar
diagonal blocks such that the reduction `(σ, h g)` has the maps `P` and `E` at `b₀`. Its basis
consists of the old basis vectors before `b₀`, the columns of `E`, and the old basis vectors after
`b₀` moved into `ker P`. -/
private theorem exists_conjTriangular_leftRow_eq_and_rightCol_eq {ι : Type*} [DecidableEq ι]
    {Dι : ι → ℕ} {S : Finset ι} {C' : ∀ s, MPSTensor d (Dι s)}
    (Q₀ : MultiBlockCompression B S C') (b₀ : BlockIndex S Q₀.z)
    {P : Matrix (Fin (slotSize Dι b₀)) (Fin D) ℂ} {E : Matrix (Fin D) (Fin (slotSize Dι b₀)) ℂ}
    (h : IsReduction B (slotTensor C' b₀) P E)
    (hU : ((Q₀.flag (Q₀.ord b₀).succ).restrictScalars ℂ).map
      (B.wordRep.asModuleEquiv).toLinearMap = reachable B E)
    (hK : ((Q₀.flag (Q₀.ord b₀).castSucc).restrictScalars ℂ).map
      (B.wordRep.asModuleEquiv).toLinearMap = reachableKer B P E)
    (hschur : ∀ X : Matrix (Fin (slotSize Dι b₀)) (Fin (slotSize Dι b₀)) ℂ,
      (∀ i, X * slotTensor C' b₀ i = slotTensor C' b₀ i * X) → ∃ μ : ℂ, X = μ • 1)
    (hpos : 0 < slotSize Dι b₀) :
    ∃ (H : Matrix (BlockSpace Dι S Q₀.z) (BlockSpace Dι S Q₀.z) ℂ)
      (ht : H.BlockTriangular fun x => Q₀.ord x.1) (μ : BlockIndex S Q₀.z → ℂ)
      (hμ : ∀ b, μ b ≠ 0) (hdiag : ∀ b, H.blockDiag' b = μ b • 1),
      (Q₀.conjTriangular ht hμ hdiag).leftRow b₀ = P ∧
        (Q₀.conjTriangular ht hμ hdiag).rightCol b₀ = E := by
  classical
  have hmemU : ∀ x : B.WordModule, x ∈ Q₀.flag (Q₀.ord b₀).succ ↔
      B.wordRep.asModuleEquiv x ∈ reachable B E := fun x => mem_iff_of_map_eq hU
  have hmemK : ∀ x : B.WordModule, x ∈ Q₀.flag (Q₀.ord b₀).castSucc ↔
      B.wordRep.asModuleEquiv x ∈ reachableKer B P E := fun x => mem_iff_of_map_eq hK
  -- the reading map of `b₀` kills `K`, and on `U` it intertwines
  have hW0 : ∀ y ∈ reachableKer B P E, Q₀.leftRow b₀ *ᵥ y = 0 := fun y hy => by
    have := Q₀.leftRow_mulVec_eq_zero_of_mem (b := b₀)
      (x := (B.wordRep.asModuleEquiv).symm y) ((hmemK _).2 (by rwa [LinearEquiv.apply_symm_apply]))
    rwa [LinearEquiv.apply_symm_apply] at this
  -- `W₀ E` commutes with the diagonal block, hence is a scalar `l`
  have hP0E : ∀ i, (Q₀.leftRow b₀ * E) * slotTensor C' b₀ i =
      slotTensor C' b₀ i * (Q₀.leftRow b₀ * E) := by
    intro i
    refine Matrix.mulVec_injective <| funext fun v => ?_
    have hEv : E *ᵥ v ∈ reachable B E := mulVec_mem_reachable_self E v
    have hRv : reductionResidual B (slotTensor C' b₀) P E i *ᵥ (E *ᵥ v) =
        B i *ᵥ (E *ᵥ v) - E *ᵥ (slotTensor C' b₀ i *ᵥ v) := by
      simp only [reductionResidual, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc, h.mul_eq_one, Matrix.mul_one]
    have h0 := hW0 _ (reductionResidual_mulVec_mem_reachableKer h i hEv)
    have h1 := Q₀.leftRow_mulVec_mulVec_of_mem (b := b₀) i
      (x := (B.wordRep.asModuleEquiv).symm (E *ᵥ v))
      ((hmemU _).2 (by rwa [LinearEquiv.apply_symm_apply]))
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [hRv, Matrix.mulVec_sub, sub_eq_zero] at h0
    simp only [← Matrix.mulVec_mulVec]
    rw [← h0, h1]
    rfl
  obtain ⟨l, hl⟩ := hschur _ hP0E
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hl
    obtain ⟨x, hx, hxv⟩ := Q₀.leftRow_surjOn b₀
      (Set.mem_univ (Pi.single (⟨0, hpos⟩ : Fin (slotSize Dι b₀)) (1 : ℂ)))
    have hxU := (hmemU x).1 hx
    have hdec : B.wordRep.asModuleEquiv x - E *ᵥ (P *ᵥ B.wordRep.asModuleEquiv x) ∈
        reachableKer B P E := mem_reachableKer_iff.2 ⟨Submodule.sub_mem _ hxU
          (mulVec_mem_reachable_self _ _), by
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h.mul_eq_one, Matrix.one_mulVec, sub_self]⟩
    have h0 := hW0 _ hdec
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec (M := Q₀.leftRow b₀) (N := E), hl,
      Matrix.zero_mulVec, sub_zero] at h0
    have h2 := congrFun (hxv.symm.trans h0) ⟨0, hpos⟩
    simp at h2
  -- the new basis, as the columns of `F`
  let G := gaugeMatrix Q₀.gauge
  let Gi := gaugeMatrixInv Q₀.gauge
  let ey : BlockSpace Dι S Q₀.z → BlockSpace Dι S Q₀.z → ℂ := fun y => Pi.single y 1
  let fvec : BlockSpace Dι S Q₀.z → Fin D → ℂ := fun y =>
    ((if y.1 = b₀ then 0 else Gi *ᵥ ey y) + E *ᵥ (fun j => ey y ⟨b₀, j⟩)) -
      (if Q₀.ord b₀ < Q₀.ord y.1 then E *ᵥ (P *ᵥ (Gi *ᵥ ey y)) else 0)
  let F : Matrix (Fin D) (BlockSpace Dι S Q₀.z) ℂ := Matrix.of fun a y => fvec y a
  let T := G * F
  have hFcol : ∀ y, F *ᵥ ey y = fvec y := fun y => by
    rw [Matrix.mulVec_single_one]
    rfl
  have hz : ∀ y : BlockSpace Dι S Q₀.z, y.1 ≠ b₀ → (fun j => ey y ⟨b₀, j⟩) = 0 :=
    fun y hy => funext fun j => Pi.single_eq_of_ne (fun h' => hy (by rw [← h'])) _
  have hb0 : ∀ j : Fin (slotSize Dι b₀), (fun j' => ey ⟨b₀, j⟩ ⟨b₀, j'⟩) = Pi.single j 1 :=
    fun j => funext fun j' => by
      by_cases hj : j' = j
      · subst hj
        simp [ey]
      · rw [Pi.single_eq_of_ne hj]
        simp only [ey, Pi.single_apply]
        split_ifs with h'
        · exact absurd (eq_of_heq (Sigma.mk.inj h').2) hj
        · rfl
  have hGimem : ∀ y, (B.wordRep.asModuleEquiv).symm (Gi *ᵥ ey y) ∈ Q₀.flag (Q₀.ord y.1).succ :=
    fun y => by
      refine Q₀.mem_flag_iff.2 fun x hx => ?_
      rw [Q₀.coord_apply, LinearEquiv.apply_symm_apply]
      change Q₀.gauge (gaugeMatrixInv Q₀.gauge *ᵥ ey y) x = 0
      rw [gaugeMatrixInv, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      have hxy : x ≠ y := by
        rintro rfl
        exact absurd hx (not_le.2 Fin.castSucc_lt_succ)
      exact Pi.single_eq_of_ne hxy _
  have hUle : ∀ b : BlockIndex S Q₀.z, Q₀.ord b₀ < Q₀.ord b →
      Q₀.flag (Q₀.ord b₀).succ ≤ Q₀.flag (Q₀.ord b).castSucc := fun b hb =>
    Q₀.flag_mono (Fin.succ_le_castSucc_iff.2 hb)
  have hEmem : ∀ w : Fin (slotSize Dι b₀) → ℂ,
      (B.wordRep.asModuleEquiv).symm (E *ᵥ w) ∈ Q₀.flag (Q₀.ord b₀).succ := fun w =>
    (hmemU _).2 (by rw [LinearEquiv.apply_symm_apply]; exact mulVec_mem_reachable_self E w)
  have hfmem : ∀ y, (B.wordRep.asModuleEquiv).symm (fvec y) ∈ Q₀.flag (Q₀.ord y.1).succ := by
    intro y
    by_cases hy : y.1 = b₀
    · have hf : fvec y = E *ᵥ (fun j => ey y ⟨b₀, j⟩) := by
        simp only [fvec, hy, ite_true, lt_irrefl, ite_false, zero_add, sub_zero]
      rw [hf, hy]
      exact hEmem _
    · by_cases hky : Q₀.ord b₀ < Q₀.ord y.1
      · have hf : fvec y = Gi *ᵥ ey y - E *ᵥ (P *ᵥ (Gi *ᵥ ey y)) := by
          simp only [fvec, hy, ite_false, hky, ite_true, hz y hy, Matrix.mulVec_zero, add_zero]
        rw [hf, map_sub]
        exact Submodule.sub_mem _ (hGimem y)
          (Q₀.flag_mono Fin.castSucc_lt_succ.le (hUle y.1 hky (hEmem _)))
      · have hf : fvec y = Gi *ᵥ ey y := by
          simp only [fvec, hy, ite_false, hky, hz y hy, Matrix.mulVec_zero, add_zero, sub_zero]
        rw [hf]
        exact hGimem y
  have hT : ∀ x y, T x y = Q₀.gauge (fvec y) x := fun x y => by
    have h1 := congrFun (Matrix.mulVec_single_one T y) x
    rw [Matrix.col_apply] at h1
    rw [← h1]
    change ((G * F) *ᵥ ey y) x = _
    rw [← Matrix.mulVec_mulVec, hFcol]
    change (gaugeMatrix Q₀.gauge *ᵥ fvec y) x = _
    rw [gaugeMatrix, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
  have ht : T.BlockTriangular fun x => Q₀.ord x.1 := fun x y hxy => by
    rw [hT]
    have := Q₀.mem_flag_iff.1 (hfmem y) x (Fin.succ_le_castSucc_iff.2 hxy)
    rwa [Q₀.coord_apply, LinearEquiv.apply_symm_apply] at this
  let μ : BlockIndex S Q₀.z → ℂ := fun b => if b = b₀ then l else 1
  have hμ : ∀ b, μ b ≠ 0 := fun b => by
    simp only [μ]
    split_ifs
    · exact hl0
    · exact one_ne_zero
  have hdiag : ∀ b, T.blockDiag' b = μ b • 1 := by
    intro b
    ext j' j
    rw [Matrix.blockDiag'_apply, hT, show Q₀.gauge (fvec ⟨b, j⟩) ⟨b, j'⟩ =
      (Q₀.leftRow b *ᵥ fvec ⟨b, j⟩) j' by rw [Q₀.leftRow_mulVec]]
    by_cases hb : b = b₀
    · subst hb
      have hf : fvec ⟨b, j⟩ = E *ᵥ Pi.single j 1 := by
        simp only [fvec, ite_true, lt_irrefl, ite_false, zero_add, sub_zero, hb0]
      rw [hf, Matrix.mulVec_mulVec, hl, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp [μ, Matrix.one_apply, Pi.single_apply]
    · have hlG : Q₀.leftRow b *ᵥ (Gi *ᵥ ey ⟨b, j⟩) = Pi.single j 1 := by
        rw [Matrix.mulVec_mulVec, MultiBlockCompression.leftRow, Matrix.mul_assoc,
          gaugeMatrix_mul_gaugeMatrixInv, Matrix.mul_one, blockProj_mulVec]
        funext j''
        by_cases hj : j'' = j
        · subst hj
          simp [ey]
        · rw [Pi.single_eq_of_ne hj]
          simp only [ey, Pi.single_apply]
          split_ifs with h'
          · exact absurd (eq_of_heq (Sigma.mk.inj h').2) hj
          · rfl
      have hval : Q₀.leftRow b *ᵥ fvec ⟨b, j⟩ = Pi.single j 1 := by
        by_cases hky : Q₀.ord b₀ < Q₀.ord b
        · have hf : fvec ⟨b, j⟩ = Gi *ᵥ ey ⟨b, j⟩ - E *ᵥ (P *ᵥ (Gi *ᵥ ey ⟨b, j⟩)) := by
            simp only [fvec, hb, ite_false, hky, ite_true, hz ⟨b, j⟩ hb, Matrix.mulVec_zero,
              add_zero]
          have h0 := Q₀.leftRow_mulVec_eq_zero_of_mem (b := b)
            (hUle b hky (hEmem (P *ᵥ (Gi *ᵥ ey ⟨b, j⟩))))
          rw [LinearEquiv.apply_symm_apply] at h0
          rw [hf, Matrix.mulVec_sub, h0, sub_zero, hlG]
        · have hf : fvec ⟨b, j⟩ = Gi *ᵥ ey ⟨b, j⟩ := by
            simp only [fvec, hb, ite_false, hky, hz ⟨b, j⟩ hb, Matrix.mulVec_zero, add_zero,
              sub_zero]
          rw [hf, hlG]
      rw [hval]
      simp [μ, hb, Matrix.one_apply, Pi.single_apply]
  have hdetT := Q₀.isUnit_det_of_blockDiag'_eq_smul ht hμ hdiag
  have hFT : F = Gi * T := by
    change F = gaugeMatrixInv Q₀.gauge * (gaugeMatrix Q₀.gauge * F)
    rw [← Matrix.mul_assoc, gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul]
  have hPF : P * F = Matrix.blockProj (slotSize Dι) b₀ := by
    have hcol : ∀ y, P *ᵥ fvec y = fun j => ey y ⟨b₀, j⟩ := by
      intro y
      by_cases hy : y.1 = b₀
      · have hf : fvec y = E *ᵥ (fun j => ey y ⟨b₀, j⟩) := by
          simp only [fvec, hy, ite_true, lt_irrefl, ite_false, zero_add, sub_zero]
        rw [hf, Matrix.mulVec_mulVec, h.mul_eq_one, Matrix.one_mulVec]
      · rw [hz y hy]
        have hne : Q₀.ord y.1 ≠ Q₀.ord b₀ := fun h' => hy (Q₀.ord.injective h')
        by_cases hky : Q₀.ord b₀ < Q₀.ord y.1
        · have hf : fvec y = Gi *ᵥ ey y - E *ᵥ (P *ᵥ (Gi *ᵥ ey y)) := by
            simp only [fvec, hy, ite_false, hky, ite_true, hz y hy, Matrix.mulVec_zero, add_zero]
          rw [hf, Matrix.mulVec_sub, Matrix.mulVec_mulVec (M := P) (N := E), h.mul_eq_one,
            Matrix.one_mulVec, sub_self]
        · have hf : fvec y = Gi *ᵥ ey y := by
            simp only [fvec, hy, ite_false, hky, hz y hy, Matrix.mulVec_zero, add_zero, sub_zero]
          have hlt : Q₀.ord y.1 < Q₀.ord b₀ := lt_of_le_of_ne (not_lt.1 hky) hne
          have hmK : (B.wordRep.asModuleEquiv).symm (Gi *ᵥ ey y) ∈
              Q₀.flag (Q₀.ord b₀).castSucc :=
            Q₀.flag_mono (Fin.succ_le_castSucc_iff.2 hlt) (hGimem y)
          have := (mem_reachableKer_iff.1 ((hmemK _).1 hmK)).2
          rw [LinearEquiv.apply_symm_apply] at this
          rw [hf, this]
    ext j y
    have h1 := congrFun (Matrix.mulVec_single_one (P * F) y) j
    have h2 := congrFun (Matrix.mulVec_single_one (Matrix.blockProj (slotSize Dι) b₀) y) j
    rw [Matrix.col_apply] at h1 h2
    rw [← h1, ← h2, ← Matrix.mulVec_mulVec]
    change (P *ᵥ (F *ᵥ ey y)) j = (Matrix.blockProj (slotSize Dι) b₀ *ᵥ ey y) j
    rw [hFcol, hcol, blockProj_mulVec]
  have hFE : F * Matrix.blockEmbed (slotSize Dι) b₀ = E := by
    ext a j
    rw [Matrix.mul_blockEmbed_apply]
    change fvec ⟨b₀, j⟩ a = E a j
    have hf : fvec ⟨b₀, j⟩ = E *ᵥ Pi.single j 1 := by
      simp only [fvec, ite_true, lt_irrefl, ite_false, zero_add, sub_zero, hb0]
    rw [hf, Matrix.mulVec_single_one, Matrix.col_apply]
  have htH := Q₀.blockTriangular_inv_of_blockDiag'_eq_smul ht hμ hdiag
  have hμH : ∀ b, (fun b => (μ b)⁻¹) b ≠ 0 := fun b => inv_ne_zero (hμ b)
  have hdiagH : ∀ b, T⁻¹.blockDiag' b = (fun b => (μ b)⁻¹) b • 1 :=
    Q₀.blockDiag'_inv_of_blockDiag'_eq_smul ht hμ hdiag
  refine ⟨T⁻¹, htH, fun b => (μ b)⁻¹, hμH, hdiagH, ?_, ?_⟩
  · change Matrix.blockProj (slotSize Dι) b₀ *
      gaugeMatrix (Q₀.conjTriangularGauge htH hμH hdiagH) = P
    rw [MultiBlockCompression.gaugeMatrix_conjTriangularGauge, ← hPF, hFT]
    change P * (gaugeMatrixInv Q₀.gauge * T) * (T⁻¹ * gaugeMatrix Q₀.gauge) = P
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc T, Matrix.mul_nonsing_inv (A := T)
      hdetT, Matrix.one_mul, gaugeMatrixInv_mul_gaugeMatrix, Matrix.mul_one]
  · change gaugeMatrixInv (Q₀.conjTriangularGauge htH hμH hdiagH) *
      Matrix.blockEmbed (slotSize Dι) b₀ = E
    rw [MultiBlockCompression.gaugeMatrixInv_conjTriangularGauge,
      Matrix.nonsing_inv_nonsing_inv (A := T) hdetT, ← hFT, hFE]

end FlagAux

/-! ### Every reduction pair sits in a flag -/

namespace IsReduction

variable {P : Matrix (Fin c) (Fin D) ℂ} {E : Matrix (Fin D) (Fin c) ℂ}

/-- **Every reduction pair sits in a flag**. For
a reduction pair `(P, E)` onto an irreducible `C` with `c ≥ 1`, the subspaces `K` and `U`
(`reachableKer B P E` and `reachable B E`) are consecutive members of an invariant flag of `B`. -/
theorem exists_compositionSeries_map_eq_reachableKer_and_map_eq_reachable
    (h : IsReduction B C P E) (hirr : Matrix.IsIrreducibleAction C) (hc : 0 < c) :
    ∃ s : CompositionSeries (Submodule (WordAlgebra d) B.WordModule),
      s.head = ⊥ ∧ s.last = ⊤ ∧ ∃ k : Fin s.length,
        ((s k.castSucc).restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap =
            reachableKer B P E ∧
          ((s k.succ).restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap =
            reachable B E := by
  obtain ⟨K', U', hcov, hU, hK, -⟩ := exists_covBy_and_map_eq h hirr hc
  obtain ⟨s, h0, h1, k, hk0, hk1⟩ := exists_compositionSeries_eq_of_covBy hcov
  exact ⟨s, h0, h1, k, by rw [hk0, hK], by rw [hk1, hU]⟩

/-- **A reduction pair is the pair of a block of a reduction adapted to its flag**. For a reduction
pair `(P, E)` onto an irreducible `C` with `c ≥ 1`, there is a multi-block reduction `Q` of `B` onto
a family indexed by `Option (Fin r)`, with block `C` at `none` and admissible blocks `C' k`
elsewhere, such that the members of the flag of `Q` just below and at the position of the block
`none` are `K = reachableKer B P E` and `U = reachable B E`, and the maps of `Q` at `none` are
exactly `P` and `E`. All blocks being irreducible of positive bond dimension, every step of the flag
of `Q` is simple, so this flag is an invariant flag of `B` with `K`, `U` consecutive members, and
the block coordinates of `Q` are a basis adapted to it. -/
theorem exists_multiBlockCompression_map_flag_eq_and_left_eq_and_right_eq
    (h : IsReduction B C P E) (hirr : Matrix.IsIrreducibleAction C) (hc : 0 < c) :
    ∃ (r : ℕ) (D' : Fin r → ℕ) (C' : ∀ k, MPSTensor d (D' k))
      (Q : MultiBlockCompression (D := fun s : Option (Fin r) => s.elim c D') B Finset.univ
        (fun s => Option.rec (motive := fun s => MPSTensor d (s.elim c D')) C C' s)),
      (∀ k, Matrix.IsIrreducibleAction (C' k)) ∧ (∀ k, ∃ i, C' k i ≠ 0) ∧
        ((Q.flag (Q.ord (Sum.inl ⟨none, Finset.mem_univ _⟩)).castSucc).restrictScalars ℂ).map
            (B.wordRep.asModuleEquiv).toLinearMap = reachableKer B P E ∧
          ((Q.flag (Q.ord (Sum.inl ⟨none, Finset.mem_univ _⟩)).succ).restrictScalars ℂ).map
              (B.wordRep.asModuleEquiv).toLinearMap = reachable B E ∧
            Q.left ⟨none, Finset.mem_univ _⟩ = P ∧ Q.right ⟨none, Finset.mem_univ _⟩ = E := by
  classical
  obtain ⟨K', U', hcov, hU, hK, ⟨q⟩⟩ := exists_covBy_and_map_eq h hirr hc
  obtain ⟨s, hs0, hs1, k, hk0, hk1⟩ := exists_compositionSeries_eq_of_covBy hcov
  let p : Fin s.length → Prop := fun j => ∃ (i : Fin d)
    (x : Submodule.subquot (s j.castSucc) (s j.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0
  have hzero : ∀ j, ¬ p j → ∀ (i : Fin d) (x : Submodule.subquot (s j.castSucc) (s j.succ)),
      (ofWord [i] : WordAlgebra d) • x = 0 := fun j hj i x => by
    simp only [p, not_exists, not_not] at hj
    exact hj i x
  let eT := Fintype.equivFin {j : Fin s.length // j ≠ k ∧ p j}
  let eZ := Fintype.equivFin {j : Fin s.length // j ≠ k ∧ ¬ p j}
  let r := Fintype.card {j : Fin s.length // j ≠ k ∧ p j}
  let z := Fintype.card {j : Fin s.length // j ≠ k ∧ ¬ p j}
  let D' : Fin r → ℕ := fun t =>
    Module.finrank ℂ (Submodule.subquot (s (eT.symm t).1.castSucc) (s (eT.symm t).1.succ))
  let C' : ∀ t, MPSTensor d (D' t) := fun t =>
    stepTensor s (eT.symm t).1 (Module.finBasis ℂ _).equivFun
  let lab : Fin s.length ≃ BlockIndex (Finset.univ : Finset (Option (Fin r))) z :=
    { toFun := fun j => if hj : j = k then Sum.inl ⟨none, Finset.mem_univ _⟩ else
        if hp : p j then Sum.inl ⟨some (eT ⟨j, hj, hp⟩), Finset.mem_univ _⟩
        else Sum.inr (eZ ⟨j, hj, hp⟩)
      invFun := fun b => Sum.elim (fun x => Option.elim x.1 k fun t => (eT.symm t).1)
        (fun t => (eZ.symm t).1) b
      left_inv := fun j => by
        by_cases hj : j = k
        · simp [hj]
        · by_cases hp : p j
          · simp [hj, hp]
          · simp [hj, hp]
      right_inv := fun b => by
        rcases b with ⟨_ | t, ht⟩ | t
        · simp
        · have h1 := (eT.symm t).2.1
          have h2 := (eT.symm t).2.2
          simp [h1, h2]
        · have h1 := (eZ.symm t).2.1
          have h2 := (eZ.symm t).2.2
          simp [h1, h2] }
  let F : FlagData B.WordModule (Finset.univ : Finset (Option (Fin r)))
      (D := fun x : Option (Fin r) => x.elim c D')
      (fun x => Option.rec (motive := fun x => MPSTensor d (x.elim c D')) C C' x) :=
    { r := s.length
      z := z
      H := s.toFun
      H_zero := hs0
      H_last := hs1
      H_mono := s.strictMono.monotone
      label := lab
      label_bijective := lab.bijective
      matched := fun j b hjb => by
        obtain rfl : j = lab.symm (Sum.inl b) := (lab.symm_apply_eq.2 hjb.symm).symm
        rcases b with ⟨_ | t, hb⟩
        · exact ⟨(Submodule.subquotCongr hk0 hk1).trans q⟩
        · exact nonempty_linearEquiv_wordModule_stepTensor s _ _
      unmatched_finrank := fun j t hjt => by
        obtain rfl : j = lab.symm (Sum.inr t) := (lab.symm_apply_eq.2 hjt.symm).symm
        exact finrank_subquot_eq_one_of_forall_smul_eq_zero s _ (hzero _ (eZ.symm t).2.2)
      unmatched_smul := fun j t hjt => by
        obtain rfl : j = lab.symm (Sum.inr t) := (lab.symm_apply_eq.2 hjt.symm).symm
        exact hzero _ (eZ.symm t).2.2 }
  let Q₀ := F.toMultiBlockCompression
  let b₀ : BlockIndex (Finset.univ : Finset (Option (Fin r))) Q₀.z :=
    Sum.inl ⟨none, Finset.mem_univ _⟩
  have hord : Q₀.ord b₀ = Fin.cast F.r_eq k := by
    change finCongr F.r_eq (F.labelEquiv.symm b₀) = Fin.cast F.r_eq k
    rw [show F.labelEquiv.symm b₀ = k from F.labelEquiv.symm_apply_eq.2 (by
      change b₀ = lab k
      simp [lab, b₀]
      rfl)]
    rfl
  have hflagK : Q₀.flag (Q₀.ord b₀).castSucc = K' :=
    ((congrArg (fun m => Q₀.flag m.castSucc) hord).trans (congrArg Q₀.flag
      (Fin.ext rfl : (Fin.cast F.r_eq k).castSucc =
        Fin.cast (congrArg (· + 1) F.r_eq) k.castSucc))).trans
      ((F.toMultiBlockCompression_flag k.castSucc).trans hk0)
  have hflagU : Q₀.flag (Q₀.ord b₀).succ = U' :=
    ((congrArg (fun m => Q₀.flag m.succ) hord).trans (congrArg Q₀.flag
      (Fin.ext rfl : (Fin.cast F.r_eq k).succ =
        Fin.cast (congrArg (· + 1) F.r_eq) k.succ))).trans
      ((F.toMultiBlockCompression_flag k.succ).trans hk1)
  obtain ⟨H, ht, μ, hμ, hdiag, hl, hr⟩ := exists_conjTriangular_leftRow_eq_and_rightCol_eq Q₀ b₀
    (P := P) (E := E) h (by rw [hflagU]; exact hU) (by rw [hflagK]; exact hK)
    (fun X hX => exists_eq_smul_one_of_intertwines hirr hX) hc
  refine ⟨r, D', C', Q₀.conjTriangular ht hμ hdiag, fun t => isIrreducibleAction_stepTensor s _ _,
    fun t => exists_stepTensor_apply_ne_zero s _ _ (eT.symm t).2.2, ?_, ?_, hl, hr⟩
  · exact (congrArg (fun M : Submodule (WordAlgebra d) B.WordModule =>
      (M.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap)
      ((MultiBlockCompression.conjTriangular_flag (P := Q₀) (ht := ht) (hμ := hμ)
        (hdiag := hdiag) _).trans hflagK)).trans hK
  · exact (congrArg (fun M : Submodule (WordAlgebra d) B.WordModule =>
      (M.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap)
      ((MultiBlockCompression.conjTriangular_flag (P := Q₀) (ht := ht) (hμ := hμ)
        (hdiag := hdiag) _).trans hflagU)).trans hU

/-- **A reduction pair onto a zero letter is the pair of a zero block**. For a reduction pair
`(P, E)` from `B` to the `1 × 1` zero tensor there is a multi-block
reduction `Q` of `B` onto a family of admissible blocks and a zero block `t` of `Q` such that the
members of the flag of `Q` just below and at the position of `t` are `K = reachableKer B P E` and `U
= reachable B E`, and the maps of `Q` at `t` are exactly `P` and `E`. As in
`exists_multiBlockCompression_map_flag_eq_and_left_eq_and_right_eq`, the flag of `Q` is an invariant
flag of `B`. -/
theorem exists_multiBlockCompression_map_flag_eq_and_leftRow_inr_eq_and_rightCol_inr_eq
    {P : Matrix (Fin 1) (Fin D) ℂ} {E : Matrix (Fin D) (Fin 1) ℂ}
    (h : IsReduction B (0 : MPSTensor d 1) P E) :
    ∃ (r : ℕ) (D' : Fin r → ℕ) (C' : ∀ k, MPSTensor d (D' k))
      (Q : MultiBlockCompression B Finset.univ C') (t : Fin Q.z),
      (∀ k, Matrix.IsIrreducibleAction (C' k)) ∧ (∀ k, ∃ i, C' k i ≠ 0) ∧
        ((Q.flag (Q.ord (Sum.inr t)).castSucc).restrictScalars ℂ).map
            (B.wordRep.asModuleEquiv).toLinearMap = reachableKer B P E ∧
          ((Q.flag (Q.ord (Sum.inr t)).succ).restrictScalars ℂ).map
              (B.wordRep.asModuleEquiv).toLinearMap = reachable B E ∧
            Q.leftRow (Sum.inr t) = P ∧ Q.rightCol (Sum.inr t) = E := by
  classical
  have hirr0 : Matrix.IsIrreducibleAction (0 : MPSTensor d 1) := by
    intro W _
    rcases eq_or_ne W ⊥ with h0 | h0
    · exact Or.inl h0
    · right
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 h0
      have hv1 : v 0 ≠ 0 := fun h' => hv0 (funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h')
      refine eq_top_iff.2 fun u _ => ?_
      have hsm := W.smul_mem (u 0 / v 0) hv
      convert hsm using 1
      funext i
      rw [Fin.fin_one_eq_zero i, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hv1]
  obtain ⟨K', U', hcov, hU, hK, ⟨q⟩⟩ := exists_covBy_and_map_eq h hirr0 Nat.one_pos
  obtain ⟨s, hs0, hs1, k, hk0, hk1⟩ := exists_compositionSeries_eq_of_covBy hcov
  let p : Fin s.length → Prop := fun j => ∃ (i : Fin d)
    (x : Submodule.subquot (s j.castSucc) (s j.succ)), (ofWord [i] : WordAlgebra d) • x ≠ 0
  have hzero : ∀ j, ¬ p j → ∀ (i : Fin d) (x : Submodule.subquot (s j.castSucc) (s j.succ)),
      (ofWord [i] : WordAlgebra d) • x = 0 := fun j hj i x => by
    simp only [p, not_exists, not_not] at hj
    exact hj i x
  have hkZ : ¬ p k := by
    simp only [p, not_exists, not_not]
    intro i x
    let e := (Submodule.subquotCongr hk0 hk1).trans q
    refine e.injective ?_
    apply (MPSTensor.wordRep (0 : MPSTensor d 1)).asModuleEquiv.injective
    rw [map_smul, asModuleEquiv_letter_smul, map_zero, map_zero]
    exact Matrix.zero_mulVec _
  let eT := Fintype.equivFin {j : Fin s.length // p j}
  let eZ := Fintype.equivFin {j : Fin s.length // ¬ p j}
  let r := Fintype.card {j : Fin s.length // p j}
  let z := Fintype.card {j : Fin s.length // ¬ p j}
  let D' : Fin r → ℕ := fun t =>
    Module.finrank ℂ (Submodule.subquot (s (eT.symm t).1.castSucc) (s (eT.symm t).1.succ))
  let C' : ∀ t, MPSTensor d (D' t) := fun t =>
    stepTensor s (eT.symm t).1 (Module.finBasis ℂ _).equivFun
  let lab : Fin s.length ≃ BlockIndex (Finset.univ : Finset (Fin r)) z :=
    { toFun := fun j => if hp : p j then Sum.inl ⟨eT ⟨j, hp⟩, Finset.mem_univ _⟩
        else Sum.inr (eZ ⟨j, hp⟩)
      invFun := fun b => Sum.elim (fun x => (eT.symm x.1).1) (fun t => (eZ.symm t).1) b
      left_inv := fun j => by
        by_cases hp : p j
        · simp [hp]
        · simp [hp]
      right_inv := fun b => by
        rcases b with ⟨t, ht⟩ | t
        · have h2 := (eT.symm t).2
          simp [h2]
        · have h2 := (eZ.symm t).2
          simp [h2] }
  let F : FlagData B.WordModule (Finset.univ : Finset (Fin r)) C' :=
    { r := s.length
      z := z
      H := s.toFun
      H_zero := hs0
      H_last := hs1
      H_mono := s.strictMono.monotone
      label := lab
      label_bijective := lab.bijective
      matched := fun j b hjb => by
        obtain rfl : j = lab.symm (Sum.inl b) := (lab.symm_apply_eq.2 hjb.symm).symm
        exact nonempty_linearEquiv_wordModule_stepTensor s _ _
      unmatched_finrank := fun j t hjt => by
        obtain rfl : j = lab.symm (Sum.inr t) := (lab.symm_apply_eq.2 hjt.symm).symm
        exact finrank_subquot_eq_one_of_forall_smul_eq_zero s _ (hzero _ (eZ.symm t).2)
      unmatched_smul := fun j t hjt => by
        obtain rfl : j = lab.symm (Sum.inr t) := (lab.symm_apply_eq.2 hjt.symm).symm
        exact hzero _ (eZ.symm t).2 }
  let Q₀ := F.toMultiBlockCompression
  let t₀ : Fin Q₀.z := eZ ⟨k, hkZ⟩
  have hord : Q₀.ord (Sum.inr t₀) = Fin.cast F.r_eq k := by
    change finCongr F.r_eq (F.labelEquiv.symm (Sum.inr t₀)) = Fin.cast F.r_eq k
    rw [show F.labelEquiv.symm (Sum.inr t₀) = k from F.labelEquiv.symm_apply_eq.2 (by
      change Sum.inr t₀ = lab k
      simp [lab, t₀, hkZ]
      rfl)]
    rfl
  have hflagK : Q₀.flag (Q₀.ord (Sum.inr t₀)).castSucc = K' :=
    ((congrArg (fun m => Q₀.flag m.castSucc) hord).trans (congrArg Q₀.flag
      (Fin.ext rfl : (Fin.cast F.r_eq k).castSucc =
        Fin.cast (congrArg (· + 1) F.r_eq) k.castSucc))).trans
      ((F.toMultiBlockCompression_flag k.castSucc).trans hk0)
  have hflagU : Q₀.flag (Q₀.ord (Sum.inr t₀)).succ = U' :=
    ((congrArg (fun m => Q₀.flag m.succ) hord).trans (congrArg Q₀.flag
      (Fin.ext rfl : (Fin.cast F.r_eq k).succ =
        Fin.cast (congrArg (· + 1) F.r_eq) k.succ))).trans
      ((F.toMultiBlockCompression_flag k.succ).trans hk1)
  obtain ⟨H, ht, μ, hμ, hdiag, hl, hr⟩ := exists_conjTriangular_leftRow_eq_and_rightCol_eq Q₀
    (Sum.inr t₀) (P := P) (E := E) h (by rw [hflagU]; exact hU) (by rw [hflagK]; exact hK)
    (fun X _ => ⟨X ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩, by
      ext i j
      have hi : i = ⟨0, Nat.one_pos⟩ := Fin.ext (by
        have := i.isLt
        change i.val < 1 at this
        change i.val = 0
        omega)
      have hj : j = ⟨0, Nat.one_pos⟩ := Fin.ext (by
        have := j.isLt
        change j.val < 1 at this
        change j.val = 0
        omega)
      subst hi
      subst hj
      simp⟩) Nat.one_pos
  refine ⟨r, D', C', Q₀.conjTriangular ht hμ hdiag, t₀,
    fun t => isIrreducibleAction_stepTensor s _ _,
    fun t => exists_stepTensor_apply_ne_zero s _ _ (eT.symm t).2, ?_, ?_, hl, hr⟩
  · exact (congrArg (fun M : Submodule (WordAlgebra d) B.WordModule =>
      (M.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap)
      ((MultiBlockCompression.conjTriangular_flag (P := Q₀) (ht := ht) (hμ := hμ)
        (hdiag := hdiag) _).trans hflagK)).trans hK
  · exact (congrArg (fun M : Submodule (WordAlgebra d) B.WordModule =>
      (M.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap)
      ((MultiBlockCompression.conjTriangular_flag (P := Q₀) (ht := ht) (hμ := hμ)
        (hdiag := hdiag) _).trans hflagU)).trans hU

end IsReduction

end MPSTensor
