/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import TNLean.MPS.Core.Reduction
import TNLean.MPS.FundamentalTheorem.Reduction.WordModule

/-!
# The reachable subspace of a reduction pair

Let `IsReduction B C P E`, so `P * E = 1` and `P * B^w * E = C^w` for every word (`P` is the
projection, `E` the embedding). The *reachable subspace* `U` is the span of the vectors
`B^w (E v)`; put `K = U ∩ ker P`. Then `U` and `K` are invariant, `P` intertwines the letters on
`U`, maps `U` onto `ℂ^c` with kernel `K`, and `U = K ⊕ ran E`. Hence `U / K` with the induced
letters is isomorphic, through `P`, to the word module of `C`. No hypothesis on `C` is needed.

## Main definitions

* `MPSTensor.reachable B E`: the span of the vectors `B^w (E v)`.
* `MPSTensor.reachableKer B P E`: its intersection with the kernel of `P`.

## Main results

* `MPSTensor.mulVec_mem_reachable`, `MPSTensor.IsReduction.mulVec_mem_reachableKer`
* `MPSTensor.IsReduction.mulVec_mulVec_of_mem_reachable`
* `MPSTensor.IsReduction.exists_mem_reachable_mulVec_eq`
* `MPSTensor.IsReduction.disjoint_reachableKer_range`,
  `MPSTensor.IsReduction.reachableKer_sup_range`
* `MPSTensor.IsReduction.exists_surjective_wordModule_ker_eq`
* `MPSTensor.IsReduction.exists_quotient_linearEquiv_wordModule`
-/

open WordAlgebra
open scoped Matrix

namespace MPSTensor

variable {d D c : ℕ}

/-- The reachable subspace of an embedding `E`: the span of the vectors `B^w (E v)` over all words
`w` and all `v`. -/
noncomputable def reachable (B : MPSTensor d D) (E : Matrix (Fin D) (Fin c) ℂ) :
    Submodule ℂ (Fin D → ℂ) :=
  Submodule.span ℂ
    (⋃ w : List (Fin d), Set.range fun v : Fin c → ℂ => Kraus.evalWord B w *ᵥ (E *ᵥ v))

/-- The intersection of the reachable subspace with the kernel of the projection `P`. -/
noncomputable def reachableKer (B : MPSTensor d D) (P : Matrix (Fin c) (Fin D) ℂ)
    (E : Matrix (Fin D) (Fin c) ℂ) : Submodule ℂ (Fin D → ℂ) :=
  reachable B E ⊓ LinearMap.ker (Matrix.toLin' P)

/-- The spanning vectors `B^w (E v)` lie in the reachable subspace. -/
theorem evalWord_mulVec_mem_reachable (B : MPSTensor d D) (E : Matrix (Fin D) (Fin c) ℂ)
    (w : List (Fin d)) (v : Fin c → ℂ) : Kraus.evalWord B w *ᵥ (E *ᵥ v) ∈ reachable B E :=
  Submodule.subset_span (Set.mem_iUnion.2 ⟨w, v, rfl⟩)

/-- The vectors `E v` lie in the reachable subspace. -/
theorem mulVec_mem_reachable_self {B : MPSTensor d D} (E : Matrix (Fin D) (Fin c) ℂ)
    (v : Fin c → ℂ) : E *ᵥ v ∈ reachable B E := by
  simpa using evalWord_mulVec_mem_reachable B E [] v

/-- Membership in `U ∩ ker P`. -/
theorem mem_reachableKer_iff {B : MPSTensor d D} {P : Matrix (Fin c) (Fin D) ℂ}
    {E : Matrix (Fin D) (Fin c) ℂ} {x : Fin D → ℂ} :
    x ∈ reachableKer B P E ↔ x ∈ reachable B E ∧ P *ᵥ x = 0 := by
  rw [reachableKer, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply]

/-- The reachable subspace is invariant under every letter. -/
theorem mulVec_mem_reachable (B : MPSTensor d D) (E : Matrix (Fin D) (Fin c) ℂ) (i : Fin d)
    {x : Fin D → ℂ} (hx : x ∈ reachable B E) : B i *ᵥ x ∈ reachable B E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, v, rfl⟩ := Set.mem_iUnion.1 hx
    rw [Matrix.mulVec_mulVec, ← Kraus.evalWord_cons]
    exact evalWord_mulVec_mem_reachable B E (i :: w) v
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

/-- A subspace invariant under every letter is invariant under every word. -/
private theorem evalWord_mulVec_mem {B : MPSTensor d D} {V : Submodule ℂ (Fin D → ℂ)}
    (hV : ∀ i, ∀ x ∈ V, B i *ᵥ x ∈ V) (w : List (Fin d)) {x : Fin D → ℂ} (hx : x ∈ V) :
    Kraus.evalWord B w *ᵥ x ∈ V := by
  induction w with
  | nil => rw [Kraus.evalWord_nil, Matrix.one_mulVec]; exact hx
  | cons i w ih => rw [Kraus.evalWord_cons, ← Matrix.mulVec_mulVec]; exact hV i _ ih

/-- A subspace invariant under every letter is invariant under the whole word algebra. -/
private theorem asAlgebraHom_mem {B : MPSTensor d D} {V : Submodule ℂ (Fin D → ℂ)}
    (hV : ∀ i, ∀ x ∈ V, B i *ᵥ x ∈ V) (p : WordAlgebra d) {x : Fin D → ℂ} (hx : x ∈ V) :
    B.wordRep.asAlgebraHom p x ∈ V := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    rw [Representation.asAlgebraHom_of, ← FreeMonoid.ofList_toList g, wordRep_ofList,
      Matrix.toLin'_apply]
    exact evalWord_mulVec_mem hV _ hx
  | add f g hf hg => rw [map_add, LinearMap.add_apply]; exact V.add_mem hf hg
  | smul r f hf => rw [map_smul, LinearMap.smul_apply]; exact V.smul_mem r hf

/-- The word-algebra submodule of the word module whose underlying subspace is an invariant
subspace `V`. -/
private noncomputable def wordSubmodule (B : MPSTensor d D) (V : Submodule ℂ (Fin D → ℂ))
    (hV : ∀ i, ∀ x ∈ V, B i *ᵥ x ∈ V) : Submodule (WordAlgebra d) B.WordModule where
  carrier := B.wordRep.asModuleEquiv ⁻¹' V
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_preimage, map_add] at ha hb ⊢
    exact V.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro p x hx
    simp only [Set.mem_preimage] at hx ⊢
    rw [Representation.asModuleEquiv_map_smul]
    exact asAlgebraHom_mem hV p hx

private theorem mem_wordSubmodule {B : MPSTensor d D} {V : Submodule ℂ (Fin D → ℂ)}
    {hV : ∀ i, ∀ x ∈ V, B i *ᵥ x ∈ V} {x : B.WordModule} :
    x ∈ wordSubmodule B V hV ↔ B.wordRep.asModuleEquiv x ∈ V := Iff.rfl

private theorem map_wordSubmodule (B : MPSTensor d D) (V : Submodule ℂ (Fin D → ℂ))
    (hV : ∀ i, ∀ x ∈ V, B i *ᵥ x ∈ V) :
    ((wordSubmodule B V hV).restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap = V := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨(B.wordRep.asModuleEquiv).symm y, ?_, ?_⟩
    · change B.wordRep.asModuleEquiv ((B.wordRep.asModuleEquiv).symm y) ∈ V
      rwa [LinearEquiv.apply_symm_apply]
    · simp

namespace IsReduction

variable {B : MPSTensor d D} {C : MPSTensor d c} {P : Matrix (Fin c) (Fin D) ℂ}
  {E : Matrix (Fin D) (Fin c) ℂ}

/-- On the reachable subspace the projection intertwines the letters: `P (B^i x) = C^i (P x)`. -/
theorem mulVec_mulVec_of_mem_reachable (h : IsReduction B C P E) (i : Fin d)
    {x : Fin D → ℂ} (hx : x ∈ reachable B E) : P *ᵥ (B i *ᵥ x) = C i *ᵥ (P *ᵥ x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, v, rfl⟩ := Set.mem_iUnion.1 hx
    simp only [Matrix.mulVec_mulVec]
    rw [show P * (B i * (Kraus.evalWord B w * E)) =P * Kraus.evalWord B (i :: w) * E by
        simp only [Kraus.evalWord_cons, Matrix.mul_assoc],
      show C i * (P * (Kraus.evalWord B w * E)) = C i * (P * Kraus.evalWord B w * E) by
        simp only [Matrix.mul_assoc],
      h.evalWord, h.evalWord, Kraus.evalWord_cons]
  | zero => simp only [Matrix.mulVec_zero]
  | add x y _ _ hx hy => simp only [Matrix.mulVec_add, hx, hy]
  | smul a x _ hx => simp only [Matrix.mulVec_smul, hx]

/-- The kernel part `K = U ∩ ker P` is invariant under every letter. -/
theorem mulVec_mem_reachableKer (h : IsReduction B C P E) (i : Fin d)
    {x : Fin D → ℂ} (hx : x ∈ reachableKer B P E) : B i *ᵥ x ∈ reachableKer B P E := by
  rw [mem_reachableKer_iff] at hx ⊢
  refine ⟨mulVec_mem_reachable B E i hx.1, ?_⟩
  rw [h.mulVec_mulVec_of_mem_reachable i hx.1, hx.2, Matrix.mulVec_zero]

/-- The projection maps the reachable subspace onto `ℂ^c`. -/
theorem exists_mem_reachable_mulVec_eq (h : IsReduction B C P E) (v : Fin c → ℂ) :
    ∃ x ∈ reachable B E, P *ᵥ x = v := by
  refine ⟨E *ᵥ v, ?_, ?_⟩
  · simpa using evalWord_mulVec_mem_reachable B E [] v
  · rw [Matrix.mulVec_mulVec, h.mul_eq_one, Matrix.one_mulVec]

/-- `K` meets the range of the embedding only in zero. -/
theorem disjoint_reachableKer_range (h : IsReduction B C P E) :
    Disjoint (reachableKer B P E) (LinearMap.range (Matrix.toLin' E)) := by
  rw [Submodule.disjoint_def]
  intro x hx hxE
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hxE
  have h0 := (mem_reachableKer_iff.1 hx).2
  rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h.mul_eq_one, Matrix.one_mulVec] at h0
  rw [h0, map_zero]

/-- `K` and the range of the embedding together span the reachable subspace: `U = K ⊕ ran E`. -/
theorem reachableKer_sup_range (h : IsReduction B C P E) :
    reachableKer B P E ⊔ LinearMap.range (Matrix.toLin' E) = reachable B E := by
  have hE : ∀ v : Fin c → ℂ, E *ᵥ v ∈ reachable B E := fun v => by
    simpa using evalWord_mulVec_mem_reachable B E [] v
  apply le_antisymm
  · refine sup_le inf_le_left ?_
    rintro _ ⟨v, rfl⟩
    rw [Matrix.toLin'_apply]
    exact hE v
  · intro u hu
    rw [Submodule.mem_sup]
    refine ⟨u - E *ᵥ (P *ᵥ u), ?_, E *ᵥ (P *ᵥ u), ⟨P *ᵥ u, Matrix.toLin'_apply _ _⟩,
      sub_add_cancel _ _⟩
    rw [mem_reachableKer_iff]
    refine ⟨Submodule.sub_mem _ hu (hE _), ?_⟩
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h.mul_eq_one, Matrix.one_mulVec, sub_self]

/-- On the reachable subspace the projection intertwines every word. -/
theorem mulVec_evalWord_mulVec_of_mem_reachable (h : IsReduction B C P E)
    (w : List (Fin d)) {x : Fin D → ℂ} (hx : x ∈ reachable B E) :
    P *ᵥ (Kraus.evalWord B w *ᵥ x) = Kraus.evalWord C w *ᵥ (P *ᵥ x) := by
  induction w with
  | nil => simp only [Kraus.evalWord_nil, Matrix.one_mulVec]
  | cons i w ih =>
    rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h.mulVec_mulVec_of_mem_reachable i
        (evalWord_mulVec_mem (fun j _ hy => mulVec_mem_reachable B E j hy) w hx), ih]

/-- On the reachable subspace the projection intertwines the whole word algebra. -/
private theorem mulVec_asAlgebraHom_of_mem_reachable (h : IsReduction B C P E)
    (p : WordAlgebra d) {x : Fin D → ℂ} (hx : x ∈ reachable B E) :
    P *ᵥ B.wordRep.asAlgebraHom p x = C.wordRep.asAlgebraHom p (P *ᵥ x) := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of,
      ← FreeMonoid.ofList_toList g, wordRep_ofList, wordRep_ofList, Matrix.toLin'_apply,
      Matrix.toLin'_apply]
    exact h.mulVec_evalWord_mulVec_of_mem_reachable _ hx
  | add f g hf hg => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      Matrix.mulVec_add, hf, hg]
  | smul r f hf => rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      Matrix.mulVec_smul, hf]

/-- **`U / K` is the word module of `C`.** There are word-algebra submodules `K' ≤ U'` of the word
module of `B` whose underlying subspaces are `K` and `U`, and a surjective word-algebra map from
`U'` onto the word module of `C`, given by `P`, with kernel `K'`. By the first isomorphism theorem
it induces an isomorphism `U' / K' ≃ C`. -/
theorem exists_surjective_wordModule_ker_eq (h : IsReduction B C P E) :
    ∃ (U' K' : Submodule (WordAlgebra d) B.WordModule) (f : U' →ₗ[WordAlgebra d] C.WordModule),
      K' ≤ U' ∧
      (U'.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap = reachable B E ∧
      (K'.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap = reachableKer B P E ∧
      Function.Surjective f ∧ LinearMap.ker f = K'.comap U'.subtype ∧
      ∀ x : U', C.wordRep.asModuleEquiv (f x) =
        P *ᵥ B.wordRep.asModuleEquiv (x : B.WordModule) := by
  let U' := wordSubmodule B (reachable B E) (fun i _ hx => mulVec_mem_reachable B E i hx)
  let K' := wordSubmodule B (reachableKer B P E) (fun i _ hx => h.mulVec_mem_reachableKer i hx)
  let f : U' →ₗ[WordAlgebra d] C.WordModule :=
    { toFun := fun x =>
        (C.wordRep.asModuleEquiv).symm (P *ᵥ B.wordRep.asModuleEquiv (x : B.WordModule))
      map_add' := fun x y => by simp only [Submodule.coe_add, map_add, Matrix.mulVec_add]
      map_smul' := fun p x => by
        apply (C.wordRep.asModuleEquiv).injective
        simp only [RingHom.id_apply, LinearEquiv.apply_symm_apply, Submodule.coe_smul,
          Representation.asModuleEquiv_map_smul]
        exact h.mulVec_asAlgebraHom_of_mem_reachable p (mem_wordSubmodule.1 x.2) }
  have hf : ∀ x : U',
      C.wordRep.asModuleEquiv (f x) = P *ᵥ B.wordRep.asModuleEquiv (x : B.WordModule) :=
    fun x => LinearEquiv.apply_symm_apply _ _
  refine ⟨U', K', f, fun x hx => (mem_reachableKer_iff.1 (mem_wordSubmodule.1 hx)).1,
    map_wordSubmodule _ _ _, map_wordSubmodule _ _ _, ?_, ?_, hf⟩
  · intro v
    obtain ⟨y, hy, hPy⟩ := h.exists_mem_reachable_mulVec_eq (C.wordRep.asModuleEquiv v)
    refine ⟨⟨(B.wordRep.asModuleEquiv).symm y, mem_wordSubmodule.2 (by simpa using hy)⟩, ?_⟩
    apply (C.wordRep.asModuleEquiv).injective
    rw [hf]
    simpa using hPy
  · ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, mem_wordSubmodule,
      mem_reachableKer_iff, ← (C.wordRep.asModuleEquiv).map_eq_zero_iff, hf]
    exact ⟨fun h0 => ⟨mem_wordSubmodule.1 x.2, h0⟩, fun h0 => h0.2⟩

/-- **`U / K` is isomorphic to the word module of `C`.** There are word-algebra submodules
`K' ≤ U'` of the word module of `B` whose underlying subspaces are `K` and `U`, and an isomorphism
of word-algebra modules from `U' / K'` onto the word module of `C`. -/
theorem exists_quotient_linearEquiv_wordModule (h : IsReduction B C P E) :
    ∃ (U' K' : Submodule (WordAlgebra d) B.WordModule), K' ≤ U' ∧
      (U'.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap = reachable B E ∧
      (K'.restrictScalars ℂ).map (B.wordRep.asModuleEquiv).toLinearMap = reachableKer B P E ∧
      -- `U' ⧸ K'.comap U'.subtype`; instance search does not find the quotient structure on a
      -- submodule of `Representation.asModule`, so it is supplied explicitly
      Nonempty (@HasQuotient.Quotient U' (Submodule (WordAlgebra d) U')
        (@Submodule.hasQuotient (WordAlgebra d) U' _ _ U'.module) (K'.comap U'.subtype)
          ≃ₗ[WordAlgebra d] C.WordModule) := by
  obtain ⟨U', K', f, hKU, hU, hK, hsurj, hker, -⟩ := h.exists_surjective_wordModule_ker_eq
  exact ⟨U', K', hKU, hU, hK,
    ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)⟩⟩

end IsReduction

end MPSTensor
