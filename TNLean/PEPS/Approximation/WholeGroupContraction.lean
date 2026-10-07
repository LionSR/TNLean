/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.NuclearNormTruncation

/-!
# Whole-group tensor bounds for finite tensor graphs

A finite graph carries at each vertex `v` a tensor whose legs are the virtual legs of the edges at
`v` and one open-leg group with configuration type `P v`. Contracting every edge by the usual
coordinate pairing gives a tensor `Z` indexed by the open-leg configurations. The graph may have
cycles and parallel edges, but no edge from a vertex to itself; edge and open-leg dimensions are
arbitrary finite types.

The open legs of each original vertex form one group, so the group space of `v` is the space of
functions on `P v`. A vertex without open legs has a one-point configuration type `P v`.

## Main definitions

* `WholeGroup.contraction`: the coordinate contraction of all edges.
* `WholeGroup.partialContraction`: the contraction of the edges inside a vertex set `S`, with the
  edges leaving `S` and the open legs of `S` left open.
* `WholeGroup.flattening`: the matrix reshaping of a tensor across a vertex bipartition.

## Main statements

* `WholeGroup.partialContraction_normSq_le`: every partially contracted subgraph has squared norm
  at most the product of the squared vertex norms.
* `WholeGroup.contraction_normSq_le_one`: the contracted tensor has norm at most one.
* `WholeGroup.nuclearNorm_flattening_le_one`: across every bipartition into whole open-leg groups,
  the flattening has nuclear norm at most one.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`,
  05-frames.tex:125–179.
-/

open scoped BigOperators Matrix

noncomputable section

namespace TNLean.PEPS.WholeGroup

/-! ### Configurations on subtypes -/

section Configurations

variable {ι : Type*} (F : ι → Type*)

/-- Splitting a configuration on `p` into its parts on two disjoint predicates `q` and `r` whose
union is `p`. -/
def piSubtypeSplit (p q r : ι → Prop) [DecidablePred q] (hp : ∀ i, p i ↔ q i ∨ r i)
    (hqr : ∀ i, q i → ¬r i) :
    ((i : {i // p i}) → F i) ≃ ((i : {i // q i}) → F i) × ((i : {i // r i}) → F i) where
  toFun x := (fun i ↦ x ⟨i, (hp i).2 (Or.inl i.2)⟩, fun i ↦ x ⟨i, (hp i).2 (Or.inr i.2)⟩)
  invFun y i := if h : q i then y.1 ⟨i, h⟩ else y.2 ⟨i, ((hp i).1 i.2).resolve_left h⟩
  left_inv x := by
    funext i
    by_cases h : q i <;> simp [h]
  right_inv y := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
    · simp [i.2]
    · have : ¬q i := fun h ↦ hqr i h i.2
      simp [this]

variable {F} {p q r : ι → Prop} [DecidablePred q] {hp : ∀ i, p i ↔ q i ∨ r i}
  {hqr : ∀ i, q i → ¬r i}

theorem piSubtypeSplit_symm_apply_left (y : ((i : {i // q i}) → F i) × ((i : {i // r i}) → F i))
    {i : ι} (hpi : p i) (hq : q i) :
    (piSubtypeSplit F p q r hp hqr).symm y ⟨i, hpi⟩ = y.1 ⟨i, hq⟩ := by
  simp [piSubtypeSplit, hq]

theorem piSubtypeSplit_symm_apply_right (y : ((i : {i // q i}) → F i) × ((i : {i // r i}) → F i))
    {i : ι} (hpi : p i) (hr : r i) :
    (piSubtypeSplit F p q r hp hqr).symm y ⟨i, hpi⟩ = y.2 ⟨i, hr⟩ := by
  simp [piSubtypeSplit, hqr i |>.mt (not_not.mpr hr)]

variable (F)

/-- Configurations on two predicates with the same extension are the same. -/
def piSubtypeCongr (p q : ι → Prop) (h : ∀ i, p i ↔ q i) :
    ((i : {i // p i}) → F i) ≃ ((i : {i // q i}) → F i) where
  toFun x i := x ⟨i, (h i).2 i.2⟩
  invFun y i := y ⟨i, (h i).1 i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A configuration on an empty predicate is unique. -/
@[instance_reducible]
def piSubtypeUniqueOfForallNot (p : ι → Prop) (h : ∀ i, ¬p i) :
    Unique ((i : {i // p i}) → F i) where
  default i := absurd i.2 (h i)
  uniq _ := funext fun i ↦ absurd i.2 (h i)

/-- Products over a subtype split along a disjoint union of predicates. -/
theorem prod_subtype_split {M : Type*} [CommMonoid M] (p q r : ι → Prop)
    [Fintype {i // p i}] [Fintype {i // q i}] [Fintype {i // r i}] [DecidablePred q]
    (hp : ∀ i, p i ↔ q i ∨ r i)
    (hqr : ∀ i, q i → ¬r i) (g : {i // p i} → M) :
    ∏ i, g i = (∏ i : {i // q i}, g ⟨i, (hp i).2 (Or.inl i.2)⟩) *
      ∏ i : {i // r i}, g ⟨i, (hp i).2 (Or.inr i.2)⟩ := by
  classical
  let e : {i // p i} ≃ {i // q i} ⊕ {i // r i} :=
    (Equiv.subtypeEquivRight hp).trans
      (subtypeOrEquiv q r fun _ hf hg i hfi ↦ hqr i (hf i hfi) (hg i hfi))
  rw [← e.symm.prod_comp, Fintype.prod_sum_type]
  congr 1

end Configurations

/-! ### Tensor graphs and their contractions -/

section Predicates

variable {V E : Type*} (tail head : E → V)

/-- An edge is incident to a vertex when the vertex is its tail or its head. -/
def IsIncident (v : V) (e : E) : Prop := tail e = v ∨ head e = v

/-- An edge lies inside a vertex set when both endpoints do. -/
def IsInternal (S : Finset V) (e : E) : Prop := tail e ∈ S ∧ head e ∈ S

/-- An edge crosses the boundary of a vertex set when exactly one endpoint lies in it. -/
def IsCut (S : Finset V) (e : E) : Prop :=
  (tail e ∈ S ∧ head e ∉ S) ∨ (tail e ∉ S ∧ head e ∈ S)

/-- An edge touches a vertex set when some endpoint lies in it. -/
def IsTouching (S : Finset V) (e : E) : Prop := tail e ∈ S ∨ head e ∈ S

variable {tail head}

theorem isTouching_iff (S : Finset V) (e : E) :
    IsTouching tail head S e ↔ IsInternal tail head S e ∨ IsCut tail head S e := by
  unfold IsTouching IsInternal IsCut
  tauto

theorem not_isCut_of_isInternal (S : Finset V) (e : E) :
    IsInternal tail head S e → ¬IsCut tail head S e := by
  unfold IsInternal IsCut
  tauto

theorem isTouching_of_isIncident {S : Finset V} {v : V} (hv : v ∈ S) (e : E)
    (he : IsIncident tail head v e) : IsTouching tail head S e := by
  rcases he with rfl | rfl
  · exact Or.inl hv
  · exact Or.inr hv

variable (tail head) [DecidableEq V]

instance (v : V) : DecidablePred (IsIncident tail head v) := fun _ ↦ by
  unfold IsIncident; infer_instance
instance (S : Finset V) : DecidablePred (IsInternal tail head S) := fun _ ↦ by
  unfold IsInternal; infer_instance
instance (S : Finset V) : DecidablePred (IsCut tail head S) := fun _ ↦ by
  unfold IsCut; infer_instance
instance (S : Finset V) : DecidablePred (IsTouching tail head S) := fun _ ↦ by
  unfold IsTouching; infer_instance

end Predicates

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (tail head : E → V) (D : E → Type*) [∀ e, Fintype (D e)]
  (P : V → Type*) [∀ v, Fintype (P v)]

/-- A tensor at each vertex, with one leg for every incident edge and one open-leg group. -/
abbrev VertexTensors := (v : V) → ((e : {e // IsIncident tail head v e}) → D e) → P v → ℂ

variable {tail head D P}

/-- The coordinate contraction: every edge carries one summed label, read by both endpoints.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, 05-frames.tex:127–130. -/
def contraction (A : VertexTensors tail head D P) (σ : (v : V) → P v) : ℂ :=
  ∑ β : (e : E) → D e, ∏ v, A v (fun e ↦ β e) (σ v)

/-- The squared Hilbert-space norm of a vertex tensor. -/
def vertexNormSq (A : VertexTensors tail head D P) (v : V) : ℝ :=
  ∑ x, ∑ p, ‖A v x p‖ ^ 2

omit [Fintype V] in
theorem vertexNormSq_nonneg (A : VertexTensors tail head D P) (v : V) :
    0 ≤ vertexNormSq A v :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Gluing a configuration of the internal edges of `S` with one of its boundary edges. -/
abbrev touchingSplit (S : Finset V) :=
  piSubtypeSplit D (IsTouching tail head S) (IsInternal tail head S) (IsCut tail head S)
    (isTouching_iff S) (not_isCut_of_isInternal S)

/-- The local virtual configuration of a vertex of `S`, read from internal and boundary labels. -/
def localConfig (S : Finset V) (γ : (e : {e // IsInternal tail head S e}) → D e)
    (b : (e : {e // IsCut tail head S e}) → D e) (v : V) (hv : v ∈ S) :
    (e : {e // IsIncident tail head v e}) → D e :=
  fun e ↦ (touchingSplit S).symm (γ, b) ⟨e, isTouching_of_isIncident hv _ e.2⟩

variable (A : VertexTensors tail head D P)

/-- The partial contraction of a vertex set `S`: the edges inside `S` are contracted, while the
open legs of `S` and the edges leaving `S` stay open.

Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 6.2 `lem:group-tensor`,
05-frames.tex:143–157. -/
def partialContraction (S : Finset V) (σ : (v : {v // v ∈ S}) → P v)
    (b : (e : {e // IsCut tail head S e}) → D e) : ℂ :=
  ∑ γ : (e : {e // IsInternal tail head S e}) → D e,
    ∏ v : {v // v ∈ S}, A v (localConfig S γ b v v.2) (σ v)

/-- The squared Hilbert-space norm of a partial contraction, summing over its open legs and its
boundary edges. -/
def partialNormSq (S : Finset V) : ℝ :=
  ∑ σ : (v : {v // v ∈ S}) → P v, ∑ b : (e : {e // IsCut tail head S e}) → D e,
    ‖partialContraction A S σ b‖ ^ 2

omit [Fintype V] in
theorem partialNormSq_nonneg (S : Finset V) : 0 ≤ partialNormSq A S :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-! ### Merging two disjoint vertex sets -/

section Merge

variable (tail head) in
/-- An edge joins `S₁` to `S₂` when one endpoint lies in each. -/
def IsLink (S₁ S₂ : Finset V) (e : E) : Prop :=
  (tail e ∈ S₁ ∧ head e ∈ S₂) ∨ (tail e ∈ S₂ ∧ head e ∈ S₁)

variable (tail head) in
/-- A boundary edge of `S₁` that does not join `S₁` to `S₂`. -/
def IsExit (S₁ S₂ : Finset V) (e : E) : Prop :=
  IsCut tail head S₁ e ∧ ¬IsLink tail head S₁ S₂ e

instance (S₁ S₂ : Finset V) : DecidablePred (IsLink tail head S₁ S₂) := fun _ ↦ by
  unfold IsLink; infer_instance
instance (S₁ S₂ : Finset V) : DecidablePred (IsExit tail head S₁ S₂) := fun _ ↦ by
  unfold IsExit; infer_instance

variable {S S₁ S₂ : Finset V}

variable (D) in
/-- The boundary edges of `S₁` split into the edges to a disjoint `S₂` and the remaining
exits. -/
def cutSplitLeft (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :=
  piSubtypeSplit D (IsCut tail head S₁) (IsLink tail head S₁ S₂) (IsExit tail head S₁ S₂)
    (fun e ↦ by
      have := hd (tail e); have := hd (head e)
      simp only [IsExit, IsLink, IsCut]; tauto)
    (fun _ h h' ↦ h'.2 h)

variable (D) in
/-- The boundary edges of `S₂` split into the edges to a disjoint `S₁` and the remaining
exits. -/
def cutSplitRight (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :=
  piSubtypeSplit D (IsCut tail head S₂) (IsLink tail head S₁ S₂) (IsExit tail head S₂ S₁)
    (fun e ↦ by
      have := hd (tail e); have := hd (head e)
      simp only [IsExit, IsLink, IsCut]; tauto)
    (fun _ h h' ↦ h'.2 (by unfold IsLink at h ⊢; tauto))

variable (D) in
/-- The boundary edges of `S = S₁ ∪ S₂` split into the exits of `S₁` and those of `S₂`. -/
def cutSplit (hS : ∀ v, v ∈ S ↔ v ∈ S₁ ∨ v ∈ S₂) (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :=
  piSubtypeSplit D (IsCut tail head S) (IsExit tail head S₁ S₂) (IsExit tail head S₂ S₁)
    (fun e ↦ by
      simp only [IsExit, IsCut, IsLink]
      by_cases a : tail e ∈ S₁ <;> by_cases b : head e ∈ S₁ <;>
        by_cases c : tail e ∈ S₂ <;> by_cases d : head e ∈ S₂ <;> simp_all)
    (fun e ↦ by
      simp only [IsExit, IsCut, IsLink]
      by_cases a : tail e ∈ S₁ <;> by_cases b : head e ∈ S₁ <;>
        by_cases c : tail e ∈ S₂ <;> by_cases d : head e ∈ S₂ <;> simp_all)

variable (P) in
/-- The open legs of `S = S₁ ∪ S₂` split into those of `S₁` and those of `S₂`. -/
def vertexSplit (hS : ∀ v, v ∈ S ↔ v ∈ S₁ ∨ v ∈ S₂) (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :=
  piSubtypeSplit P (· ∈ S) (· ∈ S₁) (· ∈ S₂) hS hd

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The three kinds of edges at a vertex of `S₁`. -/
theorem isIncident_classify_left (hS : ∀ v, v ∈ S ↔ v ∈ S₁ ∨ v ∈ S₂)
    (hd : ∀ v, v ∈ S₁ → v ∉ S₂) {v : V} {e : E} (hv : v ∈ S₁)
    (he : IsIncident tail head v e) :
    (IsInternal tail head S₁ e ∧ IsInternal tail head S e ∧ ¬IsLink tail head S₁ S₂ e) ∨
      (IsLink tail head S₁ S₂ e ∧ IsInternal tail head S e ∧ ¬IsInternal tail head S₁ e) ∨
      (IsExit tail head S₁ S₂ e ∧ ¬IsInternal tail head S e ∧ ¬IsInternal tail head S₁ e ∧
        ¬IsLink tail head S₁ S₂ e) := by
  simp only [IsInternal, IsExit, IsCut, IsLink]
  rcases he with rfl | rfl <;>
  by_cases a : tail e ∈ S₁ <;> by_cases b : head e ∈ S₁ <;>
    by_cases c : tail e ∈ S₂ <;> by_cases d : head e ∈ S₂ <;> simp_all

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The three kinds of edges at a vertex of `S₂`. -/
theorem isIncident_classify_right (hS : ∀ v, v ∈ S ↔ v ∈ S₁ ∨ v ∈ S₂)
    (hd : ∀ v, v ∈ S₁ → v ∉ S₂) {v : V} {e : E} (hv : v ∈ S₂)
    (he : IsIncident tail head v e) :
    (IsInternal tail head S₂ e ∧ IsInternal tail head S e ∧ ¬IsLink tail head S₁ S₂ e ∧
        ¬IsInternal tail head S₁ e) ∨
      (IsLink tail head S₁ S₂ e ∧ IsInternal tail head S e ∧ ¬IsInternal tail head S₂ e ∧
        ¬IsInternal tail head S₁ e) ∨
      (IsExit tail head S₂ S₁ e ∧ ¬IsInternal tail head S e ∧ ¬IsInternal tail head S₂ e ∧
        ¬IsInternal tail head S₁ e ∧ ¬IsLink tail head S₁ S₂ e ∧
        ¬IsExit tail head S₁ S₂ e) := by
  simp only [IsInternal, IsExit, IsCut, IsLink]
  rcases he with rfl | rfl <;>
  by_cases a : tail e ∈ S₁ <;> by_cases b : head e ∈ S₁ <;>
    by_cases c : tail e ∈ S₂ <;> by_cases d : head e ∈ S₂ <;> simp_all

omit [Fintype V] [∀ v, Fintype (P v)] in
/-- Merging two disjoint vertex sets contracts all edges between them at once: the partial
contraction of `S₁ ∪ S₂` is the sum over the joining labels of the product of the two partial
contractions.

Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 6.2 `lem:group-tensor`,
05-frames.tex:143–157. -/
theorem partialContraction_merge (hS : ∀ v, v ∈ S ↔ v ∈ S₁ ∨ v ∈ S₂)
    (hd : ∀ v, v ∈ S₁ → v ∉ S₂) (σ₁ : (v : {v // v ∈ S₁}) → P v)
    (σ₂ : (v : {v // v ∈ S₂}) → P v) (b₁ : (e : {e // IsExit tail head S₁ S₂ e}) → D e)
    (b₂ : (e : {e // IsExit tail head S₂ S₁ e}) → D e) :
    partialContraction A S ((vertexSplit P hS hd).symm (σ₁, σ₂))
        ((cutSplit D hS hd).symm (b₁, b₂)) =
      ∑ c : (e : {e // IsLink tail head S₁ S₂ e}) → D e,
        partialContraction A S₁ σ₁ ((cutSplitLeft D hd).symm (c, b₁)) *
          partialContraction A S₂ σ₂ ((cutSplitRight D hd).symm (c, b₂)) := by
  classical
  -- the internal edges of `S` split into joining edges and internal edges of each part
  let int12 : E → Prop := fun e ↦ IsInternal tail head S₁ e ∨ IsInternal tail head S₂ e
  let eInt := piSubtypeSplit D (IsInternal tail head S) (IsLink tail head S₁ S₂) int12
    (fun e ↦ by
      simp only [int12, IsInternal, IsLink]
      by_cases a : tail e ∈ S₁ <;> by_cases b : head e ∈ S₁ <;>
        by_cases c : tail e ∈ S₂ <;> by_cases d : head e ∈ S₂ <;> simp_all)
    (fun e ↦ by
      simp only [int12, IsInternal, IsLink]
      by_cases a : tail e ∈ S₁ <;> by_cases b : head e ∈ S₁ <;>
        by_cases c : tail e ∈ S₂ <;> by_cases d : head e ∈ S₂ <;> simp_all)
  let e12 := piSubtypeSplit D int12 (IsInternal tail head S₁) (IsInternal tail head S₂)
    (fun _ ↦ Iff.rfl) (fun e ↦ by have := hd (tail e); unfold IsInternal; tauto)
  unfold partialContraction
  rw [← eInt.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [← e12.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun γ₁ _ ↦ Finset.sum_congr rfl fun γ₂ _ ↦ ?_
  rw [prod_subtype_split (· ∈ S) (· ∈ S₁) (· ∈ S₂) hS hd]
  congr 1
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    have hv₁ := v.2
    congr 1
    · funext ⟨e, he⟩
      rcases isIncident_classify_left hS hd hv₁ he with
        ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;>
        simp [localConfig, cutSplit, cutSplitLeft, eInt, e12, int12, piSubtypeSplit, *]
    · simp [vertexSplit, piSubtypeSplit, hv₁]
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    have hv₂ := v.2
    have hv₁ : (v : V) ∉ S₁ := fun h ↦ hd v h hv₂
    congr 1
    · funext ⟨e, he⟩
      rcases isIncident_classify_right hS hd hv₂ he with
        ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ <;>
        simp [localConfig, cutSplit, cutSplitRight, eInt, e12, int12, piSubtypeSplit, *]
    · simp [vertexSplit, piSubtypeSplit, hv₁]

/-- The left factor of a merge: the partial contraction of `S₁`, as a matrix from its open legs
and remaining exits to the joining labels. -/
def mergeLeft (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :
    Matrix (((v : {v // v ∈ S₁}) → P v) × ((e : {e // IsExit tail head S₁ S₂ e}) → D e))
      ((e : {e // IsLink tail head S₁ S₂ e}) → D e) ℂ :=
  fun x c ↦ partialContraction A S₁ x.1 ((cutSplitLeft D hd).symm (c, x.2))

/-- The right factor of a merge: the partial contraction of `S₂`, as a matrix from the joining
labels to its open legs and remaining exits. -/
def mergeRight (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :
    Matrix ((e : {e // IsLink tail head S₁ S₂ e}) → D e)
      (((v : {v // v ∈ S₂}) → P v) × ((e : {e // IsExit tail head S₂ S₁ e}) → D e)) ℂ :=
  fun c y ↦ partialContraction A S₂ y.1 ((cutSplitRight D hd).symm (c, y.2))

omit [Fintype V] in
theorem hsNormSq_mergeLeft (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :
    Matrix.hsNormSq (mergeLeft A hd) = partialNormSq A S₁ := by
  classical
  unfold Matrix.hsNormSq partialNormSq mergeLeft
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ₁ _ ↦ ?_
  rw [← (cutSplitLeft D hd).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]

omit [Fintype V] in
theorem hsNormSq_mergeRight (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :
    Matrix.hsNormSq (mergeRight A hd) = partialNormSq A S₂ := by
  classical
  unfold Matrix.hsNormSq partialNormSq mergeRight
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ₂ _ ↦ ?_
  rw [← (cutSplitRight D hd).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]

omit [Fintype V] in
/-- The partial contraction of `S₁ ∪ S₂` is the product of the two merge factors. -/
theorem partialNormSq_eq_hsNormSq_mul (hS : ∀ v, v ∈ S ↔ v ∈ S₁ ∨ v ∈ S₂)
    (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :
    partialNormSq A S = Matrix.hsNormSq (mergeLeft A hd * mergeRight A hd) := by
  classical
  unfold partialNormSq Matrix.hsNormSq
  have hcut : ∀ σ, ∑ b, ‖partialContraction A S σ b‖ ^ 2 =
      ∑ b₁, ∑ b₂, ‖partialContraction A S σ ((cutSplit D hS hd).symm (b₁, b₂))‖ ^ 2 := by
    intro σ
    rw [← (cutSplit D hS hd).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [hcut]
  rw [← (vertexSplit P hS hd).symm.sum_comp, Fintype.sum_prod_type]
  simp only [partialContraction_merge A hS hd, Fintype.sum_prod_type, Matrix.mul_apply,
    mergeLeft, mergeRight]
  refine Finset.sum_congr rfl fun σ₁ _ ↦ ?_
  rw [Finset.sum_comm]

omit [Fintype V] in
/-- Merging two disjoint vertex sets is submultiplicative in the squared norm,
`‖AB‖₂ ≤ ‖A‖₂ ‖B‖₂`.

Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 6.2 `lem:group-tensor`,
05-frames.tex:143–157. -/
theorem partialNormSq_merge_le (hS : ∀ v, v ∈ S ↔ v ∈ S₁ ∨ v ∈ S₂)
    (hd : ∀ v, v ∈ S₁ → v ∉ S₂) :
    partialNormSq A S ≤ partialNormSq A S₁ * partialNormSq A S₂ := by
  rw [partialNormSq_eq_hsNormSq_mul A hS hd, ← hsNormSq_mergeLeft A hd,
    ← hsNormSq_mergeRight A hd]
  exact Matrix.hsNormSq_mul_le _ _

end Merge

/-! ### The norm bound -/

section NormBound

omit [Fintype V] in
theorem partialNormSq_empty : partialNormSq A ∅ = 1 := by
  classical
  let _ := piSubtypeUniqueOfForallNot D (IsInternal tail head (∅ : Finset V))
    (by simp [IsInternal])
  let _ := piSubtypeUniqueOfForallNot D (IsCut tail head (∅ : Finset V)) (by simp [IsCut])
  let _ := piSubtypeUniqueOfForallNot P (· ∈ (∅ : Finset V)) (by simp)
  unfold partialNormSq partialContraction
  simp

omit [Fintype V] in
/-- With no edge from a vertex to itself, a single vertex is its own partial contraction. -/
theorem partialNormSq_singleton (hloop : ∀ e, tail e ≠ head e) (w : V) :
    partialNormSq A {w} = vertexNormSq A w := by
  classical
  have hint : ∀ e, ¬IsInternal tail head ({w} : Finset V) e := by
    intro e h
    simp only [IsInternal, Finset.mem_singleton] at h
    exact hloop e (h.1.trans h.2.symm)
  have hcut : ∀ e, IsCut tail head ({w} : Finset V) e ↔ IsIncident tail head w e := by
    intro e
    have := hloop e
    simp only [IsCut, IsIncident, Finset.mem_singleton]
    by_cases a : tail e = w <;> by_cases b : head e = w <;> simp_all
  let _ := piSubtypeUniqueOfForallNot D _ hint
  let U : Unique {v // v ∈ ({w} : Finset V)} :=
    ⟨⟨⟨w, Finset.mem_singleton_self w⟩⟩, fun v ↦ Subtype.ext (Finset.mem_singleton.mp v.2)⟩
  have hZ : ∀ σ b, partialContraction A {w} σ b =
      A w (piSubtypeCongr D _ _ hcut b) (σ ⟨w, Finset.mem_singleton_self w⟩) := by
    intro σ b
    unfold partialContraction
    rw [Fintype.sum_unique, Fintype.prod_unique]
    congr 1
    funext ⟨e, he⟩
    simp [localConfig, piSubtypeSplit, piSubtypeCongr, hint e]
  unfold partialNormSq vertexNormSq
  simp_rw [hZ]
  rw [Finset.sum_comm]
  calc _ = ∑ b, ∑ p : P w, ‖A w (piSubtypeCongr D _ _ hcut b) p‖ ^ 2 :=
        Finset.sum_congr rfl fun b _ ↦
          (Equiv.piUnique (fun v : {v // v ∈ ({w} : Finset V)} ↦ P v)).sum_comp
            (fun p ↦ ‖A w (piSubtypeCongr D _ _ hcut b) p‖ ^ 2)
    _ = _ := (piSubtypeCongr D _ _ hcut).sum_comp (fun x ↦ ∑ p, ‖A w x p‖ ^ 2)

omit [Fintype V] in
/-- Every partially contracted subgraph has squared norm at most the product of the squared
vertex norms. Graphs with cycles are allowed; no edge may join a vertex to itself.

Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 6.2 `lem:group-tensor`,
05-frames.tex:143–157. -/
theorem partialNormSq_le_prod (hloop : ∀ e, tail e ≠ head e) (S : Finset V) :
    partialNormSq A S ≤ ∏ v ∈ S, vertexNormSq A v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [partialNormSq_empty]
  | insert w S hw ih =>
    calc partialNormSq A (insert w S) ≤ partialNormSq A S * partialNormSq A {w} :=
          partialNormSq_merge_le A (S₁ := S) (S₂ := {w}) (fun v ↦ by simp [or_comm])
            (fun v hv h ↦ hw (by rw [Finset.mem_singleton] at h; exact h ▸ hv))
      _ ≤ (∏ v ∈ S, vertexNormSq A v) * vertexNormSq A w := by
          rw [partialNormSq_singleton A hloop]
          exact mul_le_mul_of_nonneg_right ih (vertexNormSq_nonneg A w)
      _ = ∏ v ∈ insert w S, vertexNormSq A v := by rw [Finset.prod_insert hw, mul_comm]

omit [Fintype V] in
theorem partialNormSq_le_one (hloop : ∀ e, tail e ≠ head e)
    (hA : ∀ v, vertexNormSq A v ≤ 1) (S : Finset V) : partialNormSq A S ≤ 1 :=
  (partialNormSq_le_prod A hloop S).trans
    (Finset.prod_le_one₀ (fun v _ ↦ vertexNormSq_nonneg A v) fun v _ ↦ hA v)

omit [∀ v, Fintype (P v)] in
/-- The full contraction is the partial contraction of the whole vertex set; there are no
boundary edges. -/
theorem contraction_eq_partialContraction_univ (σ : (v : V) → P v)
    (b : (e : {e // IsCut tail head (Finset.univ : Finset V) e}) → D e) :
    contraction A σ = partialContraction A Finset.univ (fun v ↦ σ v) b := by
  classical
  let eE : ((e : {e // IsInternal tail head (Finset.univ : Finset V) e}) → D e) ≃
      ((e : E) → D e) :=
    { toFun := fun γ e ↦ γ ⟨e, ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
      invFun := fun β e ↦ β e
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  unfold partialContraction contraction
  rw [← eE.sum_comp]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [← (Equiv.subtypeUnivEquiv Finset.mem_univ).prod_comp]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  congr 1
  funext ⟨e, he⟩
  have h : IsInternal tail head Finset.univ e := ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  simp only [localConfig]
  rw [piSubtypeSplit_symm_apply_left (hq := h)]
  rfl

/-- The squared norm of the full contraction is that of the partial contraction of the whole
vertex set. -/
theorem sum_norm_sq_contraction : ∑ σ, ‖contraction A σ‖ ^ 2 = partialNormSq A Finset.univ := by
  classical
  let _ := piSubtypeUniqueOfForallNot D (IsCut tail head (Finset.univ : Finset V))
    (by simp [IsCut])
  let eV : ((v : {v // v ∈ (Finset.univ : Finset V)}) → P v) ≃ ((v : V) → P v) :=
    { toFun := fun σ v ↦ σ ⟨v, Finset.mem_univ v⟩
      invFun := fun σ v ↦ σ v
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  unfold partialNormSq
  rw [← eV.symm.sum_comp]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Fintype.sum_unique, contraction_eq_partialContraction_univ A σ default]
  rfl

/-- **Whole-group tensor bound, norm part.** For a finite graph without edges from a vertex to
itself, whose vertex tensors have norm at most one, the coordinate contraction has norm at most
one.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, 05-frames.tex:125–141;
proof 05-frames.tex:143–157. -/
theorem contraction_norm_le_one (hloop : ∀ e, tail e ≠ head e)
    (hA : ∀ v, vertexNormSq A v ≤ 1) :
    ‖(WithLp.toLp 2 (contraction A) : EuclideanSpace ℂ ((v : V) → P v))‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
  simpa [sum_norm_sq_contraction] using partialNormSq_le_one A hloop hA Finset.univ

end NormBound

/-! ### Bipartitions into whole open-leg groups -/

section Bipartition

/-- The matrix reshaping of a tensor on the open-leg groups across the bipartition of the vertices
into `T` and its complement. Each open-leg group stays whole. -/
def flattening (Z : ((v : V) → P v) → ℂ) (T : Finset V) :
    Matrix ((v : {v // v ∈ T}) → P v) ((v : {v // v ∉ T}) → P v) ℂ :=
  fun x y ↦ Z ((Equiv.piEquivPiSubtypeProd (· ∈ T) P).symm (x, y))

omit [Fintype E] [DecidableEq E] in
theorem mem_compl_disjoint (T : Finset V) : ∀ v, v ∈ T → v ∉ Tᶜ :=
  fun _ h h' ↦ Finset.mem_compl.mp h' h

omit [Fintype E] [DecidableEq E] in
theorem not_isExit_compl_left (T : Finset V) (e : E) : ¬IsExit tail head T Tᶜ e := by
  simp only [IsExit, IsCut, IsLink, Finset.mem_compl]
  tauto

omit [Fintype E] [DecidableEq E] in
theorem not_isExit_compl_right (T : Finset V) (e : E) : ¬IsExit tail head Tᶜ T e := by
  simp only [IsExit, IsCut, IsLink, Finset.mem_compl]
  tauto

/-- The partial contraction of `T`, as a matrix from the open legs of `T` to the labels of the
edges crossing the bipartition. -/
def bipartitionLeft (T : Finset V) :
    Matrix ((v : {v // v ∈ T}) → P v) ((e : {e // IsLink tail head T Tᶜ e}) → D e) ℂ :=
  fun x c ↦ partialContraction A T x
    ((cutSplitLeft D (mem_compl_disjoint T)).symm
      (c, fun e ↦ absurd e.2 (not_isExit_compl_left (tail := tail) (head := head) T e)))

/-- The partial contraction of the complement of `T`, as a matrix from its open legs to the labels
of the edges crossing the bipartition. -/
def bipartitionRight (T : Finset V) :
    Matrix ((v : {v // v ∉ T}) → P v) ((e : {e // IsLink tail head T Tᶜ e}) → D e) ℂ :=
  fun y c ↦ partialContraction A Tᶜ (fun v ↦ y ⟨v, Finset.mem_compl.mp v.2⟩)
    ((cutSplitRight D (mem_compl_disjoint T)).symm
      (c, fun e ↦ absurd e.2 (not_isExit_compl_right (tail := tail) (head := head) T e)))

omit [∀ v, Fintype (P v)] in
/-- Grouping all crossing edges into one index, the flattening of the contraction across a
bipartition into whole open-leg groups is `A Bᵀ`, with `A` and `B` the contractions of the two
sides.

Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 6.2 `lem:group-tensor`,
05-frames.tex:159–169. -/
theorem flattening_contraction (T : Finset V) :
    flattening (contraction A) T = bipartitionLeft A T * (bipartitionRight A T)ᵀ := by
  classical
  have hS : ∀ v, v ∈ (Finset.univ : Finset V) ↔ v ∈ T ∨ v ∈ Tᶜ := fun v ↦ by
    simp [Finset.mem_compl, em]
  ext x y
  rw [flattening, contraction_eq_partialContraction_univ A _
      ((cutSplit D hS (mem_compl_disjoint T)).symm
        (fun e ↦ absurd e.2 (not_isExit_compl_left (tail := tail) (head := head) T e),
          fun e ↦ absurd e.2 (not_isExit_compl_right (tail := tail) (head := head) T e)))]
  have hσ : (fun v : {v // v ∈ (Finset.univ : Finset V)} ↦
      (Equiv.piEquivPiSubtypeProd (· ∈ T) P).symm (x, y) v) =
      (vertexSplit P hS (mem_compl_disjoint T)).symm
        (x, fun v ↦ y ⟨v, Finset.mem_compl.mp v.2⟩) := by
    funext v
    by_cases hv : (v : V) ∈ T <;> simp [vertexSplit, piSubtypeSplit, hv]
  rw [hσ, partialContraction_merge A hS (mem_compl_disjoint T), Matrix.mul_apply]
  rfl

theorem hsNormSq_bipartitionLeft (T : Finset V) :
    Matrix.hsNormSq (bipartitionLeft A T) = partialNormSq A T := by
  classical
  let _ := piSubtypeUniqueOfForallNot D (IsExit tail head T Tᶜ) (not_isExit_compl_left T)
  unfold Matrix.hsNormSq partialNormSq bipartitionLeft
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← (cutSplitLeft D (mem_compl_disjoint T)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Fintype.sum_unique]
  congr 4

theorem hsNormSq_bipartitionRight (T : Finset V) :
    Matrix.hsNormSq (bipartitionRight A T) = partialNormSq A Tᶜ := by
  classical
  let _ := piSubtypeUniqueOfForallNot D (IsExit tail head Tᶜ T) (not_isExit_compl_right T)
  unfold Matrix.hsNormSq partialNormSq bipartitionRight
  rw [← (piSubtypeCongr P (· ∈ Tᶜ) (· ∉ T) fun v ↦ Finset.mem_compl).sum_comp]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← (cutSplitRight D (mem_compl_disjoint T)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Fintype.sum_unique]
  congr 4

/-- **Whole-group tensor bound, nuclear part.** For a finite graph without edges from a vertex to
itself, whose vertex tensors have norm at most one, the contraction has nuclear norm at most one
across every bipartition into whole open-leg groups. No dimension enters.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, 05-frames.tex:125–141;
proof and equation `eq:group-nuclear`, 05-frames.tex:159–169. -/
theorem nuclearNorm_flattening_le_one [∀ v, DecidableEq (P v)]
    (hloop : ∀ e, tail e ≠ head e) (hA : ∀ v, vertexNormSq A v ≤ 1) (T : Finset V) :
    Matrix.nuclearNorm (flattening (contraction A) T) ≤ 1 := by
  rw [flattening_contraction]
  refine (Matrix.nuclearNorm_mul_transpose_le _ _).trans ?_
  rw [hsNormSq_bipartitionLeft, hsNormSq_bipartitionRight]
  have h₁ := partialNormSq_le_one A hloop hA T
  have h₂ := partialNormSq_le_one A hloop hA Tᶜ
  calc √(partialNormSq A T) * √(partialNormSq A Tᶜ) ≤ 1 * 1 := by
        gcongr <;> exact Real.sqrt_le_one.mpr ‹_›
    _ = 1 := one_mul 1

end Bipartition

end TNLean.PEPS.WholeGroup
