/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.TruncatedAllTemperatures
import TNLean.Lattice.ProductFormIndexRestriction
import TNLean.Lattice.TrotterIndexCount

/-!
# Local index ranges of the truncated cluster expansion

Only clusters containing a site can occur as its cluster index in Hastings'
matrix product form. The retained clusters have bounded diameter, so their interaction
centres lie in a ball about that site. Counting subsets of those centres gives a local
index bound, independently of the total size of the lattice.

**Local fix (volume growth):** the source's exponential bound in the dimension-th power
of the truncation length uses polynomial growth of lattice balls. The metric alone does
not imply this growth; the general statement counts local interaction centres, and the
dimensional corollaries state the volume hypothesis explicitly. Documented in
`docs/paper-gaps/hastings05_planar_domain_scope.tex`.

Source: Hastings, arXiv:cond-mat/0508554v3, lines 1259–1279 and 1318–1320.
-/

open Finset Matrix QuantumCircuit
open scoped MatrixOrder ComplexOrder

namespace TNLean.Lattice.ClusterExpansion

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
  {q : ℕ}

open Classical in
/-- The index values at a site that record no cluster or a valid cluster containing it.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1259–1275. -/
noncomputable def clusterIndexSet (acts : κ → Finset σ) (near : σ → σ → Prop) (i : σ) :
    Finset (Option (Fin (Fintype.card (Finset κ))) × (Fin q × Fin q)) :=
  Finset.univ.filter fun a ↦ a.1.elim True fun k ↦
    IsValidCluster acts near ((Fintype.equivFin (Finset κ)).symm k) ∧
      i ∈ ((Fintype.equivFin (Finset κ)).symm k).biUnion acts

/-- An index not recording a cluster containing its site has zero coefficient.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1259–1275. -/
theorem coeff_clusterProductForm_eq_zero_of_not_mem_clusterIndexSet
    (acts : κ → Finset σ) (near : σ → σ → Prop) (hnear : ∀ i, near i i)
    {h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ}
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ)) (β : ℝ) (i : σ)
    (α : σ → Option (Fin (Fintype.card (Finset κ))) × (Fin q × Fin q))
    (hα : α i ∉ clusterIndexSet acts near i) :
    (clusterProductForm acts near hnear hh β).coeff i α = 0 := by
  classical
  have hbad : ¬ (α i).1.elim True (fun k ↦
      IsValidCluster acts near ((Fintype.equivFin (Finset κ)).symm k) ∧
        i ∈ ((Fintype.equivFin (Finset κ)).symm k).biUnion acts) := by
    simpa only [clusterIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hα
  change clusterCoeff acts near h β i
    (fun j ↦ ((α j).1.map (Fintype.equivFin (Finset κ)).symm, (α j).2)) = 0
  cases hc : (α i).1 with
  | none => exact (hbad (by simp only [hc, Option.elim_none])).elim
  | some k =>
    have hbad' : ¬ (IsValidCluster acts near ((Fintype.equivFin (Finset κ)).symm k) ∧
        i ∈ ((Fintype.equivFin (Finset κ)).symm k).biUnion acts) := by
      simpa only [hc, Option.elim_some] using hbad
    simp only [clusterCoeff, hc, Option.map_some, Option.elim_some]
    exact ite_eq_right fun h ↦ hbad' ⟨h.1, h.2.1⟩

/-- The cluster product form with only the index values allowed at each site.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1259–1279. -/
noncomputable def localClusterProductForm (acts : κ → Finset σ) (near : σ → σ → Prop)
    (hnear : ∀ i, near i i) {h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ}
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ)) (β : ℝ) :
    open Classical in ProductForm q near
      (∑ A with (∀ k ∈ A, (acts k).Nonempty) ∧
        NoLargeCluster (overlapGraph acts) (IsLargeSupport near acts) A, clusterOp h A β) :=
  (clusterProductForm acts near hnear hh β).restrict (clusterIndexSet acts near)
    (fun i α hα ↦ coeff_clusterProductForm_eq_zero_of_not_mem_clusterIndexSet
      acts near hnear hh β i α hα)

omit [Fintype σ] [DecidableEq κ] in
/-- If all valid clusters containing a site use terms from `T`, that site's allowed
index set has at most `(1 + 2^|T|) q²` values. Empty-support terms cannot belong to a valid
cluster and do not contribute labels. Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_clusterIndexSet_le (acts : κ → Finset σ) (near : σ → σ → Prop) (i : σ)
    (T : Finset κ)
    (hT : ∀ C, IsValidCluster acts near C → i ∈ C.biUnion acts → C ⊆ T) :
    (clusterIndexSet (q := q) acts near i).card ≤ (2 ^ T.card + 1) * (q * q) := by
  classical
  let e := Fintype.equivFin (Finset κ)
  let L : Finset (Fin (Fintype.card (Finset κ))) := Finset.univ.filter fun k ↦
    IsValidCluster acts near (e.symm k) ∧ i ∈ (e.symm k).biUnion acts
  have hIndex : clusterIndexSet (q := q) acts near i =
      (insert none (L.image some)).product (Finset.univ : Finset (Fin q × Fin q)) := by
    ext a
    rcases a with ⟨a, b⟩
    cases a <;> simp [clusterIndexSet, L, e]
  have hsub : L.image e.symm ⊆ T.powerset := by
    intro C hC
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hv, hi⟩ := (Finset.mem_filter.mp hk).2
    exact Finset.mem_powerset.mpr (hT _ hv hi)
  have hcard : L.card ≤ 2 ^ T.card := by
    calc
      L.card = (L.image e.symm).card :=
        (Finset.card_image_of_injective _ e.symm.injective).symm
      _ ≤ T.powerset.card := Finset.card_le_card hsub
      _ = 2 ^ T.card := Finset.card_powerset T
  rw [hIndex, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective _)]
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
    Nat.mul_le_mul_right (q * q) (Nat.add_le_add_right hcard 1)

omit [Fintype σ] [DecidableEq κ] in
/-- Every term of a valid cluster containing `i` has its centre within `l + R` of `i`.
Centres need not belong to their term supports. Empty supports are excluded by cluster
validity. Hastings, arXiv:cond-mat/0508554v3, lines 1103–1107 and 1273–1275. -/
theorem IsValidCluster.subset_centres_ball [PseudoMetricSpace σ]
    {acts : κ → Finset σ} {c : κ → σ} {R l : ℝ}
    (hR : ∀ k j, j ∈ acts k → dist (c k) j ≤ R)
    {C : Finset κ} (hC : IsValidCluster acts (fun a b ↦ dist a b ≤ l) C)
    {i : σ} (hi : i ∈ C.biUnion acts) :
    C ⊆ Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R) := by
  intro k hk
  obtain ⟨j, hj⟩ := hC.1 k hk
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
  have hlocal : dist i j ≤ l := hC.related hi (Finset.mem_biUnion.mpr ⟨k, hk, hj⟩)
  have hcentre : dist j (c k) ≤ R := by rw [dist_comm]; exact hR k j hj
  exact (dist_triangle i j (c k)).trans (add_le_add hlocal hcentre)

omit [Fintype σ] [DecidableEq κ] in
/-- A site's cluster index range is bounded by the number of interaction centres in a
local ball, rather than by the total number of terms.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_clusterIndexSet_le_ball [PseudoMetricSpace σ]
    (acts : κ → Finset σ) (c : κ → σ) (R l : ℝ)
    (hR : ∀ k j, j ∈ acts k → dist (c k) j ≤ R) (i : σ) :
    (clusterIndexSet (q := q) acts (fun a b ↦ dist a b ≤ l) i).card ≤
      (2 ^ (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card + 1) * (q * q) :=
  card_clusterIndexSet_le acts _ i _ fun _ hC hi ↦ hC.subset_centres_ball hR hi

/-- The restricted product form uses only the locally allowed index values, with their
actual cardinalities. Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_index_localClusterProductForm_le (acts : κ → Finset σ)
    (near : σ → σ → Prop) (hnear : ∀ i, near i i)
    {h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ}
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ)) (β : ℝ)
    (i : σ) (T : Finset κ)
    (hT : ∀ C, IsValidCluster acts near C → i ∈ C.biUnion acts → C ⊆ T) :
    Fintype.card ((localClusterProductForm acts near hnear hh β).Index i) ≤
      (2 ^ T.card + 1) * (q * q) := by
  classical
  change Fintype.card {a : Option (Fin (Fintype.card (Finset κ))) × (Fin q × Fin q) //
    a ∈ clusterIndexSet acts near i} ≤ _
  rw [Fintype.card_coe]
  exact card_clusterIndexSet_le acts near i T hT

/-- The actual diameter-truncated operator has a product form whose index range at `i`
is bounded by `(1 + 2^M) q²`, where `M` counts interaction centres within `l + R` of `i`.
Scalar terms with empty support contribute a scalar factor and no index components.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1256–1279. -/
theorem exists_productForm_truncatedExp_card_index [PseudoMetricSpace σ]
    [Nonempty σ] [NeZero q] (acts : κ → Finset σ) (c : κ → σ) (R l : ℝ)
    (hR : ∀ k j, j ∈ acts k → dist (c k) j ≤ R) (hl : 0 ≤ l)
    (h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ)) (β : ℝ) :
    ∃ P : ProductForm q (fun i j ↦ dist i j ≤ l)
        (truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β),
      ∀ i, Fintype.card (P.Index i) ≤
        (2 ^ (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card + 1) * (q * q) := by
  classical
  let near : σ → σ → Prop := fun i j ↦ dist i j ≤ l
  have hnear : ∀ i, near i i := fun i ↦ by simpa only [near, dist_self] using hl
  have hlarge : IsLargeSupport near acts = IsLargeDiam acts l := by
    funext C
    simp only [IsLargeSupport, IsLargeDiam, near, not_le]
  rw [← hlarge, truncatedExp_eq_mul acts h hh near β]
  let ρ₀ : Matrix (σ → Fin q) (σ → Fin q) ℂ :=
    ∑ A with ∀ k ∈ A, ¬ (acts k).Nonempty, clusterOp h A β
  have h₀ : ρ₀ ∈ supportedOperators q ((∅ : Finset σ) : Set σ) := by
    refine Submodule.sum_mem _ fun A hA ↦ supportedOperators_mono ?_
      (clusterOp_mem_supportedOperators hh A β)
    intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_biUnion.1 hx
    exact absurd ⟨x, hxk⟩ ((mem_filter.1 hA).2 k hk)
  let P₀ := ProductForm.ofSupported (near := near) (X := ∅) (Classical.arbitrary σ)
    (by simp) h₀
  let P₁ := localClusterProductForm acts near hnear hh β
  refine ⟨P₀.mul P₁, fun i ↦ ?_⟩
  change Fintype.card (P₀.Index i × P₁.Index i) ≤ _
  rw [Fintype.card_prod]
  have hP₀ : Fintype.card (P₀.Index i) = 1 := by
    simpa only [Finset.notMem_empty, ite_false] using
      ProductForm.card_index_ofSupported (near := near) (X := ∅) (Classical.arbitrary σ)
        (by simp) h₀ i
  rw [hP₀, one_mul]
  exact card_index_localClusterProductForm_le acts near hnear hh β i _
    fun _ hC hi ↦ hC.subset_centres_ball hR hi

/-- The every-temperature construction preserves the local index bound to the power
equal to the number of factors. Its even powers are positive semidefinite.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1311–1320. -/
theorem exists_productForm_truncatedExp_pow_card_index [PseudoMetricSpace σ]
    [Nonempty σ] [NeZero q] (acts : κ → Finset σ) (c : κ → σ) (R l : ℝ)
    (hR : ∀ k j, j ∈ acts k → dist (c k) j ≤ R) (hl : 0 ≤ l)
    (h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ))
    (hHerm : ∀ k, (h k).IsHermitian) (β : ℝ) {m : ℕ} (hm : Even m) :
    ∃ P : ProductForm q (fun i j ↦ dist i j ≤ l)
        ((truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β) ^ m),
      ((truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β) ^ m).PosSemidef ∧
        ∀ i, Fintype.card (P.Index i) ≤
          ((2 ^ (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card + 1) * (q * q)) ^ m := by
  obtain ⟨P, hP⟩ := exists_productForm_truncatedExp_card_index acts c R l hR hl h hh β
  refine ⟨P.pow m, posSemidef_pow_of_even (isHermitian_truncatedExp _ _ hHerm β) hm,
    fun i ↦ ?_⟩
  exact (ProductForm.card_index_pow P m i).trans_le (Nat.pow_le_pow_left (hP i) m)

/-- On a lattice with polynomial ball growth, the truncated operator has index range
exponential in the dimension-th power of the truncation length. The volume hypothesis
counts interaction labels, allowing more than one term at a centre.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem exists_productForm_truncatedExp_card_index_of_polynomial_growth
    [PseudoMetricSpace σ] [Nonempty σ] [NeZero q]
    (acts : κ → Finset σ) (c : κ → σ) (R l : ℝ)
    (hR : ∀ k j, j ∈ acts k → dist (c k) j ≤ R) (hl : 0 ≤ l)
    (C D : ℕ)
    (hvolume : ∀ i, (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card ≤
      C * (⌈l + R⌉₊ + 1) ^ D)
    (h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ)) (β : ℝ) :
    ∃ P : ProductForm q (fun i j ↦ dist i j ≤ l)
        (truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β),
      ∀ i, Fintype.card (P.Index i) ≤
        (q * q) * (1 + 2 ^ (C * (⌈l + R⌉₊ + 1) ^ D)) := by
  obtain ⟨P, hP⟩ := exists_productForm_truncatedExp_card_index acts c R l hR hl h hh β
  refine ⟨P, fun i ↦ (hP i).trans ?_⟩
  rw [Nat.mul_comm (q * q), Nat.add_comm 1]
  exact Nat.mul_le_mul_right (q * q)
    (Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) (hvolume i)) 1)

/-- Polynomial ball growth yields the every-temperature index range exponential in the
number of factors times the dimension-th power of the truncation length.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1318–1320. -/
theorem exists_productForm_truncatedExp_pow_card_index_of_polynomial_growth
    [PseudoMetricSpace σ] [Nonempty σ] [NeZero q]
    (acts : κ → Finset σ) (c : κ → σ) (R l : ℝ)
    (hR : ∀ k j, j ∈ acts k → dist (c k) j ≤ R) (hl : 0 ≤ l)
    (C D : ℕ)
    (hvolume : ∀ i, (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card ≤
      C * (⌈l + R⌉₊ + 1) ^ D)
    (h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ))
    (hHerm : ∀ k, (h k).IsHermitian) (β : ℝ) {m : ℕ} (hm : Even m) :
    ∃ P : ProductForm q (fun i j ↦ dist i j ≤ l)
        ((truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β) ^ m),
      ((truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β) ^ m).PosSemidef ∧
        ∀ i, Fintype.card (P.Index i) ≤
          ((q * q) * (1 + 2 ^ (C * (⌈l + R⌉₊ + 1) ^ D))) ^ m := by
  obtain ⟨P, hP⟩ := exists_productForm_truncatedExp_card_index_of_polynomial_growth
    acts c R l hR hl C D hvolume h hh β
  refine ⟨P.pow m, posSemidef_pow_of_even (isHermitian_truncatedExp _ _ hHerm β) hm,
    fun i ↦ ?_⟩
  exact (ProductForm.card_index_pow P m i).trans_le (Nat.pow_le_pow_left (hP i) m)

end TNLean.Lattice.ClusterExpansion
