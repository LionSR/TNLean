/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Support
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The exact light cone of a sweep on a perturbed ground vector

Let `f_k` be operators on a system of sites, each acting on a region `T_k` and fixing a vector `Ω`.
Let `B` be an operator on the sites together with a register `α`, whose blocks
`σ, τ ↦ B (σ, a) (τ, b)` all act on a region `U`, and put `ζ = B (Ω ⊗ ξ)`. A factor `f_k` with
`T_k` disjoint from `U` commutes with every block of `B` and fixes `Ω`, so it fixes `ζ`. A factor
meeting `U` is kept, and enlarges the region to `T_k ∪ U`. Processing the factors of a word in
order therefore gives an operator `L`, the product of the kept factors, with

`(f_{k_m} ⋯ f_{k_1} ⊗ 1) ζ = (L ⊗ 1) ζ`,

`L` acting on the final region and fixing `Ω`. This is `eq:cone` of the frustration-free
area-law note. When the word consists of layers of factors with pairwise disjoint regions, one
layer enlarges the region at most to the set of regions meeting it
(`retainedSet_subset_of_pairwise_disjoint`).

## Main definitions

* `ManyBody.LightCone.sweepProd`: the product of the factors of a word, the first acting first.
* `ManyBody.LightCone.retainedProd`, `ManyBody.LightCone.retainedSet`: the kept factors and the
  final region.

## Main statements

* `ManyBody.LightCone.kronecker_one_mulVec_sweep_eq_retained`: the light-cone identity.
* `ManyBody.LightCone.retainedProd_mem_supportedOperators`, `retainedProd_mulVec_eq_self`,
  `conjTranspose_retainedProd_mulVec_eq_self`: the kept product acts on the final region and
  fixes `Ω`, and so does its adjoint.
* `ManyBody.LightCone.retainedSet_subset_of_pairwise_disjoint`: one layer of disjoint factors.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  paragraph "Exact localization on the perturbed vector", `eq:cone`.
-/

open Matrix
open scoped Kronecker

namespace ManyBody.LightCone

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {α : Type*} [Fintype α] [DecidableEq α]

/-- The block `σ, τ ↦ B (σ, a) (τ, b)` of an operator on the sites and a register. -/
def block (B : Matrix (Config X × α) (Config X × α) ℂ) (a b : α) :
    Matrix (Config X) (Config X) ℂ :=
  B.submatrix (fun σ ↦ (σ, a)) (fun τ ↦ (τ, b))

/-- Every block of `B` acts on `U`. -/
def BlocksSupportedOn (B : Matrix (Config X × α) (Config X × α) ℂ) (U : Finset V) : Prop :=
  ∀ a b, block B a b ∈ supportedOperators X U

/-- The product vector `Ω ⊗ ξ`. -/
def prodVec (Ω : Config X → ℂ) (ξ : α → ℂ) : Config X × α → ℂ := fun p ↦ Ω p.1 * ξ p.2

omit [∀ v, DecidableEq (X v)] [DecidableEq α] in
/-- The coordinates of `B (Ω ⊗ ξ)` through the blocks of `B`. -/
theorem mulVec_prodVec_apply (B : Matrix (Config X × α) (Config X × α) ℂ) (Ω : Config X → ℂ)
    (ξ : α → ℂ) (σ : Config X) (a : α) :
    (B *ᵥ prodVec Ω ξ) (σ, a) = ∑ b, ξ b * (block B a b *ᵥ Ω) σ := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, prodVec, block, submatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ ↦ by ring

omit [∀ v, DecidableEq (X v)] in
/-- The coordinates of `(G ⊗ 1) w`. -/
theorem kronecker_one_mulVec_apply (G : Matrix (Config X) (Config X) ℂ)
    (w : Config X × α → ℂ) (σ : Config X) (a : α) :
    ((G ⊗ₖ (1 : Matrix α α ℂ)) *ᵥ w) (σ, a) = (G *ᵥ fun τ ↦ w (τ, a)) σ := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  simp

omit [∀ v, DecidableEq (X v)] in
/-- The blocks of `(G ⊗ 1) B` are `G` times the blocks of `B`. -/
theorem block_kronecker_one_mul (G : Matrix (Config X) (Config X) ℂ)
    (B : Matrix (Config X × α) (Config X × α) ℂ) (a b : α) :
    block ((G ⊗ₖ (1 : Matrix α α ℂ)) * B) a b = G * block B a b := by
  ext σ τ
  simp only [block, submatrix_apply, mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    one_apply]
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [Finset.sum_eq_single a (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp)]
  simp

/-- A factor fixing `Ω` and acting away from the blocks of `B` fixes `B (Ω ⊗ ξ)`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Exact localization on the
perturbed vector": "Its factors missing `S₀` commute past `B₀` and fix `Ω`". -/
theorem kronecker_one_mulVec_eq_self {B : Matrix (Config X × α) (Config X × α) ℂ}
    {U D : Finset V} (hB : BlocksSupportedOn B U) {G : Matrix (Config X) (Config X) ℂ}
    (hG : G ∈ supportedOperators X D) (hDU : Disjoint D U) {Ω : Config X → ℂ}
    (hGΩ : G *ᵥ Ω = Ω) (ξ : α → ℂ) :
    (G ⊗ₖ (1 : Matrix α α ℂ)) *ᵥ (B *ᵥ prodVec Ω ξ) = B *ᵥ prodVec Ω ξ := by
  ext ⟨σ, a⟩
  rw [kronecker_one_mulVec_apply]
  have hw : (fun τ ↦ (B *ᵥ prodVec Ω ξ) (τ, a)) = ∑ b, ξ b • (block B a b *ᵥ Ω) := by
    ext τ
    rw [mulVec_prodVec_apply, Finset.sum_apply]
    rfl
  rw [hw, mulVec_sum, mulVec_prodVec_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [mulVec_smul, mulVec_mulVec,
    (commute_of_mem_supportedOperators_of_disjoint hG (hB a b) hDU).eq, ← mulVec_mulVec, hGΩ]
  rfl

variable {κ : Type*} (f : κ → Matrix (Config X) (Config X) ℂ) (T : κ → Finset V)

/-- The product of the factors of a word, the first letter acting first:
`sweepProd [k₁, …, k_m] = f_{k_m} ⋯ f_{k_1}`. -/
def sweepProd : List κ → Matrix (Config X) (Config X) ℂ
  | [] => 1
  | k :: l => sweepProd l * f k

/-- The product of the kept factors of a word, starting from the region `U`: a factor is kept
when its region meets the current region, which it then enlarges. -/
def retainedProd : Finset V → List κ → Matrix (Config X) (Config X) ℂ
  | _, [] => 1
  | U, k :: l => if Disjoint (T k) U then retainedProd U l else retainedProd (T k ∪ U) l * f k

/-- The final region of `retainedProd`. -/
def retainedSet : Finset V → List κ → Finset V
  | U, [] => U
  | U, k :: l => if Disjoint (T k) U then retainedSet U l else retainedSet (T k ∪ U) l

variable {f T}

theorem sweepProd_append (l₁ l₂ : List κ) :
    sweepProd f (l₁ ++ l₂) = sweepProd f l₂ * sweepProd f l₁ := by
  induction l₁ with
  | nil => simp [sweepProd]
  | cons k l ih => simp [sweepProd, ih, Matrix.mul_assoc]

theorem sweepProd_flatten_replicate (l : List κ) (t : ℕ) :
    sweepProd f (List.replicate t l).flatten = sweepProd f l ^ t := by
  induction t with
  | zero => simp [sweepProd]
  | succ t ih => rw [List.replicate_succ, List.flatten_cons, sweepProd_append, ih, pow_succ]

omit [Fintype V] in
theorem subset_retainedSet (U : Finset V) (l : List κ) : U ⊆ retainedSet T U l := by
  induction l generalizing U with
  | nil => exact le_rfl
  | cons k l ih =>
    simp only [retainedSet]
    split_ifs
    · exact ih U
    · exact Finset.subset_union_right.trans (ih _)

omit [Fintype V] in
theorem retainedSet_append (U : Finset V) (l₁ l₂ : List κ) :
    retainedSet T U (l₁ ++ l₂) = retainedSet T (retainedSet T U l₁) l₂ := by
  induction l₁ generalizing U with
  | nil => rfl
  | cons k l ih =>
    simp only [List.cons_append, retainedSet]
    split_ifs <;> exact ih _

/-- The kept product acts on the final region. -/
theorem retainedProd_mem_supportedOperators (hf : ∀ k, f k ∈ supportedOperators X (T k))
    (U : Finset V) (l : List κ) :
    retainedProd f T U l ∈ supportedOperators X (retainedSet T U l) := by
  induction l generalizing U with
  | nil => exact one_mem _
  | cons k l ih =>
    simp only [retainedProd, retainedSet]
    split_ifs
    · exact ih U
    · exact mul_mem (ih _) (supportedOperators_mono
        (Finset.subset_union_left.trans (subset_retainedSet _ l)) (hf k))

/-- The kept product fixes every vector fixed by all factors. -/
theorem retainedProd_mulVec_eq_self {Ω : Config X → ℂ} (hΩ : ∀ k, f k *ᵥ Ω = Ω)
    (U : Finset V) (l : List κ) : retainedProd f T U l *ᵥ Ω = Ω := by
  induction l generalizing U with
  | nil => exact one_mulVec Ω
  | cons k l ih =>
    simp only [retainedProd]
    split_ifs
    · exact ih U
    · rw [← mulVec_mulVec, hΩ, ih]

/-- The adjoint of the kept product fixes every vector fixed by the adjoints of all factors. -/
theorem conjTranspose_retainedProd_mulVec_eq_self {Ω : Config X → ℂ}
    (hΩ : ∀ k, (f k)ᴴ *ᵥ Ω = Ω) (U : Finset V) (l : List κ) :
    (retainedProd f T U l)ᴴ *ᵥ Ω = Ω := by
  induction l generalizing U with
  | nil => simp [retainedProd]
  | cons k l ih =>
    simp only [retainedProd]
    split_ifs
    · exact ih U
    · rw [conjTranspose_mul, ← mulVec_mulVec, ih, hΩ]

/-- **The exact light cone** (`eq:cone` of the frustration-free area-law note). If every factor
acts on its region and fixes `Ω`, and every block of `B` acts on `U`, then the product of the
factors of a word and the product of its kept factors agree on `B (Ω ⊗ ξ)`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Exact localization on the
perturbed vector". -/
theorem kronecker_one_mulVec_sweep_eq_retained (hf : ∀ k, f k ∈ supportedOperators X (T k))
    {Ω : Config X → ℂ} (hΩ : ∀ k, f k *ᵥ Ω = Ω) (ξ : α → ℂ) (l : List κ) :
    ∀ (U : Finset V) (B : Matrix (Config X × α) (Config X × α) ℂ), BlocksSupportedOn B U →
      (sweepProd f l ⊗ₖ (1 : Matrix α α ℂ)) *ᵥ (B *ᵥ prodVec Ω ξ) =
        (retainedProd f T U l ⊗ₖ (1 : Matrix α α ℂ)) *ᵥ (B *ᵥ prodVec Ω ξ) := by
  induction l with
  | nil => intro U B _; rfl
  | cons k l ih =>
    intro U B hB
    have hsplit (L : Matrix (Config X) (Config X) ℂ) :
        (L * f k) ⊗ₖ (1 : Matrix α α ℂ) =
          (L ⊗ₖ (1 : Matrix α α ℂ)) * (f k ⊗ₖ (1 : Matrix α α ℂ)) := by
      rw [← mul_kronecker_mul, Matrix.one_mul]
    simp only [sweepProd, retainedProd]
    rw [hsplit, ← mulVec_mulVec]
    split_ifs with hk
    · rw [kronecker_one_mulVec_eq_self hB (hf k) hk (hΩ k), ih U B hB]
    · have hB' : BlocksSupportedOn ((f k ⊗ₖ (1 : Matrix α α ℂ)) * B) (T k ∪ U) := fun a b ↦ by
        rw [block_kronecker_one_mul]
        exact mul_mem (supportedOperators_mono Finset.subset_union_left (hf k))
          (supportedOperators_mono Finset.subset_union_right (hB a b))
      have h := ih _ _ hB'
      rw [← mulVec_mulVec] at h
      rw [h, hsplit, ← mulVec_mulVec]

/-- **One layer of disjoint factors.** Let `grow U` contain `U` and every region of the layer that
meets `U`. If the regions of the factors of a word are pairwise disjoint, then processing the word
from any `W` with `U ⊆ W ⊆ grow U`, whose regions avoid `W \ U`, ends inside `grow U`. In
particular `retainedSet T U l ⊆ grow U`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Exact localization on the
perturbed vector": "The factors retained enlarge the support of the perturbing operator by at most
`R` in graph distance". -/
theorem retainedSet_subset_of_pairwise_disjoint {U G : Finset V}
    (hUG : U ⊆ G) {l : List κ} (hl : l.Pairwise fun k k' ↦ Disjoint (T k) (T k'))
    (hgrow : ∀ k ∈ l, ¬Disjoint (T k) U → T k ⊆ G) :
    retainedSet T U l ⊆ G := by
  suffices h : ∀ W : Finset V, U ⊆ W → W ⊆ G → (∀ k ∈ l, Disjoint (T k) (W \ U)) →
      retainedSet T W l ⊆ G from h U le_rfl hUG (fun k _ ↦ by simp)
  induction l with
  | nil => intro W _ hWG _; exact hWG
  | cons k l ih =>
    intro W hUW hWG hdis
    rw [List.pairwise_cons] at hl
    simp only [retainedSet]
    split_ifs with hk
    · exact ih hl.2 (fun k' hk' ↦ hgrow k' (List.mem_cons_of_mem _ hk')) W hUW hWG
        fun k' hk' ↦ hdis k' (List.mem_cons_of_mem _ hk')
    · have hkU : ¬Disjoint (T k) U := fun hd ↦ hk (by
        have := hdis k (List.mem_cons_self ..)
        rw [← Finset.sdiff_union_of_subset hUW]
        exact Finset.disjoint_union_right.mpr ⟨this, hd⟩)
      refine ih hl.2 (fun k' hk' ↦ hgrow k' (List.mem_cons_of_mem _ hk')) _
        (hUW.trans Finset.subset_union_right)
        (Finset.union_subset (hgrow k (List.mem_cons_self ..) hkU) hWG) fun k' hk' ↦ ?_
      rw [Finset.union_sdiff_distrib]
      exact Finset.disjoint_union_right.mpr ⟨(hl.1 k' hk').symm.mono_right Finset.sdiff_subset,
        hdis k' (List.mem_cons_of_mem _ hk')⟩

end ManyBody.LightCone
