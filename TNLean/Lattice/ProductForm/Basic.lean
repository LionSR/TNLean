/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Logic.Function.DependsOn
import QICLean.Entropy.LocalLift
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Product forms on finite sets of sites

The coefficient at a site reads only auxiliary indices in its prescribed neighbourhood.
Local physical dimensions may vary. Source: Hastings, arXiv:cond-mat/0508554v3,
equation `mpf`, lines 1024–1039, and the product construction, lines 1053–1077.
-/

open Matrix
open scoped BigOperators

namespace TNLean.Lattice.Locality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A product form with coefficient neighbourhoods `U` and local dimensions `n`.
Source: Hastings, arXiv:cond-mat/0508554v3, equation `mpf`, lines 1024–1039. -/
structure ProductForm (U : ι → Set ι) (n : ι → ℕ)
    (ρ : Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ) where
  /-- The common finite auxiliary index type. -/
  Index : Type
  /-- Finiteness of the auxiliary indices. -/
  [fintype : Fintype Index]
  /-- The operator at each site for each auxiliary index. -/
  siteOp : (j : ι) → Index → Matrix (Fin (n j)) (Fin (n j)) ℂ
  /-- The scalar coefficient at each site. -/
  coeff : ι → (ι → Index) → ℂ
  /-- Only indices in the prescribed neighbourhood affect the coefficient. -/
  coeff_local : ∀ i, DependsOn (coeff i) (U i)
  /-- The finite expansion into products of single-site operators. -/
  eq_sum : ρ = ∑ α : ι → Index, (∏ i, coeff i α) •
    Matrix.of (fun x y ↦ ∏ j, siteOp j (α j) (x j) (y j))

attribute [instance] ProductForm.fintype

/-- Existence of a product form. Source: Hastings, arXiv:cond-mat/0508554v3,
equation `mpf`, lines 1024–1039. -/
def HasProductForm (U : ι → Set ι) (n : ι → ℕ)
    (ρ : Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ) : Prop :=
  Nonempty (ProductForm U n ρ)

/-- Uniform auxiliary indices obtained by padding finite site-dependent indices.
The bound on their number is retained in the result. Source: Hastings,
arXiv:cond-mat/0508554v3, grouping of indices, lines 1069–1077. -/
noncomputable def productFormOfSiteIndices (U : ι → Set ι) (n : ι → ℕ)
    (hU : ∀ i, i ∈ U i) (I : ι → Type) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (siteOp : (j : ι) → I j → Matrix (Fin (n j)) (Fin (n j)) ℂ)
    (coeff : ι → ((j : ι) → I j) → ℂ) (hlocal : ∀ i, DependsOn (coeff i) (U i))
    {ρ : Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ}
    (heq : ρ = ∑ α : (j : ι) → I j, (∏ i, coeff i α) •
      Matrix.of (fun x y ↦ ∏ j, siteOp j (α j) (x j) (y j)))
    (K : ℕ) (hK : ∀ j, Fintype.card (I j) ≤ K) :
    {P : ProductForm U n ρ // P.Index = Fin K} := by
  classical
  let e : (j : ι) → I j ↪ Fin K := fun j ↦
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hK j))
  let d : (j : ι) → Fin K → I j := fun j ↦ Function.invFun (e j)
  have hde (j : ι) : Function.LeftInverse (d j) (e j) :=
    Function.leftInverse_invFun (e j).injective
  refine ⟨{ Index := Fin K
            siteOp := fun j a ↦ siteOp j (d j a)
            coeff := fun i α ↦ coeff i (fun j ↦ d j (α j)) *
             if α i ∈ Set.range (e i) then 1 else 0
            coeff_local := ?_
            eq_sum := ?_ }, rfl⟩
  · intro i α β h
    dsimp only
    rw [h i (hU i),
      hlocal i (fun j hj ↦ congrArg (d j) (h j hj))]
  · refine heq.trans ?_
    refine Fintype.sum_of_injective
      (fun α : (j : ι) → I j ↦ fun j ↦ e j (α j)) ?_ _ _ ?_ ?_
    · intro α β h
      exact funext fun j ↦ (e j).injective (congrFun h j)
    · intro α hα
      have hout : ∃ j, α j ∉ Set.range (e j) := by
        by_contra! h
        choose β hβ using h
        exact hα ⟨β, funext hβ⟩
      obtain ⟨j, hj⟩ := hout
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), zero_smul]
    · intro α
      simp only [hde _ _, Set.mem_range_self, ↓reduceIte, mul_one]

/-- Enlarging coefficient neighbourhoods preserves the product form. -/
theorem HasProductForm.mono {U V : ι → Set ι} (hUV : ∀ i, U i ⊆ V i)
    {n : ι → ℕ} {ρ : Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ}
    (hρ : HasProductForm U n ρ) : HasProductForm V n ρ := by
  obtain ⟨P⟩ := hρ
  exact ⟨{ P with coeff_local := fun i ↦ (P.coeff_local i).mono (hUV i) }⟩

/-- The identity has a product form with one auxiliary index value at each site. -/
theorem hasProductForm_one (U : ι → Set ι) (n : ι → ℕ) : HasProductForm U n 1 := by
  refine ⟨{ Index := Unit
            siteOp := fun _ _ ↦ 1
            coeff := fun _ _ ↦ 1
            coeff_local := fun _ _ _ _ ↦ rfl
            eq_sum := ?_ }⟩
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.prod_const_one, smul_eq_mul, one_mul,
    Matrix.of_apply, Fintype.sum_unique]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.one_apply_ne hj

/-- Multiplication of products of single-site matrix entries.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1068–1077. -/
theorem productEntries_mul {n : ι → ℕ}
    (A B : (j : ι) → Matrix (Fin (n j)) (Fin (n j)) ℂ) :
    Matrix.of (fun (x y : (j : ι) → Fin (n j)) ↦ ∏ j, A j (x j) (y j)) *
      Matrix.of (fun (x y : (j : ι) → Fin (n j)) ↦ ∏ j, B j (x j) (y j)) =
        Matrix.of (fun (x y : (j : ι) → Fin (n j)) ↦ ∏ j, (A j * B j) (x j) (y j)) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun z _ ↦ (Finset.prod_mul_distrib).symm

/-- Multiplying product forms pairs their auxiliary indices site by site.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1068–1077. -/
theorem HasProductForm.mul {U : ι → Set ι} {n : ι → ℕ}
    {ρ σ : Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ}
    (hρ : HasProductForm U n ρ) (hσ : HasProductForm U n σ) :
    HasProductForm U n (ρ * σ) := by
  obtain ⟨P⟩ := hρ
  obtain ⟨Q⟩ := hσ
  refine ⟨{ Index := P.Index × Q.Index
            siteOp := fun j a ↦ P.siteOp j a.1 * Q.siteOp j a.2
            coeff := fun i γ ↦ P.coeff i (fun j ↦ (γ j).1) * Q.coeff i (fun j ↦ (γ j).2)
            coeff_local := fun i α β h ↦ ?_
            eq_sum := ?_ }⟩
  · dsimp only
    rw [P.coeff_local i (fun j hj ↦ congrArg Prod.fst (h j hj)),
      Q.coeff_local i (fun j hj ↦ congrArg Prod.snd (h j hj))]
  · refine (congrArg₂ (· * ·) P.eq_sum Q.eq_sum).trans ?_
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun x ↦ ?_
    simp only [Equiv.arrowProdEquivProdArrow, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, productEntries_mul, Finset.prod_mul_distrib]
    rw [mul_comm]
    rfl

/-- Finite ordered products preserve coefficient neighbourhoods. -/
theorem hasProductForm_list_prod {U : ι → Set ι} {n : ι → ℕ}
    (L : List (Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ))
    (hL : ∀ ρ ∈ L, HasProductForm U n ρ) : HasProductForm U n L.prod := by
  induction L with
  | nil => exact hasProductForm_one U n
  | cons ρ L ih =>
    rw [List.prod_cons]
    exact (hL ρ (by simp)).mul (ih fun σ hσ ↦ hL σ (by simp [hσ]))

/-- Powers preserve coefficient neighbourhoods. -/
theorem HasProductForm.pow {U : ι → Set ι} {n : ι → ℕ}
    {ρ : Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ}
    (hρ : HasProductForm U n ρ) (k : ℕ) : HasProductForm U n (ρ ^ k) := by
  induction k with
  | zero => simpa using hasProductForm_one U n
  | succ k ih => simpa [pow_succ] using ih.mul hρ

end TNLean.Lattice.Locality
