/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProductCutIteration
import TNLean.Algebra.CyclicInsertion

/-!
# Products of consecutive copies on a chain

The sites of a chain of length `K * L` are grouped into `K` consecutive blocks
of length `L`. The product of block vectors is defined on these literal site
coordinates, rather than identified with a tensor product by an assumption.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 421–479.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw

variable {K L q : ℕ}

/-- Configurations on consecutive blocks, in the order `L * i + j`. -/
def copyConfigurationEquiv (K L q : ℕ) :
    (Fin (K * L) → Fin q) ≃ (Fin K → Fin L → Fin q) where
  toFun σ i j := σ (finProdFinEquiv (i, j))
  invFun τ s := τ (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2
  left_inv σ := funext fun s ↦ congrArg σ (finProdFinEquiv.apply_symm_apply s)
  right_inv τ := by funext i j; simp

/-- The product of the supplied block vectors on `K * L` consecutive sites. -/
def copyProduct (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    EuclideanSpace ℂ (Fin (K * L) → Fin q) :=
  WithLp.toLp 2 fun σ ↦ EuclideanSpace.piTensor η (copyConfigurationEquiv K L q σ)

/-- The norm of a block product is the product of the block norms. -/
theorem norm_copyProduct (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖copyProduct η‖ = ∏ i, ‖η i‖ := by
  rw [← EuclideanSpace.norm_piTensor η]
  simp only [EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp (copyConfigurationEquiv K L q)
    (fun σ ↦ ‖EuclideanSpace.piTensor η σ‖ ^ 2)

/-- A site lies before a copy boundary exactly when its block does. -/
private theorem copySite_mem_leftBlock_iff (i : Fin K) (j : Fin L) (t : ℕ) :
    finProdFinEquiv (i, j) ∈ leftBlock (K * L) (t * L) ↔ i.val < t := by
  rw [mem_leftBlock]
  change j.val + L * i.val < t * L ↔ i.val < t
  constructor
  · intro h
    by_contra hi
    have ht : t ≤ i.val := Nat.le_of_not_gt hi
    nlinarith [Nat.mul_le_mul_right L ht]
  · intro hi
    have ht : i.val + 1 ≤ t := hi
    nlinarith [Nat.mul_le_mul_right L ht, j.isLt]

/-- A literal block product factors at every boundary between copies.
Source: arXiv:0705.0292v2, lines 421–470. -/
theorem copyProduct_factors_at_boundary
    (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) (t : ℕ) :
    ∃ (a : EuclideanSpace ℂ
        (Entropy.RegionConfig (fun _ : Fin (K * L) ↦ q) (leftBlock (K * L) (t * L))))
      (b : EuclideanSpace ℂ
        ((i : {i : Fin (K * L) // i ∉ leftBlock (K * L) (t * L)}) → Fin q)),
      Entropy.cutVector (leftBlock (K * L) (t * L)) (copyProduct η) =
        Matrix.euclideanTensorVector a b := by
  classical
  let a : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin (K * L) ↦ q) (leftBlock (K * L) (t * L))) :=
    WithLp.toLp 2 fun σ ↦ ∏ i : Fin K, if h : i.val < t then
      η i (fun j ↦ σ ⟨finProdFinEquiv (i, j), (copySite_mem_leftBlock_iff i j t).mpr h⟩)
    else 1
  let b : EuclideanSpace ℂ
      ((i : {i : Fin (K * L) // i ∉ leftBlock (K * L) (t * L)}) → Fin q) :=
    WithLp.toLp 2 fun σ ↦ ∏ i : Fin K, if h : i.val < t then 1 else
      η i (fun j ↦ σ ⟨finProdFinEquiv (i, j),
        fun hm ↦ h ((copySite_mem_leftBlock_iff i j t).mp hm)⟩)
  refine ⟨a, b, ?_⟩
  ext xy
  change (∏ i : Fin K, η i (fun j ↦
    (Entropy.cutEquiv (fun _ : Fin (K * L) ↦ q) (leftBlock (K * L) (t * L))).symm xy
      (finProdFinEquiv (i, j)))) = _
  change _ = a xy.1 * b xy.2
  dsimp only [a, b]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : i.val < t
  · simp only [dite_eq_left h, mul_one]
    apply congrArg (η i)
    funext j
    exact Entropy.cutEquiv_symm_apply_mem (n := fun _ : Fin (K * L) ↦ q) xy.1 xy.2
      ((copySite_mem_leftBlock_iff i j t).mpr h)
  · simp only [dite_eq_right h, one_mul]
    apply congrArg (η i)
    funext j
    exact Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin (K * L) ↦ q) xy.1 xy.2
      (fun hm ↦ h ((copySite_mem_leftBlock_iff i j t).mp hm))

/-- Inner products of literal block products factor over the blocks. -/
theorem inner_copyProduct (η θ : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    inner ℂ (copyProduct η) (copyProduct θ) = ∏ i, inner ℂ (η i) (θ i) := by
  rw [← EuclideanSpace.inner_piTensor η θ]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  exact Equiv.sum_comp (copyConfigurationEquiv K L q)
    (fun σ ↦ EuclideanSpace.piTensor θ σ * star (EuclideanSpace.piTensor η σ))

/-- Against a literal product target, a normalized MPS admits a replacement with
rank at most one at every copy boundary and with no smaller overlap.
Source: arXiv:0705.0292v2, lines 421–470. -/
theorem IsOpenMPS.exists_rank_one_at_copy_boundaries {D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin (K * L) → Fin q)}
    (hψ : IsOpenMPS (K * L) q D (fun x ↦ ψ x)) (hnorm : ‖ψ‖ = 1)
    (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    ∃ χ : EuclideanSpace ℂ (Fin (K * L) → Fin q),
      IsOpenMPS (K * L) q D (fun x ↦ χ x) ∧ ‖χ‖ = 1 ∧
      ‖inner ℂ (copyProduct η) ψ‖ ≤ ‖inner ℂ (copyProduct η) χ‖ ∧
      (∀ j, (cutMatrix χ j).rank ≤ (cutMatrix ψ j).rank) ∧
      ∀ t ≤ K, (cutMatrix χ (t * L)).rank ≤ 1 := by
  classical
  let S := (Finset.range (K + 1)).image (fun t ↦ t * L)
  have hf : ∀ k ∈ S,
      ∃ a b, Entropy.cutVector (leftBlock (K * L) k) (copyProduct η) =
        Matrix.euclideanTensorVector a b := by
    intro k hk
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hk
    exact copyProduct_factors_at_boundary η t
  obtain ⟨χ, hm, hn, ho, hr, hb⟩ := hψ.exists_rank_one_at_product_cuts hnorm S hf
  refine ⟨χ, hm, hn, ho, hr, fun t ht ↦ hb (t * L) ?_⟩
  exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩

end TNLean.MPS.AreaLaw
