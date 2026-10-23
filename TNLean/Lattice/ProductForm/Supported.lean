/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm.Basic

/-!
# Product forms of supported operators

Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1077. The physical
spaces may have different dimensions. Empty physical spaces are handled internally.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.Lattice.Locality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A supported operator has a product form when its support lies in the
neighbourhood of its specified centre. The support need not contain the centre.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1067. -/
noncomputable def productFormOfSupported (U : ι → Set ι) (n : ι → ℕ)
    (hU : ∀ i, i ∈ U i) (X : Finset ι) (i₀ : ι) (hX : ∀ j ∈ X, j ∈ U i₀)
    {ρ : Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ}
    (hρ : Entropy.IsSupportedOn ρ X) : ProductForm U n ρ := by
  classical
  by_cases hconfig : Nonempty ((j : ι) → Fin (n j))
  · let σ₀ := Classical.choice hconfig
    let I := fun j ↦ Fin (n j) × Fin (n j)
    letI : ∀ j, Nonempty (I j) := fun j ↦ ⟨(σ₀ j, σ₀ j)⟩
    let row : ((j : ι) → I j) → (j : ι) → Fin (n j) :=
      fun α j ↦ if j ∈ X then (α j).1 else σ₀ j
    let col : ((j : ι) → I j) → (j : ι) → Fin (n j) :=
      fun α j ↦ if j ∈ X then (α j).2 else σ₀ j
    let siteOp := fun j (a : I j) ↦ single a.1 a.2 (1 : ℂ)
    let coeff := fun i (α : (j : ι) → I j) ↦
      (if i = i₀ then ρ (row α) (col α) else 1) *
        if i ∈ X then 1 else if (α i).1 = (α i).2 then 1 else 0
    refine (productFormOfSiteIndices U n hU I siteOp coeff ?_ ?_
      (Finset.univ.sup fun j ↦ n j * n j) ?_).val
    · intro i α β h
      have hii : α i = β i := h i (hU i)
      by_cases hi : i = i₀
      · subst i
        have hrow : row α = row β := funext fun j ↦ by
          simp only [row]
          split_ifs with hj
          · rw [h j (hX j hj)]
          · rfl
        have hcol : col α = col β := funext fun j ↦ by
          simp only [col]
          split_ifs with hj
          · rw [h j (hX j hj)]
          · rfl
        simp only [coeff, hrow, hcol, hii]
      · simp [coeff, hi, hii]
    · ext u v
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (fun j ↦ (u j, v j))]
      · simp only [siteOp, single_apply_same, Finset.prod_const_one, mul_one, coeff,
          Finset.prod_mul_distrib, Fintype.prod_ite_eq']
        by_cases hoff : ∃ j ∉ X, u j ≠ v j
        · rw [hρ.1 u v hoff]
          obtain ⟨j, hj, huv⟩ := hoff
          refine (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)).symm
          simp [hj, huv]
        · push Not at hoff
          rw [Finset.prod_eq_one fun j _ ↦ ?_, mul_one]
          · exact hρ.2 _ _ _ _ (fun j hj ↦ by simp [row, hj])
              (fun j hj ↦ by simp [col, hj]) hoff (fun j hj ↦ by simp [row, col, hj])
          · by_cases hj : j ∈ X
            · simp [hj]
            · simp [hj, hoff j hj]
      · intro α _ hα
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
        refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
        rw [show siteOp j (α j) = single (α j).1 (α j).2 (1 : ℂ) from rfl, single_apply]
        split_ifs with h
        · exact absurd (Prod.ext h.1 h.2) hj
        · rfl
      · simp
    · intro j
      simpa [I] using Finset.le_sup (f := fun j ↦ n j * n j) (Finset.mem_univ j)
  · have hzero : ρ = 1 := by
      ext x y
      exact (hconfig ⟨x⟩).elim
    rw [hzero]
    exact Classical.choice (hasProductForm_one U n)

/-- Supported operators admit the product forms constructed above. -/
theorem hasProductForm_of_isSupportedOn (U : ι → Set ι) (n : ι → ℕ)
    (hU : ∀ i, i ∈ U i) (X : Finset ι) (i₀ : ι) (hX : ∀ j ∈ X, j ∈ U i₀)
    {ρ : Matrix ((j : ι) → Fin (n j)) ((j : ι) → Fin (n j)) ℂ}
    (hρ : Entropy.IsSupportedOn ρ X) : HasProductForm U n ρ :=
  ⟨productFormOfSupported U n hU X i₀ hX hρ⟩

private noncomputable def localLiftHom (n : ι → ℕ) (X : Finset ι) :
    Matrix (Entropy.RegionConfig n X) (Entropy.RegionConfig n X) ℂ →ₐ[ℂ]
      Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ where
  toFun := Entropy.localLift X
  map_one' := Entropy.localLift_one
  map_mul' := Entropy.localLift_mul
  map_zero' := by simp [Entropy.localLift]
  map_add' := Entropy.localLift_add
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Entropy.localLift_smul, Entropy.localLift_one]

/-- Exponentials of scalar multiples preserve the support of an operator.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061. -/
theorem isSupportedOn_exp_smul (n : ι → ℕ) (X : Finset ι)
    {ρ : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ}
    (hρ : Entropy.IsSupportedOn ρ X) (c : ℂ) :
    Entropy.IsSupportedOn (NormedSpace.exp (c • ρ)) X := by
  classical
  by_cases hconfig : Nonempty (Entropy.SiteConfig n)
  · obtain ⟨K, rfl⟩ := hρ.exists_localLift (Classical.choice hconfig)
    rw [← Entropy.localLift_smul]
    let : NormedAlgebra ℚ (Matrix (Entropy.RegionConfig n X) (Entropy.RegionConfig n X) ℂ) :=
      .restrictScalars ℚ ℂ _
    let f := localLiftHom n X
    change Entropy.IsSupportedOn (NormedSpace.exp (f.toRingHom (c • K))) X
    rw [← NormedSpace.map_exp f.toRingHom f.toLinearMap.continuous_of_finiteDimensional (c • K)]
    exact Entropy.isSupportedOn_localLift _
  · constructor <;> intro σ <;> exact (hconfig ⟨σ⟩).elim

/-- Ordered Trotter products preserve the coefficient neighbourhoods of their
centred supports. Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1077.
At zero steps the product is the identity. No index-component count is asserted. -/
theorem hasProductForm_trotterProduct (U : ι → Set ι) (n : ι → ℕ)
    (hU : ∀ i, i ∈ U i)
    (H : ι → Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ)
    (X : ι → Finset ι) (hX : ∀ i j, j ∈ X i → j ∈ U i)
    (hH : ∀ i, Entropy.IsSupportedOn (H i) (X i))
    (seq : List ι) (β : ℝ) (k : ℕ) :
    HasProductForm U n
      (((seq.map fun i ↦ NormedSpace.exp ((-((β : ℂ) / k)) • H i)).prod) ^ k) := by
  refine HasProductForm.pow (hasProductForm_list_prod _ fun ρ hρ ↦ ?_) k
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hρ
  exact hasProductForm_of_isSupportedOn U n hU (X i) i (hX i)
    (isSupportedOn_exp_smul n (X i) (hH i) _)

end TNLean.Lattice.Locality
