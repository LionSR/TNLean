/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CopyProduct
import TNLean.MPS.AreaLaw.IntervalSlice

/-!
# MPS bond bounds for factors of a block product

A nonzero block factor is recovered, up to a nonzero scalar, by fixing one
configuration in each other block. The interval-slice rank bound therefore
preserves the original MPS bond dimension.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 436–470.
-/

namespace TNLean.MPS.AreaLaw

variable {K L q : ℕ}

/-- Inserting an interval in block coordinates changes exactly one block. -/
private theorem copyConfigurationEquiv_insertInterval
    (σ : Fin K → Fin L → Fin q) (i : Fin K) (x : Fin L → Fin q) :
    copyConfigurationEquiv K L q
      (insertInterval (i.val * L) ((copyConfigurationEquiv K L q).symm σ) x) =
        Function.update σ i x := by
  classical
  funext j k
  change insertInterval (i.val * L) ((copyConfigurationEquiv K L q).symm σ) x
    (finProdFinEquiv (j, k)) = Function.update σ i x j k
  by_cases hji : j = i
  · subst j
    have hm : i.val * L ≤ (finProdFinEquiv (i, k)).val ∧
        (finProdFinEquiv (i, k)).val < i.val * L + L := by
      change i.val * L ≤ k.val + L * i.val ∧ k.val + L * i.val < i.val * L + L
      constructor <;> nlinarith [k.isLt]
    simp only [insertInterval, dite_eq_left hm, Function.update_self]
    apply congrArg x
    apply Fin.ext
    change k.val + L * i.val - i.val * L = k.val
    simp [Nat.mul_comm]
  · have hm : ¬(i.val * L ≤ (finProdFinEquiv (j, k)).val ∧
        (finProdFinEquiv (j, k)).val < i.val * L + L) := by
      change ¬(i.val * L ≤ k.val + L * j.val ∧ k.val + L * j.val < i.val * L + L)
      intro ⟨ha, hb⟩
      have hne : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
      rcases lt_or_gt_of_ne hne with hj | hj
      · nlinarith [Nat.mul_le_mul_right L (show j.val + 1 ≤ i.val from hj), k.isLt]
      · nlinarith [Nat.mul_le_mul_right L (show i.val + 1 ≤ j.val from hj)]
    rw [insertInterval, dite_eq_right hm, Function.update_of_ne hji]
    change σ (finProdFinEquiv.symm (finProdFinEquiv (j, k))).1
      (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2 = σ j k
    rw [finProdFinEquiv.symm_apply_apply]

/-- Fixing all other blocks leaves one block times their coefficient product. -/
private theorem intervalSlice_copyProduct
    (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q))
    (σ : Fin K → Fin L → Fin q) (i : Fin K) (x : Fin L → Fin q) :
    intervalSlice (copyProduct η) (i.val * L) ((copyConfigurationEquiv K L q).symm σ) x =
      (∏ j ∈ Finset.univ.erase i, η j (σ j)) * η i x := by
  classical
  change EuclideanSpace.piTensor η
    (copyConfigurationEquiv K L q
      (insertInterval (i.val * L) ((copyConfigurationEquiv K L q).symm σ) x)) = _
  rw [copyConfigurationEquiv_insertInterval, EuclideanSpace.piTensor_apply]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j ↦ η j (Function.update σ i x j)) (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- Every normalized factor of a product MPS has the same bond bound.
Source: arXiv:0705.0292v2, lines 436–470. No positivity assumption on the bond
bound or local dimension is needed. -/
theorem IsOpenMPS.copyProduct_factor {D : ℕ}
    {η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS (K * L) q D (fun x ↦ copyProduct η x))
    (hη : ∀ i, ‖η i‖ = 1) (i : Fin K) :
    IsOpenMPS L q D (fun x ↦ η i x) := by
  classical
  have hex : ∀ j, ∃ σ, η j σ ≠ 0 := by
    intro j
    exact Function.ne_iff.mp
      ((WithLp.ofLp_eq_zero (x := η j)).not.mpr
        (norm_ne_zero_iff.mp (by rw [hη j]; norm_num)))
  choose σ hσ using hex
  have ha : i.val * L + L ≤ K * L := by
    simpa [Nat.add_mul] using Nat.mul_le_mul_right L i.isLt
  exact hψ.of_intervalSlice_eq_mul (i.val * L) ha
    ((copyConfigurationEquiv K L q).symm σ) (η i)
    (∏ j ∈ Finset.univ.erase i, η j (σ j))
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hσ j)
    (intervalSlice_copyProduct η σ i)

end TNLean.MPS.AreaLaw
