/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.OperatorRightContraction
import QICLean.Entropy.ThreeWayCut
import QICLean.Algebra.OperatorSchmidtReindex

/-!
# Right contractions of regional operators

Contracting the exterior of a region does not increase operator-Schmidt rank across
any smaller region. The proof uses the actual three-way cut coordinates and arbitrary
linear functionals, rather than an assumed product representation of the output.

Supporting algebra for Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
Claim `c:errorreduction`, lines 584--591. The generic regional statement belongs
upstream in QICLean.
-/

open Matrix

namespace Entropy

variable {V : Type*} [Finite V] [DecidableEq V] {n : V → ℕ} {A B : Finset V}

private def outsideSplitEquiv (hAB : A ⊆ B) :
    ((v : {v : V // v ∉ A}) → Fin (n v)) ≃
      ((v : {v : V // v ∈ B \ A}) → Fin (n v)) × ((v : {v : V // v ∉ B}) → Fin (n v)) where
  toFun z := (fun v ↦ z ⟨v, (Finset.mem_sdiff.mp v.2).2⟩,
    fun v ↦ z ⟨v, fun h ↦ v.2 (hAB h)⟩)
  invFun p v := if hv : v.1 ∈ B then p.1 ⟨v, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩
    else p.2 ⟨v, hv⟩
  left_inv z := by
    funext v
    by_cases hv : v.1 ∈ B <;> simp [hv]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext v
      simp [(Finset.mem_sdiff.mp v.2).1]
    · funext v
      simp [v.2]

/-- Contracting the exterior of `B` preserves the rank bound across `A ⊆ B`.
Supporting algebra for LVV13, `algo53.tex`, Claim `c:errorreduction`, line 591. -/
theorem operatorSchmidtRank_rightContraction_subset_le (hAB : A ⊆ B)
    (K : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (φ : Matrix ((v : {v : V // v ∉ B}) → Fin (n v))
      ((v : {v : V // v ∉ B}) → Fin (n v)) ℂ →ₗ[ℂ] ℂ) :
    operatorSchmidtRank
      ((operatorRightContraction φ (cutOperator B K)).reindex
        (subsetSplitEquiv n hAB) (subsetSplitEquiv n hAB)) ≤
      operatorSchmidtRank (cutOperator A K) := by
  classical
  let := Fintype.ofFinite V
  let e := threeCutEquiv n hAB
  let ρ := K.reindex e e
  have hcontract : (operatorRightContraction φ (cutOperator B K)).reindex
      (subsetSplitEquiv n hAB) (subsetSplitEquiv n hAB) =
      operatorRightContraction φ ρ := by
    ext x y
    apply congrArg φ
    ext z z'
    change K ((cutEquiv n B).symm ((subsetSplitEquiv n hAB).symm x, z))
      ((cutEquiv n B).symm ((subsetSplitEquiv n hAB).symm y, z')) =
      K ((threeCutEquiv n hAB).symm (x, z)) ((threeCutEquiv n hAB).symm (y, z'))
    rw [threeCutEquiv_eq_trans]
    rfl
  have hcoords : e.trans (Equiv.prodAssoc _ _ _) =
      (cutEquiv n A).trans ((Equiv.refl _).prodCongr (outsideSplitEquiv hAB)) := by
    ext σ <;> rfl
  rw [hcontract]
  refine (operatorSchmidtRank_operatorRightContraction_le φ ρ).trans_eq ?_
  change operatorSchmidtRank
    (K.reindex (e.trans (Equiv.prodAssoc _ _ _)) (e.trans (Equiv.prodAssoc _ _ _))) = _
  rw [hcoords]
  exact operatorSchmidtRank_reindex_prodCongr (cutOperator A K)
    (Equiv.refl _) (outsideSplitEquiv hAB)

end Entropy
