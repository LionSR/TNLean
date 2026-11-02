/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Basic

/-!
# Numbering the sites of a left block

For a cut after `i ≤ L` sites, the configurations of the left block are the configurations of
a chain of `i` sites. This identification reads vectors and operators on that block in the
coordinates used to define their matrix product state bond dimensions.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Definition `def:viable`,
lines 240–244, and the bond-trimming step, lines 549–559.
-/

namespace TNLean.MPS.AreaLaw

variable {L q i : ℕ}

/-- Configurations of `i` sites and configurations of the left block after those sites.
Source: LVV13, `algo53.tex`, Definition `def:viable`, lines 240–244. -/
def leftConfigOfFinEquiv (hi : i ≤ L) :
    (Fin i → Fin q) ≃ Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) where
  toFun := leftConfigOfFin
  invFun x v := x ⟨⟨v.val, lt_of_lt_of_le v.isLt hi⟩, mem_leftBlock.mpr v.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reading a left-block vector on `Fin i` preserves every internal cut rank.
Source: LVV13, `algo53.tex`, the bond-trimming step, lines 549–559. -/
theorem rank_cutMatrix_leftConfigOfFin (hi : i ≤ L) (u : LeftBlockVector L q i) (j : ℕ) :
    (cutMatrix (WithLp.toLp 2 (fun x ↦ u (leftConfigOfFin x))) j).rank =
      Matrix.schmidtRank (WithLp.ofLp (Entropy.cutVector
        (Finset.univ.filter fun v : {v : Fin L // v ∈ leftBlock L i} ↦ v.1.val < j) u)) := by
  classical
  let D := Finset.univ.filter fun v : {v : Fin L // v ∈ leftBlock L i} ↦ v.1.val < j
  let e : Fin i ≃ {v : Fin L // v ∈ leftBlock L i} :=
    { toFun := fun v ↦ ⟨⟨v.val, lt_of_lt_of_le v.isLt hi⟩, mem_leftBlock.mpr v.isLt⟩
      invFun := fun v ↦ ⟨v.1.val, mem_leftBlock.mp v.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e₁ : {v : Fin i // v ∈ leftBlock i j} ≃
      {v : {v : Fin L // v ∈ leftBlock L i} // v ∈ D} :=
    e.subtypeEquiv (by intro v; simp [D, e])
  let e₂ : {v : Fin i // v ∉ leftBlock i j} ≃
      {v : {v : Fin L // v ∈ leftBlock L i} // v ∉ D} :=
    e.subtypeEquiv (by intro v; simp [D, e])
  have h : cutMatrix (WithLp.toLp 2 (fun x ↦ u (leftConfigOfFin x))) j =
      (Matrix.schmidtCoeffMatrix (WithLp.ofLp (Entropy.cutVector D u))).submatrix
        (e₁.arrowCongr (Equiv.refl (Fin q))) (e₂.arrowCongr (Equiv.refl (Fin q))) := by
    ext a b
    change u (leftConfigOfFin
      ((Entropy.cutEquiv (fun _ : Fin i ↦ q) (leftBlock i j)).symm (a, b))) =
      u ((Entropy.cutEquiv (fun _ : {v : Fin L // v ∈ leftBlock L i} ↦ q) D).symm
        (e₁.arrowCongr (Equiv.refl (Fin q)) a, e₂.arrowCongr (Equiv.refl (Fin q)) b))
    apply congrArg u
    funext v
    by_cases hv : v.1.val < j
    · have hDv : v ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      rw [Entropy.cutEquiv_symm_apply_mem _ _ hDv]
      change ((Entropy.cutEquiv (fun _ : Fin i ↦ q) (leftBlock i j)).symm (a, b))
        ⟨v.1.val, mem_leftBlock.mp v.2⟩ = _
      rw [Entropy.cutEquiv_symm_apply_mem _ _ (show
        (⟨v.1.val, mem_leftBlock.mp v.2⟩ : Fin i) ∈ leftBlock i j from mem_leftBlock.mpr hv)]
      rfl
    · have hDv : v ∉ D := fun h ↦ hv (Finset.mem_filter.mp h).2
      rw [Entropy.cutEquiv_symm_apply_not_mem _ _ hDv]
      change ((Entropy.cutEquiv (fun _ : Fin i ↦ q) (leftBlock i j)).symm (a, b))
        ⟨v.1.val, mem_leftBlock.mp v.2⟩ = _
      rw [Entropy.cutEquiv_symm_apply_not_mem _ _ (show
        (⟨v.1.val, mem_leftBlock.mp v.2⟩ : Fin i) ∉ leftBlock i j from
          fun h ↦ hv ((mem_leftBlock (L := i) (k := j)).mp h))]
      rfl
  rw [h, Matrix.rank_submatrix]
  rfl

end TNLean.MPS.AreaLaw
