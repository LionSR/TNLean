/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Relabel

/-!
# Supported operators under a permutation of sites

Relabelling the sites of a configuration by a permutation `p` carries operators supported on
`S` to operators supported on `p '' S`. This is the case of
`ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators` with one local dimension and the
identity on labels, stated for the `submatrix` form used by cyclic translations of chains.
-/

namespace ManyBody

/-- Relabelling the sites of a configuration by a permutation `p` carries operators supported
on `S` to operators supported on `p '' S`. -/
theorem submatrix_comp_perm_mem_supportedOperators {d : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : Finset ι} (p : Equiv.Perm ι) {A : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ supportedOperators (fun _ ↦ Fin d) S) :
    A.submatrix (fun σ ↦ σ ∘ p) (fun σ ↦ σ ∘ p) ∈ supportedOperators (fun _ ↦ Fin d)
        (S.image p) := by
  have h := reindex_siteConfigurationEquiv_mem_supportedOperators
    (X := fun _ : ι ↦ Fin d) (X' := fun _ : ι ↦ Fin d) p (fun _ ↦ Equiv.refl _)
    (D := S) (D' := S.image p) (fun v ↦ by simp) hA
  have hsymm : ⇑(siteConfigurationEquiv (X := fun _ : ι ↦ Fin d)
      (X' := fun _ : ι ↦ Fin d) p (fun _ ↦ Equiv.refl _)).symm = fun σ ↦ σ ∘ p := by
    funext σ v
    rw [siteConfigurationEquiv_symm_apply]
    rfl
  rwa [Matrix.reindex_apply, hsymm] at h

end ManyBody
