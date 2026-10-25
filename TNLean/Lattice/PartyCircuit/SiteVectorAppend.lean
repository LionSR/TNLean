/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.SiteRegisters
import TNLean.Lattice.PartyCircuit.PartyPartition

/-!
# Product basis vectors on concatenated site lists

The basis vector of a concatenated list is the tensor product of the basis
vectors of its two parts, read through the canonical concatenation isometry.
The register list of the second part may be identified by an equality of layouts.
No injectivity of the site list or ownership map is required.

Source: the site-register tensor construction in the polynomial-PEPS manuscript,
`05-frames.tex`, lines 13–20 and Definition 6.1.
-/

noncomputable section

open scoped TensorProduct

namespace TNLean.Lattice.Sheet

open TNLean.Lattice.PartyCircuit

variable {q : ℕ}

/-- A product basis vector on a concatenated site list factors through the
canonical concatenation isometry, with the displayed identifications of its
register lists. Source: the site-register tensor construction in
`05-frames.tex`, lines 13–20 and Definition 6.1. -/
theorem siteVec_append {ι P : Type} (own : ι → P)
    (a b : List ι) (tail : Layout P) (ht : tail = siteRegs q own b)
    (h : siteRegs q own a ++ tail = siteRegs q own (a ++ b)) (c : ι → Fin q) :
    (Layout.memCongr h).symm (siteVec own (a ++ b) c) =
      (appendIso (siteRegs q own a) tail).symm
        (siteVec own a c ⊗ₜ (Layout.memCongr ht).symm (siteVec own b c)) := by
  subst tail
  induction a with
  | nil =>
      change siteVec own b c =
        (appendIso ([] : Layout P) (siteRegs q own b)).symm
          ((1 : ℂ) ⊗ₜ siteVec own b c)
      simpa only [one_smul] using
        (appendIso_nil_symm_tmul (siteRegs q own b) (1 : ℂ) (siteVec own b c)).symm
  | cons x a ih =>
      let h' : siteRegs q own a ++ siteRegs q own b = siteRegs q own (a ++ b) := by
        simp [siteRegs, List.map_append]
      rw [← Layout.memCongr_symm h]
      change Layout.memCongr (congrArg (⟨own x, euc (Fin q)⟩ :: ·) h'.symm)
        (EuclideanSpace.single (c x) (1 : ℂ) ⊗ₜ siteVec own (a ++ b) c) = _
      rw [Layout.memCongr_cons_tmul _ h'.symm, Layout.memCongr_symm h', ih h']
      exact (appendIso_symm_cons_tmul _ _ _ _ _ _).symm

end TNLean.Lattice.Sheet
