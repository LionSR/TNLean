/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ControlledZCombinedSymmetry
import TNLean.MPS.Symmetry.MPOSymmetry.ClosedFusion

/-!
# A restricted embedding obstruction for the combined controlled-Z symmetry

The four-site configurations 1100 and 1010 have opposite controlled-Z phases and the
same single-site multiplicities. Any on-site operator gives them the same diagonal
matrix entry. The combined family's actual periodic action is therefore not on-site.
The closed-fusion theorem of arXiv:2203.12563, lines 1211--1213, then excludes every
one-site-injective, exactly closed-fusion family with the same periodic operators.

**Candidate status:** focused strict elaboration only; this continuation is not yet
exported, documented in the Blueprint, reviewed or accepted by complete hosted CI.
The physical SIMPS phase theorem and other types of embeddings remain open.
-/

open scoped BigOperators Matrix
open MPOTensor MPOTensor.GroupFamily

namespace ControlledZGauging

/-- The combined symmetry is not on-site, witnessed at length four by configurations
with the same number of zero and one bits but different nearest-neighbor phases. -/
theorem combinedFamily_not_isOnSite : ¬ combinedFamily.IsOnSite := by
  rintro ⟨u, hu⟩
  let g : Multiplicative (ZMod 2 × ZMod 2) := Multiplicative.ofAdd (0, 1)
  have h₁ := hu g 4 (by decide) ![1, 1, 0, 0] ![1, 1, 0, 0]
  have h₂ := hu g 4 (by decide) ![1, 0, 1, 0] ![1, 0, 1, 0]
  rw [mpo_combinedFamily] at h₁ h₂
  norm_num [Matrix.diagonal_apply, splitLegPhase, czSign,
    zSign, g, Fin.prod_univ_succ] at h₁ h₂
  have hr : u g 1 1 * (u g 1 1 * (u g 0 0 * u g 0 0)) =
      u g 1 1 * (u g 0 0 * (u g 1 1 * u g 0 0)) := by ring
  have hbad := (h₁.trans hr).trans h₂.symm
  norm_num at hbad

/-- No one-site-injective family with exactly the same positive-length periodic operators
can have exact closed fusion. This excludes such embeddings on the original qubits; it
does not exclude embeddings with weaker injectivity or changes of physical realization. -/
theorem no_injective_closed_periodic_embedding
    (F : GroupFamily (Multiplicative (ZMod 2 × ZMod 2)) 2)
    (hinj : ∀ g, Kraus.IsInjective (F.tensor g).toMPSTensor)
    (hphysical : ∀ g N, 0 < N →
      mpo (F.tensor g) N = mpo (combinedFamily.tensor g) N)
    (fd : FusionData F) : ¬ fd.IsClosed := by
  intro hclosed
  have hone : ∀ N, 0 < N → mpo (F.tensor 1) N = 1 := by
    intro N hN
    have : NeZero N := ⟨hN.ne'⟩
    exact (hphysical 1 N hN).trans (mpo_combinedFamily_one N)
  obtain ⟨u, hu⟩ := isOnSite_of_closed_fusion hinj hone hclosed
  apply combinedFamily_not_isOnSite
  exact ⟨u, fun g N hN σ τ ↦
    (congrArg (fun M ↦ M σ τ) (hphysical g N hN)).symm.trans (hu g N hN σ τ)⟩

end ControlledZGauging
