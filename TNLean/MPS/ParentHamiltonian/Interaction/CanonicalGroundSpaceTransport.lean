/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian

/-!
# Canonical interactions determined by their local support

Equal local boundary spaces determine equal canonical interaction matrices
and equal open Hamiltonians. The tensors may have different bond dimensions.
Only the physical support space enters the canonical projection.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `existenceinteraction`,
lines 2195--2230, the orthogonal-complement construction of the interaction.
-/

namespace MPSTensor
variable {d DA DB R : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}

/-- Equal local support spaces give equal canonical interaction matrices,
also for tensors of different bond dimensions. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma `existenceinteraction`, lines 2195--2230. -/
theorem toMatrix'_parentInteraction_eq_of_groundSpaceES_eq
    (h : groundSpaceES A R = groundSpaceES B R) :
    LinearMap.toMatrix' (parentInteraction A R) = LinearMap.toMatrix' (parentInteraction B R) := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_toMatrix'_parentInteraction, toEuclideanLin_toMatrix'_parentInteraction, h]

/-- Equal local support spaces give equal Hamiltonians of the parent interaction on the open
chain at every volume, independently of the bond dimensions. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma `existenceinteraction`, lines 2195--2230. -/
theorem hamiltonian_parentChainInteraction_eq_of_groundSpaceES_eq
    (h : groundSpaceES A R = groundSpaceES B R) (N : ℕ) :
    (parentChainInteraction A R N).hamiltonian = (parentChainInteraction B R N).hamiltonian := by
  have hP : parentInteraction A R = parentInteraction B R := by
    simp only [parentInteraction, h]
  unfold parentChainInteraction
  rw [hP]

end MPSTensor

