/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction

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
theorem canonicalParentInteractionMatrix_eq_of_groundSpaceES_eq
    (h : groundSpaceES A R = groundSpaceES B R) :
    canonicalParentInteractionMatrix A R = canonicalParentInteractionMatrix B R := by
  simp only [canonicalParentInteractionMatrix, h]

/-- Equal local support spaces give equal canonical open Hamiltonians at every
volume, independently of the bond dimensions. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma `existenceinteraction`, lines 2195--2230. -/
theorem openParentHamiltonianES_eq_of_groundSpaceES_eq
    (hR : 0 < R) (h : groundSpaceES A R = groundSpaceES B R) (N : ℕ) :
    openParentHamiltonianES A R N = openParentHamiltonianES B R N := by
  rw [← openInteractionHamiltonianES_parentInteractionES A hR,
    ← openInteractionHamiltonianES_parentInteractionES B hR,
    ← toEuclideanLin_canonicalParentInteractionMatrix,
    ← toEuclideanLin_canonicalParentInteractionMatrix,
    canonicalParentInteractionMatrix_eq_of_groundSpaceES_eq h]

end MPSTensor

