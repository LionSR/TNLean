/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix
import TNLean.MPS.ParentHamiltonian.QuasiLocalParentGroundStateFace

/-!
# The generated state has zero canonical parent energy

The quasi-local state determined by stationary normalized generating data
has zero energy for the canonical projection onto the local boundary-space
complement. This holds for every range, without faithfulness, irreducibility,
primitivity, or purity.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1 and Lemma
`existenceinteraction`, lines 2195--2230.
-/

open SpinChain
open scoped Matrix ComplexOrder BigOperators
namespace MPSTensor
variable {d D : ℕ} [NeZero d]

/-- Stationary normalized generating data define a zero-energy state of the
canonical parent interaction at every range. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.1 and Lemma `existenceinteraction`,
lines 2195--2230. -/
theorem quasiLocalExpectation_mem_parentGroundStateFace_canonicalParentInteraction
    (A : MPSTensor d D) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hFix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0) (R : ℕ) :
    quasiLocalExpectation A hTP hρ hFix htr ∈
      parentGroundStateFace (canonicalParentInteractionMatrix A R) := by
  apply quasiLocalExpectation_mem_parentGroundStateFace_of_groundSpaceES_le_ker
    A hTP hρ hFix htr
  rw [toEuclideanLin_canonicalParentInteractionMatrix]
  exact (isParentInteraction_parentInteractionES A R).ker_eq.ge

end MPSTensor

