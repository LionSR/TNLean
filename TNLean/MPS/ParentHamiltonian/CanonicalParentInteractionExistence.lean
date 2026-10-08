/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction

/-!
# The positive canonical interaction from exact open kernels

An exact kernel identity for the canonical range-\(R\) open Hamiltonian gives
an explicit positive local interaction with those same open kernels. The
witness is recorded as the canonical projection matrix itself. This equality
retains the literal local support when subsequent gap and state arguments
use the constructed interaction.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `existenceinteraction`,
lines 2195--2230, the orthogonal-complement construction of the interaction.
-/

open scoped ComplexOrder
namespace MPSTensor
variable {d D R : ℕ}

/-- Exact canonical open kernels give a positive interaction equal to the
canonical local projection matrix, with the same kernels at every volume
at least its positive range. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma `existenceinteraction`, lines 2195--2230. -/
theorem exists_positive_canonical_parent_interaction_of_exact_open_kernels
    (A : MPSTensor d D) (hR : 0 < R)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N) :
    ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h = canonicalParentInteractionMatrix A R ∧ h.PosSemidef ∧
      ∀ N, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES A N := by
  refine ⟨canonicalParentInteractionMatrix A R, rfl,
    canonicalParentInteractionMatrix_posSemidef A R, ?_⟩
  intro N hN
  rw [toEuclideanLin_canonicalParentInteractionMatrix,
    openInteractionHamiltonianES_parentInteractionES A hR]
  exact hKernel N hN

end MPSTensor
