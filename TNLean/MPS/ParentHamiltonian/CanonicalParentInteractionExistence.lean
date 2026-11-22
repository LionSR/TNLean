/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
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

open ManyBody.Interaction (chainTranslates) in
/-- Exact kernels of the Hamiltonians of the parent interaction on the open chain give a positive
semidefinite interaction equal to the matrix of the canonical parent interaction, with the same
kernels at every volume at least its range. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma `existenceinteraction`, lines 2195--2230. -/
theorem exists_posSemidef_eq_toMatrix'_parentInteraction_of_ker_hamiltonian_parentChainInteraction
    (A : MPSTensor d D)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
        groundSpaceES A N) :
    ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h = LinearMap.toMatrix' (parentInteraction A R) ∧ h.PosSemidef ∧
      ∀ N, R ≤ N →
        LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
          groundSpaceES A N :=
  ⟨LinearMap.toMatrix' (parentInteraction A R), rfl, posSemidef_toMatrix'_parentInteraction A R,
    hKernel⟩

end MPSTensor
