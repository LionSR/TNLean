import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Parent interaction and parent Hamiltonian (definitions)

This file introduces the parent interaction projector, translated local terms,
and the finite-chain parent Hamiltonian.

⚠️ **Warning**: `parentInteraction` and `localTerm` are currently **zero
placeholders**. All downstream results (annihilation, frustration-freeness)
are vacuously true until the real projector/embedding definitions are added.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- **ZERO PLACEHOLDER** — Parent interaction on `L` consecutive sites.

⚠️ This is currently defined as **zero**. The real definition should be the
orthogonal projector onto `groundSpace A L`ᗮ. Any theorem downstream of this
definition (e.g. `parentHamiltonian_annihilates`, `parentHamiltonian_frustrationFree`)
is **vacuously true** until this placeholder is replaced.

TODO(parent-hamiltonian): replace with the orthogonal projector. -/
noncomputable def parentInteraction (_A : MPSTensor d D) (L : ℕ) :
    NSiteSpace d L →ₗ[ℂ] NSiteSpace d L :=
  0

/-- **ZERO PLACEHOLDER** — Translated local term on an `N`-site periodic chain.

⚠️ This is currently defined as **zero**. The real definition should embed
`parentInteraction A L` at site `i` on the periodic chain. Any theorem
downstream of this definition is **vacuously true** until this placeholder
is replaced.

TODO(parent-hamiltonian): replace with the translated embedding. -/
noncomputable def localTerm (_A : MPSTensor d D) (_L N : ℕ) (_i : Fin N) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N :=
  0

/-- Parent Hamiltonian on an `N`-site periodic chain:
sum of translated local interaction terms. -/
noncomputable def parentHamiltonian (A : MPSTensor d D) (L N : ℕ) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N :=
  ∑ i : Fin N, localTerm A L N i

/-- Frustration-freeness for the parent model: every local term annihilates the
candidate state. -/
def IsFrustrationFree (A : MPSTensor d D) (L N : ℕ) (ψ : NSiteSpace d N) : Prop :=
  ∀ i : Fin N, localTerm A L N i ψ = 0

end MPSTensor
