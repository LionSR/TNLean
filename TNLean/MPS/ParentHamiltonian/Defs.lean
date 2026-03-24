import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Parent interaction and parent Hamiltonian (definitions)

This file introduces the parent interaction projector, translated local terms,
and the finite-chain parent Hamiltonian. The current chain-level translation
layer is intentionally lightweight and will be refined in later PRs.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Parent interaction on `L` consecutive sites.

This is currently represented by a linear operator placeholder; in the full
construction this will be refined to the orthogonal projector onto `G_L(A)ᗮ`. -/
noncomputable def parentInteraction (_A : MPSTensor d D) (_L : ℕ) :
    NSiteSpace d L →ₗ[ℂ] NSiteSpace d L :=
  -- TODO(parent-hamiltonian): replace this zero placeholder with the orthogonal
  -- projector onto `groundSpace A L`ᗮ once the geometric construction is added.
  0

/-- Placeholder translated local term on an `N`-site periodic chain.

The geometric embedding of the `L`-site interaction into the full `N`-site
space is introduced in a later installment; for now this is the zero term,
which still gives the expected algebraic API for summing translated terms. -/
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

lemma localTerm_apply (A : MPSTensor d D) (L N : ℕ) (i : Fin N)
    (ψ : NSiteSpace d N) :
    localTerm A L N i ψ = 0 := by
  simp [localTerm]

lemma parentHamiltonian_apply (A : MPSTensor d D) (L N : ℕ)
    (ψ : NSiteSpace d N) :
    parentHamiltonian A L N ψ = 0 := by
  simp [parentHamiltonian, localTerm]

end MPSTensor
