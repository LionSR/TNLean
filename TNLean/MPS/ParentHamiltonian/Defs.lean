import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Parent-Hamiltonian definitions (placeholder layer)
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Placeholder parent interaction on `L` sites.

TODO(parent-hamiltonian): replace this zero operator by the orthogonal projector onto
`(groundSpace A L)ᗮ` once the analytic construction is implemented.
TODO(parent-hamiltonian): update downstream lemmas (`localTerm`, `parentHamiltonian`) to use the
nontrivial local interaction and restore any appropriate `[simp]` attributes then.
-/
noncomputable def parentInteraction (A : MPSTensor d D) (L : ℕ) :
    NSiteSpace d L →ₗ[ℂ] NSiteSpace d L := 0

/-- Placeholder translated local term. -/
noncomputable def localTerm (A : MPSTensor d D) (L N i : ℕ) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N := 0

/-- Placeholder parent Hamiltonian. -/
noncomputable def parentHamiltonian (A : MPSTensor d D) (L N : ℕ) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N := 0

lemma localTerm_apply (A : MPSTensor d D) (L N i : ℕ) (ψ : NSiteSpace d N) :
    localTerm (d := d) (D := D) A L N i ψ = 0 := by
  simp [localTerm]

lemma parentHamiltonian_apply (A : MPSTensor d D) (L N : ℕ) (ψ : NSiteSpace d N) :
    parentHamiltonian (d := d) (D := D) A L N ψ = 0 := by
  simp [parentHamiltonian]

/-- Placeholder frustration-free predicate. -/
def IsFrustrationFree (A : MPSTensor d D) (L N : ℕ) (ψ : NSiteSpace d N) : Prop :=
  ∀ i ∈ Finset.range N, localTerm (d := d) (D := D) A L N i ψ = 0

end MPSTensor
