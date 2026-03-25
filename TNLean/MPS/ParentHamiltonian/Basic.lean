import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Basic parent-Hamiltonian properties

Initial API lemmas: the MPV is annihilated by the parent Hamiltonian and the
model is frustration-free on that state.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- PLACEHOLDER: The parent Hamiltonian annihilates the MPV state.

**Warning**: Currently vacuously true because `parentInteraction` and
`localTerm` are zero placeholders. The proof must be rewritten once the
real projector and embedding implementations land. -/
lemma parentHamiltonian_annihilates (A : MPSTensor d D) (L N : ℕ) :
    parentHamiltonian A L N (mpv A) = 0 := by
  simp [parentHamiltonian, localTerm]

/-- PLACEHOLDER: The parent Hamiltonian model is frustration-free on the MPV state.

**Warning**: Currently vacuously true because `localTerm` is a zero
placeholder. The proof must be rewritten once the real embedding
implementation lands. -/
lemma parentHamiltonian_frustrationFree (A : MPSTensor d D) (L N : ℕ) :
    IsFrustrationFree A L N (mpv A) := by
  intro i
  simp [localTerm]

end MPSTensor
