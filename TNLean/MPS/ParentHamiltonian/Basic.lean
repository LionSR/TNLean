import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Basic parent-Hamiltonian properties

Initial API lemmas: the MPV is annihilated by the parent Hamiltonian and the
model is frustration-free on that state.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- **PLACEHOLDER — VACUOUSLY TRUE**: The parent Hamiltonian annihilates the MPV state.

This lemma compiles without `sorry` but is currently **vacuously true** because
`parentInteraction` and `localTerm` are zero placeholders (see `Defs.lean`).
The proof is literally `0 = 0` and must be completely rewritten once the real
projector and embedding implementations replace the zero definitions. Do **not**
cite this as a proven result. -/
lemma parentHamiltonian_annihilates (A : MPSTensor d D) (L N : ℕ) :
    parentHamiltonian A L N (mpv A) = 0 := by
  simp [parentHamiltonian, localTerm]

/-- **PLACEHOLDER — VACUOUSLY TRUE**: The parent Hamiltonian model is frustration-free
on the MPV state.

This lemma compiles without `sorry` but is currently **vacuously true** because
`localTerm` is a zero placeholder (see `Defs.lean`). Do **not** cite this as a
proven result. -/
lemma parentHamiltonian_frustrationFree (A : MPSTensor d D) (L N : ℕ) :
    IsFrustrationFree A L N (mpv A) := by
  intro i
  simp [localTerm]

end MPSTensor
