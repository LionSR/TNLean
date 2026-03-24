import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Basic parent-Hamiltonian properties

Initial API lemmas: the MPV is annihilated by the parent Hamiltonian and the
model is frustration-free on that state.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- The parent Hamiltonian annihilates the MPV state (current lightweight
chain embedding model). -/
lemma parentHamiltonian_annihilates (A : MPSTensor d D) (L N : ℕ) :
    parentHamiltonian A L N (mpv A) = 0 := by
  simpa using parentHamiltonian_apply (A := A) (L := L) (N := N) (ψ := mpv A)

/-- The parent Hamiltonian model is frustration-free on the MPV state. -/
lemma parentHamiltonian_frustrationFree (A : MPSTensor d D) (L N : ℕ) :
    IsFrustrationFree A L N (mpv A) := by
  intro i
  simpa using localTerm_apply (A := A) (L := L) (N := N) (i := i) (ψ := mpv A)

end MPSTensor
