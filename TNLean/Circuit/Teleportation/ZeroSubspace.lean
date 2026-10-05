/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Teleportation.Hop

/-!
# The linear subspace with zero scratch registers

Requiring selected physical sites to carry the basis vector `|0⟩` defines a linear subspace.
This permits input-independent branch statements for coherent teleportation protocols.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
-/

namespace QuantumCircuit

variable {d : ℕ} [NeZero d] {ι : Type*}

/-- The subspace of states with basis label zero at every site of `S`. -/
def zeroOnSubmodule (S : Set ι) : Submodule ℂ ((ι → Fin d) → ℂ) where
  carrier := {v | IsZeroOn S v}
  zero_mem' := fun _ hx => (hx rfl).elim
  add_mem' := by
    intro u v hu hv x hx i hi
    by_cases hux : u x = 0
    · exact hv x (fun hvx => hx (by simp [hux, hvx])) i hi
    · exact hu x hux i hi
  smul_mem' := fun c v hv => hv.smul c

@[simp] theorem mem_zeroOnSubmodule {S : Set ι} {v : (ι → Fin d) → ℂ} :
    v ∈ zeroOnSubmodule S ↔ IsZeroOn S v := Iff.rfl

end QuantumCircuit
