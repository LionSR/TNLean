/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Entropy.StrongSubadditivity

/-!
# SSA equality and quantum Markov-chain structure

For a tripartite density matrix `ρ_ABC`, equality in strong subadditivity,

`S(ρ_ABC) + S(ρ_B) = S(ρ_AB) + S(ρ_BC)`,

is equivalent to the standard quantum-Markov-chain structure on the middle
subsystem `B`: after a unitary change of basis on `B`, the Hilbert space of
`B` splits as a finite direct sum `⊕_j (B_jᴸ ⊗ B_jᴿ)` and the state is a
block-diagonal direct sum `⊕_j p_j (ρ_{A B_jᴸ} ⊗ ρ_{B_jᴿ C})`.

The proof is supplied by the axiom `_root_.hayashi_ssa_equality_characterization`
in `TNLean/Axioms/Entropy.lean`; this file provides the `Entropy`-namespace
formulations.

## Main declarations

* `Entropy.QuantumMarkovDecomposition` — abbreviation for
  `_root_.HayashiMarkovDecomposition`
* `Entropy.ssaEquality_iff_exists_quantumMarkovDecomposition` — the equivalence
* `Entropy.exists_quantumMarkovDecomposition_of_ssaEquality` — forward direction
* `Entropy.isSSAEquality_of_quantumMarkovDecomposition` — reverse direction

## References

* Hayashi, J. Phys. A: Math. Gen. 37 (2004) L205--L208
* Ruskai, JMP 43, 4358 (2002)
* Hayden, Jozsa, Petz, Winter, Commun. Math. Phys. 246, 359--374 (2004)
* arXiv:1606.00608 Appendix C
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

namespace Entropy

section MarkovChain

variable {dA dB dC : ℕ}

/-- Namespace abbreviation for the quantum-Markov-chain decomposition witness
associated to equality in strong subadditivity. -/
abbrev QuantumMarkovDecomposition
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) : Type :=
  HayashiMarkovDecomposition ρ_ABC

/-- Equality in strong subadditivity is equivalent to the existence of a
quantum-Markov-chain decomposition on the middle subsystem. -/
theorem ssaEquality_iff_exists_quantumMarkovDecomposition
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    IsSSAEquality ρ_ABC hρ_dm.1.isHermitian
      ↔ Nonempty (QuantumMarkovDecomposition ρ_ABC) :=
  _root_.hayashi_ssa_equality_characterization ρ_ABC hρ_dm

/-- Forward direction of the Hayashi SSA-equality characterization: an
SSA-equality state admits a quantum-Markov-chain decomposition. -/
theorem exists_quantumMarkovDecomposition_of_ssaEquality
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hEq : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    Nonempty (QuantumMarkovDecomposition ρ_ABC) :=
  (ssaEquality_iff_exists_quantumMarkovDecomposition ρ_ABC hρ_dm).mp hEq

/-- Reverse direction of the Hayashi SSA-equality characterization: a
quantum-Markov-chain decomposition forces equality in strong subadditivity. -/
theorem isSSAEquality_of_quantumMarkovDecomposition
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hMarkov : Nonempty (QuantumMarkovDecomposition ρ_ABC)) :
    IsSSAEquality ρ_ABC hρ_dm.1.isHermitian :=
  (ssaEquality_iff_exists_quantumMarkovDecomposition ρ_ABC hρ_dm).mpr hMarkov

end MarkovChain

end Entropy
