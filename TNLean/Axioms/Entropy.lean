/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Analysis.Entropy
import TNLean.Analysis.HayashiMarkovStructure
import TNLean.Analysis.EntropyMarkovReverse

/-!
# Axiomatized entropy inequalities and equality characterizations

This module isolates the sanctioned entropy axioms so that the axiom boundary is
clear to downstream files and to CI.

## Status

* Strong subadditivity is **no longer axiomatized**: it is proved as
  `strong_subadditivity_general` in
  `TNLean.Channel.Schwarz.StrongSubadditivityPosDef`, derived from Lieb
  concavity, and applied under the name `Entropy.strongSubadditivity`.
* The Hayashi equality characterization is **split into a proved reverse
  direction and a forward-only axiom**. The reverse implication, that a
  quantum-Markov-chain state attains equality, is proved as
  `hayashi_ssa_equality_characterization_reverse` in
  `TNLean.Analysis.EntropyMarkovReverse`, from the entropy-additivity lemmas in
  `TNLean.Analysis.EntropyDecomposition`. Only the forward implication, that
  equality forces the block-diagonal structure, remains axiomatized as
  `hayashi_ssa_equality_characterization_forward`; the biconditional
  `hayashi_ssa_equality_characterization` combines the two.

## TODO

Remove the remaining axiom `hayashi_ssa_equality_characterization_forward` by
proving the forward implication of the equality case. A faithful formalization
is expected to require:
1. Conditional mutual information and recovery maps (the Petz transpose channel)
2. The saturation analysis of the data-processing inequality for relative
   entropy
3. The reconstruction of the discarded subsystem from a recovery map

## References

* Lieb, Ruskai, "Proof of the strong subadditivity of quantum-mechanical
  entropy", JMP 14, 1938 (1973) — source of SSA
* Hayashi, *Quantum Information: An Introduction*, Springer 2006,
  Theorem 5.24 — SSA equality and quantum Markov structure
* Ruskai, "Inequalities for quantum entropy: A review with conditions for
  equality", JMP 43, 4358 (2002)
* Hayden, Jozsa, Petz, Winter, Commun. Math. Phys. 246, 359--374 (2004)
  (the structural formulation cited as `Hay03` in arXiv:1606.00608 Appendix C)
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8
  (Distance Measures)][Wolf2012QChannels]
* arXiv:1606.00608 Appendix C — downstream target of MPDO entropy input
* Blueprint `ch04b_entropy.tex` (Quantum Entropy chapter): `thm:strong_subadditivity`,
  `def:hayashi_markov_decomposition`, `thm:hayashi_ssa_equality_characterization`
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real
/-! ## Equality characterization of strong subadditivity -/

section SSAEqualityCharacterization

variable {dA dB dC : ℕ}

/-- **Forward direction of the Hayashi / Ruskai / Hayden--Jozsa--Petz--Winter
characterization of strong-subadditivity equality** (sanctioned axiom).

For a tripartite density matrix `ρ_ABC`, equality in strong subadditivity forces
`ρ_ABC` to have quantum-Markov-chain structure on the middle subsystem `B`: after
a unitary change of basis on `B`, the Hilbert space of `B` decomposes as a finite
direct sum `⊕_j (B_jᴸ ⊗ B_jᴿ)` and the state takes block-diagonal form
`⊕_j p_j (ρ_{A B_jᴸ} ⊗ ρ_{B_jᴿ C})`, recorded by the structure
`HayashiMarkovDecomposition ρ_ABC`.

This implication is the deep half of the characterization: its proof needs
recovery-map and Petz-transpose theory, that is, the analysis of when the
data-processing inequality for relative entropy is saturated and the
reconstruction of the discarded subsystem from a recovery map. This machinery is
not yet formalized in Mathlib or in this repository, so the forward direction is
introduced here as a **sanctioned axiom**. The reverse direction is proved in
`TNLean.Analysis.EntropyMarkovReverse` and the biconditional below combines the
two; see `docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`.

Source: Hayashi, *Quantum Information: An Introduction*, Springer 2006,
Theorem 5.24;
Ruskai, JMP 43, 4358 (2002);
Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246, 359--374 (2004);
arXiv:1606.00608 Appendix C;
blueprint `thm:hayashi_ssa_equality_characterization`. -/
axiom hayashi_ssa_equality_characterization_forward
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    IsSSAEquality ρ_ABC hρ_dm.1.isHermitian
      → Nonempty (HayashiMarkovDecomposition ρ_ABC)

/-- **Hayashi / Ruskai / Hayden--Jozsa--Petz--Winter characterization of
strong-subadditivity equality**.

For a tripartite density matrix `ρ_ABC`, equality in strong subadditivity
holds if and only if `ρ_ABC` has quantum-Markov-chain structure on the middle
subsystem `B`: after a unitary change of basis on `B`, the Hilbert space of
`B` decomposes as a finite direct sum `⊕_j (B_jᴸ ⊗ B_jᴿ)` and the state takes
block-diagonal form `⊕_j p_j (ρ_{A B_jᴸ} ⊗ ρ_{B_jᴿ C})`, recorded by the
structure `HayashiMarkovDecomposition ρ_ABC`.

The forward implication is the sanctioned axiom
`hayashi_ssa_equality_characterization_forward`; the reverse implication is the
proved theorem `hayashi_ssa_equality_characterization_reverse` in
`TNLean.Analysis.EntropyMarkovReverse`. This biconditional combines the two, so
its only axiomatic content is the forward direction. Downstream consumers should
import the theorem statement from `TNLean/Entropy/MarkovChain.lean`, not this
axiom module.

Source: Hayashi, *Quantum Information: An Introduction*, Springer 2006,
Theorem 5.24;
Ruskai, JMP 43, 4358 (2002);
Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246, 359--374 (2004);
arXiv:1606.00608 Appendix C;
blueprint `thm:hayashi_ssa_equality_characterization`. -/
theorem hayashi_ssa_equality_characterization
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    IsSSAEquality ρ_ABC hρ_dm.1.isHermitian
      ↔ Nonempty (HayashiMarkovDecomposition ρ_ABC) :=
  ⟨hayashi_ssa_equality_characterization_forward ρ_ABC hρ_dm,
    hayashi_ssa_equality_characterization_reverse ρ_ABC hρ_dm⟩

end SSAEqualityCharacterization
