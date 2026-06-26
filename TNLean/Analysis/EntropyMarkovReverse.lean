/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.EntropyDecomposition
import TNLean.Axioms.Entropy

/-!
# Reverse direction of the Hayashi strong-subadditivity equality characterization

This file proves that a quantum-Markov-chain (block-diagonal) state attains
equality in strong subadditivity, the reverse direction of the Hayashi
characterization. The forward direction (equality forces the block-diagonal
structure) remains a sanctioned axiom resting on Petz-recovery theory; see
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`.

## Strategy

A quantum-Markov-chain decomposition `HayashiMarkovDecomposition ρ_ABC` exhibits
`ρ_ABC`, after a unitary basis change on the middle system `B` and a reindexing,
as the block-diagonal direct sum
\(\bigoplus_j p_j (\rho_{A B_j^L} \otimes \rho_{B_j^R C})\). The four reduced
states and their entropies decompose through the additivity lemmas in
`TNLean.Analysis.EntropyDecomposition`, and the four entropy terms of strong
subadditivity cancel.

## References

* Hayashi, *Quantum Information: An Introduction*, Springer 2006, Theorem 5.24
* `docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`
-/

open scoped Matrix Kronecker ComplexOrder
open Matrix Finset Real

namespace HayashiMarkov

variable {dA dC : ℕ} {m : ℕ} {dL dR : Fin m → ℕ}

/-- Entrywise value of the block-diagonal quantum-Markov-chain state. The entry
between two indices vanishes unless their block labels agree, in which case it is
the weight times the product of the left and right component entries. -/
theorem blockState_apply (p : Fin m → ℝ)
    (ρ_left : (j : Fin m) → Matrix (Fin dA × Fin (dL j)) (Fin dA × Fin (dL j)) ℂ)
    (ρ_right : (j : Fin m) → Matrix (Fin (dR j) × Fin dC) (Fin (dR j) × Fin dC) ℂ)
    (a a' : Fin dA) (c c' : Fin dC)
    (j j' : Fin m) (lr : Fin (dL j) × Fin (dR j)) (lr' : Fin (dL j') × Fin (dR j')) :
    blockState (dA := dA) (dC := dC) dL dR p ρ_left ρ_right
        (a, (⟨j, lr⟩, c)) (a', (⟨j', lr'⟩, c'))
      = if h : j = j' then
          (p j : ℂ) * ρ_left j (a, lr.1) (a', h ▸ lr'.1)
            * ρ_right j (lr.2, c) (h ▸ lr'.2, c')
        else 0 := by
  classical
  rw [blockState]
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hidx1 : (sigmaAssoc (dA := dA) (dC := dC) dL dR).symm (a, (⟨j, lr⟩, c))
      = (⟨j, ((a, lr.1), (lr.2, c))⟩ :
        Σ j : Fin m, (Fin dA × Fin (dL j)) × (Fin (dR j) × Fin dC)) := rfl
  have hidx2 : (sigmaAssoc (dA := dA) (dC := dC) dL dR).symm (a', (⟨j', lr'⟩, c'))
      = (⟨j', ((a', lr'.1), (lr'.2, c'))⟩ :
        Σ j : Fin m, (Fin dA × Fin (dL j)) × (Fin (dR j) × Fin dC)) := rfl
  rw [hidx1, hidx2]
  by_cases h : j = j'
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq, dif_pos rfl]
    simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
    ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, dif_neg h]

end HayashiMarkov
