/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Analysis.Entropy

/-!
# Quantum-Markov-chain decomposition data

This module defines the block-diagonal quantum-Markov-chain structure for a
tripartite density matrix, used by the Hayashi strong-subadditivity equality
characterization. It carries no axiom: the structure and its building blocks
(the middle-system unitary lift, the direct-sum reindexings, and the
block-diagonal state) are plain finite-dimensional matrix data.

The forward axiom and the proved reverse direction of the characterization live
in `TNLean.Axioms.Entropy` and `TNLean.Analysis.EntropyMarkovReverse`.

## References

* Hayashi, *Quantum Information: An Introduction*, Springer 2006, Theorem 5.24
* Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246, 359--374 (2004)
* Blueprint `def:hayashi_markov_decomposition`
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

namespace HayashiMarkov

/-- Reindex the `B` subsystem by an explicit direct-sum decomposition
`B ≃ ⨆ j, B_jᴸ × B_jᴿ`, keeping `A` and `C` fixed. -/
def abcEquiv {dA dB dC : ℕ} {m : ℕ} {dL dR : Fin m → ℕ}
    (decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j)) :
    (Fin dA × Fin dB × Fin dC) ≃
      (Fin dA × ((Σ j : Fin m, Fin (dL j) × Fin (dR j)) × Fin dC)) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr decompB (Equiv.refl _))

/-- Reassociate the indices of the dependent block-diagonal state into the
tripartite shape `A × (B × C)`. -/
def sigmaAssoc {dA dC : ℕ} {m : ℕ} (dL dR : Fin m → ℕ) :
    (Σ j : Fin m, (Fin dA × Fin (dL j)) × (Fin (dR j) × Fin dC)) ≃
      (Fin dA × ((Σ j : Fin m, Fin (dL j) × Fin (dR j)) × Fin dC)) :=
  calc
    (Σ j : Fin m, (Fin dA × Fin (dL j)) × (Fin (dR j) × Fin dC)) ≃
        (Σ j : Fin m, Fin dA × ((Fin (dL j) × Fin (dR j)) × Fin dC)) :=
      Equiv.sigmaCongrRight fun j =>
        (Equiv.prodAssoc (Fin dA) (Fin (dL j)) (Fin (dR j) × Fin dC)).trans
          (Equiv.prodCongr (Equiv.refl (Fin dA))
            (Equiv.prodAssoc (Fin (dL j)) (Fin (dR j)) (Fin dC)).symm)
    _ ≃ (Σ j : Fin m, ((Fin (dL j) × Fin (dR j)) × Fin dC) × Fin dA) :=
      Equiv.sigmaCongrRight fun j =>
        Equiv.prodComm (Fin dA) ((Fin (dL j) × Fin (dR j)) × Fin dC)
    _ ≃ (Σ j : Fin m, (Fin (dL j) × Fin (dR j)) × Fin dC) × Fin dA :=
      (Equiv.sigmaProdDistrib
        (fun j : Fin m => (Fin (dL j) × Fin (dR j)) × Fin dC)
        (Fin dA)).symm
    _ ≃ Fin dA × (Σ j : Fin m, (Fin (dL j) × Fin (dR j)) × Fin dC) :=
      Equiv.prodComm _ _
    _ ≃ Fin dA × ((Σ j : Fin m, Fin (dL j) × Fin (dR j)) × Fin dC) :=
      Equiv.prodCongr (Equiv.refl (Fin dA))
        (Equiv.sigmaProdDistrib
          (fun j : Fin m => Fin (dL j) × Fin (dR j)) (Fin dC)).symm

/-- Lift a unitary on the middle subsystem `B` to the tripartite space
`A ⊗ B ⊗ C` as `1_A ⊗ U_B ⊗ 1_C`. -/
def liftB {dA dB dC : ℕ} (U_B : Matrix (Fin dB) (Fin dB) ℂ) :
    Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ :=
  Matrix.kroneckerMap (fun x y : ℂ => x * y)
    (1 : Matrix (Fin dA) (Fin dA) ℂ)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y)
      U_B (1 : Matrix (Fin dC) (Fin dC) ℂ))

/-- The block-diagonal quantum-Markov-chain state
`⊕_j p_j (ρ_{A B_jᴸ} ⊗ ρ_{B_jᴿ C})`, written in the basis adapted to the
`B = ⊕_j B_jᴸ ⊗ B_jᴿ` decomposition. -/
def blockState {dA dC : ℕ} {m : ℕ} (dL dR : Fin m → ℕ)
    (p : Fin m → ℝ)
    (ρ_left : (j : Fin m) →
      Matrix (Fin dA × Fin (dL j)) (Fin dA × Fin (dL j)) ℂ)
    (ρ_right : (j : Fin m) →
      Matrix (Fin (dR j) × Fin dC) (Fin (dR j) × Fin dC) ℂ) :
    Matrix
      (Fin dA × ((Σ j : Fin m, Fin (dL j) × Fin (dR j)) × Fin dC))
      (Fin dA × ((Σ j : Fin m, Fin (dL j) × Fin (dR j)) × Fin dC)) ℂ :=
  Matrix.reindex
    (sigmaAssoc (dA := dA) (dC := dC) dL dR)
    (sigmaAssoc (dA := dA) (dC := dC) dL dR)
    (Matrix.blockDiagonal' fun j : Fin m =>
      (p j : ℂ) • Matrix.kroneckerMap (fun x y : ℂ => x * y)
        (ρ_left j) (ρ_right j))

end HayashiMarkov

/-- Data witnessing the Hayashi / Ruskai / Hayden--Jozsa--Petz--Winter
quantum-Markov-chain structure for a tripartite density matrix.

This structure specifies an explicit finite direct-sum decomposition of the middle
system `B`, an explicit unitary basis change on `B`, probabilities `p_j`, and
left/right density matrices `ρ_{A B_jᴸ}` and `ρ_{B_jᴿ C}` such that after
conjugating `ρ_ABC` by `1_A ⊗ U_B ⊗ 1_C` and reindexing `B` along the chosen
finite decomposition, the state becomes the block-diagonal direct sum
`⊕_j p_j (ρ_{A B_jᴸ} ⊗ ρ_{B_jᴿ C})`.

Source: Hayashi, *Quantum Information: An Introduction*, Springer 2006,
Theorem 5.24;
Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246, 359--374 (2004);
blueprint `def:hayashi_markov_decomposition`. -/
structure HayashiMarkovDecomposition {dA dB dC : ℕ}
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) where
  m : ℕ
  dL : Fin m → ℕ
  dR : Fin m → ℕ
  decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j)
  U_B : Matrix.unitaryGroup (Fin dB) ℂ
  p : Fin m → ℝ
  hp_nonneg : ∀ j : Fin m, 0 ≤ p j
  hp_sum : ∑ j : Fin m, p j = 1
  ρ_left : (j : Fin m) →
    Matrix (Fin dA × Fin (dL j)) (Fin dA × Fin (dL j)) ℂ
  ρ_right : (j : Fin m) →
    Matrix (Fin (dR j) × Fin dC) (Fin (dR j) × Fin dC) ℂ
  hρ_left_dm :
    ∀ j : Fin m, (ρ_left j).PosSemidef ∧ (ρ_left j).trace = 1
  hρ_right_dm :
    ∀ j : Fin m, (ρ_right j).PosSemidef ∧ (ρ_right j).trace = 1
  h_state :
    Matrix.reindex
        (HayashiMarkov.abcEquiv (dA := dA) (dB := dB) (dC := dC)
          (dL := dL) (dR := dR) decompB)
        (HayashiMarkov.abcEquiv (dA := dA) (dB := dB) (dC := dC)
          (dL := dL) (dR := dR) decompB)
        (HayashiMarkov.liftB (dA := dA) (dB := dB) (dC := dC)
          (U_B : Matrix (Fin dB) (Fin dB) ℂ)
          * ρ_ABC *
          (HayashiMarkov.liftB (dA := dA) (dB := dB) (dC := dC)
            (U_B : Matrix (Fin dB) (Fin dB) ℂ))ᴴ)
      = HayashiMarkov.blockState (dA := dA) (dC := dC) dL dR p ρ_left ρ_right
