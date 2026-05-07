/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Analysis.Entropy

/-!
# Axiomatized entropy inequalities and equality characterizations

This module isolates the sanctioned entropy axioms so that the axiom boundary is
clear to downstream files and to CI.

## Status

* `strong_subadditivity` is an **axiom** (proof deferred; see TODO below).
* `hayashi_ssa_equality_characterization` is an **axiom** stating the
  standard equality case of strong subadditivity as a quantum-Markov-chain
  decomposition on the middle subsystem.
* A `subadditivity` result can be derived from `strong_subadditivity` by
  specializing `dC = 1`; this is left for downstream modules.

## TODO

Replace `strong_subadditivity` with a proof from Klein's inequality and
Lieb concavity (Lieb–Ruskai 1973). This requires:
1. Quantum relative entropy `D(ρ‖σ) = tr(ρ(log ρ - log σ))`
2. Klein's inequality: `D(ρ‖σ) ≥ 0`
3. Joint convexity of relative entropy
4. Monotonicity of relative entropy under partial trace

Replace `hayashi_ssa_equality_characterization` with a proof of the equality
case of strong subadditivity. A faithful formalization is expected to require:
1. Conditional mutual information and recovery maps
2. A finite-dimensional direct-sum / tensor-factorization theory compatible with
   basis changes on the middle subsystem
3. The equivalence between equality in SSA and the quantum Markov-chain
   structure of the tripartite state

## References

* Lieb, Ruskai, "Proof of the strong subadditivity of quantum-mechanical
  entropy", JMP 14, 1938 (1973) — source of SSA
* Hayashi, J. Phys. A: Math. Gen. 37 (2004) L205--L208 — SSA equality
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
      (Fin dA × ((Σ j : Fin m, Fin (dL j) × Fin (dR j)) × Fin dC)) where
  toFun := fun ⟨j, x⟩ =>
    let a : Fin dA := x.1.1
    let l : Fin (dL j) := x.1.2
    let r : Fin (dR j) := x.2.1
    let c : Fin dC := x.2.2
    (a, (⟨j, (l, r)⟩, c))
  invFun := fun x =>
    let a : Fin dA := x.1
    let j : Fin m := x.2.1.1
    let l : Fin (dL j) := x.2.1.2.1
    let r : Fin (dR j) := x.2.1.2.2
    let c : Fin dC := x.2.2
    ⟨j, ((a, l), (r, c))⟩
  left_inv := by
    rintro ⟨j, ⟨⟨a, l⟩, ⟨r, c⟩⟩⟩
    rfl
  right_inv := by
    rintro ⟨a, ⟨⟨j, ⟨l, r⟩⟩, c⟩⟩
    rfl

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

Source: Hayashi, J. Phys. A: Math. Gen. 37 (2004) L205--L208;
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

/-! ## Strong subadditivity (axiom) -/

section StrongSubadditivity

variable {dA dB dC : ℕ}

/-- **Strong subadditivity** (Lieb–Ruskai 1973).

For a tripartite density matrix `ρ_ABC` on `A ⊗ B ⊗ C`:
  `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`

This is axiomatized; see the module docstring for the deferred proof plan.
Hermiticity of reduced states is derived via `traceA_ABC_isHermitian` etc.
from `hρ_dm.1.isHermitian`.

Source: Lieb, Ruskai, JMP 14, 1938 (1973);
[Wolf, Chapter 8, Section 8.7 (Contractivity and the increase of entropy)][Wolf2012QChannels];
blueprint `thm:strong_subadditivity`. -/
axiom strong_subadditivity
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
      + vonNeumannEntropy (traceAC_ABC ρ_ABC)
          (traceAC_ABC_isHermitian hρ_dm.1.isHermitian)
    ≤ vonNeumannEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
      + vonNeumannEntropy (traceA_ABC ρ_ABC)
          (traceA_ABC_isHermitian hρ_dm.1.isHermitian)

end StrongSubadditivity

/-! ## Equality characterization of strong subadditivity (axiom) -/

section SSAEqualityCharacterization

variable {dA dB dC : ℕ}

/-- **Hayashi / Ruskai / Hayden--Jozsa--Petz--Winter characterization of
strong-subadditivity equality**.

For a tripartite density matrix `ρ_ABC`, equality in strong subadditivity
holds if and only if `ρ_ABC` has quantum-Markov-chain structure on the middle
subsystem `B`: after a unitary change of basis on `B`, the Hilbert space of
`B` decomposes as a finite direct sum `⊕_j (B_jᴸ ⊗ B_jᴿ)` and the state takes
block-diagonal form
`⊕_j p_j (ρ_{A B_jᴸ} ⊗ ρ_{B_jᴿ C})`.

The right-hand side is packaged by the structure
`HayashiMarkovDecomposition ρ_ABC`, which stores the explicit dimensions, the
unitary basis change on `B`, the probabilities `p_j`, the component density
matrices, and the block-diagonal equality.

This result is introduced here as a **sanctioned axiom**: the full proof needs
operator-algebra and recovery-map theory that is not yet formalized in
Mathlib or in this repository. Downstream consumers should import the theorem
statement from `TNLean/Entropy/MarkovChain.lean`, not this axiom module.

Source: Hayashi, J. Phys. A: Math. Gen. 37 (2004) L205--L208;
Ruskai, JMP 43, 4358 (2002);
Hayden--Jozsa--Petz--Winter, Commun. Math. Phys. 246, 359--374 (2004);
arXiv:1606.00608 Appendix C;
blueprint `thm:hayashi_ssa_equality_characterization`. -/
axiom hayashi_ssa_equality_characterization
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    IsSSAEquality ρ_ABC hρ_dm.1.isHermitian
      ↔ Nonempty (HayashiMarkovDecomposition ρ_ABC)

end SSAEqualityCharacterization
