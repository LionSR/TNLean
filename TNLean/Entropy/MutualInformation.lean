/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Entropy.StrongSubadditivity

/-!
# Quantum mutual information

The quantum mutual information of a bipartite density matrix is
`I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)`. It measures the total
correlations (classical + quantum) between the two subsystems.

This module provides the `Entropy.mutualInformation` wrapper and a
small collection of algebraic corollaries that follow from the
axiomatized `Entropy.strongSubadditivity`. Together with
`Entropy.VonNeumann` and `Entropy.StrongSubadditivity`, it forms the
bootstrap entropy surface used by the Simple MPDO RFP track
(see issue #613, #236, #239).

## Main declarations

* `Entropy.mutualInformation` — the bipartite mutual information
  `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)`.
* `Entropy.mutualInformation_def` — unfolding lemma expressing the
  mutual information as marginal entropies minus the joint entropy.
* `Entropy.mutualInformation_ssa_trivial_B_nonneg` — the nonnegativity
  of the tripartite mutual information in the trivial-middle form
  (a direct consequence of `subadditivity_ssa_trivial_B`).

Downstream: the Simple MPDO RFP track uses these declarations via
`TNLean.Entropy` to state the MPDO monotonicity of `I_L` from Prop 4.5
of arXiv:1606.00608.

## References

* arXiv:1606.00608 §4.4 (Prop 4.5)
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

namespace Entropy

/-! ## Mutual information -/

section MutualInformation

variable {dA dB : ℕ}

/-- **Quantum mutual information** between subsystems A and B.

`I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)`

Measures the total correlations (classical + quantum) between A and B.
Hermiticity of the reduced states `ρ_A = traceRight ρ_AB` and
`ρ_B = traceLeft ρ_AB` is derived from `hρ_AB` via the partial-trace
preservation lemmas in `TNLean.Analysis.Entropy`.

This is a thin wrapper around `_root_.mutualInformation`. -/
noncomputable def mutualInformation
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.IsHermitian) : ℝ :=
  _root_.mutualInformation ρ_AB hρ_AB

/-- Unfolding lemma relating the namespaced wrapper to the underlying
definition in `TNLean.Analysis.Entropy`. -/
@[simp] theorem mutualInformation_eq
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.IsHermitian) :
    mutualInformation ρ_AB hρ_AB = _root_.mutualInformation ρ_AB hρ_AB := rfl

/-- Explicit formula for the mutual information as the sum of the
marginal entropies minus the joint entropy. -/
theorem mutualInformation_def
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.IsHermitian) :
    mutualInformation ρ_AB hρ_AB
      = _root_.vonNeumannEntropy (Matrix.traceRight ρ_AB)
          (Matrix.traceRight_isHermitian hρ_AB)
        + _root_.vonNeumannEntropy (Matrix.traceLeft ρ_AB)
            (Matrix.traceLeft_isHermitian hρ_AB)
        - _root_.vonNeumannEntropy ρ_AB hρ_AB := rfl

end MutualInformation

/-! ## Nonnegativity via subadditivity (trivial-middle form)

When a bipartite state on `A ⊗ C` is embedded in a trivial-middle
tripartite state on `A ⊗ 1 ⊗ C`, subadditivity (Theorem
`subadditivity_ssa_trivial_B`) immediately gives nonnegativity of the
tripartite mutual information `I(A:C) = S(ρ_A) + S(ρ_C) − S(ρ_AC)`.

We state this corollary in the same tripartite form used by
`subadditivity_ssa_trivial_B` to avoid any reshuffling of indices; it
is the version directly consumed by MPDO RFP applications. -/

section Nonnegativity

variable {dA dC : ℕ}

/-- Mutual information is nonneg in the tripartite trivial-middle
form: `S(ρ_AB) + S(ρ_BC) − S(ρ_ABC) ≥ 0`. Direct corollary of
`subadditivity_ssa_trivial_B`. -/
theorem mutualInformation_ssa_trivial_B_nonneg
    (ρ_ABC : Matrix (Fin dA × Fin 1 × Fin dC)
      (Fin dA × Fin 1 × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (h_mid_trace : (traceAC_ABC ρ_ABC).trace = 1) :
    0 ≤ _root_.vonNeumannEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
        + _root_.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian)
        - _root_.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian := by
  have h := subadditivity_ssa_trivial_B ρ_ABC hρ_dm h_mid_trace
  linarith

end Nonnegativity

end Entropy
