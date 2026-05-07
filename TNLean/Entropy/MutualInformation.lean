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

This module exposes the bipartite mutual information of
`TNLean.Analysis.Entropy` under the `Entropy` namespace via a
Mathlib-style `alias` (rather than a `noncomputable def` wrapper), and
adds a small algebraic corollary that follows from the sanctioned
`Entropy.strongSubadditivity` wrapper. Together with
`Entropy.VonNeumann` and `Entropy.StrongSubadditivity`, it forms the
entropy namespace used by the Simple MPDO RFP track
(see issue #613, #236, #239).

## Main declarations

* `Entropy.mutualInformation` — alias of `_root_.mutualInformation`,
  the bipartite mutual information
  `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)`.
* `Entropy.mutualInformation_ssa_trivial_B_nonneg` — the nonnegativity
  of the tripartite mutual information in the trivial-middle form,
  derived from `subadditivity_ssa_trivial_B` with no extra reduced-trace
  hypothesis.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8][Wolf2012QChannels]
* arXiv:1606.00608 Section 4.4 (Proposition 4.5)
* Blueprint `def:entropy_mutual_information`, `thm:mutual_information_nonneg`
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

namespace Entropy

/-- **Quantum mutual information** between subsystems A and B,
namespaced alias.

`I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)` measures the total correlations
between A and B. Definitionally equal to `_root_.mutualInformation`.

Source: blueprint `def:entropy_mutual_information`. -/
noncomputable alias mutualInformation := _root_.mutualInformation

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
`subadditivity_ssa_trivial_B`.

Source: blueprint `thm:mutual_information_nonneg`. -/
theorem mutualInformation_ssa_trivial_B_nonneg
    (ρ_ABC : Matrix (Fin dA × Fin 1 × Fin dC)
      (Fin dA × Fin 1 × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    0 ≤ Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
        + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian)
        - Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian := by
  have h := subadditivity_ssa_trivial_B ρ_ABC hρ_dm
  linarith

end Nonnegativity

end Entropy
