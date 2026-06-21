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
Mathlib-style `alias` (rather than a restated `noncomputable def`), adds
the trivial-middle nonnegativity corollary, and provides two downstream
consequences used by the MPDO / RFP track (issues #236, #239, #785):

* a **monotonicity** inequality under enlargement of a subsystem
  (`mutualInformation_monotone_tripartite`), which is the SSA-level
  inequality underlying the MPDO `I_L ≤ I_{L+1}` monotonicity
  (arXiv:1606.00608 Prop C.1);
* an **elementary area-law bound**
  `I(A:B) ≤ log d_A + log d_B`
  (`mutualInformation_le_log_dim_add_log_dim`), which is the entropy
  bound underlying the "`I_L ≤ 4 log D`" MPDO area-law estimate once one
  specializes to MPDO bond-dimension hypotheses.

Together with `Entropy.VonNeumann` and `Entropy.StrongSubadditivity`, it
forms the entropy namespace used by the Simple MPDO RFP track
(see issue #613, #236, #239, #785).

## Main declarations

* `Entropy.mutualInformation` — alias of `_root_.mutualInformation`,
  the bipartite mutual information
  `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)`.
* `Entropy.mutualInformation_ssa_trivial_B_nonneg` — the nonnegativity
  of the tripartite mutual information in the trivial-middle form,
  derived from `subadditivity_ssa_trivial_B` with no extra reduced-trace
  hypothesis.
* `Entropy.vonNeumannEntropy_nonneg_of_posSemidef_trace_one` — a
  nonnegativity lemma for the von Neumann entropy of a PSD+trace-1
  Hermitian matrix over an arbitrary finite index set; reused by the
  area-law bound for bipartite `Fin dA × Fin dB` indices.
* `Entropy.mutualInformation_monotone_tripartite` — mutual information
  is monotone under enlargement of a subsystem, in the tripartite form
  `I(A:B) ≤ I(A:BC)` directly used by the MPDO area-law argument.
* `Entropy.mutualInformation_le_log_dim_add_log_dim` — elementary
  area-law bound `I(A:B) ≤ log d_A + log d_B` for bipartite density
  matrices with density-matrix reduced states.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8][Wolf2012QChannels]
* arXiv:1606.00608 §4.4 (Prop 4.5) and Appendix C (Prop C.1)
* Blueprint `def:entropy_mutual_information`, `thm:mutual_information_nonneg`,
  `thm:mutual_information_monotone_tripartite`, and
  `thm:mutual_information_le_log_dim_add_log_dim`
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

/-! ## Entropy nonnegativity for finite index sets

The `Fin D`-restricted `_root_.vonNeumannEntropy_nonneg` does not directly
apply to bipartite density matrices indexed by `Fin dA × Fin dB`. The
following version records the same assertion for an arbitrary finite index set. -/

section FiniteIndexEntropyNonneg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Nonnegativity of the von Neumann entropy for a PSD+trace-1
Hermitian matrix. Mirrors `_root_.vonNeumannEntropy_nonneg` without the
`Fin D`-index restriction. -/
alias vonNeumannEntropy_nonneg_of_posSemidef_trace_one :=
  _root_.vonNeumannEntropy_nonneg_of_posSemidef_trace_one

end FiniteIndexEntropyNonneg

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

/-! ## Monotonicity under enlargement of a subsystem

The MPDO mutual-information monotonicity `I_L ≤ I_{L+1}`
(arXiv:1606.00608 Prop C.1) decomposes into two steps: an SSA-level
monotonicity `I(A:B) ≤ I(A:BC)` on a tripartite state, and a
translation-invariance step identifying contiguous-block entropies.
The SSA-level step is the entropy-theoretic content formalised here;
the translation-invariance step belongs to the downstream MPDO module. -/

section Monotonicity

variable {dA dB dC : ℕ}

/-- The bipartite `B` reduced state matches the tripartite `B` reduced
state: for any `ρ_ABC` on `A ⊗ B ⊗ C`,
`tr_A (tr_C ρ_ABC) = tr_{AC} ρ_ABC` as matrices on `Fin dB`. -/
private theorem traceLeft_traceC_ABC_eq_traceAC_ABC
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) :
    Matrix.traceLeft (traceC_ABC (dA := dA) (dB := dB) (dC := dC) ρ_ABC)
      = traceAC_ABC ρ_ABC := by
  ext b₁ b₂
  simp only [Matrix.traceLeft_apply, traceC_ABC, traceAC_ABC]

/-- **Mutual information is monotone under enlargement of a subsystem**
(tripartite form). For a tripartite density matrix `ρ_ABC` on
`A ⊗ B ⊗ C`:

`I(A:B)` evaluated on the reduced state `ρ_AB = tr_C(ρ_ABC)` is bounded
above by `I(A:BC)` evaluated on the full state `ρ_ABC` viewed bipartitely
as `A ⊗ (B ⊗ C)`:

  `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)
         ≤ S(ρ_A) + S(ρ_BC) − S(ρ_ABC) = I(A:BC)`.

After cancelling `S(ρ_A)` on both sides, the inequality reduces to
strong subadditivity
`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)` (Lieb–Ruskai 1973).

The right-hand side uses the tripartite partial traces:
`ρ_BC = tr_A(ρ_ABC)` (`traceA_ABC`). The left-hand side uses the bipartite
mutual information of the reduced `ρ_AB = tr_C(ρ_ABC)` (`traceC_ABC`).

This is the SSA-level monotonicity consumed by the MPDO area-law
argument (arXiv:1606.00608 Prop C.1); translation invariance lifts it
to the `I_L ≤ I_{L+1}` statement on contiguous-block mutual information. -/
theorem mutualInformation_monotone_tripartite
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    Entropy.mutualInformation (traceC_ABC ρ_ABC)
        (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
      ≤ Entropy.vonNeumannEntropy
            (Matrix.traceRight (traceC_ABC ρ_ABC))
            (Matrix.traceRight_isHermitian
              (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian)
        - Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian := by
  have h_SSA :
      Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
        + Entropy.vonNeumannEntropy (traceAC_ABC ρ_ABC)
            (traceAC_ABC_isHermitian hρ_dm.1.isHermitian)
      ≤ Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
            (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
        + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian) :=
    Entropy.strongSubadditivity ρ_ABC hρ_dm
  have h_rhoB_eq :=
    traceLeft_traceC_ABC_eq_traceAC_ABC (dA := dA) (dB := dB) (dC := dC) ρ_ABC
  have h_rhoB_entropy :
      Entropy.vonNeumannEntropy
          (Matrix.traceLeft (traceC_ABC ρ_ABC))
          (Matrix.traceLeft_isHermitian
            (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        = Entropy.vonNeumannEntropy (traceAC_ABC ρ_ABC)
            (traceAC_ABC_isHermitian hρ_dm.1.isHermitian) := by
    cases h_rhoB_eq
    rfl
  change Entropy.vonNeumannEntropy
          (Matrix.traceRight (traceC_ABC ρ_ABC))
          (Matrix.traceRight_isHermitian
            (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        + Entropy.vonNeumannEntropy
            (Matrix.traceLeft (traceC_ABC ρ_ABC))
            (Matrix.traceLeft_isHermitian
              (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        - Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
            (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
      ≤ Entropy.vonNeumannEntropy
            (Matrix.traceRight (traceC_ABC ρ_ABC))
            (Matrix.traceRight_isHermitian
              (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian)
        - Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
  rw [h_rhoB_entropy]
  linarith

end Monotonicity

/-! ## Elementary area-law bound on mutual information

Combining the single-system entropy bound `S(ρ) ≤ log D` with
nonnegativity of the joint entropy gives the elementary area-law bound
`I(A:B) ≤ log d_A + log d_B` for any bipartite density matrix whose
reduced states are density matrices. This is the entropy bound underlying
the MPDO area-law bound `I_L ≤ 4 log D` (arXiv:1606.00608 line 1319 and
references therein), prior to the MPS/MPDO-specific
bond-dimension refinement. -/

section AreaLaw

variable {dA dB : ℕ}

/-- **Elementary area-law bound on mutual information**. For a bipartite
density matrix `ρ_AB` on `Fin d_A × Fin d_B` with `0 < d_A`, `0 < d_B`
and whose reduced states are density matrices, the quantum mutual
information satisfies

  `I(A:B) ≤ log d_A + log d_B`.

The reduced states are density matrices because partial trace preserves
positive semidefiniteness and trace. Then `S(ρ_A) ≤ log d_A` and
`S(ρ_B) ≤ log d_B` by
`vonNeumannEntropy_le_log_dim`, and `S(ρ_AB) ≥ 0` by
`vonNeumannEntropy_nonneg_of_posSemidef_trace_one`.

This is the entropy-level bound underlying the MPDO area-law bound
`I_L ≤ 4 log D` (arXiv:1606.00608 line 1319); the MPS/MPDO-specific
bond-dimension refinement specialises this bound by taking `d_A = d_B`
to be controlled by the bond dimension via the MPDO representation. -/
theorem mutualInformation_le_log_dim_add_log_dim
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.PosSemidef ∧ ρ_AB.trace = 1)
    (hdA : 0 < dA) (hdB : 0 < dB) :
    Entropy.mutualInformation ρ_AB hρ_AB.1.isHermitian
      ≤ Real.log dA + Real.log dB := by
  have h_A_dm : Matrix.traceRight ρ_AB ∈ densityMatrices dA := by
    exact ⟨hρ_AB.1.traceRight, by
      rw [Matrix.traceRight, Matrix.trace_partialTraceRight]
      exact hρ_AB.2⟩
  have h_B_dm : Matrix.traceLeft ρ_AB ∈ densityMatrices dB := by
    exact ⟨hρ_AB.1.traceLeft, by
      rw [← Matrix.trace_eq_trace_traceLeft ρ_AB]
      exact hρ_AB.2⟩
  have hSA : Entropy.vonNeumannEntropy (Matrix.traceRight ρ_AB)
      (Matrix.traceRight_isHermitian hρ_AB.1.isHermitian)
        ≤ Real.log dA :=
    Entropy.vonNeumannEntropy_le_log_dim h_A_dm hdA
  have hSB : Entropy.vonNeumannEntropy (Matrix.traceLeft ρ_AB)
      (Matrix.traceLeft_isHermitian hρ_AB.1.isHermitian)
        ≤ Real.log dB :=
    Entropy.vonNeumannEntropy_le_log_dim h_B_dm hdB
  have hSAB : 0 ≤ Entropy.vonNeumannEntropy ρ_AB hρ_AB.1.isHermitian :=
    vonNeumannEntropy_nonneg_of_posSemidef_trace_one hρ_AB.1 hρ_AB.2
  change Entropy.vonNeumannEntropy (Matrix.traceRight ρ_AB)
            (Matrix.traceRight_isHermitian hρ_AB.1.isHermitian)
        + Entropy.vonNeumannEntropy (Matrix.traceLeft ρ_AB)
            (Matrix.traceLeft_isHermitian hρ_AB.1.isHermitian)
        - Entropy.vonNeumannEntropy ρ_AB hρ_AB.1.isHermitian
      ≤ Real.log dA + Real.log dB
  linarith

end AreaLaw

end Entropy
