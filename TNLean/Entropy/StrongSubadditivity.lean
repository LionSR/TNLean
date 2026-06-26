/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.StrongSubadditivityPosDef
import TNLean.Entropy.TripartiteTrace
import TNLean.Entropy.VonNeumann

/-!
# Strong subadditivity (theorem formulation and basic corollaries)

This module states **strong subadditivity** (SSA) of the von Neumann
entropy as a theorem inside the `Entropy` namespace, following the
roadmap of issue #613 for the Simple MPDO RFP track (issue #236,
umbrella #239).

SSA is the statement that for any tripartite density matrix
`ρ_ABC` on `A ⊗ B ⊗ C`,
`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.
This is a deep theorem of Lieb–Ruskai (1973). The full Lean proof is
supplied by `strong_subadditivity_general` in
`TNLean.Channel.Schwarz.StrongSubadditivityPosDef`, derived from Lieb
concavity; the theorem `Entropy.strongSubadditivity` stated here
applies that result, so the inequality is available in the
`Entropy` namespace under the name used by the downstream entropy
results.

## Main declarations

* `Entropy.strongSubadditivity` — **theorem** (not an axiom).
  Forwards to `strong_subadditivity_general` from
  `TNLean/Channel/Schwarz/StrongSubadditivityPosDef.lean`.
* `Entropy.vonNeumannEntropy_eq_zero_of_fin_one` — a 1×1 Hermitian
  matrix with trace 1 has vanishing entropy; proved from Mathlib via
  `Real.negMulLog_one`.
* `Entropy.strongSubadditivity_rearranged` — the algebraic
  rearrangement `S(ρ_ABC) − S(ρ_AB) ≤ S(ρ_BC) − S(ρ_B)` (the
  conditional-entropy form), proved from SSA alone.
* `Entropy.subadditivity_ssa_trivial_B` — subadditivity
  `S(ρ_ABC) ≤ S(ρ_AB) + S(ρ_BC)` in the tripartite form with
  trivial middle subsystem (`dB = 1`). The middle factor contributes
  zero entropy, and `Matrix.trace_eq_trace_traceAC_ABC` supplies the
  trace-one hypothesis for the reduced middle state.

## Provenance

Strong subadditivity is no longer axiomatized. The underlying inequality
is `strong_subadditivity_general` (in
`TNLean.Channel.Schwarz.StrongSubadditivityPosDef`), proved from Lieb
concavity along the relative-entropy route:
1. `Entropy.quantumRelativeEntropy`, the trace-log relative entropy
   `D(ρ‖σ) = Re tr(ρ(log ρ − log σ))`.
2. Klein's inequality: `D(ρ‖σ) ≥ 0` for density matrices.
3. Lieb's joint concavity of `(A, B) ↦ tr(Kᴴ Aᵗ K B^{1-t})`.
4. Monotonicity of the relative entropy under partial trace
   (the "data-processing inequality").

See Lieb–Ruskai, JMP 14, 1938 (1973) and the modern
operator-concavity proof in Ruskai, "Inequalities for quantum entropy:
A review with conditions for equality", JMP 43, 4358 (2002).

## References

* Lieb, Ruskai, "Proof of the strong subadditivity of quantum-mechanical
  entropy", JMP 14, 1938 (1973) — source of SSA
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8][Wolf2012QChannels]
* arXiv:1606.00608 Section 4.4
* Blueprint `thm:entropy_strong_subadditivity`,
  `thm:entropy_subadditivity_trivial_B`,
  `thm:entropy_fin_one_zero`
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

namespace Entropy

/-! ## The strong subadditivity theorem -/

section StrongSubadditivity

variable {dA dB dC : ℕ}

/-- **Strong subadditivity** (Lieb–Ruskai 1973), stated in the
`Entropy` namespace.

For a tripartite density matrix `ρ_ABC` on `A ⊗ B ⊗ C`:
  `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`

where the reduced states are obtained via the tripartite partial
traces `traceAC_ABC`, `traceC_ABC`, `traceA_ABC` (see
`TNLean.Analysis.Entropy`).

This theorem forwards the proved result
`strong_subadditivity_general` (in
`TNLean/Channel/Schwarz/StrongSubadditivityPosDef.lean`), which derives
strong subadditivity for every positive-semidefinite unit-trace
tripartite density matrix from Lieb concavity. No axiom is introduced
by this module.

Source: Lieb, Ruskai, JMP 14, 1938 (1973);
blueprint `thm:entropy_strong_subadditivity`. -/
theorem strongSubadditivity
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
      + Entropy.vonNeumannEntropy (traceAC_ABC ρ_ABC)
          (traceAC_ABC_isHermitian hρ_dm.1.isHermitian)
    ≤ Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
      + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
          (traceA_ABC_isHermitian hρ_dm.1.isHermitian) :=
  strong_subadditivity_general ρ_ABC hρ_dm

/-- Algebraic rearrangement of `strongSubadditivity` in the
"conditional entropy" form: `S(ρ_ABC) − S(ρ_AB) ≤ S(ρ_BC) − S(ρ_B)`.

This follows from `strongSubadditivity` by adding `−S(ρ_AB) − S(ρ_B)`
to both sides of the basic SSA inequality.

Source: [Wolf, Chapter 8, Section 8.7][Wolf2012QChannels]. -/
theorem strongSubadditivity_rearranged
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
      - Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
    ≤ Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
          (traceA_ABC_isHermitian hρ_dm.1.isHermitian)
      - Entropy.vonNeumannEntropy (traceAC_ABC ρ_ABC)
          (traceAC_ABC_isHermitian hρ_dm.1.isHermitian) := by
  have h := strongSubadditivity ρ_ABC hρ_dm
  linarith

end StrongSubadditivity

/-! ## Fin-one density matrices have vanishing entropy

The following lemma is the main ingredient for deriving ordinary
subadditivity from SSA with trivial middle subsystem `B`. It is
proved from Mathlib (eigenvalue sum = trace, and
`Real.negMulLog_one = 0`). -/

section FinOneEntropy

/-- A `Fin 1`-indexed Hermitian matrix with trace 1 has vanishing
von Neumann entropy.

The single eigenvalue equals the trace (which is `1`), and
`negMulLog 1 = -(1 * log 1) = 0`.

Source: blueprint `thm:entropy_fin_one_zero`. -/
theorem vonNeumannEntropy_eq_zero_of_fin_one
    (M : Matrix (Fin 1) (Fin 1) ℂ)
    (hM : M.IsHermitian) (hM_trace : M.trace = 1) :
    _root_.vonNeumannEntropy M hM = 0 := by
  have h_sum : ∑ i : Fin 1, hM.eigenvalues i = 1 := by
    have h := hM.trace_eq_sum_eigenvalues
    have h_cast : (∑ i : Fin 1, (hM.eigenvalues i : ℂ)) = 1 := h ▸ hM_trace
    exact_mod_cast h_cast
  have h_eig : hM.eigenvalues 0 = 1 := by
    simpa [Fin.sum_univ_one] using h_sum
  change ∑ i : Fin 1, Real.negMulLog (hM.eigenvalues i) = 0
  rw [Fin.sum_univ_one, h_eig, Real.negMulLog_one]

end FinOneEntropy

/-! ## Subadditivity from SSA with trivial middle subsystem

We state subadditivity in the tripartite form with `dB = 1`: the
middle subsystem contributes zero entropy, so SSA reduces to the
classical subadditivity `S(ρ_AC) ≤ S(ρ_A) + S(ρ_C)` on bipartite
states lifted through the trivial middle factor. The reduced middle
state has trace `1` because `Matrix.trace_eq_trace_traceAC_ABC` carries
trace `ρ_ABC = 1` to the `AC`-partial trace. -/

section Subadditivity

variable {dA dC : ℕ}

/-- **Subadditivity of the von Neumann entropy** (tripartite form with
trivial middle subsystem).

For a density matrix `ρ_ABC` on `A ⊗ 1 ⊗ C`, SSA reduces to
`S(ρ_ABC) ≤ S(ρ_AB) + S(ρ_BC)` because the `Fin 1`-indexed middle
reduced state contributes zero entropy, and
`Matrix.trace_eq_trace_traceAC_ABC` supplies the unit-trace condition
needed by `vonNeumannEntropy_eq_zero_of_fin_one`.

Source: blueprint `thm:entropy_subadditivity_trivial_B`;
[Wolf, Chapter 8 (SSA corollary)][Wolf2012QChannels]. -/
theorem subadditivity_ssa_trivial_B
    (ρ_ABC : Matrix (Fin dA × Fin 1 × Fin dC)
      (Fin dA × Fin 1 × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
    ≤ Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
      + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
          (traceA_ABC_isHermitian hρ_dm.1.isHermitian) := by
  have hSSA := strongSubadditivity ρ_ABC hρ_dm
  have h_mid_trace : (traceAC_ABC ρ_ABC).trace = 1 := by
    rw [← Matrix.trace_eq_trace_traceAC_ABC ρ_ABC]
    exact hρ_dm.2
  have h_mid_zero :
      Entropy.vonNeumannEntropy (traceAC_ABC ρ_ABC)
          (traceAC_ABC_isHermitian hρ_dm.1.isHermitian) = 0 :=
    vonNeumannEntropy_eq_zero_of_fin_one _
      (traceAC_ABC_isHermitian hρ_dm.1.isHermitian) h_mid_trace
  linarith

end Subadditivity

end Entropy
