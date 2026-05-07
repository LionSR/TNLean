/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Axioms.Entropy
import TNLean.Entropy.TripartiteTrace
import TNLean.Entropy.VonNeumann

/-!
# Strong subadditivity

Strong subadditivity (SSA) of the von Neumann entropy:
for any tripartite density matrix `ρ_ABC` on `A ⊗ B ⊗ C`,
`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

This is a theorem of Lieb–Ruskai (1973). The proof is currently
supplied by the axiom `_root_.strong_subadditivity` in
`TNLean/Axioms/Entropy.lean`; the theorem `Entropy.strongSubadditivity`
stated here wraps that single axiom in the `Entropy` namespace.

## Main declarations

* `Entropy.strongSubadditivity` — strong subadditivity in the `Entropy` namespace
* `Entropy.vonNeumannEntropy_eq_zero_of_fin_one` — a `Fin 1`-indexed Hermitian
  matrix with trace 1 has vanishing entropy
* `Entropy.strongSubadditivity_rearranged` — the conditional-entropy form
  `S(ρ_ABC) − S(ρ_AB) ≤ S(ρ_BC) − S(ρ_B)`
* `Entropy.subadditivity_ssa_trivial_B` — subadditivity
  `S(ρ_ABC) ≤ S(ρ_AB) + S(ρ_BC)` with trivial middle subsystem (`dB = 1`)

## TODO

Replace the axiom `_root_.strong_subadditivity` with a proof:
1. Quantum relative entropy `D(ρ‖σ) = tr(ρ(log ρ − log σ))`
2. Klein's inequality: `D(ρ‖σ) ≥ 0` for density matrices
3. Lieb's joint concavity
4. Monotonicity of relative entropy under partial trace

See issue #239 and Lieb–Ruskai, JMP 14, 1938 (1973).

## References

* Lieb, Ruskai, "Proof of the strong subadditivity of quantum-mechanical
  entropy", JMP 14, 1938 (1973)
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*][Wolf2012QChannels]
* arXiv:1606.00608 Section 4.4
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

References:
* Lieb, Ruskai, JMP 14, 1938 (1973). -/
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
  _root_.strong_subadditivity ρ_ABC hρ_dm

/-- Algebraic rearrangement of `strongSubadditivity` in the
"conditional entropy" form: `S(ρ_ABC) − S(ρ_AB) ≤ S(ρ_BC) − S(ρ_B)`.

This follows from the axiom by adding `−S(ρ_AB) − S(ρ_B)` to both
sides of the basic SSA inequality. -/
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
`negMulLog 1 = -(1 * log 1) = 0`. -/
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
  have h1 : Real.negMulLog (1 : ℝ) = 0 := by
    simp [Real.negMulLog]
  change ∑ i : Fin 1, Real.negMulLog (hM.eigenvalues i) = 0
  rw [Fin.sum_univ_one, h_eig, h1]

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
needed by `vonNeumannEntropy_eq_zero_of_fin_one`. -/
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
