/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.Entropy

/-!
# Axiomatized entropy inequalities

This module isolates the axiom for **strong subadditivity** (Lieb–Ruskai 1973)
so that it does not pollute the stable import surface `TNLean.lean`.

## Status

* `strong_subadditivity` is an **axiom** (proof deferred; see TODO below).
* A `subadditivity` result can be derived from `strong_subadditivity` by
  specializing `dC = 1`; this is left for downstream modules.

## TODO

Replace `strong_subadditivity` with a proof from Klein's inequality and
Lieb concavity (Lieb–Ruskai 1973). This requires:
1. Quantum relative entropy `D(ρ‖σ) = tr(ρ(log ρ - log σ))`
2. Klein's inequality: `D(ρ‖σ) ≥ 0`
3. Joint convexity of relative entropy
4. Monotonicity of relative entropy under partial trace

## References

* Lieb, Ruskai, "Proof of the strong subadditivity of quantum-mechanical
  entropy", JMP 14, 1938 (1973)
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

/-! ## Strong subadditivity (axiom) -/

section StrongSubadditivity

variable {dA dB dC : ℕ}

/-- **Strong subadditivity** (Lieb–Ruskai 1973).

For a tripartite density matrix `ρ_ABC` on `A ⊗ B ⊗ C`:
  `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`

This is axiomatized; see the module docstring for the deferred proof plan.

References:
* Lieb, Ruskai, JMP 14, 1938 (1973) -/
axiom strong_subadditivity
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_ABC : ρ_ABC.IsHermitian)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hρ_B : (traceAC_ABC ρ_ABC).IsHermitian)
    (hρ_AB : (traceC_ABC ρ_ABC).IsHermitian)
    (hρ_BC : (traceA_ABC ρ_ABC).IsHermitian) :
    vonNeumannEntropy ρ_ABC hρ_ABC
      + vonNeumannEntropy (traceAC_ABC ρ_ABC) hρ_B
    ≤ vonNeumannEntropy (traceC_ABC ρ_ABC) hρ_AB
      + vonNeumannEntropy (traceA_ABC ρ_ABC) hρ_BC

end StrongSubadditivity
