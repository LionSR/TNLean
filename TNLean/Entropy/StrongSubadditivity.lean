/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Axioms.Entropy
import TNLean.Entropy.VonNeumann

/-!
# Strong subadditivity (namespaced wrapper + basic corollaries)

This module exposes **strong subadditivity** (SSA) of the von Neumann
entropy inside the `Entropy` namespace, following the roadmap of
issue #613 for the Simple MPDO RFP bootstrap (issue #236, umbrella
#239).

SSA is the statement that for any tripartite density matrix
`ρ_ABC` on `A ⊗ B ⊗ C`,
`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.
This is a deep theorem of Lieb–Ruskai (1973). Its full Lean proof is
deferred to the sanctioned axiom `_root_.strong_subadditivity` in
`TNLean.Axioms.Entropy`; the theorem `Entropy.strongSubadditivity`
provided here is a thin *theorem* wrapper around that single
axiom, so that the sanctioned axiom inventory under
`TNLean/Axioms/` remains authoritative and no duplicate
axiomatization of SSA is introduced.

## Main declarations

* `Entropy.strongSubadditivity` — **theorem** (not a new axiom).
  Forwards to `_root_.strong_subadditivity` from
  `TNLean/Axioms/Entropy.lean`.
* `Entropy.vonNeumannEntropy_eq_zero_of_fin_one` — a 1×1 density
  matrix (PSD with trace 1) has vanishing entropy; proved from
  Mathlib via `Real.negMulLog_one`.
* `Entropy.strongSubadditivity_rearranged` — the algebraic
  rearrangement `S(ρ_ABC) − S(ρ_AB) ≤ S(ρ_BC) − S(ρ_B)` (the
  conditional-entropy form), proved from SSA alone.
* `Matrix.traceA_ABC_trace`, `Matrix.traceC_ABC_trace`,
  `Matrix.traceAC_ABC_trace` — total-trace preservation for the
  tripartite partial traces. These are used below to derive the trace
  of a reduced state from `ρ_ABC.trace = 1` without an auxiliary
  caller-supplied hypothesis.
* `Entropy.subadditivity_ssa_trivial_B` — subadditivity
  `S(ρ_ABC) ≤ S(ρ_AB) + S(ρ_BC)` in the tripartite form with
  trivial middle subsystem (`dB = 1`). The middle factor contributes
  zero entropy (by the `Fin 1` lemma above), so SSA specializes to
  this inequality; the trace of `(traceAC_ABC ρ_ABC)` equals
  `ρ_ABC.trace = 1` by `Matrix.traceAC_ABC_trace`.

## TODO

Replace the sanctioned axiom `_root_.strong_subadditivity` (in
`TNLean/Axioms/Entropy.lean`) with a proof along the classical route:
1. Define quantum relative entropy `D(ρ‖σ) = tr(ρ(log ρ − log σ))`.
2. Establish Klein's inequality: `D(ρ‖σ) ≥ 0` for density matrices.
3. Lieb's joint concavity of `(A, B) ↦ tr(Kᴴ Aᵗ K B^{1-t})`.
4. Monotonicity of the relative entropy under partial trace
   (the "data-processing inequality").

See Lieb–Ruskai, JMP 14, 1938 (1973) and also the modern
operator-concavity proof in Ruskai, "Inequalities for quantum entropy:
A review with conditions for equality", JMP 43, 4358 (2002).

## References

* Lieb, Ruskai, "Proof of the strong subadditivity of quantum-mechanical
  entropy", JMP 14, 1938 (1973)
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*][Wolf2012QChannels]
* arXiv:1606.00608 §4.4
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

/-! ## Trace preservation for the tripartite partial traces

The following three lemmas record that the tripartite partial traces
`traceA_ABC`, `traceC_ABC`, `traceAC_ABC` (defined in
`TNLean.Analysis.Entropy`) preserve the total trace of the underlying
state. They let downstream SSA corollaries derive the auxiliary
`trace = 1` hypothesis on a reduced state from the full-system
`ρ.trace = 1` hypothesis, without the caller needing to re-prove it. -/

namespace Matrix

variable {dA dB dC : ℕ}

/-- Total-trace preservation for the tripartite partial trace `traceA_ABC`:
`tr(tr_A ρ) = tr ρ`. -/
theorem traceA_ABC_trace
    (ρ : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) :
    (Matrix.traceA_ABC ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.traceA_ABC]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type
    (fun x : Fin dA × (Fin dB × Fin dC) => ρ x x)).symm

/-- Total-trace preservation for the tripartite partial trace `traceC_ABC`:
`tr(tr_C ρ) = tr ρ`. -/
theorem traceC_ABC_trace
    (ρ : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) :
    (Matrix.traceC_ABC ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.traceC_ABC]
  rw [Fintype.sum_prod_type
    (fun ab : Fin dA × Fin dB => ∑ c, ρ (ab.1, ab.2, c) (ab.1, ab.2, c))]
  rw [show (∑ x : Fin dA × Fin dB × Fin dC, ρ x x)
        = ∑ a : Fin dA, ∑ bc : Fin dB × Fin dC, ρ (a, bc) (a, bc) from
      Fintype.sum_prod_type
        (fun x : Fin dA × (Fin dB × Fin dC) => ρ x x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Fintype.sum_prod_type
    (fun bc : Fin dB × Fin dC => ρ (a, bc) (a, bc))).symm

/-- Total-trace preservation for the tripartite partial trace `traceAC_ABC`:
`tr(tr_{AC} ρ) = tr ρ`. -/
theorem traceAC_ABC_trace
    (ρ : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) :
    (Matrix.traceAC_ABC ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.traceAC_ABC]
  rw [Finset.sum_comm]
  rw [show (∑ x : Fin dA × Fin dB × Fin dC, ρ x x)
        = ∑ a : Fin dA, ∑ bc : Fin dB × Fin dC, ρ (a, bc) (a, bc) from
      Fintype.sum_prod_type
        (fun x : Fin dA × (Fin dB × Fin dC) => ρ x x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Fintype.sum_prod_type
    (fun bc : Fin dB × Fin dC => ρ (a, bc) (a, bc))).symm

end Matrix

namespace Entropy

/-! ## The strong subadditivity wrapper -/

section StrongSubadditivity

variable {dA dB dC : ℕ}

/-- **Strong subadditivity** (Lieb–Ruskai 1973), namespaced wrapper.

For a tripartite density matrix `ρ_ABC` on `A ⊗ B ⊗ C`:
  `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`

where the reduced states are obtained via the tripartite partial
traces `traceAC_ABC`, `traceC_ABC`, `traceA_ABC` (see
`TNLean.Analysis.Entropy`).

This is a thin theorem wrapper around the sanctioned axiom
`_root_.strong_subadditivity` (in `TNLean/Axioms/Entropy.lean`); no
new axiom is introduced by this module. See the module-level TODO for
the roadmap replacing the underlying axiom with a proof.

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
  -- The sum of eigenvalues equals the (real cast of the) trace.
  have h_sum : ∑ i : Fin 1, hM.eigenvalues i = 1 := by
    have h := hM.trace_eq_sum_eigenvalues
    have h_cast : (∑ i : Fin 1, (hM.eigenvalues i : ℂ)) = 1 := h ▸ hM_trace
    exact_mod_cast h_cast
  have h_eig : hM.eigenvalues 0 = 1 := by
    simpa [Fin.sum_univ_one] using h_sum
  -- Entropy of a one-element sum reduces to `negMulLog` of the one eigenvalue.
  have h1 : Real.negMulLog (1 : ℝ) = 0 := by
    simp [Real.negMulLog]
  change ∑ i : Fin 1, Real.negMulLog (hM.eigenvalues i) = 0
  rw [Fin.sum_univ_one, h_eig, h1]

end FinOneEntropy

/-! ## Subadditivity from SSA with trivial middle subsystem

We state subadditivity in the tripartite form with `dB = 1`: the
middle subsystem contributes zero entropy, so SSA reduces to the
classical subadditivity `S(ρ_AC) ≤ S(ρ_A) + S(ρ_C)` on bipartite
states lifted through the trivial middle factor.

The trace of `ρ_B = traceAC_ABC ρ_ABC` is derived internally from
`ρ_ABC.trace = 1` via the trace-preservation lemma
`Matrix.traceAC_ABC_trace`; no auxiliary hypothesis is required. -/

section Subadditivity

variable {dA dC : ℕ}

/-- **Subadditivity of the von Neumann entropy** (tripartite form with
trivial middle subsystem).

For a density matrix `ρ_ABC` on `A ⊗ 1 ⊗ C`, SSA reduces to
`S(ρ_ABC) ≤ S(ρ_AB) + S(ρ_BC)` because the `Fin 1`-indexed middle
reduced state contributes zero entropy (see
`vonNeumannEntropy_eq_zero_of_fin_one`). The middle reduced state
has unit trace by `Matrix.traceAC_ABC_trace`. -/
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
    rw [Matrix.traceAC_ABC_trace]; exact hρ_dm.2
  have h_mid_zero :
      Entropy.vonNeumannEntropy (traceAC_ABC ρ_ABC)
          (traceAC_ABC_isHermitian hρ_dm.1.isHermitian) = 0 :=
    vonNeumannEntropy_eq_zero_of_fin_one _
      (traceAC_ABC_isHermitian hρ_dm.1.isHermitian) h_mid_trace
  linarith

end Subadditivity

end Entropy
