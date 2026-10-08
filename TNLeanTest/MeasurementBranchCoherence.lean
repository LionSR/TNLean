/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Measurement.CoherentRounds
import TNLean.Circuit.Teleportation.ZeroSubspace

/-! Fixed-history coherence includes zero branches and zero- and one-dimensional input spaces.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
* Mathlib, `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`.
-/

open Matrix QuantumCircuit QuantumCircuit.MeasurementRound

variable {d N : ℕ} [NeZero N]

example (R R' : MeasurementRound d N) (m : R.measured → Fin d)
    (m' : R'.measured → Fin d) :
    historyKraus [R, R'] (m, m', ()) = R'.kraus m' * R.kraus m := by
  simp [historyKraus]

example {Rs : List (MeasurementRound d N)}
    {W : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (h : IsRoundsImplementationOn Rs (⊥ : Submodule ℂ ((Fin N → Fin d) → ℂ)) W)
    (hW : W ∈ unitary _) (m : OutcomeHistory Rs) :
    ∃ c : ℂ, ∀ v ∈ (⊥ : Submodule ℂ ((Fin N → Fin d) → ℂ)),
      historyKraus Rs m *ᵥ v = c • (W *ᵥ v) :=
  h.exists_history_scalar hW m

example {Rs : List (MeasurementRound d N)}
    {W : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (u : (Fin N → Fin d) → ℂ)
    (h : IsRoundsImplementationOn Rs (Submodule.span ℂ {u} : Set _) W)
    (hW : W ∈ unitary _) (m : OutcomeHistory Rs) :
    ∃ c : ℂ, ∀ v ∈ Submodule.span ℂ {u},
      historyKraus Rs m *ᵥ v = c • (W *ᵥ v) :=
  h.exists_history_scalar hW m

example {Rs : List (MeasurementRound d N)}
    (W : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (m : OutcomeHistory Rs)
    (hzero : historyKraus Rs m = 0) :
    ∃ c : ℂ, c = 0 ∧ ∀ v, historyKraus Rs m *ᵥ v = c • (W *ᵥ v) := by
  exact ⟨0, rfl, fun v => by simp [hzero]⟩

example [NeZero d] {Rs : List (MeasurementRound d N)}
    {W : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ} (S : Set (Fin N))
    (h : IsRoundsImplementationOn Rs {v | IsZeroOn S v} W)
    (hW : W ∈ unitary _) (m : OutcomeHistory Rs) :
    ∃ c : ℂ, ∀ v, IsZeroOn S v → historyKraus Rs m *ᵥ v = c • (W *ᵥ v) :=
  h.exists_history_scalar (E := zeroOnSubmodule S) hW m
