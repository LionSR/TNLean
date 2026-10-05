/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Center
import TNLean.Circuit.Measurement.Rounds

/-!
# Input-independent branch amplitudes

For a fixed sequence of measurement outcomes, the output is a linear map of the input.
If a sequence implements a unitary on every vector of a linear subspace, each fixed branch
therefore equals one scalar multiple of that unitary throughout the subspace. The scalar
may be zero, and there is no lower bound on the dimension of the input subspace.

This strengthens the pointwise output characterization of measurement rounds to a coherent
fixed-branch statement, as needed for superpositions of logical sectors in
arXiv:2307.01696, "Tree-RG circuit with measurements" and "Long-range MPS using measurements".
The linear-algebra step is Mathlib's characterization of endomorphisms that preserve every
one-dimensional subspace.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
* Mathlib, `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`.
-/

open Matrix

namespace QuantumCircuit.MeasurementRound

variable {d N : ℕ} [NeZero N]

/-- One computational-basis outcome for each round, in execution order. -/
def OutcomeHistory : List (MeasurementRound d N) → Type
  | [] => Unit
  | R :: Rs => (R.measured → Fin d) × OutcomeHistory Rs

/-- The Kraus matrix of a complete outcome history. The first round acts first. -/
noncomputable def historyKraus : (Rs : List (MeasurementRound d N)) →
    OutcomeHistory Rs → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ
  | [], _ => 1
  | R :: Rs, m => historyKraus Rs m.2 * R.kraus m.1

/-- The fixed-history output is one of the outputs of the rounds, including zero branches. -/
theorem historyKraus_mulVec_mem_outputs (Rs : List (MeasurementRound d N))
    (m : OutcomeHistory Rs) (v : (Fin N → Fin d) → ℂ) :
    historyKraus Rs m *ᵥ v ∈ outputs Rs v := by
  induction Rs generalizing v with
  | nil => simp [historyKraus]
  | cons R Rs ih =>
    rw [historyKraus, ← mulVec_mulVec]
    exact R.mem_outputs_cons.mpr ⟨m.1, ih m.2 _⟩

/-- A deterministic unitary action on a linear input subspace has an input-independent scalar
on each fixed measurement branch. Zero branch maps and zero- or one-dimensional input spaces
are included. -/
theorem IsRoundsImplementationOn.exists_history_scalar
    {Rs : List (MeasurementRound d N)}
    {E : Submodule ℂ ((Fin N → Fin d) → ℂ)}
    {W : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (h : IsRoundsImplementationOn Rs (E : Set _) W)
    (hW : W ∈ unitary (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ))
    (m : OutcomeHistory Rs) :
    ∃ c : ℂ, ∀ v ∈ E, historyKraus Rs m *ᵥ v = c • (W *ᵥ v) := by
  classical
  let K := historyKraus Rs m
  have hpoint : ∀ v ∈ E, ∃ c : ℂ, K *ᵥ v = c • (W *ᵥ v) :=
    fun v hv => h v hv _ (historyKraus_mulVec_mem_outputs Rs m v)
  have hleft : Wᴴ * W = 1 := (Unitary.mem_iff.mp hW).1
  have hright : W * Wᴴ = 1 := (Unitary.mem_iff.mp hW).2
  have hmem : ∀ v : E, Wᴴ *ᵥ (K *ᵥ (v : (Fin N → Fin d) → ℂ)) ∈ E := by
    intro v
    obtain ⟨c, hc⟩ := hpoint v v.property
    rw [hc, mulVec_smul, mulVec_mulVec, hleft, one_mulVec]
    exact E.smul_mem c v.property
  let f : E →ₗ[ℂ] E :=
    { toFun := fun v => ⟨Wᴴ *ᵥ (K *ᵥ (v : (Fin N → Fin d) → ℂ)), hmem v⟩
      map_add' := fun u v => Subtype.ext (by simp [mulVec_add])
      map_smul' := fun c v => Subtype.ext (by simp [mulVec_smul]) }
  have hf : ∀ v : E, ∃ c : ℂ, f v = c • v := by
    intro v
    obtain ⟨c, hc⟩ := hpoint v v.property
    refine ⟨c, Subtype.ext ?_⟩
    change Wᴴ *ᵥ (K *ᵥ (v : (Fin N → Fin d) → ℂ)) = c • (v : (Fin N → Fin d) → ℂ)
    rw [hc, mulVec_smul, mulVec_mulVec, hleft, one_mulVec]
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := f) fun v => by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · rw [LinearIndependent.pair_iff' hv]
        obtain ⟨a, ha⟩ := hf v
        exact fun hlin => hlin a ha.symm
  refine ⟨c, fun v hv => ?_⟩
  have hvf := congrArg (fun g : E →ₗ[ℂ] E => ((g ⟨v, hv⟩ : E) : (Fin N → Fin d) → ℂ)) hc
  change Wᴴ *ᵥ (K *ᵥ v) = c • v at hvf
  have hout := congrArg (fun u => W *ᵥ u) hvf
  simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hright, Matrix.one_mul,
    mulVec_smul] using hout

end QuantumCircuit.MeasurementRound
