/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MeasurementCircuit

/-!
# Several rounds of measurements

A *measurement round* on the ring of `N` sites is a local circuit, a computational-basis
measurement of a set of sites, and, for every outcome string, a unitary at every site applied
after the measurement. Its Kraus operator for the outcome `m` is
`V_m P_m U`, with `U` the circuit, `P_m` the outcome projection and `V_m` the product of the
corrections. A sequence of rounds is applied one after the other; the circuit of a later round
does not depend on earlier outcomes, and its corrections depend only on its own outcomes. The
depth of the sequence is the total number of layers of its circuits.

A vector is *prepared with measurement rounds in depth `T`* when some sequence of rounds of total
depth at most `T`, applied to a nonzero product vector, gives after every sequence of outcomes
of nonzero probability a scalar multiple of the vector.

A single round is the protocol of `MPSPreparation.MeasurementProtocol`
(`MPSPreparation.isPreparedWithMeasurementRoundsInDepth_of_isPreparedWithMeasurementsInDepth`).
Several rounds are needed when a correction must be applied before later gates that do not
commute with it, as in the tree-RG circuit with measurements of arXiv:2307.01696 (paragraph
"Tree-RG circuit with measurements"), where the teleportation of a register is corrected before
an isometry acts on it. arXiv:2103.13367 performs one round in its definition of `QCcc_ℓ` and
notes, in the paragraph "State transformations with QC and LOCC", that "one could also define a
more general scheme with multiple rounds of LOCC"; its paragraph "Phases of matter" composes
`k` such transformations (`QCcc^{(k)}_ℓ`). The model here is the composition of rounds, each of
the one-round model of `MPSPreparation.MeasurementProtocol`, with the depth counted as the total
number of layers.

A round *implements* a matrix `W` on a set `E` of vectors when for every outcome `m` there is a
scalar `c` with `V_m P_m U v = c W v` for every `v ∈ E`: whatever the outcome, the round acts on
`E` as `W`, up to a scalar independent of the input. A sequence of rounds implements `W` on `E`
when every output from `v ∈ E` is a scalar multiple of `W v`
(`MPSPreparation.MeasurementRound.IsRoundsImplementationOn`). Implementations compose along
sequences of rounds (`MPSPreparation.MeasurementRound.IsRoundsImplementationOn.append`), and an
implementation applied to a nonzero product vector is a preparation.

## Main definitions

* `MPSPreparation.MeasurementRound` and `MPSPreparation.MeasurementRound.kraus`.
* `MPSPreparation.MeasurementRound.outputs` — the vectors reached by a sequence of rounds.
* `MPSPreparation.IsPreparedWithMeasurementRoundsInDepth`.
* `MPSPreparation.MeasurementRound.IsImplementationOn`,
  `MPSPreparation.MeasurementRound.IsRoundsImplementationOn`.

## Main results

* `MPSPreparation.MeasurementRound.exists_mem_outputs_ne_zero` — a nonzero vector has an output
  of nonzero probability, so the definition is not vacuous
  (`MPSPreparation.IsPreparedWithMeasurementRoundsInDepth.ne_zero`).
* `MPSPreparation.isPreparedWithMeasurementRoundsInDepth_of_isPreparedWithMeasurementsInDepth`.
* `MPSPreparation.MeasurementRound.IsImplementationOn.exists_mem_outputs`,
  `MPSPreparation.MeasurementRound.IsRoundsImplementationOn.append`,
  `MPSPreparation.MeasurementRound.IsRoundsImplementationOn.isPreparedWithMeasurementRoundsInDepth`.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), paragraphs "State transformations with QC and
  LOCC" and "Phases of matter".
* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ} [NeZero N]

/-- A measurement round on the ring of `N` sites: a local circuit, a set of sites measured in the
computational basis after it, and, for every outcome string, a unitary at every site applied after
the measurement. The circuit is a list of layers, the head of the list applied first.

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC" (one round: "We
first apply a depth-`ℓ` circuit ... Then, we sequentially measure each ancilla ... and apply
`U ∈ LU` depending on the outcomes"), and paragraph "Phases of matter" (composition of `k` such
transformations). -/
structure MeasurementRound (d N : ℕ) [NeZero N] where
  /-- The local circuit of the round. -/
  circuit : List (Layer d N)
  /-- The sites measured in the computational basis after the circuit. -/
  measured : Finset (Fin N)
  /-- The unitary applied at the site `i` after the outcome `m`. -/
  correction : (measured → Fin d) → Fin N → Matrix (Fin d) (Fin d) ℂ
  correction_mem_unitary : ∀ m i, correction m i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)

namespace MeasurementRound

variable (R : MeasurementRound d N)

/-- The Kraus operator `V_m P_m U` of the outcome `m`: the circuit, the projection onto the
outcome, and the product of the corrections. -/
noncomputable def kraus (m : R.measured → Fin d) : Matrix (Cfg d N) (Cfg d N) ℂ :=
  finKronecker (R.correction m) * outcomeProj R.measured m * circuitOp R.circuit

/-- The number of layers of the circuit of the round. -/
def depth : ℕ := R.circuit.length

/-- The one-round protocol of `MPSPreparation.MeasurementProtocol` with the initial product
vector `v` and the round `R`. -/
def toProtocol (v : Fin N → Fin d → ℂ) : MeasurementProtocol d N where
  initial := v
  first := R.circuit
  measured := R.measured
  correction := R.correction
  correction_mem_unitary := R.correction_mem_unitary

theorem toProtocol_output (v : Fin N → Fin d → ℂ) (m : R.measured → Fin d) :
    (R.toProtocol v).output m = R.kraus m *ᵥ productVector v := by
  simp only [MeasurementProtocol.output, MeasurementProtocol.postMeasurement,
    MeasurementProtocol.preMeasurement, kraus, toProtocol, mulVec_mulVec, Matrix.mul_assoc]

/-- A nonzero vector stays nonzero for some outcome. -/
theorem exists_kraus_mulVec_ne_zero {v : Cfg d N → ℂ} (hv : v ≠ 0) :
    ∃ m, R.kraus m *ᵥ v ≠ 0 := by
  by_contra h
  have h' : ∀ m, R.kraus m *ᵥ v = 0 := fun m => not_not.mp fun hm => h ⟨m, hm⟩
  have hpost : ∀ m, outcomeProj R.measured m *ᵥ (circuitOp R.circuit *ᵥ v) = 0 := fun m => by
    have hU := finKronecker_mem_unitary (R.correction_mem_unitary m)
    have := h' m
    rw [kraus, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec] at this
    rw [← one_mulVec (outcomeProj _ _ *ᵥ _), ← Unitary.star_mul_self_of_mem hU,
      ← mulVec_mulVec, this, mulVec_zero]
  have hsum : circuitOp R.circuit *ᵥ v = 0 := by
    rw [← one_mulVec (circuitOp R.circuit *ᵥ v), ← sum_outcomeProj R.measured, sum_mulVec]
    exact Finset.sum_eq_zero fun m _ => hpost m
  refine hv ?_
  rw [← one_mulVec v, ← Unitary.star_mul_self_of_mem (circuitOp_mem_unitary R.circuit),
    ← mulVec_mulVec, hsum, mulVec_zero]

/-! ### Sequences of rounds -/

/-- The vectors reached from `v` by the sequence of rounds `Rs`, the head applied first, over all
the sequences of outcomes. -/
def outputs : List (MeasurementRound d N) → (Cfg d N → ℂ) → Set (Cfg d N → ℂ)
  | [], v => {v}
  | R :: Rs, v => ⋃ m, outputs Rs (R.kraus m *ᵥ v)

@[simp] theorem outputs_nil (v : Cfg d N → ℂ) : outputs [] v = {v} := rfl

theorem mem_outputs_cons {Rs : List (MeasurementRound d N)} {v w : Cfg d N → ℂ} :
    w ∈ outputs (R :: Rs) v ↔ ∃ m, w ∈ outputs Rs (R.kraus m *ᵥ v) := by
  simp [outputs]

/-- The outputs of a scalar multiple are the scalar multiples of the outputs. -/
theorem mem_outputs_smul {Rs : List (MeasurementRound d N)} {v w : Cfg d N → ℂ} (c : ℂ)
    (hw : w ∈ outputs Rs (c • v)) : ∃ u ∈ outputs Rs v, w = c • u := by
  induction Rs generalizing v with
  | nil => exact ⟨v, rfl, hw⟩
  | cons R Rs ih =>
    obtain ⟨m, hm⟩ := (R.mem_outputs_cons).mp hw
    rw [mulVec_smul] at hm
    obtain ⟨u, hu, rfl⟩ := ih hm
    exact ⟨u, (R.mem_outputs_cons).mpr ⟨m, hu⟩, rfl⟩

/-- A nonzero vector has a nonzero output: some sequence of outcomes has nonzero probability. -/
theorem exists_mem_outputs_ne_zero (Rs : List (MeasurementRound d N)) {v : Cfg d N → ℂ}
    (hv : v ≠ 0) : ∃ w ∈ outputs Rs v, w ≠ 0 := by
  induction Rs generalizing v with
  | nil => exact ⟨v, rfl, hv⟩
  | cons R Rs ih =>
    obtain ⟨m, hm⟩ := R.exists_kraus_mulVec_ne_zero hv
    obtain ⟨w, hw, hw0⟩ := ih hm
    exact ⟨w, (R.mem_outputs_cons).mpr ⟨m, hw⟩, hw0⟩

end MeasurementRound

/-- A vector `ψ` is *prepared with measurement rounds in depth `T`* when a sequence of rounds
whose circuits have at most `T` layers in total, applied to a nonzero product vector, gives a
scalar multiple of `ψ` after every sequence of outcomes of nonzero probability.

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC" (deterministic
preparation, and "a more general scheme with multiple rounds of LOCC"), and paragraph "Phases of
matter" (`QCcc^{(k)}_ℓ`, the composition of `k` such transformations); arXiv:2307.01696,
paragraph "Tree-RG circuit with measurements". -/
def IsPreparedWithMeasurementRoundsInDepth (T : ℕ) (ψ : Cfg d N → ℂ) : Prop :=
  ∃ (v : Fin N → Fin d → ℂ) (Rs : List (MeasurementRound d N)),
    (Rs.map MeasurementRound.depth).sum ≤ T ∧ productVector v ≠ 0 ∧
      ∀ w ∈ MeasurementRound.outputs Rs (productVector v), w ≠ 0 → ∃ c : ℂ, w = c • ψ

/-- A vector prepared with measurement rounds is nonzero. -/
theorem IsPreparedWithMeasurementRoundsInDepth.ne_zero {T : ℕ} {ψ : Cfg d N → ℂ}
    (h : IsPreparedWithMeasurementRoundsInDepth T ψ) : ψ ≠ 0 := by
  obtain ⟨v, Rs, -, hv, hRs⟩ := h
  obtain ⟨w, hw, hw0⟩ := MeasurementRound.exists_mem_outputs_ne_zero Rs hv
  obtain ⟨c, rfl⟩ := hRs w hw hw0
  rintro rfl
  exact hw0 (smul_zero c)

theorem IsPreparedWithMeasurementRoundsInDepth.mono {T T' : ℕ} {ψ : Cfg d N → ℂ}
    (h : IsPreparedWithMeasurementRoundsInDepth T ψ) (hT : T ≤ T') :
    IsPreparedWithMeasurementRoundsInDepth T' ψ := by
  obtain ⟨v, Rs, hd, hv, hRs⟩ := h
  exact ⟨v, Rs, hd.trans hT, hv, hRs⟩

/-- **One round is a protocol.** A vector prepared with measurements in depth `T` is prepared with
one measurement round in depth `T`. -/
theorem isPreparedWithMeasurementRoundsInDepth_of_isPreparedWithMeasurementsInDepth {T : ℕ}
    {ψ : Cfg d N → ℂ} (h : IsPreparedWithMeasurementsInDepth T ψ) :
    IsPreparedWithMeasurementRoundsInDepth T ψ := by
  obtain ⟨P, hT, h0, hP⟩ := h
  let R : MeasurementRound d N :=
    ⟨P.first, P.measured, P.correction, P.correction_mem_unitary⟩
  refine ⟨P.initial, [R], by simpa [MeasurementRound.depth] using hT, h0, fun w hw hw0 => ?_⟩
  obtain ⟨m, hm⟩ := (R.mem_outputs_cons).mp hw
  rw [MeasurementRound.outputs_nil, Set.mem_singleton_iff] at hm
  subst hm
  have hout : P.output m = R.kraus m *ᵥ productVector P.initial := R.toProtocol_output _ m
  rw [← hout]
  refine hP m fun hpost => hw0 ?_
  rw [← hout, MeasurementProtocol.output, hpost, mulVec_zero]

namespace MeasurementRound

/-- The round `R` *implements* the matrix `W` on the set `E` of vectors when, for every outcome
`m`, its Kraus operator agrees on `E` with a scalar multiple of `W`, the scalar depending on `m`
only.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("correcting (without
postselection) based on the measurement outcomes"); arXiv:2103.13367, paragraph "State
transformations with QC and LOCC" (deterministic transformations). -/
def IsImplementationOn (R : MeasurementRound d N) (E : Set (Cfg d N → ℂ))
    (W : Matrix (Cfg d N) (Cfg d N) ℂ) : Prop :=
  ∀ m, ∃ c : ℂ, ∀ v ∈ E, R.kraus m *ᵥ v = c • (W *ᵥ v)

/-- **Implementations compose.** If the round `R` implements `W` on `E` and `v ∈ E`, every output
of `R` followed by `Rs` is a scalar multiple of an output of `Rs` from `W v`. -/
theorem IsImplementationOn.exists_mem_outputs {R : MeasurementRound d N}
    {E : Set (Cfg d N → ℂ)} {W : Matrix (Cfg d N) (Cfg d N) ℂ} (hR : R.IsImplementationOn E W)
    {Rs : List (MeasurementRound d N)} {v w : Cfg d N → ℂ} (hv : v ∈ E)
    (hw : w ∈ outputs (R :: Rs) v) : ∃ c : ℂ, ∃ u ∈ outputs Rs (W *ᵥ v), w = c • u := by
  obtain ⟨m, hm⟩ := (R.mem_outputs_cons).mp hw
  obtain ⟨c, hc⟩ := hR m
  rw [hc v hv] at hm
  obtain ⟨u, hu, rfl⟩ := mem_outputs_smul c hm
  exact ⟨c, u, hu, rfl⟩

/-! ### Sequences of rounds implementing a matrix -/

theorem mem_outputs_append {Rs Rs' : List (MeasurementRound d N)} {v w : Cfg d N → ℂ} :
    w ∈ outputs (Rs ++ Rs') v ↔ ∃ u ∈ outputs Rs v, w ∈ outputs Rs' u := by
  induction Rs generalizing v with
  | nil => simp
  | cons R Rs ih =>
    simp only [List.cons_append, R.mem_outputs_cons, ih]
    exact ⟨fun ⟨m, u, hu, hw⟩ => ⟨u, ⟨m, hu⟩, hw⟩, fun ⟨u, ⟨m, hu⟩, hw⟩ => ⟨m, u, hu, hw⟩⟩

/-- The sequence of rounds `Rs` *implements* the matrix `W` on the set `E` of vectors when, for
every `v ∈ E`, every output of `Rs` from `v` is a scalar multiple of `W v`: whatever the
outcomes, the rounds act on `E` as `W`, up to a scalar.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("correcting (without
postselection) based on the measurement outcomes"). -/
def IsRoundsImplementationOn (Rs : List (MeasurementRound d N)) (E : Set (Cfg d N → ℂ))
    (W : Matrix (Cfg d N) (Cfg d N) ℂ) : Prop :=
  ∀ v ∈ E, ∀ w ∈ outputs Rs v, ∃ c : ℂ, w = c • (W *ᵥ v)

theorem isRoundsImplementationOn_nil (E : Set (Cfg d N → ℂ)) :
    IsRoundsImplementationOn ([] : List (MeasurementRound d N)) E 1 := by
  intro v _ w hw
  rw [outputs_nil, Set.mem_singleton_iff] at hw
  exact ⟨1, by rw [hw, one_mulVec, one_smul]⟩

theorem IsRoundsImplementationOn.mono {Rs : List (MeasurementRound d N)}
    {E E' : Set (Cfg d N → ℂ)} {W : Matrix (Cfg d N) (Cfg d N) ℂ}
    (h : IsRoundsImplementationOn Rs E W) (hE : E' ⊆ E) : IsRoundsImplementationOn Rs E' W :=
  fun v hv => h v (hE hv)

/-- **Implementations compose.** If `Rs` implements `W` on `E`, `W` maps `E` into `E'`, and
`Rs'` implements `W'` on `E'`, then `Rs` followed by `Rs'` implements `W' W` on `E`. -/
theorem IsRoundsImplementationOn.append {Rs Rs' : List (MeasurementRound d N)}
    {E E' : Set (Cfg d N → ℂ)} {W W' : Matrix (Cfg d N) (Cfg d N) ℂ}
    (h : IsRoundsImplementationOn Rs E W) (h' : IsRoundsImplementationOn Rs' E' W')
    (hE : ∀ v ∈ E, W *ᵥ v ∈ E') : IsRoundsImplementationOn (Rs ++ Rs') E (W' * W) := by
  intro v hv w hw
  obtain ⟨u, hu, hw⟩ := mem_outputs_append.mp hw
  obtain ⟨c, rfl⟩ := h v hv u hu
  obtain ⟨w', hw', rfl⟩ := mem_outputs_smul c hw
  obtain ⟨c', rfl⟩ := h' _ (hE v hv) w' hw'
  exact ⟨c * c', by rw [smul_smul, mulVec_mulVec]⟩

/-- **Preparation from an implementation.** If `Rs` implements `W` on `E` and the nonzero
product vector `π` lies in `E`, then `W π` is prepared with measurement rounds in the total
depth of `Rs`. -/
theorem IsRoundsImplementationOn.isPreparedWithMeasurementRoundsInDepth
    {Rs : List (MeasurementRound d N)} {E : Set (Cfg d N → ℂ)}
    {W : Matrix (Cfg d N) (Cfg d N) ℂ} (h : IsRoundsImplementationOn Rs E W)
    {v : Fin N → Fin d → ℂ} (hv : productVector v ≠ 0) (hvE : productVector v ∈ E) :
    IsPreparedWithMeasurementRoundsInDepth (Rs.map depth).sum (W *ᵥ productVector v) :=
  ⟨v, Rs, le_rfl, hv, fun w hw _ => h _ hvE w hw⟩

end MeasurementRound

end MPSPreparation
