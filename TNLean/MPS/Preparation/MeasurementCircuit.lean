/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CircuitComposition

/-!
# Local circuits assisted by measurements

A measurement-assisted preparation on the ring of `N` sites starts from a product vector,
applies a local circuit, measures a set `S` of sites in the computational basis, and then,
for every outcome string `m`, applies a local circuit chosen according to `m`. It prepares
`ψ` in depth `T` when every outcome of nonzero probability leaves the chain in `ψ` up to a
nonzero scalar (phase and normalization), and the two circuits together have at most `T`
layers for every outcome. Only the layers of the circuits are counted: the measurement and
the classical processing of its outcomes are free.

This is the class `QCcc` of Piroli, Styliaris and Cirac (arXiv:2103.13367, paragraph
"Quantum circuits and LOCC" and Definition "Transformations under QC and LOCC"), which is the
model behind the paragraph "Preparations using measurements" of arXiv:2307.01696: a depth-`ℓ`
circuit followed by measurements and by local unitaries "depending on the outcomes of all
previous measurements", the outcomes being "classically communicated among all the qudits".
The correction applied at a site may therefore depend on the whole outcome string, not only
on outcomes measured nearby: classical communication is global and free. In the Example 1
preparation of the GHZ state the correction at the site `n` is `X^{k₂ + ⋯ + kₙ}`, which
depends on outcomes at every distance.

This differs from the relation `MPSPreparation.IsLocalChannelConversion`
(`TNLean.MPS.Preparation.LocalChannelConversion`), which models the circuits of the same
paragraph with ancillas and local operations but without measurements and without classical
communication: there every step is a local channel, and connected correlations beyond the
light cone vanish (`trace_mul_mul_eq_of_isLocalChannelConversion`). Global classical
communication breaks this light cone, which is why GHZ-type states, whose connected
correlations do not decay, can be prepared in constant depth with measurements
(`TNLean.MPS.Preparation.GHZMeasurement`).

## Conventions

Every protocol of this model is a protocol of the source's, of no larger depth, so a
preparation proved here is a preparation in the source's sense. The differences are these.

* Ancillas are sites of the ring, of the same local dimension as the system: a preparation
  of a state of the system with its ancillas left in `|0⟩` is a preparation of the
  corresponding state of the ring. The source's free local unitaries, acting on a site and
  its ancillas, are counted here as gates of the circuits.
* Any site may be measured; in the source a qudit is measured after a free local unitary
  swaps it into an ancilla.
* The measurement is in the computational basis and is fixed in advance. The source
  measures the ancillas one after the other in orthonormal bases that may depend on the
  earlier outcomes; a measurement in another product basis is a computational-basis
  measurement after one layer of single-site unitaries.
* The corrections are local circuits whose layers are counted; in the source they are free
  local unitaries.

The source performs a single round of measurements and corrections, and so does this
definition.

## Main definitions

* `MPSPreparation.outcomeProj` — the projection onto an outcome of a computational-basis
  measurement of a set of sites.
* `MPSPreparation.MeasurementProtocol` — product vector, first circuit, measured sites, and
  outcome-dependent correction circuits.
* `MPSPreparation.IsPreparedWithMeasurementsInDepth` — preparation with measurements in
  depth `T`.

## Main results

* `MPSPreparation.sum_outcomeProj` — the outcome projections sum to the identity.
* `MPSPreparation.MeasurementProtocol.Prepares.ne_zero` — a prepared vector is nonzero, so
  the definition is not vacuous.
* `MPSPreparation.isPreparedWithMeasurementsInDepth_of_isPreparedInDepth`,
  `MPSPreparation.isPreparedInDepth_of_prepares_of_measured_eq_empty` — without
  measurements, preparation with measurements is preparation by a local circuit.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), main text, paragraph "Quantum circuits and
  LOCC" and Definition "Transformations under QC and LOCC".
* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Preparations using measurements".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ}

/-- The projection onto the outcome `m` of a measurement of the sites `S` in the
computational basis: the diagonal projection onto the configurations agreeing with `m`
on `S`.

Source: arXiv:2103.13367, paragraph "Quantum circuits and LOCC" ("local (orthogonal)
measurements"). -/
noncomputable def outcomeProj (S : Finset (Fin N)) (m : S → Fin d) :
    Matrix (Cfg d N) (Cfg d N) ℂ :=
  diagonal fun x => if ∀ i : S, x i = m i then 1 else 0

theorem outcomeProj_mulVec_apply (S : Finset (Fin N)) (m : S → Fin d) (v : Cfg d N → ℂ)
    (x : Cfg d N) :
    (outcomeProj S m *ᵥ v) x = if ∀ i : S, x i = m i then v x else 0 := by
  simp [outcomeProj, mulVec_diagonal]

/-- The outcome projections of a measurement sum to the identity. -/
theorem sum_outcomeProj (S : Finset (Fin N)) :
    ∑ m : S → Fin d, outcomeProj S m = 1 := by
  classical
  have h : ∀ x : Cfg d N, ∑ m : S → Fin d, (if ∀ i : S, x i = m i then (1 : ℂ) else 0) = 1 := by
    intro x
    have hiff : ∀ m : S → Fin d, (∀ i : S, x i = m i) ↔ (fun i : S => x i) = m := fun m =>
      ⟨fun h => funext h, fun h i => congrFun h i⟩
    simp only [hiff]
    simp
  ext x y
  rw [Matrix.sum_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [outcomeProj, diagonal_apply_eq, one_apply_eq]
    exact h x
  · simp [outcomeProj, diagonal_apply_ne _ hxy, one_apply_ne hxy]

/-- Measuring no site: the only outcome projection is the identity. -/
theorem outcomeProj_empty (m : (∅ : Finset (Fin N)) → Fin d) : outcomeProj ∅ m = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [outcomeProj]
  · simp [outcomeProj, diagonal_apply_ne _ hxy, one_apply_ne hxy]

/-- A scalar multiple of a product vector is a product vector: the scalar is absorbed into
the vector of one site. -/
theorem smul_productVector (c : ℂ) (v : Fin N → Fin d → ℂ) (i : Fin N) :
    c • productVector v = productVector (Function.update v i (c • v i)) := by
  classical
  funext x
  simp only [productVector, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, Pi.smul_apply,
    smul_eq_mul, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem eq_zero_of_mem_unitary_of_mulVec_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) {v : n → ℂ} (h : U *ᵥ v = 0) :
    v = 0 := by
  rw [← one_mulVec v, ← Unitary.star_mul_self_of_mem hU, ← mulVec_mulVec, h, mulVec_zero]

/-! ### Measurement-assisted protocols -/

variable [NeZero N]

/-- A measurement-assisted preparation protocol on the ring of `N` sites: a product vector, a
local circuit applied to it, a set of sites measured in the computational basis, and, for
every outcome string, a local circuit applied after the measurement. The circuits are lists
of layers, the head of the list applied first.

Source: arXiv:2103.13367, paragraph "Quantum circuits and LOCC": "We first apply a depth-`ℓ`
circuit ... Then, we sequentially measure each ancilla ... and apply `U` depending on the
outcomes of all previous measurements". -/
structure MeasurementProtocol (d N : ℕ) [NeZero N] where
  /-- The site vectors of the product vector the protocol starts from. -/
  initial : Fin N → Fin d → ℂ
  /-- The local circuit applied before the measurement. -/
  first : List (Layer d N)
  /-- The sites measured in the computational basis. -/
  measured : Finset (Fin N)
  /-- The local circuit applied after the outcome `m`; it may depend on the whole outcome
  string. -/
  correction : (measured → Fin d) → List (Layer d N)

namespace MeasurementProtocol

variable (P : MeasurementProtocol d N)

/-- The vector before the measurement: the first circuit applied to the product vector. -/
noncomputable def preMeasurement : Cfg d N → ℂ :=
  circuitOp P.first *ᵥ productVector P.initial

/-- The unnormalized vector after the outcome `m`; its squared norm is the probability of `m`
times that of the product vector. -/
noncomputable def postMeasurement (m : P.measured → Fin d) : Cfg d N → ℂ :=
  outcomeProj P.measured m *ᵥ P.preMeasurement

/-- The vector after the outcome `m` and its correction. -/
noncomputable def output (m : P.measured → Fin d) : Cfg d N → ℂ :=
  circuitOp (P.correction m) *ᵥ P.postMeasurement m

/-- The protocol prepares `ψ`: it starts from a nonzero product vector, and after every
outcome of nonzero probability the corrected vector is a scalar multiple of `ψ`.

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC" (the state
is prepared "deterministically"). -/
def Prepares (ψ : Cfg d N → ℂ) : Prop :=
  productVector P.initial ≠ 0 ∧
    ∀ m, P.postMeasurement m ≠ 0 → ∃ c : ℂ, P.output m = c • ψ

theorem sum_postMeasurement : ∑ m, P.postMeasurement m = P.preMeasurement := by
  simp only [postMeasurement, ← sum_mulVec, sum_outcomeProj, one_mulVec]

theorem preMeasurement_ne_zero (h : productVector P.initial ≠ 0) : P.preMeasurement ≠ 0 :=
  fun h0 => h (eq_zero_of_mem_unitary_of_mulVec_eq_zero (circuitOp_mem_unitary _) h0)

/-- Some outcome has nonzero probability. -/
theorem exists_postMeasurement_ne_zero (h : productVector P.initial ≠ 0) :
    ∃ m, P.postMeasurement m ≠ 0 := by
  by_contra hc
  have hc' : ∀ m, P.postMeasurement m = 0 := fun m => not_not.mp fun h => hc ⟨m, h⟩
  exact P.preMeasurement_ne_zero h (by rw [← sum_postMeasurement]; simp [hc'])

theorem output_ne_zero {m : P.measured → Fin d} (hm : P.postMeasurement m ≠ 0) :
    P.output m ≠ 0 :=
  fun h0 => hm (eq_zero_of_mem_unitary_of_mulVec_eq_zero (circuitOp_mem_unitary _) h0)

/-- A vector prepared by a protocol is nonzero. -/
theorem Prepares.ne_zero {ψ : Cfg d N → ℂ} (h : P.Prepares ψ) : ψ ≠ 0 := by
  obtain ⟨m, hm⟩ := P.exists_postMeasurement_ne_zero h.1
  obtain ⟨c, hc⟩ := h.2 m hm
  intro hψ
  exact P.output_ne_zero hm (by rw [hc, hψ, smul_zero])

end MeasurementProtocol

/-- A vector `ψ` is *prepared with measurements in depth `T`* when a measurement-assisted
protocol prepares it and, for every outcome, the circuits before and after the measurement
have at most `T` layers together.

Source: arXiv:2103.13367, Definition "Transformations under QC and LOCC" (`QCcc_ℓ`), and
arXiv:2307.01696, paragraph "Preparations using measurements". -/
def IsPreparedWithMeasurementsInDepth (T : ℕ) (ψ : Cfg d N → ℂ) : Prop :=
  ∃ P : MeasurementProtocol d N,
    (∀ m, P.first.length + (P.correction m).length ≤ T) ∧ P.Prepares ψ

/-- **Circuits are protocols without measurements.** A nonzero vector prepared by a local
circuit of depth `T` is prepared with measurements in depth `T`, measuring no site. -/
theorem isPreparedWithMeasurementsInDepth_of_isPreparedInDepth {T : ℕ} {ψ : Cfg d N → ℂ}
    (hψ : IsPreparedInDepth T ψ) (hψ0 : ψ ≠ 0) : IsPreparedWithMeasurementsInDepth T ψ := by
  obtain ⟨U, ⟨Ls, hl, rfl⟩, v, rfl⟩ := hψ
  refine ⟨⟨v, Ls, ∅, fun _ => []⟩, fun _ => by simp [hl], fun h0 => hψ0 (by simp [h0]),
    fun m _ => ⟨1, ?_⟩⟩
  simp [MeasurementProtocol.output, MeasurementProtocol.postMeasurement,
    MeasurementProtocol.preMeasurement, outcomeProj_empty, circuitOp]

/-- **Protocols without measurements are circuits.** A protocol measuring no site prepares
only vectors prepared by a local circuit of the same depth. -/
theorem isPreparedInDepth_of_prepares_of_measured_eq_empty {T : ℕ} {ψ : Cfg d N → ℂ}
    (P : MeasurementProtocol d N) (hP : P.measured = ∅)
    (hT : ∀ m, P.first.length + (P.correction m).length ≤ T) (h : P.Prepares ψ) :
    IsPreparedInDepth T ψ := by
  obtain ⟨m, hm⟩ := P.exists_postMeasurement_ne_zero h.1
  obtain ⟨c, hc⟩ := h.2 m hm
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact P.output_ne_zero hm (by rw [hc, zero_smul])
  have hpost : P.postMeasurement m = P.preMeasurement := by
    have hall : ∀ (x : Cfg d N) (i : P.measured), x i = m i := fun x i =>
      absurd i.2 (by simp [hP])
    have : outcomeProj P.measured m = 1 := by
      ext x y
      simp only [outcomeProj, diagonal_apply, one_apply, hall, implies_true, ite_true]
    rw [MeasurementProtocol.postMeasurement, this, one_mulVec]
  have hcirc : IsCircuitOn (Set.univ : Set (Fin N)) T
      (circuitOp (P.first ++ P.correction m)) :=
    IsCircuitOn.mono ⟨P.first ++ P.correction m, rfl,
      fun _ _ _ _ => Set.subset_univ _, rfl⟩ (by simpa using hT m)
  refine ⟨_, hcirc.isLocalCircuitOfDepth, Function.update P.initial 0 (c⁻¹ • P.initial 0), ?_⟩
  rw [← smul_productVector, mulVec_smul, circuitOp_append, ← mulVec_mulVec]
  change ψ = c⁻¹ • (circuitOp (P.correction m) *ᵥ P.preMeasurement)
  rw [← hpost, ← MeasurementProtocol.output, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end MPSPreparation
