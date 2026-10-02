/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CircuitComposition
import TNLean.MPS.Preparation.ControlledGates

/-!
# Local circuits assisted by measurements

A measurement-assisted preparation on the ring of `N` sites starts from a product vector,
applies a local circuit, measures a set `S` of sites in the computational basis, and then,
for every outcome string `m`, applies a product of single-site unitaries chosen according to
`m`. It prepares `ψ` in depth `T` when every outcome of nonzero probability leaves the chain in
`ψ` up to a nonzero scalar (phase and normalization), and the circuit before the measurement
has at most `T` layers. Only the layers of that circuit are counted: the measurement, the
classical processing of its outcomes, and the single-site corrections are free.

This is the class `QCcc` of Piroli, Styliaris and Cirac (arXiv:2103.13367, paragraphs
"Quantum circuits and LOCC" and "State transformations with QC and LOCC", and Definition
"Transformations under QC and LOCC"). In the words of arXiv:2103.13367, a depth-`ℓ` circuit
is followed by measurements and by local unitaries: "apply `U ∈ LU` depending on the outcomes
of all previous measurements", the outcomes being "classically communicated among all the
qudits". The correction applied at a site may therefore depend on the whole outcome string,
not only on outcomes measured nearby: classical communication is global and free. In the
Example 1 preparation of the GHZ state the correction at the site `n` is
`X^{k₂ + ⋯ + kₙ}`, which depends on outcomes at every distance.

The paragraph "Preparations using measurements" of arXiv:2307.01696 states the idea,
"Measurements and subsequent conditional unitaries can make state preparation much faster",
without fixing a model and without citing arXiv:2103.13367; that paper cites
arXiv:2103.13367 for the constant-depth preparation of GHZ-like states (paragraph
"Long-range MPS using measurements" and the paragraph after eq. (19)).

This differs from the relation `MPSPreparation.IsLocalChannelConversion`
(`TNLean.MPS.Preparation.LocalChannelConversion`), which models the circuits of arXiv:2307.01696
with ancillas and local operations but without measurements and without classical
communication: there every step is a local channel, and connected correlations beyond the
light cone vanish (`trace_mul_mul_eq_of_isLocalChannelConversion`). Global classical
communication breaks this light cone, which is why GHZ-type states, whose connected
correlations do not decay, can be prepared in constant depth with measurements
(`TNLean.MPS.Preparation.GHZMeasurement`).

## Conventions

Every protocol of this model is a protocol of arXiv:2103.13367, of no larger depth, so a
preparation proved here is a preparation in the sense of that paper. The differences are
these.

* Ancillas are sites of the ring, of the same local dimension as the system: a preparation
  of a state of the system with its ancillas left in `|0⟩` is a preparation of the
  corresponding state of the ring. The free local unitaries of arXiv:2103.13367 between the
  layers of the circuit, acting on a site and its ancillas, are counted here as gates of the
  circuit.
* Any site may be measured; in arXiv:2103.13367 a qudit is measured after a free local
  unitary swaps it into an ancilla, and the correction swaps it back.
* The measurement is in the computational basis and is fixed in advance. arXiv:2103.13367
  measures the ancillas one after the other in orthonormal bases that may depend on the
  earlier outcomes; a measurement in another product basis is a computational-basis
  measurement after one layer of single-site unitaries.
* The correction is a product of single-site unitaries of the ring, applied once after all
  the measurements; in arXiv:2103.13367 it is a local unitary, acting on a site and its
  ancillas, and one may be applied after each measurement.

arXiv:2103.13367 performs a single round of measurements and corrections, and so does this
definition.

## Main definitions

* `MPSPreparation.outcomeProj` — the projection onto an outcome of a computational-basis
  measurement of a set of sites.
* `MPSPreparation.MeasurementProtocol` — product vector, circuit, measured sites, and
  outcome-dependent single-site corrections.
* `MPSPreparation.IsPreparedWithMeasurementsInDepth` — preparation with measurements in
  depth `T`.

## Main results

* `MPSPreparation.sum_outcomeProj` — the outcome projections sum to the identity.
* `MPSPreparation.MeasurementProtocol.IsPreparationOf.ne_zero` — a prepared vector is
  nonzero, so the definition is not vacuous.
* `MPSPreparation.isPreparedWithMeasurementsInDepth_of_isPreparedInDepth`,
  `MPSPreparation.exists_isPreparedInDepth_of_isPreparationOf_of_measured_eq_empty` — without
  measurements, preparation with measurements is preparation by a local circuit, up to
  single-site unitaries.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), main text, paragraphs "Quantum circuits and
  LOCC" and "State transformations with QC and LOCC", and Definition "Transformations under
  QC and LOCC".
* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraphs "Preparations using
  measurements" and "Long-range MPS using measurements".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ}

/-- The projection onto the outcome `m` of a measurement of the sites `S` in the
computational basis: the diagonal projection onto the configurations agreeing with `m`
on `S`. It is `MPSPreparation.ctrlProj S c` for every configuration `c` extending `m`
(`MPSPreparation.outcomeProj_eq_ctrlProj`); the outcome is indexed by `S → Fin d` so that
the outcomes of the measurement are the strings on `S`.

Source: arXiv:2103.13367, paragraph "Quantum circuits and LOCC" ("local (orthogonal)
measurements"). -/
noncomputable def outcomeProj (S : Finset (Fin N)) (m : S → Fin d) :
    Matrix (Cfg d N) (Cfg d N) ℂ :=
  diagonal fun x => if ∀ i : S, x i = m i then 1 else 0

theorem outcomeProj_eq_ctrlProj (S : Finset (Fin N)) (m : S → Fin d) (c : Cfg d N)
    (hc : ∀ i : S, c i = m i) : outcomeProj S m = ctrlProj S c := by
  unfold outcomeProj ctrlProj
  congr 1
  funext x
  refine if_congr ⟨fun h i hi => ?_, fun h i => ?_⟩ rfl rfl
  · rw [h ⟨i, hi⟩, hc ⟨i, hi⟩]
  · rw [h i i.2, hc i]

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

/-- Measuring no site leaves every vector unchanged. -/
private theorem outcomeProj_mulVec_of_isEmpty {S : Finset (Fin N)} [IsEmpty S] (m : S → Fin d)
    (v : Cfg d N → ℂ) : outcomeProj S m *ᵥ v = v := by
  funext x
  rw [outcomeProj_mulVec_apply]
  exact ite_eq_left fun i => isEmptyElim i

/-- A product of single-site unitaries is unitary. -/
theorem finKronecker_mem_unitary {u : Fin N → Matrix (Fin d) (Fin d) ℂ}
    (hu : ∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    finKronecker u ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ) := by
  rw [Unitary.mem_iff, star_eq_conjTranspose, finKronecker_conjTranspose, finKronecker_mul,
    finKronecker_mul]
  simp only [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem (hu _),
    Unitary.mul_star_self_of_mem (hu _), finKronecker_one, and_self]

/-- A unitary matrix maps only the zero vector to zero. -/
theorem eq_zero_of_mem_unitary_of_mulVec_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) {v : n → ℂ} (h : U *ᵥ v = 0) :
    v = 0 := by
  rw [← one_mulVec v, ← Unitary.star_mul_self_of_mem hU, ← mulVec_mulVec, h, mulVec_zero]

/-! ### Measurement-assisted protocols -/

variable [NeZero N]

/-- A measurement-assisted preparation protocol on the ring of `N` sites: a product vector, a
local circuit applied to it, a set of sites measured in the computational basis, and, for
every outcome string, a unitary at every site applied after the measurement. The circuit is
a list of layers, the head of the list applied first.

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC": "We first apply
a depth-`ℓ` circuit, with possibly local unitaries acting in between different layers of
gates ... Then, we sequentially measure each ancilla `a_i` in some orthonormal basis ... and
apply `U ∈ LU` depending on the outcomes of all previous measurements". -/
structure MeasurementProtocol (d N : ℕ) [NeZero N] where
  /-- The site vectors of the product vector the protocol starts from. -/
  initial : Fin N → Fin d → ℂ
  /-- The local circuit applied before the measurement. -/
  first : List (Layer d N)
  /-- The sites measured in the computational basis. -/
  measured : Finset (Fin N)
  /-- The unitary applied at the site `i` after the outcome `m`; it may depend on the whole
  outcome string. -/
  correction : (measured → Fin d) → Fin N → Matrix (Fin d) (Fin d) ℂ
  correction_mem_unitary : ∀ m i, correction m i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)

namespace MeasurementProtocol

variable (P : MeasurementProtocol d N)

/-- The vector before the measurement: the first circuit applied to the product vector. -/
noncomputable def preMeasurement : Cfg d N → ℂ :=
  circuitOp P.first *ᵥ productVector P.initial

/-- The unnormalized vector after the outcome `m`; its squared norm is the probability of `m`
times that of the product vector. -/
noncomputable def postMeasurement (m : P.measured → Fin d) : Cfg d N → ℂ :=
  outcomeProj P.measured m *ᵥ P.preMeasurement

/-- The vector after the outcome `m` and its correction, the product of the unitaries
`P.correction m i` over the sites `i`. -/
noncomputable def output (m : P.measured → Fin d) : Cfg d N → ℂ :=
  finKronecker (P.correction m) *ᵥ P.postMeasurement m

/-- The protocol prepares `ψ`: it starts from a nonzero product vector, and after every
outcome of nonzero probability the corrected vector is a scalar multiple of `ψ`.

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC" (the state
is prepared "deterministically"). -/
def IsPreparationOf (ψ : Cfg d N → ℂ) : Prop :=
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
  fun h0 => hm (eq_zero_of_mem_unitary_of_mulVec_eq_zero
    (finKronecker_mem_unitary (P.correction_mem_unitary m)) h0)

/-- A vector prepared by a protocol is nonzero. -/
theorem IsPreparationOf.ne_zero {ψ : Cfg d N → ℂ} (h : P.IsPreparationOf ψ) :
    ψ ≠ 0 := by
  obtain ⟨m, hm⟩ := P.exists_postMeasurement_ne_zero h.1
  obtain ⟨c, hc⟩ := h.2 m hm
  intro hψ
  exact P.output_ne_zero hm (by rw [hc, hψ, smul_zero])

end MeasurementProtocol

/-- A vector `ψ` is *prepared with measurements in depth `T`* when a measurement-assisted
protocol whose circuit has at most `T` layers prepares it.

Source: arXiv:2103.13367, Definition "Transformations under QC and LOCC" (`QCcc_ℓ`). -/
def IsPreparedWithMeasurementsInDepth (T : ℕ) (ψ : Cfg d N → ℂ) : Prop :=
  ∃ P : MeasurementProtocol d N, P.first.length ≤ T ∧ P.IsPreparationOf ψ

/-- **Circuits are protocols without measurements.** A nonzero vector prepared by a local
circuit of depth `T` is prepared with measurements in depth `T`, measuring no site. -/
theorem isPreparedWithMeasurementsInDepth_of_isPreparedInDepth {T : ℕ} {ψ : Cfg d N → ℂ}
    (hψ : IsPreparedInDepth T ψ) (hψ0 : ψ ≠ 0) : IsPreparedWithMeasurementsInDepth T ψ := by
  obtain ⟨U, ⟨Ls, hl, rfl⟩, v, rfl⟩ := hψ
  refine ⟨⟨v, Ls, ∅, fun _ _ => 1, fun _ _ => one_mem _⟩, hl.le,
    fun h0 => hψ0 (by simp [h0]), fun m _ => ⟨1, ?_⟩⟩
  change finKronecker (fun _ => 1) *ᵥ (outcomeProj ∅ m *ᵥ (circuitOp Ls *ᵥ productVector v)) =
    (1 : ℂ) • (circuitOp Ls *ᵥ productVector v)
  rw [outcomeProj_mulVec_of_isEmpty, finKronecker_one, one_mulVec, one_smul]

/-- **Protocols without measurements are circuits up to single-site unitaries.** If a protocol
measuring no site, with at most `T` layers, prepares `ψ`, then some product of single-site
unitaries takes `ψ` to a vector prepared by a local circuit of depth `T`. -/
theorem exists_isPreparedInDepth_of_isPreparationOf_of_measured_eq_empty {T : ℕ} {ψ : Cfg d N → ℂ}
    (P : MeasurementProtocol d N) (hP : P.measured = ∅) (hT : P.first.length ≤ T)
    (h : P.IsPreparationOf ψ) :
    ∃ u : Fin N → Matrix (Fin d) (Fin d) ℂ, (∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) ∧
      IsPreparedInDepth T (finKronecker u *ᵥ ψ) := by
  obtain ⟨m, hm⟩ := P.exists_postMeasurement_ne_zero h.1
  obtain ⟨c, hc⟩ := h.2 m hm
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact P.output_ne_zero hm (by rw [hc, zero_smul])
  have : IsEmpty P.measured := by rw [hP]; infer_instance
  have hpost : P.postMeasurement m = P.preMeasurement :=
    outcomeProj_mulVec_of_isEmpty m _
  have hcirc : IsCircuitOn (Set.univ : Set (Fin N)) T (circuitOp P.first) :=
    IsCircuitOn.mono ⟨P.first, rfl, fun _ _ _ _ => Set.subset_univ _, rfl⟩ hT
  refine ⟨fun i => star (P.correction m i),
    fun i => Unitary.star_mem (P.correction_mem_unitary m i),
    _, hcirc.isLocalCircuitOfDepth, Function.update P.initial 0 (c⁻¹ • P.initial 0), ?_⟩
  rw [← smul_productVector, mulVec_smul]
  have hψ : ψ = c⁻¹ • P.output m := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hψ, mulVec_smul, MeasurementProtocol.output, mulVec_mulVec, hpost]
  have hstar : finKronecker (fun i => star (P.correction m i)) *
      finKronecker (P.correction m) = 1 := by
    rw [finKronecker_mul]
    simp only [Unitary.star_mul_self_of_mem (P.correction_mem_unitary m _), finKronecker_one]
  rw [hstar, one_mulVec]
  rfl

end MPSPreparation
