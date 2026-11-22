/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FiniteGroupDetectorCircuit
import TNLean.MPS.MPU.FiniteGroupDetectorTensor

/-!
# A single retained circuit realizing the even cyclic obstruction

The circuit is fixed before the interval is chosen. Retaining its nominal
two-site gates in each interval gives exactly `detectorIntervalTensor`.
Consequently the complete interval word obtained from this one circuit has
value `-1` at every positive even cyclic order in the clock/shift instance.

This is the explicit family in the endpoint audit of arXiv:2405.00439,
Section V, lines 2081–2087 and `detectG`, lines 2108–2117. It is not a proof
of the source's anomaly detection claim for arbitrary circuit truncations.
-/

open Matrix

namespace MPOTensor.FiniteGroupDetector

variable {d N : ℕ} [NeZero N]

/-- The interval obtained by deleting gates outside the indicated cells of
one fixed depth-two circuit. Source context: arXiv:2405.00439, Section V,
lines 2081–2087. -/
noncomputable def detectorRetainedInterval (u w : unitary (Matrix (Fin d) (Fin d) ℂ))
    (M : ℕ) [NeZero M] (a b : ℕ) : Matrix (Fin M × Bool → Fin d) (Fin M × Bool → Fin d) ℂ :=
  (dressedPairCircuit (cellSuccessor M) u w
    (Finset.univ.filter fun k ↦ a ≤ k.val ∧ k.val ≤ b)).op

/-- Gate deletion gives the specified dressed tensor interval, with the
identity proved from the layer products and the interval geometry.
Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
theorem detectorRetainedInterval_eq_intervalTensor
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) (a b : ℕ) (hab : a ≤ b) (hb : b + 1 < N) :
    detectorRetainedInterval u w N a b = detectorIntervalTensor u w N a b := by
  let a' : Fin N := ⟨a, by omega⟩
  let b' : Fin N := ⟨b, by omega⟩
  have hab' : a' ≤ b' := hab
  have hset : (Finset.univ.filter fun k : Fin N ↦ a ≤ k.val ∧ k.val ≤ b) =
      Finset.Icc a' b' := by
    ext k
    simp [a', b', Fin.le_def]
  rw [detectorRetainedInterval, hset,
    op_dressedPairCircuit_single_entry (cellSuccessor N) u w _ a'
      (Finset.mem_Icc.mpr ⟨le_rfl, hab'⟩)
      (cellSuccessor_Icc_single_entry a' b' (Or.inr hb)),
    detectorIntervalTensor, rectKronecker_mul]
  congr 1
  funext s
  rcases s with ⟨k, leg⟩
  cases leg <;> by_cases hk : a ≤ k.val ∧ k.val ≤ b <;>
    by_cases hka : k.val = a <;>
    simp [intervalSiteFactor, a', b', Finset.mem_Icc, Fin.le_def, Fin.ext_iff, hk, hka, hab]

/-- The complete detector word formed from intervals of the same fixed
circuit. Source: arXiv:2405.00439, `detectG`, lines 2108–2117, with the
chronological forward convention of the endpoint audit. -/
noncomputable def detectorCircuitWord (u w : unitary (Matrix (Fin d) (Fin d) ℂ))
    (m M : ℕ) [NeZero M] : Matrix (Fin M × Bool → Fin d) (Fin M × Bool → Fin d) ℂ :=
  (detectorRetainedInterval u w M 0 (2 * m + 1))ᴴ *
    ((List.range m).map fun r ↦ (detectorRetainedInterval u w M (r + 1) (2 * m - r))ᴴ).prod *
    ((List.range m).map fun r ↦ detectorRetainedInterval u w M (r + 1) (m + 2 + r)).prod *
    detectorRetainedInterval u w M 0 (m + 1)

/-- The complete word of actual retained circuit operators equals the tensor
word evaluated in the spatial construction. No circuit-to-interval identity
is assumed. Source context: arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorCircuitWord_eq_tensorWord (u w : unitary (Matrix (Fin d) (Fin d) ℂ))
    (m : ℕ) (hN : 2 * m + 2 < N) :
    detectorCircuitWord u w m N = detectorTensorWord u w m N := by
  have hback : ((List.range m).map fun r ↦
      (detectorRetainedInterval u w N (r + 1) (2 * m - r))ᴴ) =
      ((List.range m).map fun r ↦ (detectorIntervalTensor u w N (r + 1) (2 * m - r))ᴴ) := by
    refine List.map_congr_left fun r hr ↦ ?_
    have hrm := List.mem_range.mp hr
    rw [detectorRetainedInterval_eq_intervalTensor u w _ _ (by omega) (by omega)]
  have hforward : ((List.range m).map fun r ↦
      detectorRetainedInterval u w N (r + 1) (m + 2 + r)) =
      ((List.range m).map fun r ↦ detectorIntervalTensor u w N (r + 1) (m + 2 + r)) := by
    refine List.map_congr_left fun r hr ↦ ?_
    have hrm := List.mem_range.mp hr
    exact detectorRetainedInterval_eq_intervalTensor u w _ _ (by omega) (by omega)
  rw [detectorCircuitWord, detectorTensorWord, hback, hforward,
    detectorRetainedInterval_eq_intervalTensor u w 0 (2 * m + 1) (by omega) hN,
    detectorRetainedInterval_eq_intervalTensor u w 0 (m + 1) (by omega) (by omega)]

private noncomputable def detectorFinReindex (m : ℕ) [NeZero m] :
    unitary (Matrix (ZMod m) (ZMod m) ℂ) →* unitary (Matrix (Fin m) (Fin m) ℂ) where
  toFun u := ⟨Matrix.reindex (ZMod.finEquiv m).toEquiv.symm (ZMod.finEquiv m).toEquiv.symm u,
    Matrix.reindex_mem_unitaryGroup (ZMod.finEquiv m).toEquiv.symm _ u.property⟩
  map_one' := Subtype.ext (map_one (Matrix.reindexAlgEquiv ℂ ℂ (ZMod.finEquiv m).toEquiv.symm))
  map_mul' u v := Subtype.ext
    (map_mul (Matrix.reindexAlgEquiv ℂ ℂ (ZMod.finEquiv m).toEquiv.symm)
      (u : Matrix (ZMod m) (ZMod m) ℂ) (v : Matrix (ZMod m) (ZMod m) ℂ))

/-- The existing cyclic shift reindexed by the standard finite labels used by
the circuit library. Source context: the endpoint audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
noncomputable def detectorShiftFin (m : ℕ) [NeZero m] :
    unitary (Matrix (Fin m) (Fin m) ℂ) := detectorFinReindex m (detectorShift m)

/-- The existing clock reindexed by the standard finite circuit labels.
Source context: the endpoint audit of arXiv:2405.00439, `detectG`. -/
noncomputable def detectorClockFin {m : ℕ} [NeZero m] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    unitary (Matrix (Fin m) (Fin m) ℂ) := detectorFinReindex m (detectorClock hζ)

/-- The finite circuit's bulk shift has the specified cyclic period.
Source context: the cyclic construction in the endpoint audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorShiftFin_pow_order (m : ℕ) [NeZero m] : detectorShiftFin m ^ m = 1 := by
  rw [detectorShiftFin, ← map_pow, detectorShift_pow_order, map_one]

/-- Every positive even cyclic order has a fixed depth-two circuit whose
retained intervals give a complete detector equal to minus the identity.
The clock and shift, all retained layers, the interval comparison, and the
full spatial tensor word are constructed, with no whole-detector phase
hypothesis. Source context: the explicit obstruction to arbitrary circuit
truncations in the endpoint audit of arXiv:2405.00439, `detectG`. -/
theorem detectorCircuitWord_clock_even {k : ℕ} [NeZero (2 * k)] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * k)) (hN : 2 * (2 * k) + 2 < N) :
    detectorCircuitWord (detectorShiftFin (2 * k)) (detectorClockFin hζ) (2 * k) N = -1 := by
  have hk : k ≠ 0 := by
    intro h
    exact NeZero.ne (2 * k) (by simp [h])
  have hm : 1 < 2 * k := by omega
  let f := detectorFinReindex (2 * k)
  let c := f (detectorClockPhase hζ)
  have hc : Commute c (detectorShiftFin (2 * k)) :=
    (detectorClockPhase_commute hζ hm).map f
  have hconj : (detectorClockFin hζ)⁻¹ * detectorShiftFin (2 * k) * detectorClockFin hζ =
      c * detectorShiftFin (2 * k) := by
    change (f (detectorClock hζ))⁻¹ * f (detectorShift (2 * k)) * f (detectorClock hζ) =
      f (detectorClockPhase hζ) * f (detectorShift (2 * k))
    simpa only [map_mul, map_inv] using congrArg f (detectorClock_conjugation hζ)
  have hscalar : (c : Matrix (Fin (2 * k)) (Fin (2 * k)) ℂ) = ζ • 1 := by
    change Matrix.reindexAlgEquiv ℂ ℂ (ZMod.finEquiv (2 * k)).toEquiv.symm
      (detectorClockPhase hζ : Matrix (ZMod (2 * k)) (ZMod (2 * k)) ℂ) = ζ • 1
    rw [detectorClockPhase_coe hζ hm, map_smul, map_one]
  rw [detectorCircuitWord_eq_tensorWord _ _ (2 * k) hN,
    detectorTensorWord_eq_smul _ _ c ζ hc hconj hscalar (2 * k) N hN,
    detectorRoot_triangular_even hζ, neg_one_smul]

/-- The complete detector of the single fixed circuit has expectation minus
one in every normalized state at positive even cyclic order. Source context:
the explicit obstruction in the endpoint audit of arXiv:2405.00439, `detectG`.
This does not identify the value with an anomaly or a domain-wall invariant. -/
theorem star_dotProduct_detectorCircuitWord_clock_even {k : ℕ} [NeZero (2 * k)] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * k)) (hN : 2 * (2 * k) + 2 < N)
    {ψ : (Fin N × Bool → Fin (2 * k)) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ (detectorCircuitWord (detectorShiftFin (2 * k)) (detectorClockFin hζ)
      (2 * k) N *ᵥ ψ) = -1 := by
  rw [detectorCircuitWord_clock_even hζ hN, neg_mulVec, one_mulVec, dotProduct_neg, hψ]

/-- Every positive even cyclic order admits the claimed concrete circuit,
without a primitive root supplied as an additional hypothesis. The root is
constructed as the complex exponential, and all interval operators come from
this one depth-two circuit. Source context: the explicit obstruction family
in the endpoint audit of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem exists_detectorCircuitWord_even (k : ℕ) [NeZero (2 * k)]
    (hN : 2 * (2 * k) + 2 < N) :
    ∃ u w : unitary (Matrix (Fin (2 * k)) (Fin (2 * k)) ℂ),
      u ^ (2 * k) = 1 ∧
      (dressedPairCircuit (cellSuccessor N) u w Finset.univ).layers.length = 2 ∧
      (dressedPairCircuit (cellSuccessor N) u w Finset.univ).op =
        rectKronecker (fun _ : Fin N × Bool ↦ (u : Matrix (Fin (2 * k)) (Fin (2 * k)) ℂ)) ∧
      detectorCircuitWord u w (2 * k) N = -1 := by
  let hζ := Complex.isPrimitiveRoot_exp (2 * k) (NeZero.ne (2 * k))
  exact ⟨detectorShiftFin (2 * k), detectorClockFin hζ, detectorShiftFin_pow_order (2 * k),
    dressedPairCircuit_length _ _ _ _, op_dressedPairCircuit_univ _ _ _,
    detectorCircuitWord_clock_even hζ hN⟩

end MPOTensor.FiniteGroupDetector
