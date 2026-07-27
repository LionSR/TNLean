/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KoashiImoto.SingleWitness
import TNLean.Channel.FixedPoint.MeanErgodicAdjoint

/-!
# HJPW's mean-ergodic projection onto the common invariant algebra

HJPW, arXiv:quant-ph/0304007v2, lines 838-851, introduces a Cesàro-limit projection `P_0^*`
onto `A_0`. This file defines the corresponding map as the trace-pairing adjoint of the
finite-dimensional Schrödinger mean-ergodic projection for the single witness `F_0` from
`Kraus.exists_preservingKrausFamily_adjointFixedPointsStarSubalgebra_eq`. The machinery in
`TNLean.Analysis.MeanErgodic` and `TNLean.Channel.FixedPoint.MeanErgodicAdjoint` proves that this
map is a positive, unital, idempotent retraction onto the adjoint fixed points. A bridge lemma
identifies the trace-pairing adjoint of a Schrödinger Kraus map with its Heisenberg adjoint
`Kraus.adjointMap`.

This file does not prove that the Cesàro averages of the Heisenberg iterates converge to the
packaged map; that source identity remains a separate analytic statement.

## Main declarations

* `Kraus.isPositiveMap_mapLM`: the Schrödinger action of any Kraus family is a positive map
  (it is completely positive).
* `Kraus.isTracePreservingMap_mapLM_of_isTP`: a trace-preserving Kraus family's Schrödinger
  action is a trace-preserving map.
* `Matrix.traceAdjointMap_mapLM`: the trace-pairing adjoint of a Kraus family's Schrödinger
  action is its Heisenberg adjoint map.
* `Kraus.commonInvariantMeanErgodicProjection`: HJPW's `P_0^*`, the mean-ergodic projection of
  the single witness `F_0`'s Heisenberg adjoint, derived via
  `IsPositiveMap.traceAdjoint_meanErgodicProjection_isPositiveUnitalRetraction`.
* `Kraus.commonInvariantMeanErgodicProjection_isPositiveMap`,
  `Kraus.commonInvariantMeanErgodicProjection_one`,
  `Kraus.commonInvariantMeanErgodicProjection_idempotent`: positivity, unitality, and
  idempotence of `P_0^*`.
* `Kraus.mem_range_commonInvariantMeanErgodicProjection_iff`: the range (equivalently, the
  fixed-point set) of `P_0^*` is exactly the common invariant algebra `A_0`.

**Scope restriction (joint support):** inherits the `PosDef (commonAverage ρ)` hypothesis of
`commonInvariantStarSubalgebra` in place of HJPW's joint-support reduction
(arXiv:quant-ph/0304007v2, lines 761-763). Documented in
`docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex`.

As in `SingleWitness.lean`, the declarations below state the finite state-family instances in
their own signatures so that dependent projections through the bundled witness remain stable
during elaboration.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.Frobenius
open Matrix Finset Complex

namespace Kraus

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

section Bridge

variable {d : ℕ}

/-- **A Kraus family's Schrödinger action is completely positive.**

`map K X = ∑ i, K i X (K i)ᴴ` is literally a Kraus sum, witnessing `IsCPMap` directly. -/
theorem isCPMap_mapLM (K : Fin d → Mat) : IsCPMap (mapLM K) :=
  ⟨d, K, fun X => (mapLM_apply K X).trans (map_apply K X)⟩

/-- **A Kraus family's Schrödinger action is positive.**

Completely positive maps are positive (`IsCPMap.isPositiveMap`). -/
theorem isPositiveMap_mapLM (K : Fin d → Mat) : IsPositiveMap (mapLM K) :=
  (isCPMap_mapLM K).isPositiveMap

/-- **A trace-preserving Kraus family's Schrödinger action is a trace-preserving map.**

`tr(E(X)) = tr(1 · E(X)) = tr(E^*(1) · X) = tr(1 · X) = tr(X)`, using the weighted trace
identity `Kraus.trace_mul_map_eq_trace_adjointMap_mul` at `ρ := 1` and
`Kraus.adjointMap_one_of_isTP`. -/
theorem isTracePreservingMap_mapLM_of_isTP (K : Fin d → Mat) (h_tp : IsTP K) :
    IsTracePreservingMap (mapLM K) := by
  intro X
  show Matrix.trace (mapLM K X) = Matrix.trace X
  rw [mapLM_apply]
  have h1 : Matrix.trace ((1 : Mat) * map K X) = Matrix.trace (adjointMap K 1 * X) :=
    trace_mul_map_eq_trace_adjointMap_mul K 1 X
  rw [one_mul] at h1
  rw [h1, adjointMap_one_of_isTP K h_tp, one_mul]

/-- **The trace-pairing adjoint of a Kraus family's Schrödinger action is its Heisenberg
adjoint.**

Both `Matrix.traceAdjointMap (mapLM K)` and `adjointMapLM K` satisfy the same trace-pairing
characterization `tr(E^*(ρ) X) = tr(ρ E(X))` (`Matrix.trace_traceAdjointMap_mul` and
`Kraus.trace_mul_map_eq_trace_adjointMap_mul`), so they agree by nondegeneracy of the trace
pairing (`Matrix.ext_iff_trace_mul_right`). -/
theorem traceAdjointMap_mapLM (K : Fin d → Mat) :
    Matrix.traceAdjointMap (mapLM K) = adjointMapLM K := by
  apply LinearMap.ext
  intro ρ
  refine (Matrix.ext_iff_trace_mul_right
    (A := Matrix.traceAdjointMap (mapLM K) ρ) (B := adjointMapLM K ρ)).2 fun X => ?_
  rw [Matrix.trace_traceAdjointMap_mul, mapLM_apply, adjointMapLM_apply,
    trace_mul_map_eq_trace_adjointMap_mul]

end Bridge

section CommonInvariantProjection

/-- **HJPW's single witness `F_0`.**

arXiv:quant-ph/0304007v2, lines 846-849: the preserving Kraus family with `A_0 = A_{F_0}`,
given by `Kraus.exists_preservingKrausFamily_adjointFixedPointsStarSubalgebra_eq`. -/
noncomputable def commonInvariantKrausFamily {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx]
    {ρ : Kidx → Mat} (hρbar : (commonAverage ρ).PosDef) : PreservingKrausFamily ρ :=
  (exists_preservingKrausFamily_adjointFixedPointsStarSubalgebra_eq hρbar).choose

/-- The witness `F_0`'s adjoint fixed-point subalgebra is exactly `A_0`
(arXiv:quant-ph/0304007v2, lines 846-847). -/
theorem adjointFixedPointsStarSubalgebra_commonInvariantKrausFamily
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) :
    adjointFixedPointsStarSubalgebra (commonInvariantKrausFamily hρbar).Kfam
        (commonInvariantKrausFamily hρbar).isPreserving.1 hρbar
        (commonInvariantKrausFamily hρbar).map_commonAverage
      = commonInvariantStarSubalgebra ρ hρbar :=
  (exists_preservingKrausFamily_adjointFixedPointsStarSubalgebra_eq hρbar).choose_spec

/-- The Schrödinger action of the witness `F_0`, as a matrix endomorphism. -/
noncomputable def commonInvariantMapLM {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx]
    {ρ : Kidx → Mat} (hρbar : (commonAverage ρ).PosDef) : Mat →ₗ[ℂ] Mat :=
  mapLM (commonInvariantKrausFamily hρbar).Kfam

theorem isPositiveMap_commonInvariantMapLM {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx]
    {ρ : Kidx → Mat} (hρbar : (commonAverage ρ).PosDef) :
    IsPositiveMap (commonInvariantMapLM hρbar) :=
  isPositiveMap_mapLM _

theorem isTracePreservingMap_commonInvariantMapLM {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx]
    {ρ : Kidx → Mat} (hρbar : (commonAverage ρ).PosDef) :
    IsTracePreservingMap (commonInvariantMapLM hρbar) :=
  isTracePreservingMap_mapLM_of_isTP _ (commonInvariantKrausFamily hρbar).isPreserving.1

/-- **The packaged projection `P_0^*`.**

This is the trace-pairing adjoint of the finite-dimensional Schrödinger mean-ergodic projection
for the single witness `F_0`. Its positivity, unitality, idempotence, and range agree with HJPW's
projection onto `A_0` (arXiv:quant-ph/0304007v2, lines 838-851). The convergence of the
Heisenberg Cesàro averages to this map is not asserted here. -/
noncomputable def commonInvariantMeanErgodicProjection
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) : Mat →ₗ[ℂ] Mat :=
  Matrix.traceAdjointMap
    (LinearMap.meanErgodicProjection (commonInvariantMapLM hρbar)
      ((isPositiveMap_commonInvariantMapLM hρbar).hasBoundedOrbits_of_tracePreserving
        (isTracePreservingMap_commonInvariantMapLM hρbar)))

/-- The defining bundle of properties of `P_0^*`, transported directly from
`IsPositiveMap.traceAdjoint_meanErgodicProjection_isPositiveUnitalRetraction`. -/
theorem commonInvariantMeanErgodicProjection_bundle
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) :
    IsPositiveMap (commonInvariantMeanErgodicProjection hρbar) ∧
      commonInvariantMeanErgodicProjection hρbar 1 = 1 ∧
      (∀ Y, commonInvariantMeanErgodicProjection hρbar
          (commonInvariantMeanErgodicProjection hρbar Y) =
        commonInvariantMeanErgodicProjection hρbar Y) ∧
      LinearMap.range (commonInvariantMeanErgodicProjection hρbar) =
        LinearMap.ker (Matrix.traceAdjointMap (commonInvariantMapLM hρbar) - 1) ∧
      (∀ Y, commonInvariantMeanErgodicProjection hρbar Y = Y ↔
        Matrix.traceAdjointMap (commonInvariantMapLM hρbar) Y = Y) := by
  unfold commonInvariantMeanErgodicProjection
  exact IsPositiveMap.traceAdjoint_meanErgodicProjection_isPositiveUnitalRetraction
    (isPositiveMap_commonInvariantMapLM hρbar) (isTracePreservingMap_commonInvariantMapLM hρbar)

/-- **Positivity of `P_0^*`.** -/
theorem commonInvariantMeanErgodicProjection_isPositiveMap
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) :
    IsPositiveMap (commonInvariantMeanErgodicProjection hρbar) :=
  (commonInvariantMeanErgodicProjection_bundle hρbar).1

/-- **Unitality of `P_0^*`.** -/
theorem commonInvariantMeanErgodicProjection_one
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) :
    commonInvariantMeanErgodicProjection hρbar 1 = 1 :=
  (commonInvariantMeanErgodicProjection_bundle hρbar).2.1

/-- **Idempotence of `P_0^*`.** -/
theorem commonInvariantMeanErgodicProjection_idempotent
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) (Y : Mat) :
    commonInvariantMeanErgodicProjection hρbar (commonInvariantMeanErgodicProjection hρbar Y)
      = commonInvariantMeanErgodicProjection hρbar Y :=
  (commonInvariantMeanErgodicProjection_bundle hρbar).2.2.1 Y

/-- **The range of `P_0^*` is the common invariant algebra `A_0`.**

arXiv:quant-ph/0304007v2, line 843: `A_0` is the fixed-point set of every preserving operation's
adjoint map, in particular of `F_0^*`; the mean-ergodic projection `P_0^*` is idempotent with
range exactly that fixed-point set. -/
theorem mem_range_commonInvariantMeanErgodicProjection_iff
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) (Y : Mat) :
    Y ∈ LinearMap.range (commonInvariantMeanErgodicProjection hρbar) ↔
      Y ∈ commonInvariantStarSubalgebra ρ hρbar := by
  obtain ⟨-, -, -, hrange, -⟩ := commonInvariantMeanErgodicProjection_bundle hρbar
  rw [hrange, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  change Matrix.traceAdjointMap (mapLM (commonInvariantKrausFamily hρbar).Kfam) Y = Y ↔ _
  rw [traceAdjointMap_mapLM, adjointMapLM_apply, ← mem_adjointFixedPoints,
    ← mem_adjointFixedPointsStarSubalgebra (commonInvariantKrausFamily hρbar).Kfam
      (commonInvariantKrausFamily hρbar).isPreserving.1 hρbar
      (commonInvariantKrausFamily hρbar).map_commonAverage,
    adjointFixedPointsStarSubalgebra_commonInvariantKrausFamily]

end CommonInvariantProjection

end Kraus
