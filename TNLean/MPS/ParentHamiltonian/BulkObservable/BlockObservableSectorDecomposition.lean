/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BulkObservable.BoundaryObservableCompression
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableState
import QICLean.Analysis.Projection.ProjectorSumConvergence
/-!
# Asymptotic sector decomposition of interior observables

For finitely many inequivalent primitive sectors, the compression of an
interior observable to the joint finite-chain MPS space approaches the sum
of sector projections weighted by their insertion expectations. The sector
projections need not be orthogonal at finite length. Their sum approaches
the joint projection as the chain grows, and the centered column limits
control the remaining error. Both free intervals tend to infinity.

This is a finite-sector consequence of Nachtergaele,
arXiv:cond-mat/9410110, equations (3.8)--(3.9), Lemma commutation (i),
and equation boundXm. It concerns finite-chain compressions and does not
assume or assert a classification of quasi-local ground states.
-/

open Filter
open scoped Topology Matrix ComplexOrder BigOperators

namespace MPSTensor
variable {ι : Type*} [Finite ι] {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- Each sector column of the full joint compression approaches its sector
expectation times the sector projection. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.8)--(3.9), combined with the full
centered projection limit in lines 2649--2675. -/
theorem bulkObservable_iSup_groundSpace_column_tendsto_scalar
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (α : ι) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {κ : Type*} {f : Filter κ} {ℓ r : κ → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n =>
      ‖(⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection.comp
        ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
          (bulkObservable X (ℓ n) (r n))).comp
            (groundSpaceES (A α) ((ℓ n + k) + r n)).starProjection) -
        observableInsertionExpectation (A α) (ρ α) X •
          (groundSpaceES (A α) ((ℓ n + k) + r n)).starProjection‖) f (𝓝 0) := by
  let c := observableInsertionExpectation (A α) (ρ α) X
  have hcenter : observableInsertionExpectation (A α) (ρ α) (X - c • 1) = 0 := by
    change (observableInsertionExpectationₗ (A α) (ρ α) k) (X - c • 1) = 0
    have hOne : (observableInsertionExpectationₗ (A α) (ρ α) k) 1 = 1 :=
      observableInsertionExpectation_one (A α) (ρ α)
        (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero k
    rw [map_sub, map_smul, hOne, smul_eq_mul, mul_one]
    exact sub_self c
  have hbulk (n : κ) : bulkObservable (X - c • 1) (ℓ n) (r n) =
      bulkObservable X (ℓ n) (r n) - c • 1 := by
    rw [bulkObservable_eq_placeAlong_chainWindow, bulkObservable_eq_placeAlong_chainWindow,
      ManyBody.placeAlong_sub, ManyBody.placeAlong_smul, ManyBody.placeAlong_one]
  have hPP (n : κ) :
      (⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection.comp
        (groundSpaceES (A α) ((ℓ n + k) + r n)).starProjection =
          (groundSpaceES (A α) ((ℓ n + k) + r n)).starProjection :=
    ContinuousLinearMap.ext fun v => Submodule.starProjection_eq_self_iff.mpr
      ((le_iSup (fun i => groundSpaceES (A i) ((ℓ n + k) + r n)) α)
        ((groundSpaceES (A α) ((ℓ n + k) + r n)).starProjection_apply_mem v))
  simpa only [hbulk, map_sub, map_smul, map_one,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, hPP] using
    bulkObservable_iSup_groundSpace_compression_tendsto_zero A ρ hP hρ hDistinct
      α (X - c • 1) hcenter hℓ hr
end MPSTensor

namespace MPSTensor
variable {ι : Type*} [Fintype ι] {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- The joint compression of an interior observable approaches its finite
sector decomposition in operator norm as both free intervals grow.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.8)--(3.9)
and Lemma commutation (i), equation boundXm. -/
theorem bulkObservable_iSup_groundSpace_sector_decomposition_tendsto_zero
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {κ : Type*} {f : Filter κ} {ℓ r : κ → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n =>
      ‖(⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection.comp
        ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
          (bulkObservable X (ℓ n) (r n))).comp
            (⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection) -
        ∑ i, observableInsertionExpectation (A i) (ρ i) X •
          (groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection‖) f (𝓝 0) := by
  let N := fun n => (ℓ n + k) + r n
  have hN : Tendsto N f atTop := tendsto_atTop_mono (fun n => by dsimp [N]; omega) hℓ
  refine Submodule.tendsto_norm_joint_compression_sub_sector_sum_zero
    (E := fun n => EuclideanSpace ℂ (Cfg d (N n)))
    (C := ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖)
    (fun n i => groundSpaceES (A i) (N n))
    (fun n => Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ)
      (bulkObservable X (ℓ n) (r n)))
    (fun i => observableInsertionExpectation (A i) (ρ i) X) ?_ ?_ ?_
  · apply Submodule.tendsto_norm_sum_starProjection_sub_iSup_zero
    exact fun ε hε => hN.eventually (eventually_all.2 fun i => eventually_all.2 fun j =>
      eventually_all.2 fun hij =>
        (hP i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
          (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε)
  · exact Eventually.of_forall fun n => norm_toEuclideanCLM_bulkObservable_le X (ℓ n) (r n)
  · exact fun i => bulkObservable_iSup_groundSpace_column_tendsto_scalar
      A ρ hP hρ hDistinct i X hℓ hr
end MPSTensor
