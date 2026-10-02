/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockBoundaryObservableCompression
import TNLean.MPS.ParentHamiltonian.LocalObservableState
/-!
# Asymptotic sector decomposition of interior observables

For finitely many inequivalent primitive sectors, the compression of an
interior observable to the joint finite-chain MPS space approaches the sum
of sector projections weighted by their insertion expectations. The sector
projections need not be orthogonal at finite length. Their sum approaches
the joint projection as the chain grows, and the centered column limits
control the remaining error. Both free intervals tend to infinity.

This is a finite-sector consequence of Nachtergaele,
arXiv:cond-mat/9410110, equations (3.8)--(3.9), Lemma `commutation` (i),
and equation `boundXm`. It concerns finite-chain compressions and does not
assume or assert a classification of quasi-local ground states.
-/

open Filter
open scoped Topology Matrix ComplexOrder BigOperators

namespace Submodule
variable {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

private theorem norm_joint_compression_sub_sector_sum_le
    (G : ι → Submodule ℂ F) (X : F →L[ℂ] F) (c : ι → ℂ) :
    ‖(⨆ i, G i).starProjection.comp (X.comp (⨆ i, G i).starProjection) -
      ∑ i, c i • (G i).starProjection‖ ≤
      ‖(∑ i, (G i).starProjection) - (⨆ i, G i).starProjection‖ * ‖X‖ +
        ∑ i, ‖(⨆ j, G j).starProjection.comp (X.comp (G i).starProjection) -
          c i • (G i).starProjection‖ := by
  let P := (⨆ i, G i).starProjection
  let Q := ∑ i, (G i).starProjection
  have hEq : P.comp (X.comp P) - ∑ i, c i • (G i).starProjection =
      P.comp (X.comp (P - Q)) +
        ∑ i, (P.comp (X.comp (G i).starProjection) - c i • (G i).starProjection) := by
    simp only [ContinuousLinearMap.comp_sub, Q,
      ContinuousLinearMap.comp_finsetSum, Finset.sum_sub_distrib]
    abel
  change ‖P.comp (X.comp P) - ∑ i, c i • (G i).starProjection‖ ≤
    ‖Q - P‖ * ‖X‖ +
      ∑ i, ‖P.comp (X.comp (G i).starProjection) - c i • (G i).starProjection‖
  rw [hEq]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right (⨆ i, G i).starProjection_norm_le
    (norm_nonneg _)).trans ?_
  simpa only [one_mul, norm_sub_rev, mul_comm] using
    ContinuousLinearMap.opNorm_comp_le X (P - Q)

variable {κ : Type*} {f : Filter κ}
  {E : κ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, FiniteDimensional ℂ (E n)]

/-- Vanishing sector column errors and vanishing projection-sum error give
vanishing joint compression error for uniformly bounded observables.
The Hilbert spaces may vary along the filter. This is the finite-family
operator estimate used with Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (i) and equations (3.8)--(3.9). -/
theorem tendsto_norm_joint_compression_sub_sector_sum_zero
    (G : (n : κ) → ι → Submodule ℂ (E n))
    (X : (n : κ) → E n →L[ℂ] E n) (c : ι → ℂ) {C : ℝ}
    (hError : Tendsto (fun n =>
      ‖(∑ i, (G n i).starProjection) - (⨆ i, G n i).starProjection‖) f (𝓝 0))
    (hX : ∀ᶠ n in f, ‖X n‖ ≤ C)
    (hColumns : ∀ i, Tendsto (fun n =>
      ‖(⨆ j, G n j).starProjection.comp ((X n).comp (G n i).starProjection) -
        c i • (G n i).starProjection‖) f (𝓝 0)) :
    Tendsto (fun n =>
      ‖(⨆ i, G n i).starProjection.comp ((X n).comp (⨆ i, G n i).starProjection) -
        ∑ i, c i • (G n i).starProjection‖) f (𝓝 0) := by
  have hSum : Tendsto (fun n => ∑ i,
      ‖(⨆ j, G n j).starProjection.comp ((X n).comp (G n i).starProjection) -
        c i • (G n i).starProjection‖) f (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hColumns i)
  have hUpper : Tendsto (fun n =>
      ‖(∑ i, (G n i).starProjection) - (⨆ i, G n i).starProjection‖ * C +
        ∑ i, ‖(⨆ j, G n j).starProjection.comp ((X n).comp (G n i).starProjection) -
          c i • (G n i).starProjection‖) f (𝓝 0) := by
    simpa only [zero_mul, zero_add] using (hError.mul_const C).add hSum
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hUpper
  filter_upwards [hX] with n hn
  exact (norm_joint_compression_sub_sector_sum_le (G n) (X n) c).trans
    (add_le_add (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) le_rfl)
end Submodule


namespace MPSTensor
variable {ι : Type*} [Finite ι] {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- Each sector column of the full joint compression approaches its sector
expectation times the sector projection. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.8)--(3.9), combined with the full
centered projection limit in lines 2649--2675. -/
theorem bulkObservable_iSup_groundSpace_column_tendsto_scalar
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (α : ι) {k : ℕ} (hk : 0 < k) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
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
    rw [bulkObservable_eq_chainWindowOperator hk,
      chainWindowOperator_sub_smul_one (by omega) (by omega),
      ← bulkObservable_eq_chainWindowOperator hk]
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
      α hk (X - c • 1) hcenter hℓ hr
end MPSTensor

namespace MPSTensor
variable {ι : Type*} [Fintype ι] {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- The joint compression of an interior observable approaches its finite
sector decomposition in operator norm as both free intervals grow.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.8)--(3.9)
and Lemma `commutation` (i), equation `boundXm`. -/
theorem bulkObservable_iSup_groundSpace_sector_decomposition_tendsto_zero
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {k : ℕ} (hk : 0 < k) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
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
  · exact Eventually.of_forall fun n => norm_toEuclideanCLM_bulkObservable_le hk X (ℓ n) (r n)
  · exact fun i => bulkObservable_iSup_groundSpace_column_tendsto_scalar
      A ρ hP hρ hDistinct i hk X hℓ hr
end MPSTensor
