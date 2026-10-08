/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ConvexWeightsCompactness
import TNLean.MPS.ParentHamiltonian.BlockObservableSectorDecomposition
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces
import TNLean.MPS.ParentHamiltonian.IntervalStateProjection
import TNLean.MPS.ParentHamiltonian.QuasiLocalCommutatorLocality

/-!
# Convex decomposition of states with joint MPS support

Let finitely many pairwise inequivalent primitive sectors have faithful
invariant density matrices. A normalized positive quasi-local state
supported in their joint finite-chain spaces on sufficiently large
centered intervals is a convex combination of the sector states.

The finite sector-projection expectations provide weights in \([0,1]\).
Their total mass tends to one by the projection-sum comparison. Joint
compression of an interior observable approaches its sector-diagonal
part. A convergent subsequence of the weights therefore identifies all
local evaluations simultaneously, and continuity identifies the states
on the completed algebra. The competing state need not be translation
invariant.

This supplies the support-to-convex-hull implication in the argument for
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1, lines 858--926. Its
hypothesis is eventual support on expanding intervals.
-/

open Filter SpinChain
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
namespace MPSTensor
variable {d b : ℕ} [NeZero d] {D : Fin b → ℕ} [∀ j, NeZero (D j)]

omit [NeZero d] in
private theorem projection_sum_error_tendsto_zero
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    Tendsto (fun n : ℕ =>
      ‖Matrix.toEuclideanCLM (n := Cfg d (2 * n + 1)) (𝕜 := ℂ)
        ((∑ j, groundSpaceProjectionMatrix (A j) (2 * n + 1)) -
          groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (2 * n + 1))‖)
      atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2 * n + 1; omega) tendsto_id
  have hError := Submodule.tendsto_norm_sum_starProjection_sub_iSup_zero
    (E := fun n : ℕ => EuclideanSpace ℂ (Cfg d (2 * n + 1)))
    (fun n j => groundSpaceES (A j) (2 * n + 1))
    (fun ε hε => hN.eventually (eventually_all.2 fun i => eventually_all.2 fun j =>
      eventually_all.2 fun hij =>
        (hP i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
          (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε))
  simpa only [map_sub, map_sum, groundSpaceProjectionMatrix,
    StarAlgEquiv.apply_symm_apply, groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ]
    using hError

private noncomputable def sectorWeight
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (A : ∀ j, MPSTensor d (D j))
    (n : ℕ) (j : Fin b) : ℝ :=
  (φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
    (groundSpaceProjectionMatrix (A j) (2 * n + 1)))).re

private theorem sectorWeight_sum_tendsto_one
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hSupport : ∀ᶠ n : ℕ in atTop,
      φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
        (groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (2 * n + 1))) = 1) :
    Tendsto (fun n => ∑ j, sectorWeight φ A n j) atTop (𝓝 1) := by
  have hError := projection_sum_error_tendsto_zero μ A hμ ρ hP hρ hDistinct
  let z := fun n : ℕ => ∑ j, φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
    (groundSpaceProjectionMatrix (A j) (2 * n + 1)))
  have hbound : ∀ᶠ n : ℕ in atTop, ‖z n - 1‖ ≤
      ‖Matrix.toEuclideanCLM (n := Cfg d (2 * n + 1)) (𝕜 := ℂ)
        ((∑ j, groundSpaceProjectionMatrix (A j) (2 * n + 1)) -
          groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (2 * n + 1))‖ := by
    filter_upwards [hSupport] with n hn
    simpa only [z, map_sub, map_sum, hn] using norm_quasiLocalState_interval_le φ hφ
      (-(n : ℤ)) ((∑ j, groundSpaceProjectionMatrix (A j) (2 * n + 1)) -
        groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (2 * n + 1))
  have hnorm : Tendsto (fun n => ‖z n - 1‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hError
  simpa only [Function.comp_def, z, sectorWeight, Complex.re_sum, Complex.one_re] using
    (Complex.continuous_re.tendsto (1 : ℂ)).comp
      (tendsto_iff_norm_sub_tendsto_zero.mpr hnorm)

private theorem sectorWeight_centered_evaluation_tendsto_zero
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hSupport : ∀ᶠ n : ℕ in atTop,
      φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
        (groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (2 * n + 1))) = 1)
    (m : ℕ) (X : Matrix (Cfg d (2 * m + 1)) (Cfg d (2 * m + 1)) ℂ) :
    Tendsto (fun n => φ (quasiLocalIntervalObservable d (-(m : ℤ)) (2 * m + 1) X) -
      ∑ j, (sectorWeight φ A n j : ℂ) * observableInsertionExpectation (A j) (ρ j) X)
      atTop (𝓝 0) := by
  have hdec := bulkObservable_iSup_groundSpace_sector_decomposition_tendsto_zero
    A ρ hP hρ hDistinct (show 0 < 2 * m + 1 by omega) X
      (tendsto_sub_atTop_nat m) (tendsto_sub_atTop_nat m)
  let N := fun n : ℕ => ((n - m) + (2 * m + 1)) + (n - m)
  let p := fun n => groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (N n)
  let Y := fun n => ∑ j, observableInsertionExpectation (A j) (ρ j) X •
    groundSpaceProjectionMatrix (A j) (N n)
  have hmat : Tendsto (fun n =>
      ‖Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ)
        (p n * bulkObservable X (n - m) (n - m) * p n - Y n)‖) atTop (𝓝 0) := by
    simpa only [p, Y, N, groundSpaceProjectionMatrix, map_sub, map_mul, map_sum, map_smul,
      StarAlgEquiv.apply_symm_apply, groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hdec
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖φ (quasiLocalIntervalObservable d (-(m : ℤ)) (2 * m + 1) X) -
        ∑ j, (sectorWeight φ A n j : ℂ) * observableInsertionExpectation (A j) (ρ j) X‖ ≤
      ‖Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ)
        (p n * bulkObservable X (n - m) (n - m) * p n - Y n)‖ := by
    filter_upwards [hSupport, eventually_ge_atTop m] with n hn hnm
    have hlength : N n = 2 * n + 1 := by dsimp [N]; omega
    have hstart : -(m : ℤ) - ((n - m : ℕ):ℤ) = -(n : ℤ) := by omega
    have hsupport : φ (quasiLocalIntervalObservable d
        (-(m : ℤ) - ((n - m : ℕ):ℤ)) (N n) (p n)) = 1 := by
      change φ (quasiLocalIntervalObservable d (-(m : ℤ) - ((n - m : ℕ):ℤ)) (N n)
        (groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (N n))) = 1
      rw [hstart, hlength]
      exact hn
    have hsector (j : Fin b) : φ (quasiLocalIntervalObservable d
        (-(m : ℤ) - ((n - m : ℕ):ℤ)) (N n) (groundSpaceProjectionMatrix (A j) (N n))) =
        (sectorWeight φ A n j : ℂ) := by
      rw [hstart, hlength]
      exact intervalStateFunctional_projection_eq_ofReal_re φ hφ (-(n : ℤ))
        (groundSpaceProjectionMatrix (A j) (2 * n + 1))
          (isStarProjection_groundSpaceProjectionMatrix (A j) (2 * n + 1))
    have hestimate := norm_quasiLocalState_interval_sub_le_projection_compression φ hφ
      (-(m : ℤ) - ((n - m : ℕ):ℤ)) (p n) (bulkObservable X (n - m) (n - m)) (Y n)
      (isStarProjection_groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (N n))
      hsupport
    have hbulk : quasiLocalIntervalObservable d (-(m : ℤ) - ((n - m : ℕ):ℤ)) (N n)
        (bulkObservable X (n - m) (n - m)) =
        quasiLocalIntervalObservable d (-(m : ℤ)) (2 * m + 1) X :=
      SpinChain.quasiLocalIntervalObservable_bulkObservable (-(m : ℤ)) X (n - m) (n - m)
    simpa only [Y, hbulk,
      map_sum, map_smul, hsector, smul_eq_mul, mul_comm] using hestimate
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hmat)

/-- Every normalized positive quasi-local state eventually supported in the
joint finite-chain spaces of finitely many inequivalent primitive sectors
is a convex combination of their constructed states. No translation
invariance is assumed. This is the support-to-convex-hull implication used
in Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1, lines 858--926. -/
theorem exists_convex_combination_quasiLocalExpectation_of_eventually_groundSpace_support
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hSupport : ∀ᶠ n : ℕ in atTop,
      φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
        (groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) (2 * n + 1))) = 1) :
    ∃ w : Fin b → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      φ = ∑ j, w j • quasiLocalExpectation (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
  obtain ⟨w, hw, hsum, heval⟩ := exists_convex_weights_of_approximate_evaluations
    (fun t : (m : ℕ) × Matrix (Cfg d (2 * m + 1)) (Cfg d (2 * m + 1)) ℂ =>
      φ (quasiLocalIntervalObservable d (-(t.1 : ℤ)) (2 * t.1 + 1) t.2))
    (fun j t => observableInsertionExpectation (A j) (ρ j) t.2)
    (sectorWeight φ A)
    (Eventually.of_forall fun n j => intervalStateFunctional_projection_mem_unitInterval
      φ hφ (-(n : ℤ)) (groundSpaceProjectionMatrix (A j) (2 * n + 1))
      (isStarProjection_groundSpaceProjectionMatrix (A j) (2 * n + 1)))
    (sectorWeight_sum_tendsto_one μ A hμ ρ hP hρ hDistinct φ hφ hSupport)
    (fun t => sectorWeight_centered_evaluation_tendsto_zero μ A hμ ρ hP hρ hDistinct
      φ hφ hSupport t.1 t.2)
  refine ⟨w, hw, hsum, ?_⟩
  refine ContinuousLinearMap.ext fun Z => ?_
  refine UniformSpace.Completion.induction_on Z
    (isClosed_eq φ.continuous (∑ j, w j • quasiLocalExpectation (A j) (hP j).norm
      (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero).continuous) ?_
  intro Y
  induction Y using DirectLimit.induction with
  | _ Λ X =>
    change φ (quasiLocalObservable d Λ X) =
      (∑ j, w j • quasiLocalExpectation (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
          (quasiLocalObservable d Λ X)
    simp only [sum_apply, smul_apply,
      Complex.real_smul, quasiLocalExpectation_quasiLocalObservable]
    change φ (quasiLocalObservable d Λ X) = ∑ j, (w j : ℂ) *
      observableInsertionExpectation (A j) (ρ j)
        (intervalCoordinates d (-((Λ.sup Int.natAbs : ℕ) : ℤ)) (2 * Λ.sup Int.natAbs + 1)
          (localInclusion _ X))
    rw [← heval ⟨Λ.sup Int.natAbs, _⟩]
    simp only [quasiLocalIntervalObservable_apply, StarAlgEquiv.symm_apply_apply,
      quasiLocalObservable_localInclusion]
end MPSTensor
