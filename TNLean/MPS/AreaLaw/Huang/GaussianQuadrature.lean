/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GaussianFilter.MatrixIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite Gaussian quadrature for error reduction

Partition a bounded time interval into disjoint intervals of a prescribed maximum width.
Weight each sample by the exact Gaussian mass of its interval. The weights are nonnegative
and have sum at most one. A Lipschitz estimate bounds the discretization error by the mesh
times the Lipschitz constant, with an explicit bound on the number of samples.

This is the finite-integral step of Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19 and
equation (22). Gaussian interval masses replace the displayed rectangular weights; no
derivative of the Gaussian density is needed. No approximation to the full propagator by
a matrix product operator is assumed or constructed here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace TNLean.MPS.AreaLaw

/-- The number of mesh intervals, including the possible final endpoint cell.
Huang, arXiv:1406.6355v6, Section 5.4, equation (22). -/
noncomputable def timeMeshCount (T delta : ℝ) : ℕ := ⌈2 * T / delta⌉₊ + 1

/-- Disjoint time cells cut out by the uniform mesh. The final cell retains the endpoint
when the interval length is an integer multiple of the mesh. Huang, equation (22). -/
def timeMeshCell (T delta : ℝ) (j : Fin (timeMeshCount T delta)) : Set ℝ :=
  Set.Icc (-T) T ∩ Set.Ico (-T + (j.val : ℝ) * delta) (-T + (j.val + 1 : ℝ) * delta)

/-- A representative in the truncated time interval, including cells of zero measure.
Huang, arXiv:1406.6355v6, Section 5.4, equation (22). -/
noncomputable def timeMeshNode (T delta : ℝ) (j : Fin (timeMeshCount T delta)) : ℝ :=
  min (-T + (j.val : ℝ) * delta) T

private theorem measurableSet_timeMeshCell (T delta : ℝ)
    (j : Fin (timeMeshCount T delta)) : MeasurableSet (timeMeshCell T delta j) :=
  measurableSet_Icc.inter measurableSet_Ico

private theorem pairwise_disjoint_timeMeshCell (T : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    Pairwise (fun j k ↦ Disjoint (timeMeshCell T delta j) (timeMeshCell T delta k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro t htj htk
  have hj := htj.2
  have hk := htk.2
  rcases lt_or_gt_of_ne (show j.val ≠ k.val from fun h ↦ hjk (Fin.ext h)) with h | h
  · have hcast : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_right hcast hdelta.le
    linarith [hj.2, hk.1]
  · have hcast : (k.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_right hcast hdelta.le
    linarith [hk.2, hj.1]

private theorem iUnion_timeMeshCell {T delta : ℝ} (_hT : 0 ≤ T) (hdelta : 0 < delta) :
    (⋃ j, timeMeshCell T delta j) = Set.Icc (-T) T := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun _ ↦ Set.inter_subset_left
  intro t ht
  let j : Fin (timeMeshCount T delta) :=
    ⟨⌊(t + T) / delta⌋₊, by
      have hle : (t + T) / delta ≤ 2 * T / delta := by gcongr; linarith [ht.2]
      have := (Nat.floor_mono hle).trans (Nat.floor_le_ceil (2 * T / delta))
      dsimp only [timeMeshCount]
      omega⟩
  apply Set.mem_iUnion.mpr
  refine ⟨j, ht, ?_, ?_⟩
  · have hfloor := Nat.floor_le (div_nonneg (show 0 ≤ t + T by linarith [ht.1]) hdelta.le)
    have hmul := (le_div_iff₀ hdelta).mp hfloor
    change -T + (⌊(t + T) / delta⌋₊ : ℝ) * delta ≤ t
    linarith
  · have hfloor := Nat.lt_floor_add_one ((t + T) / delta)
    have hmul := (div_lt_iff₀ hdelta).mp hfloor
    change t < -T + (⌊(t + T) / delta⌋₊ + 1 : ℝ) * delta
    linarith

/-- Every sample lies in the truncated time interval. Huang, Section 5.4, equation (22). -/
theorem timeMeshNode_mem {T delta : ℝ} (hT : 0 ≤ T) (hdelta : 0 < delta)
    (j : Fin (timeMeshCount T delta)) : timeMeshNode T delta j ∈ Set.Icc (-T) T := by
  dsimp only [timeMeshNode]
  constructor
  · exact le_min (le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) hdelta.le)) (by linarith)
  · exact min_le_right _ _

private theorem abs_sub_timeMeshNode_le {T delta : ℝ}
    (j : Fin (timeMeshCount T delta)) {t : ℝ} (ht : t ∈ timeMeshCell T delta j) :
    |t - timeMeshNode T delta j| ≤ delta := by
  have hlo : -T + (j.val : ℝ) * delta ≤ T := ht.2.1.trans ht.1.2
  rw [timeMeshNode, min_eq_left hlo, abs_of_nonneg (sub_nonneg.mpr ht.2.1)]
  linarith [ht.2.2]

/-- The uniform mesh supplies a node within one mesh width of every point in the closed
interval. This is the geometric covering property in Huang, arXiv:1406.6355v6,
Section 5.4, equation (22); it also supplies finite energy guesses for equation (19). -/
theorem exists_timeMeshNode_abs_sub_le {T delta t : ℝ}
    (hT : 0 ≤ T) (hdelta : 0 < delta) (ht : t ∈ Set.Icc (-T) T) :
    ∃ j : Fin (timeMeshCount T delta), |t - timeMeshNode T delta j| ≤ delta := by
  have hcover : t ∈ ⋃ j, timeMeshCell T delta j := by
    rw [iUnion_timeMeshCell hT hdelta]
    exact ht
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hcover
  exact ⟨j, abs_sub_timeMeshNode_le j hj⟩

/-- The sample count is linear in interval length divided by mesh size.
Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19. -/
theorem timeMeshCount_le {T delta : ℝ} (hT : 0 ≤ T) (hdelta : 0 < delta) :
    (timeMeshCount T delta : ℝ) ≤ 2 * T / delta + 2 := by
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2 * T / delta by positivity)).le
  dsimp only [timeMeshCount]
  push_cast
  linarith

/-- The exact Gaussian mass of a time cell. Huang, equation (22), with interval masses
in place of rectangular quadrature weights. -/
noncomputable def timeMeshWeight (h : ℝ≥0) (T delta : ℝ)
    (j : Fin (timeMeshCount T delta)) : ℝ :=
  (gaussianReal 0 h).real (timeMeshCell T delta j)

/-- Gaussian cell weights are nonnegative. Huang, Section 5.4, equation (22). -/
theorem timeMeshWeight_nonneg (h : ℝ≥0) (T delta : ℝ)
    (j : Fin (timeMeshCount T delta)) : 0 ≤ timeMeshWeight h T delta j :=
  measureReal_nonneg

/-- The finite weights retain exactly the mass of the truncated Gaussian.
Huang, arXiv:1406.6355v6, Section 5.4, equation (22). -/
theorem sum_timeMeshWeight {T delta : ℝ} (h : ℝ≥0) (hT : 0 ≤ T) (hdelta : 0 < delta) :
    (∑ j, timeMeshWeight h T delta j) = (gaussianReal 0 h).real (Set.Icc (-T) T) := by
  rw [← iUnion_timeMeshCell hT hdelta]
  exact (measureReal_iUnion_fintype (pairwise_disjoint_timeMeshCell T hdelta)
    (measurableSet_timeMeshCell T delta)).symm

/-- The positive quadrature weights have sum at most one. Huang, equation (22). -/
theorem sum_timeMeshWeight_le_one {T delta : ℝ} (h : ℝ≥0) (hT : 0 ≤ T)
    (hdelta : 0 < delta) : (∑ j, timeMeshWeight h T delta j) ≤ 1 := by
  rw [sum_timeMeshWeight h hT hdelta]
  exact measureReal_le_one

/-- Discretizing the truncated Gaussian integral of a Lipschitz function costs at most
the Lipschitz constant times the mesh. This is the finite-integral estimate in Huang,
arXiv:1406.6355v6, Lemma 19 and equation (22), with exact positive cell weights. -/
theorem norm_setIntegral_sub_timeMesh_sum_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : ℝ≥0) {T delta M : ℝ} (hT : 0 ≤ T) (hdelta : 0 < delta) (hM : 0 ≤ M)
    (f : ℝ → E) (hf : Integrable f (gaussianReal 0 h))
    (hLip : ∀ t ∈ Set.Icc (-T) T, ∀ s ∈ Set.Icc (-T) T,
      ‖f t - f s‖ ≤ M * |t - s|) :
    ‖(∫ t in Set.Icc (-T) T, f t ∂gaussianReal 0 h) -
      ∑ j, timeMeshWeight h T delta j • f (timeMeshNode T delta j)‖ ≤ M * delta := by
  have heq : (∫ t in Set.Icc (-T) T, f t ∂gaussianReal 0 h) -
      ∑ j, timeMeshWeight h T delta j • f (timeMeshNode T delta j) =
      ∑ j, ∫ t in timeMeshCell T delta j,
        f t - f (timeMeshNode T delta j) ∂gaussianReal 0 h := by
    rw [← iUnion_timeMeshCell hT hdelta,
      integral_iUnion_fintype (measurableSet_timeMeshCell T delta)
        (pairwise_disjoint_timeMeshCell T hdelta) (fun _ ↦ hf.restrict),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_sub hf.restrict (integrable_const _), setIntegral_const]
    rfl
  rw [heq]
  calc
    _ ≤ ∑ j, ‖∫ t in timeMeshCell T delta j,
        f t - f (timeMeshNode T delta j) ∂gaussianReal 0 h‖ := norm_sum_le _ _
    _ ≤ ∑ j, M * delta * timeMeshWeight h T delta j := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun t ht ↦
        (hLip t ht.1 _ (timeMeshNode_mem hT hdelta j)).trans
          (mul_le_mul_of_nonneg_left (abs_sub_timeMeshNode_le j ht) hM)
    _ = M * delta * ∑ j, timeMeshWeight h T delta j := by rw [Finset.mul_sum]
    _ ≤ M * delta := mul_le_of_le_one_right (mul_nonneg hM hdelta.le)
      (sum_timeMeshWeight_le_one h hT hdelta)

/-- Gaussian tail and mesh errors add for a bounded Lipschitz integrand. The statement
includes zero variance and retains the same nodes and weights for every integrand.
Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19 and equation (22). -/
theorem norm_integral_sub_timeMesh_sum_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : ℝ≥0) {T delta M : ℝ} (hT : 0 ≤ T) (hdelta : 0 < delta) (hM : 0 ≤ M)
    (f : ℝ → E) (hf : Integrable f (gaussianReal 0 h)) (hnorm : ∀ t, ‖f t‖ ≤ 1)
    (hLip : ∀ t ∈ Set.Icc (-T) T, ∀ s ∈ Set.Icc (-T) T,
      ‖f t - f s‖ ≤ M * |t - s|) :
    ‖(∫ t, f t ∂gaussianReal 0 h) -
      ∑ j, timeMeshWeight h T delta j • f (timeMeshNode T delta j)‖ ≤
      2 * Real.exp (-T ^ 2 / (2 * (h : ℝ))) + M * delta := by
  have htail : ‖(∫ t, f t ∂gaussianReal 0 h) -
      ∫ t in Set.Icc (-T) T, f t ∂gaussianReal 0 h‖ ≤
      2 * Real.exp (-T ^ 2 / (2 * (h : ℝ))) := by
    have hbound := norm_integral_sub_setIntegral_le (s := Set.Icc (-T) T)
      (Filter.Eventually.of_forall hnorm) measurableSet_Icc hf
    simpa only [mul_one] using hbound.trans
      (by simpa only [mul_one] using GaussianFilter.measure_compl_Icc_le h hT)
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∫ t in Set.Icc (-T) T, f t ∂gaussianReal 0 h) _).trans
      (add_le_add htail (norm_setIntegral_sub_timeMesh_sum_le h hT hdelta hM f hf hLip))

/-- At prescribed mesh error, the number of samples is polynomial in the cutoff,
Lipschitz bound and inverse error. Huang, Section 5.4, Lemma 19. -/
theorem timeMeshCount_accuracy_le {T M epsilon : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hepsilon : 0 < epsilon) :
    (timeMeshCount T (epsilon / (M + 1)) : ℝ) ≤ 2 * T * (M + 1) / epsilon + 2 := by
  have hdelta : 0 < epsilon / (M + 1) := div_pos hepsilon (by linarith)
  have h := timeMeshCount_le hT hdelta
  convert h using 1
  field_simp

/-- A prescribed mesh error is achieved by one fixed set of positive Gaussian weights
and sample times, independently of the integrand. The explicit sample count is bounded by
`timeMeshCount_accuracy_le`. Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19. -/
theorem norm_integral_sub_timeMesh_accuracy_sum_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : ℝ≥0) {T M epsilon : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hepsilon : 0 < epsilon)
    (f : ℝ → E) (hf : Integrable f (gaussianReal 0 h)) (hnorm : ∀ t, ‖f t‖ ≤ 1)
    (hLip : ∀ t ∈ Set.Icc (-T) T, ∀ s ∈ Set.Icc (-T) T,
      ‖f t - f s‖ ≤ M * |t - s|) :
    ‖(∫ t, f t ∂gaussianReal 0 h) -
      ∑ j, timeMeshWeight h T (epsilon / (M + 1)) j •
        f (timeMeshNode T (epsilon / (M + 1)) j)‖ ≤
      2 * Real.exp (-T ^ 2 / (2 * (h : ℝ))) + epsilon := by
  have hM1 : 0 < M + 1 := by linarith
  have hdelta : 0 < epsilon / (M + 1) := div_pos hepsilon hM1
  have hmesh : M * (epsilon / (M + 1)) ≤ epsilon := by
    rw [← mul_div_assoc, div_le_iff₀ hM1]
    nlinarith
  exact (norm_integral_sub_timeMesh_sum_le h hT hdelta hM f hf hnorm hLip).trans
    (add_le_add_right hmesh _)

end TNLean.MPS.AreaLaw
