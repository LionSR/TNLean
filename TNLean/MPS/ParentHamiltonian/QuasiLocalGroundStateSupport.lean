/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalUniqueness
import TNLean.MPS.ParentHamiltonian.QuasiLocalOpenInteractionExpectation
import TNLean.MPS.ParentHamiltonian.PrimitiveLocalParentInteractionGap
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison

/-!
# Local zero energy implies finite-interval ground-space support

A finite positive Hamiltonian dominates a positive multiple of the projection
onto the complement of its kernel. A normalized positive functional vanishing
on the Hamiltonian therefore assigns expectation one to its kernel projection.
For a weighted multiblock tensor at simultaneous injectivity, the open-chain
kernel is the joint MPS space. Vanishing expectations on every translated
parent term imply support in that space on every sufficiently large interval.
Translation invariance of the state and a uniform spectral gap are unnecessary.
A further theorem uses the source's eventual finite-volume kernel identity
directly, without a local parent-kernel hypothesis or an injectivity bound on
the interaction range.

**Scope restriction (sufficient interaction range):** The simultaneous-word-span
consequences assume a positive simultaneous injectivity length \(S\) and range
at least \(S+1\). See
docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
equation (3.12), and the finite-interval support discussion in Section 3.
-/

open scoped ComplexOrder
namespace PositiveLinearMap
variable {E : Type*} [Ring E] [PartialOrder E] [Module ℂ E] [StarRing E]
  [StarOrderedRing E]

/-- A normalized positive functional annihilating an operator which dominates
a positive multiple of a projection complement has full projection expectation.
This is the finite-dimensional support implication used in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.1 and Section 3. -/
theorem apply_projection_eq_one_of_le_of_apply_eq_zero
    (f : E →ₚ[ℂ] ℂ) (p H : E) (hp : IsStarProjection p)
    (hf1 : f 1 = 1) (hfH : f H = 0) {κ : ℝ} (hκ : 0 < κ)
    (hLower : (κ : ℂ) • (1 - p) ≤ H) : f p = 1 := by
  have hLower' := f.monotone hLower
  have hq : 0 ≤ f (1 - p) := f.map_nonneg hp.one_sub_nonneg
  change f ((κ : ℂ) • (1 - p)) ≤ f H at hLower'
  have hscale : (κ : ℂ) * f (1 - p) ≤ 0 := by
    simpa only [map_smul, smul_eq_mul, hfH] using hLower'
  have hreal : κ * (f (1 - p)).re ≤ 0 := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.zero_re] using (Complex.le_def.mp hscale).1
  have hqzero : f (1 - p) = 0 := by
    apply Complex.ext
    · change (f (1 - p)).re = 0
      nlinarith [(Complex.nonneg_iff.mp hq).1]
    · exact (Complex.nonneg_iff.mp hq).2.symm
  exact (sub_eq_zero.mp (by simpa only [map_sub, hf1] using hqzero)).symm
end PositiveLinearMap

open SpinChain
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
namespace MPSTensor
variable {d D : ℕ} [NeZero d]
/-- Zero expectation of a finite positive Hamiltonian with prescribed MPS
kernel gives expectation one on the MPS support projection. No uniform gap is
required. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3. -/
theorem quasiLocalState_groundSpaceProjection_eq_one_of_interval_eq_zero
    (A : MPSTensor d D) (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d) (a : ℤ) {N : ℕ}
    (H : Matrix (Cfg d N) (Cfg d N) ℂ) (hH : H.PosSemidef)
    (hker : LinearMap.ker (Matrix.toEuclideanLin H) = groundSpaceES A N)
    (hzero : φ (quasiLocalIntervalObservable d a N H) = 0) :
    φ (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1 := by
  obtain ⟨κ, hκ, hLower⟩ :=
    (Matrix.isPositive_toEuclideanLin_iff.mpr hH).exists_pos_smul_orthogonal_ker_projection_le
  rw [hker] at hLower
  have hLowerMatrix : (κ : ℂ) • (1 - groundSpaceProjectionMatrix A N) ≤ H := by
    rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff]
    simpa only [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, map_sub, map_smul,
      map_one, groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply,
      Submodule.starProjection_orthogonal, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_one, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.coe_id, Module.End.one_eq_id]
      using LinearMap.le_def.mp hLower
  refine PositiveLinearMap.apply_projection_eq_one_of_le_of_apply_eq_zero
    (intervalStateFunctional φ hφ.2.2 a N) (groundSpaceProjectionMatrix A N) H
    (isStarProjection_groundSpaceProjectionMatrix A N) ?_ hzero hκ hLowerMatrix
  simpa only [intervalStateFunctional_apply, map_one] using hφ.2.1

/-- A state with zero expectation on every translated parent term is supported
in the joint MPS space of each interval of length at least the interaction range.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1 and equation (3.12);
CPGSV21, arXiv:2011.12127, lines 2114--2129. -/
theorem quasiLocalState_groundSpaceProjection_eq_one_of_isParentInteraction_wordTupleSpanTop
    {b : ℕ} {dim : Fin b → ℕ} [∀ i, NeZero (dim i)]
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (dim i)) (hμ : ∀ i, μ i ≠ 0)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (a : ℤ) {N : ℕ} (hN : R ≤ N) :
    φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix (toTensorFromBlocks (d := d) (μ := μ) A) N)) = 1 := by
  refine quasiLocalState_groundSpaceProjection_eq_one_of_interval_eq_zero
    (toTensorFromBlocks (d := d) (μ := μ) A) φ hφ a (openInteractionMatrix h N) ?_ ?_ ?_
  · apply Matrix.isPositive_toEuclideanLin_iff.mp
    rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix
      h (by omega) hN]
    exact openInteractionHamiltonianES_isPositive hh.isPositive N
  · rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix
      h (by omega) hN,
      hh.ker_openInteractionHamiltonianES_eq_ker_openParentHamiltonianES (by omega)]
    exact ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_wordTupleSpanTop
      μ A hμ hS hSpan hR hN
  · exact apply_quasiLocalIntervalObservable_openInteractionMatrix_eq_zero
      φ.toLinearMap h (by omega) hzero a N

/-- Local zero energy gives eventual joint MPS support on the symmetric
intervals with endpoints tending to both infinities. No invariance is assumed.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1 and Section 3. -/
theorem eventually_quasiLocalState_symmetric_groundSpaceProjection_eq_one
    {b : ℕ} {dim : Fin b → ℕ} [∀ i, NeZero (dim i)]
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (dim i)) (hμ : ∀ i, μ i ≠ 0)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
        (groundSpaceProjectionMatrix (toTensorFromBlocks (d := d) (μ := μ) A)
          (2 * n + 1))) = 1 := by
  filter_upwards [Filter.eventually_ge_atTop R] with n hn
  exact quasiLocalState_groundSpaceProjection_eq_one_of_isParentInteraction_wordTupleSpanTop
    μ A hμ hS hSpan hR h hh φ hφ hzero (-(n : ℤ)) (by omega)
/-- The source's eventual finite-volume kernel hypothesis gives joint support
on expanding symmetric intervals for every locally zero-energy state. This
requires no parent-kernel condition at the interaction range and no simultaneous
injectivity bound on that range. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, and Section 3. -/
theorem eventually_quasiLocalState_symmetric_groundSpaceProjection_eq_one_of_eventual_kernel
    (A : MPSTensor d D) {R : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES A N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
        (groundSpaceProjectionMatrix A (2 * n + 1))) = 1 := by
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => by dsimp only [id]; omega) Filter.tendsto_id
  filter_upwards [hlim.eventually hker, Filter.eventually_ge_atTop R] with n hkerN hn
  refine quasiLocalState_groundSpaceProjection_eq_one_of_interval_eq_zero
    A φ hφ (-(n : ℤ)) (openInteractionMatrix h (2 * n + 1)) ?_ ?_ ?_
  · apply Matrix.isPositive_toEuclideanLin_iff.mp
    rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix
      h hR (by omega)]
    exact openInteractionHamiltonianES_isPositive
      (Matrix.isPositive_toEuclideanLin_iff.mpr hh) _
  · rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix
      h hR (by omega)]
    exact hkerN
  · exact apply_quasiLocalIntervalObservable_openInteractionMatrix_eq_zero
      φ.toLinearMap h hR hzero (-(n : ℤ)) (2 * n + 1)

end MPSTensor
