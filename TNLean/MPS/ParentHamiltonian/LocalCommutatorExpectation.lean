/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalParentExpectation
import TNLean.MPS.ParentHamiltonian.BulkObservableCommutator
import TNLean.MPS.ParentHamiltonian.PrimitiveLocalParentInteractionGap
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces

/-!
# Positivity of local commutator expectations

If a positive finite-volume Hamiltonian annihilates the local MPS space,
then the expectation of \(B^*[H,B]\) equals that of \(B^*HB\) and is
nonnegative. Thus the fixed commutator patch associated with a positive
parent interaction has real nonnegative expectation in each sector.

Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675.
The argument uses finite local support and positivity, not primitivity,
simultaneous injectivity, or a spectral gap.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D N : ℕ}

/-- Positivity and local ground-space support make the commutator expectation
real and nonnegative. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 2649--2675, the finite-volume commutator energy. -/
theorem observableInsertionExpectation_adjoint_commutator_nonneg
    (A : MPSTensor d D) {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (H B : Matrix (Cfg d N) (Cfg d N) ℂ) (hH : H.PosSemidef)
    (hker : groundSpaceES A N ≤ LinearMap.ker (Matrix.toEuclideanLin H)) :
    0 ≤ observableInsertionExpectation A ρ (Bᴴ * (H * B - B * H)) := by
  have hsecond : groundSpaceES A N ≤ LinearMap.ker (Matrix.toEuclideanLin ((Bᴴ * B) * H)) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    exact hker.trans (LinearMap.ker_le_ker_comp _ _)
  have hzero := observableInsertionExpectation_eq_zero_of_groundSpaceES_le_ker
    A ρ ((Bᴴ * B) * H) hsecond
  change 0 ≤ observableInsertionExpectationₗ A ρ N (Bᴴ * (H * B - B * H))
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, map_sub]
  change 0 ≤ observableInsertionExpectation A ρ (Bᴴ * H * B) -
    observableInsertionExpectation A ρ (Bᴴ * B * H)
  simpa only [hzero, sub_zero] using
    observableInsertionExpectation_nonneg A hρ (hH.conjTranspose_mul_mul_same B)

/-- The local commutator patch of a positive parent interaction has real
nonnegative expectation in every block, at every positive interaction range.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem IsParentInteraction.localCommutatorObservable_nonneg
    {b : ℕ} {dim : Fin b → ℕ}
    (μ : Fin b → ℂ) (A : ∀ α, MPSTensor d (dim α)) (hμ : ∀ α, μ α ≠ 0)
    (α : Fin b) {ρ : Matrix (Fin (dim α)) (Fin (dim α)) ℂ} (hρ : ρ.PosSemidef)
    {R k : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k) :
    0 ≤ observableInsertionExpectation (A α) ρ (localCommutatorObservable h X) := by
  let w := (R - 1 + k) + (R - 1)
  have hw : R ≤ w := by dsimp [w]; omega
  have hH : (openInteractionMatrix h w).PosSemidef := by
    apply Matrix.isPositive_toEuclideanLin_iff.mp
    rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hw]
    exact openInteractionHamiltonianES_isPositive hh.isPositive w
  have hker : groundSpaceES (A α) w ≤
      LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h w)) := by
    rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hw,
      hh.ker_openInteractionHamiltonianES_eq_ker_openParentHamiltonianES hR]
    apply le_trans ?_ (groundSpaceES_le_ker_openParentHamiltonianES
      (toTensorFromBlocks (d := d) (μ := μ) A) R w)
    exact groundSpaceES_block_le_toTensorFromBlocks μ A hμ α w
  exact observableInsertionExpectation_adjoint_commutator_nonneg
    (A α) hρ (openInteractionMatrix h w) (bulkObservable X (R - 1) (R - 1)) hH hker

/-- The positive-parent commutator expectation has zero imaginary part in
every block. Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem IsParentInteraction.localCommutatorObservable_im_eq_zero
    {b : ℕ} {dim : Fin b → ℕ}
    (μ : Fin b → ℂ) (A : ∀ α, MPSTensor d (dim α)) (hμ : ∀ α, μ α ≠ 0)
    (α : Fin b) {ρ : Matrix (Fin (dim α)) (Fin (dim α)) ℂ} (hρ : ρ.PosSemidef)
    {R k : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k) :
    (observableInsertionExpectation (A α) ρ (localCommutatorObservable h X)).im = 0 := by
  exact (RCLike.nonneg_iff.mp
    (IsParentInteraction.localCommutatorObservable_nonneg μ A hμ α hρ h hh X hR hk)).2

/-- Every constructed block state has real nonnegative expectation for each
translate of the positive-parent commutator patch. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 3 and lines 2649--2675. -/
theorem IsParentInteraction.quasiLocalExpectation_localCommutatorObservable_nonneg
    {b : ℕ} {dim : Fin b → ℕ} [NeZero d]
    (μ : Fin b → ℂ) (A : ∀ α, MPSTensor d (dim α)) (hμ : ∀ α, μ α ≠ 0)
    (α : Fin b) (hTP : ∑ i, (A α i)ᴴ * A α i = 1)
    {ρ : Matrix (Fin (dim α)) (Fin (dim α)) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap (A α) ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    {R k : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k) :
    0 ≤ quasiLocalExpectation (A α) hTP hρ hfix htr
      (SpinChain.quasiLocalIntervalObservable d a ((R - 1 + k) + (R - 1))
        (localCommutatorObservable h X)) := by
  rw [SpinChain.quasiLocalIntervalObservable_apply, quasiLocalExpectation_interval,
    StarAlgEquiv.apply_symm_apply]
  exact IsParentInteraction.localCommutatorObservable_nonneg μ A hμ α hρ h hh X hR hk

end MPSTensor
