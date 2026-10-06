/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.MultiblockQuasiLocalFace
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalPurity
import TNLean.QCA.FinitePureStateDecomposition

/-!
# States supported in a finite sum of primitive MPS spaces

Let \(A_j\) be finitely many inequivalent primitive tensors with faithful
invariant matrices, and let all block coefficients be nonzero. A normalized
positive state satisfies \(\varphi(P_I)=1\) for the joint MPS support
projection of every nonempty interval exactly when
\(\varphi=\sum_j w_j\omega_j\), with \(w_j\geq0\) and
\(\sum_j w_j=1\). Its pure states are precisely the \(\omega_j\).

The forward implication follows from the centered-interval compression
argument. Each sector state has exact joint support, so every convex combination
has the same support. Extremality in the full state space then identifies
the pure supported states. No interaction or translation invariance is assumed.

**Scope restriction (primitive sector families):** The two classification
theorems concern primitive sectors with faithful invariant matrices. Identifying
an arbitrary periodic GVBS presentation with such a family after blocking is
separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
The joint projection-expectation identity does not require primitivity.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 854--926, and the support and purity discussion in Section 3.
-/

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open SpinChain
namespace MPSTensor
variable {d b : ℕ} [NeZero d] {D : Fin b → ℕ} [∀ j, NeZero (D j)]

omit [∀ j, NeZero (D j)] in
/-- Every normalized sector state has expectation one on the joint weighted
MPS support projection. No primitivity is needed. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, finite-interval support spaces and
Theorem 1.1, lines 906--926. -/
theorem quasiLocalExpectation_toTensorFromBlocks_groundSpaceProjection_eq_one
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (j : Fin b) (hTP : ∑ i, (A j i)ᴴ * A j i = 1)
    {ρ : Matrix (Fin (D j)) (Fin (D j)) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap (A j) ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (a : ℤ) (N : ℕ) :
    quasiLocalExpectation (A j) hTP hρ hfix htr
      (quasiLocalIntervalObservable d a N
        (groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) N)) = 1 := by
  have hX : groundSpaceES (A j) N ≤ LinearMap.ker
      (Matrix.toEuclideanLin
        (1 - groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) N)) := by
    intro v hv
    change Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (1 - groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) N) v = 0
    simp only [map_sub, map_one, groundSpaceProjectionMatrix,
      StarAlgEquiv.apply_symm_apply, sub_apply, one_apply_eq_self,
      Submodule.starProjection_eq_self_iff.mpr
        (groundSpaceES_block_le_toTensorFromBlocks μ A hμ j N hv), sub_self]
  have hzero := quasiLocalExpectation_interval_eq_zero_of_groundSpaceES_le_ker
    (A j) hTP hρ hfix htr a
    (1 - groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) N) hX
  rw [map_sub, map_one, map_sub,
    (quasiLocalExpectation_isState (A j) hTP hρ hfix htr).2.1] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- A normalized positive state is supported in all nonempty joint MPS
intervals exactly when it is a convex combination of the primitive sector
states. The coefficients are derived; translation invariance is unnecessary.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 854--926, and Section 3. -/
theorem groundSpace_supported_iff_convex_combination_of_isPrimitiveMPS
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d) :
    (∀ (a : ℤ) (N : ℕ), 0 < N → φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) N)) = 1) ↔
      ∃ w : Fin b → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
        φ = ∑ j, w j • quasiLocalExpectation (A j) (hP j).norm
          (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
  constructor
  · exact fun hSupport =>
      exists_convex_combination_quasiLocalExpectation_of_eventually_groundSpace_support
        μ A hμ ρ hP hρ hDistinct φ hφ
        (Filter.Eventually.of_forall fun n => hSupport (-(n : ℤ)) (2 * n + 1) (by omega))
  · rintro ⟨w, hw, hsum, rfl⟩ a N hN
    simp only [sum_apply, smul_apply,
      quasiLocalExpectation_toTensorFromBlocks_groundSpaceProjection_eq_one μ A hμ]
    simp only [← Finset.sum_smul, hsum, one_smul]

/-- The pure states supported in all nonempty joint MPS intervals are
precisely the constructed primitive sector states. Purity is taken among all
states. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 854--887 and 1469--1482, and Theorem 1.1. -/
theorem isPure_groundSpace_supported_iff_sector_of_isPrimitiveMPS
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    ((∀ (a : ℤ) (N : ℕ), 0 < N → φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix (toTensorFromBlocks (μ := μ) A) N)) = 1) ∧
      IsPureQuasiLocalState d φ) ↔
      ∃ j, φ = quasiLocalExpectation (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
  constructor
  · rintro ⟨hSupport, hPure⟩
    obtain ⟨w, hw, hsum, hdecomp⟩ :=
      (groundSpace_supported_iff_convex_combination_of_isPrimitiveMPS
        μ A hμ ρ hP hρ hDistinct φ hPure.1).mp hSupport
    exact exists_eq_of_isPureQuasiLocalState_of_finite_decomposition φ hPure
      (fun j => quasiLocalExpectation (A j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
      (fun j => quasiLocalExpectation_isState (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
      w hw hsum hdecomp
  · rintro ⟨j, rfl⟩
    exact ⟨fun a N _ =>
      quasiLocalExpectation_toTensorFromBlocks_groundSpaceProjection_eq_one μ A hμ j
        (hP j).norm (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed
        (hP j).trace_ne_zero a N,
      (hP j).isPureQuasiLocalState_quasiLocalExpectation (hρ j)⟩
end MPSTensor
