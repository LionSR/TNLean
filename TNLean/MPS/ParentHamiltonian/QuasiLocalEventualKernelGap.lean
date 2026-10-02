/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.EventualKernelOpenGap
import TNLean.MPS.ParentHamiltonian.MultiblockLocalCommutatorGap
import TNLean.MPS.ParentHamiltonian.LocalCommutatorExpectation
import TNLean.MPS.ParentHamiltonian.QuasiLocalPrimitiveGap
import TNLean.MPS.ParentHamiltonian.QuasiLocalCommutatorLocality

/-!
# Finite-chain and quasi-local gaps from eventual kernel equality

A positive finite-range interaction whose sufficiently long open-chain kernels
are the joint MPS boundary-condition spaces has a uniform finite-chain norm gap.
For a finite family of distinct primitive sectors, the same positive constant
bounds the literal infinite-volume commutator energy in every constructed
sector state. The two outer endpoints may diverge along any filter.

The commutator energy is real and nonnegative: choose a sufficiently large
positive finite-volume Hamiltonian with the exact joint kernel, apply sector
support, and identify its expectation with the fixed local commutator patch.
No equality of the original local kernel with an MPS space is assumed.

**Scope restriction (primitive sector family):** The gap statements concern
finitely many pairwise gauge-phase inequivalent primitive tensors with faithful
invariant matrices. The source permits more general periodic GVBS presentations;
see `docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
The interaction range is arbitrary and positive. Classification of pure
zero-energy states is a separate result.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675.
-/

open Filter SpinChain
open scoped Matrix ComplexOrder BigOperators Topology
namespace MPSTensor
variable {d b : ℕ} {D : Fin b → ℕ} [NeZero d]
/-- The eventual joint kernel gives a real nonnegative local commutator
expectation in each normalized sector. Primitivity and faithfulness are not
needed for this positivity statement. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem quasiLocalExpectation_localCommutatorObservable_nonneg_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (α : Fin b) (hTP : ∑ i, (A α i)ᴴ * A α i = 1)
    {ρ : Matrix (Fin (D α)) (Fin (D α)) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap (A α) ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    {R k : ℕ} (hR : 0 < R) (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N)
    (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hk : 0 < k) :
    0 ≤ quasiLocalExpectation (A α) hTP hρ hfix htr
      (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hker
  let n := N₀ + R
  let N := (n + k) + n
  have hRN : R ≤ N := by dsimp [n, N]; omega
  have hH : (openInteractionMatrix h N).PosSemidef := by
    apply Matrix.isPositive_toEuclideanLin_iff.mp
    rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hRN]
    exact openInteractionHamiltonianES_isPositive
      (Matrix.isPositive_toEuclideanLin_iff.mpr hh) N
  have hsupport : groundSpaceES (A α) N ≤
      LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h N)) := by
    rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hRN,
      hN₀ N (by dsimp [N, n]; omega)]
    exact groundSpaceES_block_le_toTensorFromBlocks μ A hμ α N
  have hnonneg := observableInsertionExpectation_adjoint_commutator_nonneg
    (A α) hρ (openInteractionMatrix h N) (bulkObservable X n n) hH hsupport
  rw [← quasiLocalIntervalObservable_bulkObservable_commutator a h X hR hk
    (by dsimp [n]; omega : R - 1 ≤ n) (by dsimp [n]; omega : R - 1 ≤ n)]
  rw [quasiLocalExpectation_quasiLocalIntervalObservable]
  exact hnonneg
variable [∀ i, NeZero (D i)]
/-- One positive constant bounds every finite-chain norm gap and the
local commutator expectation in every centered primitive sector.
The original interaction has arbitrary positive range, and only its eventual
global kernel is prescribed. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, lines 933--947, and Section 6, lines 2649--2675. -/
theorem exists_pos_multiblock_localCommutator_gap_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) :
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        γ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖) ∧
      ∀ α : Fin b, ∀ {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → observableInsertionExpectation (A α) (ρ α) X = 0 →
        γ * (observableInsertionExpectation (A α) (ρ α) (Xᴴ * X)).re ≤
          (observableInsertionExpectation (A α) (ρ α) (localCommutatorObservable h X)).re := by
  obtain ⟨γ, hγ, hgap⟩ := exists_openInteractionMatrix_gap_of_eventual_kernel
    μ A hμ ρ hP hρ hDistinct hR h hh hker
  refine ⟨γ, hγ, hgap, ?_⟩
  intro α k X hk hcenter
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  have hN : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [N]; omega) tendsto_id
  obtain ⟨ψ, hg, hu⟩ := (hP α).exists_eventually_unit_groundSpaceES (hρ α) N hN
  apply multiblock_localCommutator_gap_of_openInteraction_gap
    A ρ hP hρ hDistinct α h (Matrix.isPositive_toEuclideanLin_iff.mpr hh) X hR hk hcenter ψ hγ.le
  · filter_upwards [hN.eventually hker] with n hn
    rwa [groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ] at hn
  · exact Eventually.of_forall fun n => hgap (N n)
  · exact Eventually.of_forall hg
  · exact hu

/-- The same finite-chain constant bounds the local commutator patch in
each constructed quasi-local sector state, uniformly over positions and
centered observables. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, lines 933--947, and Section 6, lines 2649--2675. -/
theorem exists_pos_multiblock_quasiLocalCommutator_gap_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) :
    let ω := fun α => quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        γ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖) ∧
      ∀ (α : Fin b) (a : ℤ) {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → ω α (quasiLocalIntervalObservable d a k X) = 0 →
        γ * (ω α (star (quasiLocalIntervalObservable d a k X) *
          quasiLocalIntervalObservable d a k X)).re ≤
        (ω α (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
          ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X))).re := by
  dsimp only
  obtain ⟨γ, hγ, hfinite, hgap⟩ := exists_pos_multiblock_localCommutator_gap_of_eventual_kernel
    μ A hμ ρ hP hρ hDistinct hR h hh hker
  refine ⟨γ, hγ, hfinite, ?_⟩
  intro α a k X hk hcenter
  rw [quasiLocalExpectation_quasiLocalIntervalObservable] at hcenter
  rw [← map_star (quasiLocalIntervalObservable d a k) X, ← map_mul,
    quasiLocalExpectation_quasiLocalIntervalObservable,
    quasiLocalExpectation_quasiLocalIntervalObservable]
  exact hgap α X hk hcenter

/-- One positive constant simultaneously bounds every finite-chain norm
gap and the literal infinite-volume commutator energy in every constructed
primitive sector. Both endpoints may diverge along an arbitrary filter;
the energy limit and its reality are derived from locality and exact eventual
support. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, lines 933--947, and Section 6, lines 2649--2675. -/
theorem exists_pos_multiblock_quasiLocalCommutator_limit_gap_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    let ω := fun α => quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        γ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖) ∧
      ∀ (α : Fin b) (a : ℤ) {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → ω α (quasiLocalIntervalObservable d a k X) = 0 →
        ∃ e : ℂ, Tendsto (fun n => ω α (star (quasiLocalIntervalObservable d a k X) *
          (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
              (openInteractionMatrix h ((ℓ n + k) + r n)) *
            quasiLocalIntervalObservable d a k X -
            quasiLocalIntervalObservable d a k X *
              quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                (openInteractionMatrix h ((ℓ n + k) + r n))))) f (𝓝 e) ∧
          (γ : ℂ) * ω α (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X) ≤ e := by
  dsimp only
  obtain ⟨γ, hγ, hfinite, hgap⟩ :=
    exists_pos_multiblock_quasiLocalCommutator_gap_of_eventual_kernel
      μ A hμ ρ hP hρ hDistinct hR h hh hker
  refine ⟨γ, hγ, hfinite, ?_⟩
  intro α a k X hk hcenter
  refine ⟨quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
    (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
      (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)), ?_, ?_⟩
  · exact tendsto_apply_quasiLocalIntervalObservable_commutator
      (quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
        (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero) a h X (by omega) hk hℓ hr
  · rw [Complex.le_def]
    constructor
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using hgap α a X hk hcenter
    · have hsquare := (quasiLocalExpectation_isState (A α) (hP α).norm
        (hP α).fixedPoint_psd (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero).2.2
          (quasiLocalIntervalObservable d a k X)
      have hsquareIm := (Complex.nonneg_iff.mp hsquare).2
      have henergy :=
        quasiLocalExpectation_localCommutatorObservable_nonneg_of_eventual_kernel
        μ A hμ α (hP α).norm (hP α).fixedPoint_psd (hP α).fixedPoint_is_fixed
        (hP α).trace_ne_zero hR h hh hker a X hk
      have henergyIm := (Complex.nonneg_iff.mp henergy).2
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        ← hsquareIm, ← henergyIm, mul_zero, zero_mul, add_zero]

end MPSTensor
