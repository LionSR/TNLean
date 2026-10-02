/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.NormalizedQuasiLocalGroundStates
import TNLean.MPS.ParentHamiltonian.QuasiLocalEventualKernelGap

/-!
# Uniform finite-chain and pure ground-state commutator gaps

For an inequivalent primitive sector family with faithful invariant matrices,
a positive finite-range interaction whose eventual open-chain kernel is the
joint MPS space has one positive constant controlling every finite-chain gap
and the literal infinite-volume commutator energy in every pure ground state.
Both interval endpoints may tend to infinity along an arbitrary filter.
The classification of pure zero-energy states identifies each with a sector;
the finite-volume bound, full ground-projection decay, locality, and reality
of the energy expectation have already been proved for these sectors.
Simultaneous word span of an original family also suffices: its primitive
representatives and faithful invariant matrices are derived internally.
No lower bound on the original interaction range beyond positivity is imposed.

**Scope restriction (primitive and simultaneously spanning families):** The
first conclusion concerns the given primitive family; the second derives it
from simultaneous word span in the original family. The source also treats
more general periodic GVBS
presentations; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, and Section 6, lines 2649--2675.
-/
open Filter SpinChain
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d b : ℕ} [NeZero d] {D : Fin b → ℕ} [∀ j, NeZero (D j)]

/-- One positive constant controls every finite-chain gap and the literal
commutator inequality in every pure locally zero-energy state. No invariance
of the competing state is assumed. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, and Section 6,
lines 2649--2675. -/
theorem exists_pos_pure_ground_state_commutator_limit_gap_of_eventual_kernel
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
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        γ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖) ∧
      ∀ (φ : QuasiLocalAlgebra d →L[ℂ] ℂ),
      φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
      ∀ (a : ℤ) {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
        ∃ e : ℂ, Tendsto (fun n => φ (star (quasiLocalIntervalObservable d a k X) *
          (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
              (openInteractionMatrix h ((ℓ n + k) + r n)) *
            quasiLocalIntervalObservable d a k X -
            quasiLocalIntervalObservable d a k X *
              quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                (openInteractionMatrix h ((ℓ n + k) + r n))))) f (𝓝 e) ∧
          (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X) ≤ e := by
  obtain ⟨γ, hγ, hfinite, hsector⟩ :=
    exists_pos_multiblock_quasiLocalCommutator_limit_gap_of_eventual_kernel
      μ A hμ ρ hP hρ hDistinct hR h hh hker hℓ hr
  refine ⟨γ, hγ, hfinite, ?_⟩
  intro φ hφ hPure a k X hk hcenter
  obtain ⟨j, rfl⟩ :=
    (isPure_mem_parentGroundStateFace_iff_sector_of_eventually_open_kernel
      μ A hμ ρ hP hρ hDistinct h hR hh hker φ).mp ⟨hφ, hPure⟩
  exact hsector j a X hk hcenter

/-- Simultaneous word span in the original block family gives one positive
constant for every finite-chain gap and the literal commutator inequality in
all pure locally zero-energy states under the eventual kernel hypothesis.
Primitive representatives and invariant matrices are derived internally;
no comparison between the original range and the span length is imposed.
Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129;
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675. -/
theorem exists_pos_pure_ground_state_commutator_limit_gap_of_wordTupleSpanTop
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    {S : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S)
    {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        γ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖) ∧
      ∀ (φ : QuasiLocalAlgebra d →L[ℂ] ℂ),
      φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
      ∀ (a : ℤ) {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
        ∃ e : ℂ, Tendsto (fun n => φ (star (quasiLocalIntervalObservable d a k X) *
          (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
              (openInteractionMatrix h ((ℓ n + k) + r n)) *
            quasiLocalIntervalObservable d a k X -
            quasiLocalIntervalObservable d a k X *
              quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                (openInteractionMatrix h ((ℓ n + k) + r n))))) f (𝓝 e) ∧
          (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X) ≤ e := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, _, hJoint, _⟩ :=
    exists_normalized_parentGroundStateFace_classification_of_eventually_open_kernel
      μ A hμ hS hSpan h hR hh hker
  have hkerB : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (μ := μ) B) N :=
    hker.mono fun N hN => hN.trans (hJoint N)
  have hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := fun i j hij e => by
    simpa only [eqRec_eq_cast] using
      not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij e
  exact exists_pos_pure_ground_state_commutator_limit_gap_of_eventual_kernel
    μ B hμ ρ hP hρ hDistinct hR h hh hkerB hℓ hr

end MPSTensor
