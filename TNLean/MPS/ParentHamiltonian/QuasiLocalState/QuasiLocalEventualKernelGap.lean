/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BulkObservable.BulkObservableCommutator
import TNLean.MPS.ParentHamiltonian.Interaction.EventualKernelOpenGap
import TNLean.MPS.ParentHamiltonian.BulkObservable.MultiblockLocalCommutatorGap
import TNLean.MPS.ParentHamiltonian.BulkObservable.LocalCommutatorExpectation
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalMultiblockGap
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalCommutatorLocality
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.MultiblockQuasiLocalGroundStates

/-!
# Finite-chain and quasi-local gaps from eventual kernel equality

A positive finite-range interaction whose sufficiently long open-chain kernels
are the joint MPS boundary-condition spaces has a uniform finite-chain gap: every
nonzero eigenvalue of its finite-chain Hamiltonians is at least one positive constant.
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
see docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
The interaction range is arbitrary and positive. Classification of pure
zero-energy states is a separate result.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675.

It also contains the following results.

* `MPSTensor.exists_pos_pure_ground_state_commutator_limit_gap_of_eventual_kernel`,
  `MPSTensor.exists_pos_pure_ground_state_commutator_limit_gap_of_wordTupleSpanTop`: uniform
  finite-chain and pure ground-state commutator gaps.
-/

open MPTensor

open Filter SpinChain

section QuasiLocalEventualKernelGap

open scoped Matrix ComplexOrder BigOperators Topology
open ManyBody.Interaction (chainTranslates)

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
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    0 ≤ quasiLocalExpectation (A α) hTP hρ hfix htr
      (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hker
  let n := N₀ + R
  let N := (n + k) + n
  have hH : ((chainTranslates R N h).hamiltonian).PosSemidef :=
    ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates hh N
  have hsupport : ((groundSpace (A α) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) ≤
      LinearMap.ker (Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian)) := by
    rw [hN₀ N (by dsimp [N, n]; omega)]
    exact map_groundSpace_block_le_toTensorFromBlocks μ A hμ α N
  have hnonneg := observableInsertionExpectation_adjoint_commutator_nonneg
    (A α) hρ ((chainTranslates R N h).hamiltonian) (bulkObservable X n n) hH hsupport
  rw [← quasiLocalIntervalObservable_bulkObservable_commutator a h X hR
    (by dsimp [n]; omega : R - 1 ≤ n) (by dsimp [n]; omega : R - 1 ≤ n)]
  rw [quasiLocalExpectation_quasiLocalIntervalObservable]
  exact hnonneg
variable [∀ i, NeZero (D i)]
/-- One positive constant bounds every finite-chain gap above the kernel and the
local commutator expectation in every centered primitive sector.
The original interaction has arbitrary positive range, and only its eventual
global kernel is prescribed. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, lines 933--947, and Section 6, lines 2649--2675. -/
theorem exists_pos_multiblock_localCommutator_gap_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) z →
          z = 0 ∨ (γ : ℂ) ≤ z) ∧
      ∀ α : Fin b, ∀ {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → observableInsertionExpectation (A α) (ρ α) X = 0 →
        γ * (observableInsertionExpectation (A α) (ρ α) (Xᴴ * X)).re ≤
          (observableInsertionExpectation (A α) (ρ α) (localCommutatorObservable h X)).re := by
  obtain ⟨γ, hγ, hgap⟩ := exists_hamiltonian_chainTranslates_gap_of_eventual_kernel
    μ A hμ ρ hP hρ hDistinct h hh hker
  refine ⟨γ, hγ, hgap, ?_⟩
  intro α k X _ hcenter
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  have hN : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [N]; omega) tendsto_id
  obtain ⟨ψ, hg, hu⟩ := (hP α).exists_eventually_unit_map_groundSpace (hρ α) N hN
  apply multiblock_localCommutator_gap_of_openInteraction_gap
    A ρ hP hρ hDistinct α h hh X hR hcenter ψ hγ.le
  · filter_upwards [hN.eventually hker] with n hn
    rwa [map_groundSpace_toTensorFromBlocks_eq_iSup μ A hμ] at hn
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
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    let ω := fun α => quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) z →
          z = 0 ∨ (γ : ℂ) ≤ z) ∧
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

/-- One positive constant simultaneously bounds every finite-chain gap above the kernel
and the literal infinite-volume commutator energy in every constructed
primitive sector. Both endpoints may diverge along an arbitrary filter;
the energy limit and its reality are derived from locality and exact eventual
support. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, lines 933--947, and Section 6, lines 2649--2675. -/
theorem exists_pos_multiblock_quasiLocalCommutator_limit_gap_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    let ω := fun α => quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) z →
          z = 0 ∨ (γ : ℂ) ≤ z) ∧
      ∀ (α : Fin b) (a : ℤ) {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → ω α (quasiLocalIntervalObservable d a k X) = 0 →
      ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
        Tendsto ℓ f atTop → Tendsto r f atTop →
        ∃ e : ℂ, Tendsto (fun n => ω α (star (quasiLocalIntervalObservable d a k X) *
          (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
              ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
            quasiLocalIntervalObservable d a k X -
            quasiLocalIntervalObservable d a k X *
              quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
          (γ : ℂ) * ω α (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X) ≤ e := by
  dsimp only
  obtain ⟨γ, hγ, hfinite, hgap⟩ :=
    exists_pos_multiblock_quasiLocalCommutator_gap_of_eventual_kernel
      μ A hμ ρ hP hρ hDistinct hR h hh hker
  refine ⟨γ, hγ, hfinite, ?_⟩
  intro α a k X hk hcenter ι f ℓ r hℓ hr
  refine ⟨quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
    (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
      (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)), ?_, ?_⟩
  · exact tendsto_apply_quasiLocalIntervalObservable_commutator
      (quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
        (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero) a h X (by omega) hℓ hr
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
        (hP α).trace_ne_zero hR h hh hker a X
      have henergyIm := (Complex.nonneg_iff.mp henergy).2
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        ← hsquareIm, ← henergyIm, mul_zero, zero_mul, add_zero]

end MPSTensor

end QuasiLocalEventualKernelGap

section QuasiLocalGroundStateGap

/-!
## Uniform finite-chain and pure ground-state commutator gaps

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
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, and Section 6, lines 2649--2675.
-/

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open ManyBody.Interaction (chainTranslates)

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
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) z →
          z = 0 ∨ (γ : ℂ) ≤ z) ∧
      ∀ (φ : QuasiLocalAlgebra d →L[ℂ] ℂ),
      φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
      ∀ (a : ℤ) {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
      ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
        Tendsto ℓ f atTop → Tendsto r f atTop →
        ∃ e : ℂ, Tendsto (fun n => φ (star (quasiLocalIntervalObservable d a k X) *
          (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
              ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
            quasiLocalIntervalObservable d a k X -
            quasiLocalIntervalObservable d a k X *
              quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
          (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X) ≤ e := by
  obtain ⟨γ, hγ, hfinite, hsector⟩ :=
    exists_pos_multiblock_quasiLocalCommutator_limit_gap_of_eventual_kernel
      μ A hμ ρ hP hρ hDistinct hR h hh hker
  refine ⟨γ, hγ, hfinite, ?_⟩
  intro φ hφ hPure a k X hk hcenter ι f ℓ r hℓ hr
  obtain ⟨j, rfl⟩ :=
    (isPure_mem_parentGroundStateFace_iff_sector_of_eventually_open_kernel
      μ A hμ ρ hP hρ hDistinct h hh hker φ).mp ⟨hφ, hPure⟩
  exact hsector j a X hk hcenter hℓ hr

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
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ∃ γ : ℝ, 0 < γ ∧
      (∀ N : ℕ, ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) z →
          z = 0 ∨ (γ : ℂ) ≤ z) ∧
      ∀ (φ : QuasiLocalAlgebra d →L[ℂ] ℂ),
      φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
      ∀ (a : ℤ) {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
      ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
        Tendsto ℓ f atTop → Tendsto r f atTop →
        ∃ e : ℂ, Tendsto (fun n => φ (star (quasiLocalIntervalObservable d a k X) *
          (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
              ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
            quasiLocalIntervalObservable d a k X -
            quasiLocalIntervalObservable d a k X *
              quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
          (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X) ≤ e := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, _, hJoint, _⟩ :=
    exists_normalized_parentGroundStateFace_classification_of_eventually_open_kernel
      μ A hμ hS hSpan h hh hker
  have hkerB : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (μ := μ) B) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) :=
    hker.mono fun N hN => hN.trans (hJoint N)
  have hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := fun i j hij e => by
    simpa only [eqRec_eq_cast] using
      not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij e
  exact exists_pos_pure_ground_state_commutator_limit_gap_of_eventual_kernel
    μ B hμ ρ hP hρ hDistinct hR h hh hkerB

end MPSTensor

end QuasiLocalGroundStateGap
