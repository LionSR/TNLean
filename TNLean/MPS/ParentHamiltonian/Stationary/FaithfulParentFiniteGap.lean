/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.ParentHamiltonian.Stationary.FaithfulPeriodicGroundSpace
import TNLean.MPS.ParentHamiltonian.Periodic.PeriodicBlockFamilyQuasiLocalGap
import TNLean.MPS.ParentHamiltonian.Periodic.PeriodicBlockFamilyOpenParentGap
import TNLean.MPS.ParentHamiltonian.Interaction.PrimitiveFamilyIntersection
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalParentGroundStateFace
import TNLean.MPS.ParentHamiltonian.Interaction.ParentInteractionGap

/-!
# Infinite-volume gaps for faithful normalized generators

A left-canonical tensor with a positive-definite stationary matrix admits a
finite periodic-sector presentation of every finite boundary space. Therefore
a positive finite-range interaction whose eventual open-chain kernels are
these spaces has a common positive commutator gap in all pure zero-energy
states. The energy is the literal finite-volume commutator limit along any
exhaustion with both boundary margins diverging. The tensor itself need not
be irreducible, primitive, or periodic.

**Scope restriction (supplied faithful generating data):** A normalized tensor
and a faithful stationary matrix are supplied. The result does not construct
these data from an arbitrary GVBS boundary limit. That separate passage is
recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, the normalized generating data in Section 3, lines 1394--1483,
and the infinite-volume argument in Section 6, lines 2649--2675.

## Finite and infinite parent gaps for faithful stationary generators

Normalized tensors with a faithful stationary matrix have exact canonical
parent kernels at every sufficiently large interaction range. The same
canonical interaction has a uniform finite-volume gap above the kernel at every original
length, and a common literal infinite-volume commutator gap in all pure
zero-energy states. The generated stationary state itself has zero energy;
its purity is not assumed.

**Scope restriction (supplied stationary generators):** The normalized
tensor and faithful stationary matrix are supplied. Their construction from
an arbitrary GVBS boundary-limit presentation remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Lemma existenceinteraction, lines 2195--2230, and Section 6.

## Gaps for a given interaction with faithful stationary generators

Every positive interaction of positive range whose eventual open kernels are
the boundary spaces of supplied faithful stationary normalized generators
has a uniform finite-volume gap at every original chain length. The same
given interaction also has a common literal infinite-volume commutator gap
in every pure zero-energy state. The local kernel is not assumed to equal the
boundary space at the interaction range.

**Scope restriction (supplied stationary generators):** The generators are
supplied; their construction from an arbitrary GVBS boundary-limit
presentation remains separate. See
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, and Section 6, lines 2593--2675.
-/

open MPTensor

section

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d D R : ℕ}

/-- Faithful normalized generating data and an eventual exact open-chain
kernel identity give one positive literal commutator gap in every pure
zero-energy state, for every centered local observable and every diverging
pair of boundary margins. No irreducibility, primitivity, periodicity, or
translation invariance of a competing state is assumed.
Source context: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, Section 3, lines 1394--1483, and Section 6, lines 2649--2675. -/
theorem exists_pos_quasiLocalCommutator_limit_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
        ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
          ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
            Tendsto ℓ f atTop → Tendsto r f atTop →
          ∃ e : ℂ, Tendsto (fun n => φ
            (star (quasiLocalIntervalObservable d a k X) *
              (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                  ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨b, _hb, dim, _hdim, B, _V, m, hPeriodic, _hV, _hSum, _hOrth,
    _hInt, _hCoInt, _hCorner, hGS⟩ :=
    exists_periodic_groundSpaceDecomposition_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix
  have hJointKer : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) B) N).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap) :=
    hker.mono fun N hN => hN.trans (hGS N)
  exact exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    (fun _ => 1) B (fun _ => one_ne_zero) m hPeriodic h hR hh hJointKer

end MPSTensor

end

section

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d D : ℕ}

/-- Faithful stationary normalized generators give exact canonical kernels
at all sufficiently large interaction ranges and one gap above the kernel at every
original volume for each such range. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2 and Section 6,
in the supplied generating-data setting. -/
theorem exists_hamiltonian_parentChainInteraction_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ) :
    ∃ R₀, 0 < R₀ ∧ ∀ R, R₀ ≤ R →
      (∀ N, R ≤ N →
        LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
            ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N,
        ∀ μ : ℂ, Module.End.HasEigenvalue
          (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
            μ = 0 ∨ (δ : ℂ) ≤ μ := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨b, _hb, dim, _hdim, B, _V, m, hPeriodic, _hV, _hSum, _hOrth,
    _hInt, _hCoInt, _hCorner, hGS⟩ :=
    exists_periodic_groundSpaceDecomposition_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix
  obtain ⟨R₀, hR₀, hFamily⟩ := exists_hamiltonian_parentChainInteraction_gap_of_periodic_family
    (fun _ => 1) B (fun _ => one_ne_zero) m hPeriodic
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨hKernel, δ, hδ, hGap⟩ := hFamily R hR
  have hH := hamiltonian_parentChainInteraction_eq_of_map_groundSpace_eq (hGS R)
  refine ⟨fun N hN => ?_, δ, hδ, fun N => ?_⟩
  · rw [hH N, hKernel N hN]
    exact (hGS N).symm
  · rw [hH N]
    exact hGap N

/-- One constructed parent interaction has exact open kernels, contains the
generated stationary state in its zero-energy face, and has both an all-length
finite-volume gap and a common literal infinite-volume commutator gap in every
pure zero-energy state. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorems 1.1--1.2 and Section 6, in the supplied generating-data setting. -/
theorem exists_positive_parent_finite_and_quasiLocal_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N, R ≤ N → LinearMap.ker
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) = ((groundSpace A N).map
            (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) ∧
      quasiLocalExpectation A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) ∈
        parentGroundStateFace h ∧
      ∃ δ : ℝ, 0 < δ ∧
      (∀ N, ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ) ∧
      ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
        ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
          ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
            Tendsto ℓ f atTop → Tendsto r f atTop →
          ∃ e : ℂ, Tendsto (fun n => φ
            (star (quasiLocalIntervalObservable d a k X) *
              (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                  ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  change (∑ i, (A i)ᴴ * A i) = 1 at hA
  obtain ⟨R, hR, hRange⟩ :=
    exists_hamiltonian_parentChainInteraction_gap_of_leftCanonical_of_posDef_fixedPoint A hA hρ hFix
  obtain ⟨hCanonicalKernel, δ, hδ, hFinite⟩ := hRange R le_rfl
  obtain ⟨h, hEq, hh, hKernel⟩ :=
    exists_posSemidef_eq_toMatrix'_parentInteraction_of_ker_hamiltonian_parentChainInteraction
      A hCanonicalKernel
  have hMember : quasiLocalExpectation A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) ∈
      parentGroundStateFace h := by
    rw [hEq]
    exact quasiLocalExpectation_mem_parentGroundStateFace_canonicalParentInteraction
      A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) R
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_pos_quasiLocalCommutator_limit_gap_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix h hR hh ((eventually_ge_atTop R).mono fun N hN => hKernel N hN)
  refine ⟨R, hR, h, hh, hKernel, hMember, δ, hδ, ?_, γ, hγ, hGap⟩
  rw [hEq]
  exact hFinite

end MPSTensor

end

section

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d D R : ℕ}

/-- The supplied interaction's eventual exact boundary kernels suffice for
an all-length gap above the kernel. No local kernel condition is added. Source:
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
in the supplied faithful generating-data setting. -/
theorem exists_given_interaction_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop, LinearMap.ker
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) = ((groundSpace A N).map
          (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨R₀, hR₀, hCanonical⟩ :=
    exists_hamiltonian_parentChainInteraction_gap_of_leftCanonical_of_posDef_fixedPoint A hA hρ hFix
  exact exists_toEuclideanLin_hamiltonian_chainTranslates_gap_of_canonical_gaps_of_eventual_kernel
    A hR₀ hCanonical h hh hKernel

/-- The same given positive interaction has a uniform finite gap above the kernel and
one literal infinite-volume commutator gap in every pure zero-energy state.
Only its eventual exact open kernels are supplied. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, and Section 6,
in the supplied faithful generating-data setting. -/
theorem exists_given_interaction_finite_quasiLocal_gap_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop, LinearMap.ker
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) = ((groundSpace A N).map
          (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    ∃ δ : ℝ, 0 < δ ∧
      (∀ N, ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ) ∧
      ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
        ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
          ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
            Tendsto ℓ f atTop → Tendsto r f atTop →
          ∃ e : ℂ, Tendsto (fun n => φ
            (star (quasiLocalIntervalObservable d a k X) *
              (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                  ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨δ, hδ, hFinite⟩ :=
    exists_given_interaction_gap_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix h hh hKernel
  obtain ⟨γ, hγ, hInfinite⟩ :=
    exists_pos_quasiLocalCommutator_limit_gap_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix h hR hh hKernel
  exact ⟨δ, hδ, hFinite, γ, hγ, hInfinite⟩

end MPSTensor

end
