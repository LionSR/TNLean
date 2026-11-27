/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableTranslationInvariance
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalCommutatorLocality
import TNLean.QCA.QuasiLocal.BlockingIntervalCoordinates
import TNLean.QCA.State.BlockingStateTransport
import TNLean.QCA.QuasiLocal.BlockingTranslation
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicBlockFamilyPresentation
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalGroundStateSupport
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedQuasiLocalFace
import TNLean.MPS.CanonicalForm.BNT.Separation
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicPrimitiveGroundSpace

/-!
# Local expectations of periodic ground-state components

A normalized stationary MPS state on a chain of blocks becomes a state on the
original lattice by inverse blocking of observables. It is invariant under translations
by the block length. Aligned interval expectations are the original
blocked insertion formula. On an interval beginning inside a block, the
observable is first placed in a containing aligned interval and then reindexed
into block coordinates. This formula retains the position within a block.

The existing periodic-family ground-state classification therefore gives one
common positive translation period for every pure zero-energy component.
Neither one-site invariance nor minimality of the resulting period is asserted.

Source: Nachtergaele, arXiv:cond-mat/9410110, lines 825--836 (periodic states
and site grouping), Theorem 1.1, and Section 3, equations (3.1)--(3.2b).

**Scope restriction (tensor presentation):** The ground-state consequence
starts from supplied normalized periodic tensors and an eventual exact open
kernel. The passage from arbitrary GVBS data to such generating tensors remains
separate; see docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

It also contains the following results.

* `MPSTensor.exists_parentGroundStateFace_classification_of_periodic_family`,
  `MPSTensor.IsPeriodic.exists_parentGroundStateFace_classification_of_eventually_open_kernel`:
  quasi-local ground states of finite periodic block families.
-/

open MPTensor

section PeriodicBlockFamilyGroundStates

/-!
## Quasi-local ground states of finite periodic block families

A finite weighted family of normalized periodic tensors admits a positive
blocking length and an exact presentation of its blocked boundary spaces by
inequivalent primitive sectors with faithful invariant matrices. If a positive
interaction of positive range has the original joint MPS space as its eventual
open-chain kernel, its entire zero-energy state face is the convex hull of the
primitive sector states transported to the original lattice. Its pure states
are exactly these transported states.

Periodicity derives the sector tensors, invariant matrices, and inequivalence.
The original family may be empty, in which case the state face is empty.
Competing states are not assumed translation invariant. No bound relating the
interaction range to an injectivity length is imposed. This result does not
assert existence of the interaction or a spectral gap.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, site grouping at lines 825--836, and Section 3;
DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451.

**Scope restriction (periodic tensor families):** The theorem starts from an
explicit finite periodic MPS family. Identifying a general GVBS presentation
with such tensor data and its finite support spaces remains separate. See
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

### Quasi-local ground states of a periodic MPS tensor

A periodic tensor, blocked by its period, admits a nonempty finite presentation
by inequivalent primitive sectors with faithful invariant matrices. If a
positive interaction of positive range has the original tensor's open MPS
space as its eventual finite-volume kernel, its entire zero-energy state face
is the convex hull of the sector states transported to the original lattice.
Its pure ground states are exactly those transported sector states.

The sector tensors, invariant matrices, and inequivalence are derived from
periodicity. States are not assumed translation invariant. No injectivity
bound is imposed on the original interaction range, and this result makes no
claim about the existence of an interaction or its spectral gap.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, site grouping at lines 825--836, and the local support and
purity discussion in Section 3, lines 1394--1538; DCCSP17,
arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451.

**Scope restriction (periodic tensor presentations):** The theorem starts
from an explicit periodic MPS tensor. Identifying a general periodic GVBS
presentation with this tensor and its finite support spaces remains separate.
See docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

section

open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
open SpinChain
open Kraus (blockPhysDim blockTensor)
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d r R : ℕ} [NeZero d] {dim : Fin r → ℕ}

/-- A finite periodic family determines, after positive blocking, primitive
faithful inequivalent sectors that classify the whole zero-energy state face
and its pure states under the original eventual open-chain kernel identity.
The representative family may be empty. Translation invariance of a competing
state, supplied fixed-point matrices, and original sector inequivalence are
not assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, the site grouping at lines 825--836, and Section 3;
DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem exists_parentGroundStateFace_classification_of_periodic_family
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ∃ (L : ℕ) (hL : 0 < L),
      let _ : NeZero L := ⟨Nat.ne_of_gt hL⟩
      ∃ (g : ℕ) (bdim : Fin g → ℕ) (hdim : ∀ j, 0 < bdim j),
        let _ : ∀ j, NeZero (bdim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
        ∃ (B : ∀ j, MPSTensor (blockPhysDim d L) (bdim j))
          (ρ : ∀ j, Matrix (Fin (bdim j)) (Fin (bdim j)) ℂ)
          (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)),
          (∀ j, (ρ j).PosDef) ∧ BlocksNotGaugePhaseEquiv B ∧
          (∀ N, ((groundSpace (blockTensor (toTensorFromBlocks μ A) L) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) =
            ((groundSpace (toTensorFromBlocks (fun _ => 1) B) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) ∧
          let ω := fun j => quasiLocalBlockingFunctional d L
            (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
              (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
          (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
            φ ∈ parentGroundStateFace h ↔ ∃ w : Fin g → ℝ,
              (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ φ = ∑ j, w j • ω j) ∧
          (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
            (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔
              ∃ j, φ = ω j) := by
  obtain ⟨L, hL, g, bdim, hdim, B, ρ, hP, hρ, hDistinct, hJoint⟩ :=
    exists_primitive_blockFamilyPresentation_of_isPeriodic μ A hμ m hPeriodic
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let : ∀ j, NeZero (bdim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  let ω := fun j => quasiLocalBlockingFunctional d L
    (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
      (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
  have hState : ∀ j, ω j ∈ quasiLocalStateSpace d := fun j =>
    (quasiLocalBlockingFunctional_mem_stateSpace_iff d L _).mpr
      (quasiLocalExpectation_isState (B j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
  refine ⟨L, hL, g, bdim, hdim, B, ρ, hP, hρ, hDistinct, hJoint, ?_, ?_⟩
  · refine fun φ => ⟨?_, ?_⟩
    · exact fun hφ =>
        (groundSpace_supported_iff_convex_combination_of_blocked_primitive_family
          (toTensorFromBlocks μ A) (fun _ => 1) B (fun _ => one_ne_zero)
          ρ hP hρ hDistinct.forall_ne_transport hJoint φ hφ.1).mp
            ((mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
              (toTensorFromBlocks μ A) h hR hh hker φ).mp hφ).2
    · rintro ⟨w, hw, hsum, hdecomp⟩
      have hφ : φ ∈ quasiLocalStateSpace d := hdecomp.symm ▸
        convex_quasiLocalStateSpace.sum_mem (fun j _ => hw j) hsum (fun j _ => hState j)
      exact (mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
        (toTensorFromBlocks μ A) h hR hh hker φ).mpr ⟨hφ,
          (groundSpace_supported_iff_convex_combination_of_blocked_primitive_family
            (toTensorFromBlocks μ A) (fun _ => 1) B (fun _ => one_ne_zero)
            ρ hP hρ hDistinct.forall_ne_transport hJoint φ hφ).mpr ⟨w, hw, hsum, hdecomp⟩⟩
  · refine fun φ => ⟨?_, ?_⟩
    · exact fun hφ =>
        (isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
          (toTensorFromBlocks μ A) (fun _ => 1) B (fun _ => one_ne_zero)
          ρ hP hρ hDistinct.forall_ne_transport hJoint φ hφ.1.1).mp
            ⟨((mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
              (toTensorFromBlocks μ A) h hR hh hker φ).mp hφ.1).2, hφ.2⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨hSupport, hPure⟩ :=
        (isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
          (toTensorFromBlocks μ A) (fun _ => 1) B (fun _ => one_ne_zero)
          ρ hP hρ hDistinct.forall_ne_transport hJoint (ω j) (hState j)).mpr ⟨j, rfl⟩
      exact ⟨(mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
        (toTensorFromBlocks μ A) h hR hh hker (ω j)).mpr ⟨hState j, hSupport⟩, hPure⟩
end MPSTensor

end

section

open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
open SpinChain
open Kraus (blockPhysDim blockTensor)
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d D m R : ℕ} [NeZero d]

/-- Periodicity derives a finite primitive sector family whose transported
states classify both the entire zero-energy face and its pure states under
the original interaction's eventual open-chain kernel identity.
The output retains faithful invariant matrices, sector inequivalence, and
exact blocked support at every length, including zero.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, site grouping at lines 825--836, and Section 3;
DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem IsPeriodic.exists_parentGroundStateFace_classification_of_eventually_open_kernel
    {A : MPSTensor d D} (hA : IsPeriodic m A)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (g : ℕ), 0 < g ∧
      ∃ (dim : Fin g → ℕ) (hdim : ∀ j, 0 < dim j),
        let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
        ∃ (B : ∀ j, MPSTensor (blockPhysDim d m) (dim j))
          (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
          (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)),
          (∀ j, (ρ j).PosDef) ∧ BlocksNotGaugePhaseEquiv B ∧
          (∀ N, ((groundSpace (blockTensor A m) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) =
            ((groundSpace (toTensorFromBlocks (μ := fun _ => 1) B) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) ∧
          let ω := fun j => quasiLocalBlockingFunctional d m
            (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
              (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
          (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
            φ ∈ parentGroundStateFace h ↔ ∃ w : Fin g → ℝ,
              (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ φ = ∑ j, w j • ω j) ∧
          (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
            (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔
              ∃ j, φ = ω j) := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨g, hg, dim, hdim, B, ρ, hP, hρ, hDistinct, hJoint⟩ :=
    hA.exists_inequivalent_primitive_groundStatePresentation
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hDistinct' : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := hDistinct.forall_ne_transport
  let ω := fun j => quasiLocalBlockingFunctional d m
    (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
      (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
  have hState : ∀ j, ω j ∈ quasiLocalStateSpace d := fun j =>
    (quasiLocalBlockingFunctional_mem_stateSpace_iff d m _).mpr
      (quasiLocalExpectation_isState (B j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
  refine ⟨g, hg, dim, hdim, B, ρ, hP, hρ, hDistinct, hJoint, ?_, ?_⟩
  · refine fun φ => ⟨?_, ?_⟩
    · exact fun hφ =>
        (groundSpace_supported_iff_convex_combination_of_blocked_primitive_family
          A (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ hDistinct' hJoint φ hφ.1).mp
            ((mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
              A h hR hh hker φ).mp hφ).2
    · rintro ⟨w, hw, hsum, hdecomp⟩
      have hφ : φ ∈ quasiLocalStateSpace d := hdecomp.symm ▸
        convex_quasiLocalStateSpace.sum_mem (fun j _ => hw j) hsum (fun j _ => hState j)
      exact (mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
        A h hR hh hker φ).mpr ⟨hφ,
          (groundSpace_supported_iff_convex_combination_of_blocked_primitive_family
            A (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ hDistinct' hJoint φ hφ).mpr
              ⟨w, hw, hsum, hdecomp⟩⟩
  · refine fun φ => ⟨?_, ?_⟩
    · exact fun hφ =>
        (isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
          A (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ hDistinct' hJoint φ hφ.1.1).mp
            ⟨((mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
              A h hR hh hker φ).mp hφ.1).2, hφ.2⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨hSupport, hPure⟩ :=
        (isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
          A (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ hDistinct' hJoint
            (ω j) (hState j)).mpr ⟨j, rfl⟩
      exact ⟨(mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
        A h hR hh hker (ω j)).mpr ⟨hState j, hSupport⟩, hPure⟩
end MPSTensor

end

end PeriodicBlockFamilyGroundStates

section PeriodicSectorExpectations

open scoped Matrix MatrixOrder ComplexOrder BigOperators
open SpinChain
open Kraus (blockPhysDim)
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d D L : ℕ} [NeZero d] [NeZero L]

/-- A blocked stationary expectation is invariant under translations by
integer multiples of the block length. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 825--836. -/
theorem blockedQuasiLocalExpectation_quasiLocalTranslation
    (B : MPSTensor (blockPhysDim d L) D)
    (hTP : ∑ i, (B i)ᴴ * B i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap B ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (b : ℤ) (X : QuasiLocalAlgebra d) :
    quasiLocalBlockingFunctional d L (quasiLocalExpectation B hTP hρ hfix htr)
        (quasiLocalTranslation d (b * L) X) =
      quasiLocalBlockingFunctional d L (quasiLocalExpectation B hTP hρ hfix htr) X := by
  simp only [quasiLocalBlockingFunctional_apply]
  have h := congrArg (quasiLocalBlocking d L).symm
    (quasiLocalBlocking_translation d L b ((quasiLocalBlocking d L).symm X))
  simp only [StarAlgEquiv.symm_apply_apply, StarAlgEquiv.apply_symm_apply] at h
  rw [← h]
  exact quasiLocalExpectation_quasiLocalTranslation B hTP hρ hfix htr b _

/-- On an aligned interval, the transported state is the blocked insertion
expectation after the exact configuration reindexing. Length zero is included.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 825--836 and
Section 3, equations (3.1)--(3.2b). -/
theorem blockedQuasiLocalExpectation_interval
    (B : MPSTensor (blockPhysDim d L) D)
    (hTP : ∑ i, (B i)ᴴ * B i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap B ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (a : ℤ) (N : ℕ)
    (X : Matrix (Cfg (blockPhysDim d L) N) (Cfg (blockPhysDim d L) N) ℂ) :
    quasiLocalBlockingFunctional d L (quasiLocalExpectation B hTP hρ hfix htr)
      (quasiLocalIntervalObservable d (a * L) (N * L)
        (Matrix.reindex (Kraus.blockedConfigEquiv d N L) (Kraus.blockedConfigEquiv d N L) X)) =
      observableInsertionExpectation B ρ X := by
  rw [← quasiLocalBlocking_quasiLocalIntervalObservable,
    quasiLocalBlockingFunctional_apply, StarAlgEquiv.symm_apply_apply,
    quasiLocalExpectation_quasiLocalIntervalObservable]

/-- An interval observable has the blocked insertion expectation of its
nonwrapping placement in any containing aligned interval, reindexed into
block coordinates. The position inside a block remains explicit.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 825--836 and
Section 3, equations (3.1)--(3.2b). -/
theorem blockedQuasiLocalExpectation_window
    (B : MPSTensor (blockPhysDim d L) D)
    (hTP : ∑ i, (B i)ᴴ * B i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap B ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (a : ℤ) (N b : ℕ) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hb : b + k ≤ N * L) :
    quasiLocalBlockingFunctional d L (quasiLocalExpectation B hTP hρ hfix htr)
      (quasiLocalIntervalObservable d (a * L + (b : ℤ)) k X) =
      observableInsertionExpectation B ρ
        (Matrix.reindex (Kraus.blockedConfigEquiv d N L).symm (Kraus.blockedConfigEquiv d N L).symm
          (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow b hb) X)) := by
  rw [← quasiLocalIntervalObservable_placeAlong_chainWindow (a * L) (N * L) b X hb]
  have h := blockedQuasiLocalExpectation_interval B hTP hρ hfix htr a N
    (Matrix.reindex (Kraus.blockedConfigEquiv d N L).symm (Kraus.blockedConfigEquiv d N L).symm
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow b hb) X))
  have hidx : Matrix.reindex (Kraus.blockedConfigEquiv d N L) (Kraus.blockedConfigEquiv d N L)
      (Matrix.reindex (Kraus.blockedConfigEquiv d N L).symm (Kraus.blockedConfigEquiv d N L).symm
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow b hb) X)) =
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow b hb) X := by
    ext σ τ
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [hidx] at h
  exact h

/-- Every pure zero-energy state of a finite periodic tensor family has a
common positive translation period, derived before the state and observable
are chosen. No one-site invariance or minimal-period assertion is made.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 907--930, and the grouping convention at lines 825--836. -/
theorem exists_common_translation_period_of_pure_parentGroundStates_of_periodic_family
    {r R : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ∃ L : ℕ, 0 < L ∧ ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
      φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
      ∀ (b : ℤ) (X : QuasiLocalAlgebra d), φ (quasiLocalTranslation d (b * L) X) = φ X := by
  obtain ⟨L, hL, g, bdim, hdim, B, ρ, hP, hρ, hDistinct, hJoint, hConvex, hPure⟩ :=
    exists_parentGroundStateFace_classification_of_periodic_family μ A hμ m hPeriodic h hR hh hker
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let : ∀ j, NeZero (bdim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  refine ⟨L, hL, ?_⟩
  intro φ hφ hφpure
  obtain ⟨j, rfl⟩ := (hPure φ).mp ⟨hφ, hφpure⟩
  exact blockedQuasiLocalExpectation_quasiLocalTranslation (B j) (hP j).norm
    (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero

end MPSTensor

end PeriodicSectorExpectations
