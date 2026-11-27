/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableQuasiLocalState
import TNLean.MPS.ParentHamiltonian.BulkObservable.PrimitiveLocalParentInteractionGap
import TNLean.QCA.QuasiLocal.QuasiLocalInterval
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.BulkObservable.MultiblockLocalCommutatorGap
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalCommutatorLocality
import TNLean.MPS.ParentHamiltonian.BulkObservable.LocalCommutatorExpectation
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.PrimitiveQuasiLocalUniqueness

/-!
# A primitive-sector commutator gap in the quasi-local state

The normalized positive quasi-local MPS state has the original trace
insertion expectations on finite intervals. The primitive local commutator
bound therefore gives a positive energy inequality for every centered local
observable in this constructed state. All finite-volume and limiting estimates
are derived from the tensor and the positive parent interaction.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172.

**Scope restriction (one primitive sector):** The commutator theorem assumes
a normalized primitive tensor with a positive-definite invariant matrix and
interaction range at least \(D^4+1\). Identification of all pure multiblock
GVBS states and construction of the GNS Hamiltonian remain separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

## A common quasi-local commutator gap for all canonical sectors

For a finite family of normalized primitive tensors, simultaneous injectivity
at a positive length gives a common positive parent-interaction gap at every
larger interaction range. The exact full-ground projection decay and local
commutator limits yield one positive inequality in each constructed sector
state, uniformly over sectors, positions, and centered local observables.
Primitive representatives and their invariant matrices can also be derived
from simultaneous injectivity of an arbitrary original block family.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172.

**Scope restriction (constructed primitive sectors at sufficient range):**
The statement concerns the quasi-local state of each given primitive block,
with range exceeding a simultaneous injectivity length. Identification of the
full pure GVBS ground-state face remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

## Infinite-volume commutator gap in the constructed MPS sectors

The literal finite-volume energy of a local observable is eventually constant
in the quasi-local algebra. Its expectation in each constructed primitive
sector therefore converges to the fixed local commutator expectation. Positivity
and local ground-space support make this limit real and nonnegative. The common
finite-volume gap gives the same positive lower bound in every sector. A further
corollary derives the primitive representatives and purity from the original
simultaneous word-spanning family, preserving all block ground spaces.

**Scope restriction (constructed primitive sectors at sufficient range):** The
family has a supplied positive simultaneous injectivity length \(S\), and the
interaction range is at least \(S+1\). The theorem concerns the constructed
sector states. Classification of every pure state in the source ground-state
face is separate. See
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and the infinite-volume commutator argument, lines 2649--2675.
-/

open MPTensor

section

open scoped Matrix BigOperators ComplexOrder
open SpinChain

namespace Kraus.HasComplementaryFixedPointGap

open MPSTensor

variable {d D : ℕ}

/-- Every positive parent interaction at range at least \(D^4+1\) has a
positive commutator bound in the constructed primitive quasi-local state.
The constant is independent of the interval, its position, and the observable.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem exists_pos_quasiLocalCommutator_gap_of_isParentInteraction
    [NeZero d] [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef) {R : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) (hR : D ^ 4 + 1 ≤ R) :
    let ω := quasiLocalExpectation A hP.norm hP.fixedPoint_psd
      hP.fixedPoint_is_fixed hP.trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧ ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → ω (quasiLocalIntervalObservable d a k X) = 0 →
        γ * (ω (star (quasiLocalIntervalObservable d a k X) *
          quasiLocalIntervalObservable d a k X)).re ≤
        (ω (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ)) ((R - 1 + k) + (R - 1))
          (localCommutatorObservable h X))).re := by
  dsimp only
  obtain ⟨γ, hγ, hgap⟩ := hP.exists_pos_localCommutator_gap_of_isParentInteraction hρ h hh hR
  refine ⟨γ, hγ, ?_⟩
  intro a k X hk hcenter
  rw [quasiLocalExpectation_quasiLocalIntervalObservable] at hcenter
  rw [← map_star (quasiLocalIntervalObservable d a k) X, ← map_mul,
    quasiLocalExpectation_quasiLocalIntervalObservable,
    quasiLocalExpectation_quasiLocalIntervalObservable]
  exact hgap X hk hcenter

end Kraus.HasComplementaryFixedPointGap

end

section

open scoped Matrix ComplexOrder BigOperators
open SpinChain

namespace MPSTensor

variable {d b : ℕ} {D : Fin b → ℕ} [NeZero d] [∀ i, NeZero (D i)]

/-- Every positive parent interaction of a weighted canonical block family
has one positive quasi-local commutator constant for all constructed sector
states and all centered local observables, at sufficient range.
No boundary vectors or limiting estimates are supplied.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem exists_pos_multiblock_quasiLocalCommutator_gap_of_isParentInteraction
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R
      (Matrix.toEuclideanLin h)) :
    let ω := fun α => quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧ ∀ (α : Fin b) (a : ℤ) {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → ω α (quasiLocalIntervalObservable d a k X) = 0 →
        γ * (ω α (star (quasiLocalIntervalObservable d a k X) *
          quasiLocalIntervalObservable d a k X)).re ≤
        (ω α (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
          ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X))).re := by
  dsimp only
  obtain ⟨γ, hγ, hgap⟩ := exists_pos_multiblock_localCommutator_gap_of_isParentInteraction
    μ A hμ ρ hP hρ hS hSpan hR h hh
  refine ⟨γ, hγ, ?_⟩
  intro α a k X hk hcenter
  rw [quasiLocalExpectation_quasiLocalIntervalObservable] at hcenter
  rw [← map_star (quasiLocalIntervalObservable d a k) X, ← map_mul,
    quasiLocalExpectation_quasiLocalIntervalObservable,
    quasiLocalExpectation_quasiLocalIntervalObservable]
  exact hgap α X hk hcenter

/-- Simultaneous injectivity of an arbitrary block family produces primitive
representatives with the same local support spaces, and a common positive
quasi-local commutator bound for every positive parent interaction of the
original weighted tensor. No normalized blocks or invariant matrices are
supplied as hypotheses. Source: CPGSV21, arXiv:2011.12127, Section IV.C,
lines 2114--2129; Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and
Section 6, lines 2649--2675. -/
theorem exists_primitiveFamily_quasiLocalCommutator_gap_of_wordTupleSpanTop
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R
      (Matrix.toEuclideanLin h)) :
    ∃ (B : ∀ i, MPSTensor d (D i))
      (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
      (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (B i) (ρ i)),
      (∀ i, (ρ i).PosDef) ∧ (∀ i N, groundSpace (A i) N = groundSpace (B i) N) ∧
      (let ω := fun α => quasiLocalExpectation (B α) (hP α).norm (hP α).fixedPoint_psd
        (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
      ∃ γ : ℝ, 0 < γ ∧ ∀ (α : Fin b) (a : ℤ) {k : ℕ}
        (X : Matrix (Cfg d k) (Cfg d k) ℂ),
        0 < k → ω α (quasiLocalIntervalObservable d a k X) = 0 →
          γ * (ω α (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X)).re ≤
          (ω α (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
            ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X))).re) := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop A hS hSpan
  refine ⟨B, ρ, hP, hρ, hGS, ?_⟩
  apply exists_pos_multiblock_quasiLocalCommutator_gap_of_isParentInteraction
    μ B hμ ρ hP hρ hS hSpanB hR h
  refine ⟨hh.isPositive, hh.ker_eq.trans ?_⟩
  exact congrArg (fun G => G.map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
    (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ μ A B hμ hμ
      (fun i => hGS i R))


end MPSTensor

end

section

open Filter SpinChain
open scoped Matrix ComplexOrder BigOperators Topology
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d b : ℕ} {D : Fin b → ℕ} [NeZero d] [∀ i, NeZero (D i)]

/-- Every positive parent interaction at range exceeding simultaneous injectivity
has a common positive literal infinite-volume commutator bound in its constructed
primitive sectors. Both free intervals may grow along any filter. The energy
limit and its reality are derived, with no finite-volume uniqueness assumption.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675. -/
theorem exists_pos_multiblock_quasiLocalCommutator_limit_gap
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R
      (Matrix.toEuclideanLin h)) :
    let ω := fun α => quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧ ∀ (α : Fin b) (a : ℤ) {k : ℕ}
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
  obtain ⟨γ, hγ, hgap⟩ := exists_pos_multiblock_quasiLocalCommutator_gap_of_isParentInteraction
    μ A hμ ρ hP hρ hS hSpan hR h hh
  refine ⟨γ, hγ, ?_⟩
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
      have henergy := IsParentInteraction.quasiLocalExpectation_localCommutatorObservable_nonneg
        μ A hμ α (hP α).norm (hP α).fixedPoint_psd (hP α).fixedPoint_is_fixed
        (hP α).trace_ne_zero h hh (a - ((R - 1 : ℕ) : ℤ)) X (by omega) hk
      have henergyIm := (Complex.nonneg_iff.mp henergy).2
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        ← hsquareIm, ← henergyIm, mul_zero, zero_mul, add_zero]

/-- Simultaneous word span for the original family produces primitive
representatives preserving every block ground space, pure completed sector
states, and a common literal infinite-volume commutator gap for the original
positive interaction. No normalized blocks or invariant matrices are supplied.
Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129;
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6, lines 2649--2675. -/
theorem exists_pure_primitiveFamily_quasiLocalCommutator_limit_gap_of_wordTupleSpanTop
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R
      (Matrix.toEuclideanLin h)) :
    ∃ (B : ∀ i, MPSTensor d (D i))
      (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
      (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (B i) (ρ i)),
      (∀ i, (ρ i).PosDef) ∧ (∀ i N, groundSpace (A i) N = groundSpace (B i) N) ∧
    let ω := fun α => quasiLocalExpectation (B α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    (∀ α, IsPureQuasiLocalState d (ω α)) ∧
    ∃ γ : ℝ, 0 < γ ∧ ∀ (α : Fin b) (a : ℤ) {k : ℕ}
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
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop A hS hSpan
  refine ⟨B, ρ, hP, hρ, hGS, ?_, ?_⟩
  · exact fun α => TNLean.MPS.ParentHamiltonian.isPureQuasiLocalState_quasiLocalExpectation (hP α)
      (hρ α)
  · apply exists_pos_multiblock_quasiLocalCommutator_limit_gap
      μ B hμ ρ hP hρ hS hSpanB hR h _
    refine ⟨hh.isPositive, hh.ker_eq.trans ?_⟩
    exact congrArg (fun G => G.map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
      (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ μ A B hμ hμ
        (fun i => hGS i R))

end MPSTensor

end
