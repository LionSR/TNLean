/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.MultiblockLocalCommutatorGap
import TNLean.MPS.ParentHamiltonian.QuasiLocalPrimitiveGap

/-!
# A common quasi-local commutator gap for all canonical sectors

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
-/

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
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
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
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h)) :
    ∃ (B : ∀ i, MPSTensor d (D i))
      (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
      (hP : ∀ i, IsPrimitiveMPS (B i) (ρ i)),
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
    exists_isPrimitiveMPS_family_of_wordTupleSpanTop A hS hSpan
  refine ⟨B, ρ, hP, hρ, hGS, ?_⟩
  apply exists_pos_multiblock_quasiLocalCommutator_gap_of_isParentInteraction
    μ B hμ ρ hP hρ hS hSpanB hR h
  refine ⟨hh.isPositive, hh.ker_eq.trans ?_⟩
  exact congrArg (fun G => G.map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
    (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ μ A B hμ hμ
      (fun i => hGS i R))


end MPSTensor
