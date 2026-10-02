/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalMultiblockGap
import TNLean.MPS.ParentHamiltonian.QuasiLocalCommutatorLocality
import TNLean.MPS.ParentHamiltonian.LocalCommutatorExpectation
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalPurity

/-!
# Infinite-volume commutator gap in the constructed MPS sectors

The literal finite-volume energy of a local observable is eventually constant
in the quasi-local algebra. Its expectation in each constructed primitive
sector therefore converges to the fixed local commutator expectation. Positivity
and local ground-space support make this limit real and nonnegative. The common
finite-volume gap gives the same positive lower bound in every sector. A further
corollary derives the primitive representatives and purity from the original
simultaneous word-spanning family, preserving all block ground spaces.

**Scope restriction (constructed primitive sectors at sufficient range):** The
family has a supplied positive simultaneous injectivity length `S`, and the
interaction range is at least `S + 1`. The theorem concerns the constructed
sector states. Classification of every pure state in the source ground-state
face is separate. See
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and the infinite-volume commutator argument, lines 2649--2675.
-/

open Filter SpinChain
open scoped Matrix ComplexOrder BigOperators Topology
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
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    let ω := fun α => quasiLocalExpectation (A α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    ∃ γ : ℝ, 0 < γ ∧ ∀ (α : Fin b) (a : ℤ) {k : ℕ}
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
  obtain ⟨γ, hγ, hgap⟩ := exists_pos_multiblock_quasiLocalCommutator_gap_of_isParentInteraction
    μ A hμ ρ hP hρ hS hSpan hR h hh
  refine ⟨γ, hγ, ?_⟩
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
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    ∃ (B : ∀ i, MPSTensor d (D i))
      (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
      (hP : ∀ i, IsPrimitiveMPS (B i) (ρ i)),
      (∀ i, (ρ i).PosDef) ∧ (∀ i N, groundSpace (A i) N = groundSpace (B i) N) ∧
    let ω := fun α => quasiLocalExpectation (B α) (hP α).norm (hP α).fixedPoint_psd
      (hP α).fixedPoint_is_fixed (hP α).trace_ne_zero
    (∀ α, IsPureQuasiLocalState d (ω α)) ∧
    ∃ γ : ℝ, 0 < γ ∧ ∀ (α : Fin b) (a : ℤ) {k : ℕ}
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
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_isPrimitiveMPS_family_of_wordTupleSpanTop A hS hSpan
  refine ⟨B, ρ, hP, hρ, hGS, ?_, ?_⟩
  · exact fun α => (hP α).isPureQuasiLocalState_quasiLocalExpectation (hρ α)
  · apply exists_pos_multiblock_quasiLocalCommutator_limit_gap
      μ B hμ ρ hP hρ hS hSpanB hR h _ hℓ hr
    refine ⟨hh.isPositive, hh.ker_eq.trans ?_⟩
    exact congrArg (fun G => G.map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
      (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ μ A B hμ hμ
        (fun i => hGS i R))

end MPSTensor
