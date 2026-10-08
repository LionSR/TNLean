/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.BlockWordSpanSeparation
import TNLean.MPS.ParentHamiltonian.MultiblockQuasiLocalGroundStates

/-!
# Ground-state classification after primitive normalization

A simultaneous word span at a positive length allows independent primitive
normalization of the blocks. This preserves every block boundary-condition
space and the weighted joint space at every length. An eventual open-chain
kernel identity for the original family therefore transfers to the normalized
family, whose full zero-energy state face is the convex hull of its primitive
sector states and whose pure ground states are precisely those sectors.
The range of the original positive interaction is arbitrary and positive.

Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129;
Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
lines 1394--1435, and Theorems 1.1--1.2, lines 854--947.

**Scope restriction (original simultaneously spanning families):** This
corollary constructs primitive representatives of the supplied original family
from its simultaneous word span. It does not establish the passage from a
general periodic GVBS presentation to that family. See
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open scoped Topology ComplexOrder BigOperators
open SpinChain
namespace MPSTensor
variable {d b R : ℕ} [NeZero d] {D : Fin b → ℕ} [∀ j, NeZero (D j)]
/-- Primitive normalization of an original simultaneously spanning family
preserves its finite-volume supports and classifies the whole zero-energy
state face under an eventual kernel identity. Source: CPGSV21,
arXiv:2011.12127, Section IV.C, lines 2114--2129; Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2, lines 854--947. -/
theorem exists_normalized_parentGroundStateFace_classification_of_eventually_open_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    {S : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (μ := μ) A) N) :
    ∃ (B : ∀ j, MPSTensor d (D j))
      (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
      (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)),
      (∀ j, (ρ j).PosDef) ∧ WordTupleSpanTop B S ∧
      (∀ j N, groundSpace (A j) N = groundSpace (B j) N) ∧
      (∀ N, groundSpaceES (toTensorFromBlocks (μ := μ) A) N =
        groundSpaceES (toTensorFromBlocks (μ := μ) B) N) ∧
      let ω := fun j => quasiLocalExpectation (B j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero
      (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h ↔ ∃ w : Fin b → ℝ,
          (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ φ = ∑ j, w j • ω j) ∧
      (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔
          ∃ j, φ = ω j) := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_isPrimitiveMPS_family_of_wordTupleSpanTop A hS hSpan
  have hJoint : ∀ N, groundSpaceES (toTensorFromBlocks (μ := μ) A) N =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N :=
    fun N => congrArg (fun G => G.map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
      (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq
        μ μ A B hμ hμ (fun j => hGS j N))
  have hkerB : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (μ := μ) B) N :=
    hker.mono fun N hN => hN.trans (hJoint N)
  have hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := fun i j hij e => by
    simpa only [eqRec_eq_cast] using
      not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij e
  exact ⟨B, ρ, hP, hρ, hSpanB, hGS, hJoint,
    fun φ => mem_parentGroundStateFace_iff_convex_combination_of_eventually_open_kernel
      μ B hμ ρ hP hρ hDistinct h hR hh hkerB φ,
    fun φ => isPure_mem_parentGroundStateFace_iff_sector_of_eventually_open_kernel
      μ B hμ ρ hP hρ hDistinct h hR hh hkerB φ⟩
end MPSTensor
