/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.MultiblockQuasiLocalFace
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalGroundStateSupport
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalParentGroundStateFace
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalOpenInteractionExpectation
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.PrimitiveQuasiLocalUniqueness
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockWordSpanSeparation
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockOpenGroundSpace
import TNLean.MPS.ParentHamiltonian.ParentInteraction.CanonicalParentInteractionMatrix

/-!
# Classification of the quasi-local ground-state face

Let a weighted tensor consist of finitely many inequivalent primitive sectors
with faithful invariant matrices. If a positive finite-range interaction has
this tensor's MPS space as its open-chain kernel at every sufficiently large
length, its entire zero-energy state face is the convex hull of the constructed
sector states. Its pure ground states are precisely those sector states.
The state being classified need not be translation invariant. No comparison
between the original interaction range and an injectivity length is assumed.

**Scope restriction (primitive sector families):** The source also permits
more general periodic GVBS presentations. The present classification concerns
the given primitive tensor family; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 854--947, and the support analysis in Section 3.

## Ground-state classification after primitive normalization

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

## An interaction realizing the ground-state face of primitive sectors

For finitely many inequivalent primitive tensors with faithful invariant
matrices, choose a sufficiently long canonical parent projection. Its open
Hamiltonian has exactly the joint boundary-condition space as kernel at every
volume at least its interaction range. Its entire zero-energy state face is
the convex hull of the constructed sector states, and its pure zero-energy
states are precisely those sectors. No interaction range or simultaneous
injectivity length is supplied.

The bound on the number of sites is \(N\geq R\), including the single-window
volume. This is stronger than the source convention \(N\geq R+1\), obtained
from \(N_{\mathrm{right}}-N_{\mathrm{left}}\geq R\) on inclusive intervals.

**Scope restriction (primitive sector family):** The source existence theorem
allows arbitrary GVBS states, including more general periodic presentations.
The statements here concern the given finite primitive family; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
Purity means extremality among all normalized positive quasi-local states;
translation invariance of a state being classified is not assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1, lines 906--917,
and its finite-family consequence, lines 919--924. The open-kernel threshold
is PGVWC07, arXiv:quant-ph/0608197, Theorem 12, lines 1430--1454.
-/

section

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open SpinChain
namespace MPSTensor
variable {d b R : ℕ} [NeZero d] {D : Fin b → ℕ} [∀ j, NeZero (D j)]

/-- For finitely many inequivalent primitive sectors, the eventual open-chain
kernel identity classifies all locally zero-energy states as convex combinations
of the constructed sector states. The coefficients are derived, and translation
invariance of the state is unnecessary. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2, lines 854--947, and Section 3. -/
theorem mem_parentGroundStateFace_iff_convex_combination_of_eventually_open_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (μ := μ) A) N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    φ ∈ parentGroundStateFace h ↔
      ∃ w : Fin b → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
        φ = ∑ j, w j • quasiLocalExpectation (A j) (hP j).norm
          (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
  constructor
  · intro hφ
    exact exists_convex_combination_quasiLocalExpectation_of_eventually_groundSpace_support
      μ A hμ ρ hP hρ hDistinct φ hφ.1
      (eventually_quasiLocalState_symmetric_groundSpaceProjection_eq_one_of_eventual_kernel
        (toTensorFromBlocks (μ := μ) A) h hR hh hker φ hφ.1 hφ.2)
  · rintro ⟨w, hw, hsum, rfl⟩
    exact (convex_parentGroundStateFace h).sum_mem (fun j _ => hw j) hsum
      (fun j _ => ⟨quasiLocalExpectation_isState (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero,
        quasiLocalExpectation_interval_eq_zero_of_eventually_open_kernel μ A hμ j
          (hP j).norm (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed
          (hP j).trace_ne_zero h hR hker⟩)
/-- The pure locally zero-energy states are precisely the constructed primitive
sector states. Purity means extremality among all normalized positive states.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 854--947, and the purity discussion at lines 1469--1482. -/
theorem isPure_mem_parentGroundStateFace_iff_sector_of_eventually_open_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (μ := μ) A) N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔
      ∃ j, φ = quasiLocalExpectation (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
  constructor
  · rintro ⟨hφ, hPure⟩
    obtain ⟨w, hw, hsum, hdecomp⟩ :=
      (mem_parentGroundStateFace_iff_convex_combination_of_eventually_open_kernel
        μ A hμ ρ hP hρ hDistinct h hR hh hker φ).mp hφ
    exact exists_eq_of_isPureQuasiLocalState_of_finite_decomposition φ hPure
      (fun j => quasiLocalExpectation (A j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
      (fun j => quasiLocalExpectation_isState (A j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero) w hw hsum hdecomp
  · rintro ⟨j, rfl⟩
    exact ⟨⟨quasiLocalExpectation_isState (A j) (hP j).norm
      (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero,
      quasiLocalExpectation_interval_eq_zero_of_eventually_open_kernel μ A hμ j
        (hP j).norm (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed
        (hP j).trace_ne_zero h hR hker⟩,
      (hP j).isPureQuasiLocalState_quasiLocalExpectation (hρ j)⟩

end MPSTensor

end

section

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
      (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)),
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
    exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop A hS hSpan
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

end

section

open Filter SpinChain
open scoped Matrix ComplexOrder BigOperators Topology
namespace MPSTensor
variable {d b : ℕ} {D : Fin b → ℕ} [NeZero d] [∀ i, NeZero (D i)]
/-- A finite inequivalent primitive family admits a positive canonical
parent interaction of a derived range \(R>0\), with exact joint open kernel
for every volume \(N\geq R\). Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.1, lines 906--917; PGVWC07,
arXiv:quant-ph/0608197, Theorem 12, lines 1430--1454. -/
theorem exists_positive_parent_interaction_of_hasComplementaryFixedPointGap
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧ ∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N := by
  obtain ⟨R, hR, hKernel⟩ :=
    exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES
      μ A hμ ρ hP hρ hDistinct
  let T := toTensorFromBlocks (d := d) (μ := μ) A
  let h := canonicalParentInteractionMatrix T R
  have hmatrix : Matrix.toEuclideanLin h = parentInteractionES T R :=
    toEuclideanLin_canonicalParentInteractionMatrix T R
  refine ⟨R, hR, h, ?_, ?_⟩
  · exact canonicalParentInteractionMatrix_posSemidef T R
  · intro N hN
    rw [hmatrix, openInteractionHamiltonianES_parentInteractionES T hR]
    exact hKernel R N le_rfl hN

/-- One positive interaction realizes both the exact joint open kernels
at all volumes at least its derived range and the entire convex face of
constructed primitive sector states. Its pure zero-energy states are precisely
the sectors, with no translation-invariance assumption on the state.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 906--917, and the finite-family consequence, lines 919--924. -/
theorem exists_positive_parent_interaction_groundStateFace_of_hasComplementaryFixedPointGap
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) ∧
      (∀ᶠ N : ℕ in atTop,
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) ∧
      let ω := fun j => quasiLocalExpectation (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero
      (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h ↔
          ∃ w : Fin b → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ φ = ∑ j, w j • ω j) ∧
      (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔ ∃ j, φ = ω j) := by
  obtain ⟨R, hR, h, hh, hKernel⟩ :=
    exists_positive_parent_interaction_of_hasComplementaryFixedPointGap μ A hμ ρ hP hρ hDistinct
  have hEventual : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N :=
    (eventually_ge_atTop R).mono fun N hN => hKernel N hN
  refine ⟨R, hR, h, hh, hKernel, hEventual, ?_, ?_⟩
  · exact fun φ => mem_parentGroundStateFace_iff_convex_combination_of_eventually_open_kernel
      μ A hμ ρ hP hρ hDistinct h hR hh hEventual φ
  · exact fun φ => isPure_mem_parentGroundStateFace_iff_sector_of_eventually_open_kernel
      μ A hμ ρ hP hρ hDistinct h hR hh hEventual φ

end MPSTensor

end
