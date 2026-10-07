/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CompactParentInteractionGap
import TNLean.MPS.ParentHamiltonian.Martingale.CanonicalOpenGap
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction
import TNLean.MPS.ParentHamiltonian.Martingale.PositiveComparisonGap

/-!
# Uniform open-chain gaps for positive parent interactions

Positive local parent interactions are comparable with the canonical parent
projection. Summing nonwrapping translates preserves the comparison, so the
canonical open-chain gap transfers to each fixed interaction. Compactness gives
a common lower comparison constant for continuous families. In particular,
for a fixed canonical tensor, compact families of positive local parent
interactions have one positive gap uniform in the parameter and chain length.

Source: CPGSV21, arXiv:2011.12127, lines 2170--2172; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6.

**Scope restriction (sufficient interaction range):** The canonical-tensor
consequences assume either \(R\geq S+1\) at a supplied simultaneous injectivity
length, or \(R\geq3D^5\). The comparison theorems have no injectivity assumption.
The range restriction is documented in
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.
-/

open scoped Topology ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A fixed positive parent interaction is comparable in both directions to the
canonical open parent Hamiltonian, with constants independent of chain length.
Source: CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem IsParentInteraction.exists_pos_open_comparison {R : ℕ} {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) (hR : 0 < R) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ N : ℕ,
      (κ : ℂ) • openParentHamiltonianES A R N ≤ openInteractionHamiltonianES h N ∧
      openInteractionHamiltonianES h N ≤ (C : ℂ) • openParentHamiltonianES A R N := by
  obtain ⟨κ, C, hκ, hC, hLower, hUpper⟩ := hh.exists_pos_comparison
  refine ⟨κ, C, hκ, hC, fun N ↦ ⟨?_, ?_⟩⟩
  · simpa only [openInteractionHamiltonianES_smul,
      openInteractionHamiltonianES_parentInteractionES A hR] using
      openInteractionHamiltonianES_mono hLower N
  · simpa only [openInteractionHamiltonianES_smul,
      openInteractionHamiltonianES_parentInteractionES A hR] using
      openInteractionHamiltonianES_mono hUpper N
/-- A uniform canonical open-chain gap transfers to a fixed positive parent
interaction. Source: CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem IsParentInteraction.exists_open_uniform_gap_of_canonical_gap
    {R : ℕ} {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) (hR : 0 < R) {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ N : ℕ, R ≤ N → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ v ∈
      (LinearMap.ker (openInteractionHamiltonianES h N))ᗮ,
      δ * ‖v‖ ≤ ‖openInteractionHamiltonianES h N v‖ := by
  obtain ⟨κ, C, hκ, hC, hComp⟩ := hh.exists_pos_open_comparison hR
  refine ⟨κ * γ, mul_pos hκ hγ, fun N hN ↦ ?_⟩
  simpa only [div_one] using
    (openParentHamiltonianES_isPositive A R N).norm_gap_of_smul_le_of_le_smul
      (openInteractionHamiltonianES_isPositive hh.isPositive N)
      (b := 1) hκ zero_lt_one hC hγ
      (by simpa only [Complex.ofReal_one, one_smul] using (hComp N).1)
      (by simpa only [Complex.ofReal_one, one_smul] using (hComp N).2)
      (hGap N hN)
/-- Every fixed positive parent interaction of a canonical tensor has a uniform
open-chain gap at an admissible simultaneous injectivity range.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6;
CPGSV21, arXiv:2011.12127, lines 2114--2129 and 2170--2172. -/
theorem CPSVCanonicalFormData.exists_openInteraction_uniform_gap_of_wordTupleSpanTop
    [NeZero d] {A : MPSTensor d D} (data : CPSVCanonicalFormData A) {S R : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S) (hR : S + 1 ≤ R)
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ v ∈
      (LinearMap.ker (openInteractionHamiltonianES h N))ᗮ,
      δ * ‖v‖ ≤ ‖openInteractionHamiltonianES h N v‖ := by
  obtain ⟨γ, hγ, hGap⟩ := data.exists_openParentHamiltonianES_gap_of_wordTupleSpanTop
    hS hSpan hR
  exact hh.exists_open_uniform_gap_of_canonical_gap (by omega) hγ
    (fun N hN ↦ by
      simpa only [data.ker_openParentHamiltonianES_eq_groundSpaceES_of_wordTupleSpanTop
        hS hSpan hR hN] using hGap N hN)
/-- A supplied uniform open-chain canonical gap transfers to a compact continuous
family of positive parent interactions with continuous local ground projections.
This proves the positive comparison step; the canonical family gap is supplied.
Source: CPGSV21, arXiv:2011.12127, lines 2170--2172; arXiv:1010.3732,
Appendix A, lines 2477--2480 and 2575--2578. -/
theorem exists_uniform_openInteractionHamiltonianES_gap_of_compact_canonical_gap
    {X : Type*} [TopologicalSpace X] {R N₀ : ℕ}
    (A : X → MPSTensor d D)
    (hProj : Continuous fun x ↦ (groundSpaceES (A x) R).starProjection)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction (A x) R (H x).toLinearMap)
    {K : Set X} (hK : IsCompact K) (hR : 0 < R) {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ x ∈ K, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES (A x) R N))ᗮ,
        γ * ‖v‖ ≤ ‖openParentHamiltonianES (A x) R N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  obtain ⟨κ, hκ, hLower⟩ :=
    exists_uniform_pos_parentInteractionES_le_of_compact A hProj H hH hParent hK
  refine ⟨κ * γ, mul_pos hκ hγ, fun x hx N hN ↦ ?_⟩
  obtain ⟨_, C, _, hC, hComparison⟩ := (hParent x).exists_pos_open_comparison hR
  have hLowerN : (κ : ℂ) • openParentHamiltonianES (A x) R N ≤
      openInteractionHamiltonianES (H x).toLinearMap N := by
    simpa only [openInteractionHamiltonianES_smul,
      openInteractionHamiltonianES_parentInteractionES (A x) hR] using
      openInteractionHamiltonianES_mono (hLower x hx) N
  simpa only [div_one] using
    (openParentHamiltonianES_isPositive (A x) R N).norm_gap_of_smul_le_of_le_smul
      (openInteractionHamiltonianES_isPositive (hParent x).isPositive N)
      (b := 1) hκ zero_lt_one hC hγ
      (by simpa only [Complex.ofReal_one, one_smul] using hLowerN)
      (by simpa only [Complex.ofReal_one, one_smul] using (hComparison N).2)
      (hGap x hx N hN)
/-- A compact continuous family of positive parent interactions for one fixed
canonical tensor has one positive open-chain gap uniform in the parameter and
all admissible lengths. The tensor and its simultaneous injectivity length are
fixed. This is a consequence of the local projector comparison in CPGSV21,
arXiv:2011.12127, lines 2170--2172, and Nachtergaele's finite-interval gap,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem CPSVCanonicalFormData.exists_uniform_openInteraction_gap_of_compact
    [NeZero d] {X : Type*} [TopologicalSpace X]
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) {S R : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop
      (fun j ↦ data.blocks (data.representativeIndex j)) S) (hR : S + 1 ≤ R)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction A R (H x).toLinearMap)
    {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  obtain ⟨γ, hγ, hGap⟩ := data.exists_openParentHamiltonianES_gap_of_wordTupleSpanTop
    hS hSpan hR
  exact exists_uniform_openInteractionHamiltonianES_gap_of_compact_canonical_gap
    (fun _ ↦ A) continuous_const H hH hParent hK (by omega) hγ
    (fun _ _ N hN ↦ by
      simpa only [data.ker_openParentHamiltonianES_eq_groundSpaceES_of_wordTupleSpanTop
        hS hSpan hR hN] using hGap N hN)
/-- At range \(R\geq3D^5\), a compact continuous family of positive parent
interactions for a fixed canonical tensor of positive bond dimension \(D\)
has one uniform open-chain gap for all chain lengths \(N\geq R\).
Source: arXiv:1606.00608, lines 317--345; the positive comparison is
CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem IsCPSVCanonicalForm.exists_uniform_openInteraction_gap_of_compact_of_bounded_range
    [NeZero d] [NeZero D] {X : Type*} [TopologicalSpace X]
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) {R : ℕ} (hR : 3 * D ^ 5 ≤ R)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction A R (H x).toLinearMap)
    {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  let data := Classical.choice hA
  obtain ⟨S, hS, hBound, hSpan⟩ :=
    data.exists_positive_wordTupleSpanTop_succ_le_three_bondDim_pow_five
  exact data.exists_uniform_openInteraction_gap_of_compact
    hS hSpan (hBound.trans hR) H hH hParent hK

end MPSTensor
