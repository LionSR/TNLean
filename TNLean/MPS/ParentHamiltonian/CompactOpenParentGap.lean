/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactGapBounds
import TNLean.MPS.MPDO.CPSVSharpBlocking
import TNLean.MPS.ParentHamiltonian.Martingale.BlockOpenGapAllLengths
import TNLean.MPS.ParentHamiltonian.Martingale.OpenFiniteRangeKnabeGap
import TNLean.MPS.ParentHamiltonian.Martingale.OpenGapContinuity

/-!
# Compact uniform gaps for open multiblock parent Hamiltonians

A simultaneous word span at a positive length \(S\) gives a pointwise
open-chain gap at each range \(R\geq S+1\). For one tensor, choose a finite
Knabe window whose threshold is strictly smaller than this gap. Continuity
preserves a common lower bound on every shorter interval needed at the two
endpoints. Zero padding applies the cyclic finite-range inequality to the
open interaction without adding physical sites. It follows that one positive
gap holds on a parameter neighborhood for all chain lengths. A finite
subcover makes the constant uniform on a compact parameter set.

Nonzero block weights do not alter the local spaces, and no continuity of
the weights is needed. The normal-block consequence derives a common
simultaneous injectivity length from the bond dimensions.

Source: arXiv:1010.3732, Appendix A, lines 2475--2580, for the finite-window
compactness argument; Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and
Section 6, for the pointwise open-chain gap. The open finite-range coefficient
is a derivation recorded in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`.

**Scope restriction (sufficient interaction range):** The supplied-span
assertion assumes \(R\geq S+1\), and the normal-block consequence uses a
sufficient dimension bound. The unrestricted shorter-range assertion and
its counterexample are recorded in
`docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.
-/

open scoped Topology

namespace MPSTensor

variable {d : ℕ}

/-- An open-chain gap uniform in the chain length at one parameter persists
with some positive constant on a parameter neighborhood. The open finite-size
criterion reduces this assertion to finitely many continuously varying
intervals. Source: arXiv:1010.3732, Appendix A, lines 2475--2580, for the
finite-window compactness argument; the derived open Knabe criterion is
recorded in `docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem eventually_openParentHamiltonianES_toTensorFromBlocks_gap_of_uniform_gap
    {X : Type*} [TopologicalSpace X] {r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x ↦ A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) {x₀ : X} {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ N : ℕ, R ≤ N → ∀ v ∈
      (groundSpaceES (toTensorFromBlocks (d := d) (μ := μ x₀) (A x₀)) N)ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x₀) (A x₀)) R N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 x₀, ∀ N : ℕ, R ≤ N → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N v‖ := by
  obtain ⟨n, hn⟩ := exists_lt_nsmul (half_pos hγ) (((R : ℝ) - 1) ^ 2)
  let m := n + R
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.le_add_right n R)
  have hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * (γ / 2) :=
    hn.trans_le (by simpa only [nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right hnm (half_pos hγ).le)
  have hnear := eventually_openParentHamiltonianES_toTensorFromBlocks_gap_bounded_volumes
    μ A hμ hA hS hSpan hR (m + R - 1) hγ (half_lt_self hγ)
    (fun N hN _ ↦ hgap N hN)
  have hmR : R ≤ m := Nat.le_add_left R n
  have hden : 0 < (m : ℝ) - (R : ℝ) + 1 := by
    have hmR' : (R : ℝ) ≤ m := by exact_mod_cast hmR
    linarith
  refine ⟨((m : ℝ) * (γ / 2) - ((R : ℝ) - 1) ^ 2) /
    ((m : ℝ) - R + 1), div_pos (sub_pos.mpr hnum) hden, ?_⟩
  filter_upwards [hnear] with x hx
  apply (openParentHamiltonianES_gap_of_finite_open_gaps
    (toTensorFromBlocks (d := d) (μ := μ x) (A x)) (by omega) hmR hnum ?_).2
  intro W hRW hWM
  simpa only [ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_wordTupleSpanTop
    (μ x) (A x) (hμ x) hS (hSpan x) hR hRW] using hx W hRW hWM
/-- A compact continuous family of simultaneously injective blocks has one
positive canonical open-chain gap uniform in the parameter and every chain
length containing the interaction. Nonzero block weights need not be
continuous. Source: arXiv:1010.3732, Appendix A, lines 2475--2580, for
compactness; Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
for the pointwise open-chain gap. -/
theorem exists_uniform_openParentHamiltonianES_toTensorFromBlocks_gap_of_compact_all_lengths
    {X : Type*} [TopologicalSpace X] {r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x ↦ A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, R ≤ N → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N v‖ := by
  have hlocal : ∀ x ∈ K, ∃ δ : ℝ, 0 < δ ∧ ∃ n : ℕ,
      ∀ᶠ y in 𝓝 x, ∀ N : ℕ, R ≤ N → ∀ v ∈
        (LinearMap.ker (openParentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ y) (A y)) R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ y) (A y)) R N v‖ := by
    intro x _
    obtain ⟨γ, hγ, hgap⟩ :=
      exists_openParentHamiltonianES_toTensorFromBlocks_gap_of_wordTupleSpanTop
        (μ x) (A x) (hμ x) hS (hSpan x) hR
    exact (eventually_openParentHamiltonianES_toTensorFromBlocks_gap_of_uniform_gap
      μ A hμ hA hS hSpan hR hγ hgap).imp fun δ h ↦ ⟨h.1, 0, h.2⟩
  obtain ⟨δ, hδ, _, hgap⟩ := hK.exists_uniform_pos_nat_bounds
    (fun δ _ x ↦ ∀ N : ℕ, R ≤ N → ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N v‖)
    (fun {_δ _δ' _n _x} hle hgap N hN v hv ↦
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap N hN v hv))
    (fun {_δ _n _n' _x} _hle hgap ↦ hgap) hlocal
  exact ⟨δ, hδ, hgap⟩
variable {r : ℕ} {dim : Fin r → ℕ} [NeZero d]

/-- A compact continuous family of pairwise inequivalent normal blocks has a
positive open-chain gap uniform in the parameter and every chain containing
an interaction of range at least \(3\max(\sum_jD_j,1)^5\).
A common simultaneous injectivity length is derived from the dimensions.
Source: arXiv:1010.3732, Appendix A, and arXiv:1606.00608, lines 317--345. -/
theorem exists_uniform_block_openParentHamiltonianES_gap_of_compact_isNormalTensor
    {X : Type*} [TopologicalSpace X]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    (hNormal : ∀ x j, IsNormalTensor (A x j))
    (hDistinct : ∀ x, BlocksNotGaugePhaseEquiv (A x)) {R : ℕ}
    (hR : 3 * (max (∑ j, dim j) 1) ^ 5 ≤ R) {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N v‖ := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · let := hX
    exact ⟨1, one_pos, fun x => isEmptyElim x⟩
  let : ∀ j, NeZero (dim j) :=
    fun j => ⟨(hNormal (Classical.choice hX) j).bondDim_ne_zero⟩
  let cap := max (∑ j, dim j) 1
  have hCap : 0 < cap := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let S := 3 * cap ^ 5 - 1
  have hPow : 0 < cap ^ 5 := Nat.pow_pos hCap
  have hS : 0 < S := by dsimp only [S]; omega
  have hRcap : 3 * cap ^ 5 ≤ R := hR
  have hSpan (x : X) : WordTupleSpanTop (A x) S := by
    obtain ⟨L, hL, hBound, hSpanL⟩ :=
      exists_positive_wordTupleSpanTop_succ_le_three_cap_pow_five_of_isNormalTensor
        (A x) hCap (le_max_left _ _) (hNormal x) (hDistinct x)
    exact wordTupleSpanTop_of_ge (A x) hL hSpanL (by dsimp only [S]; omega)
  exact exists_uniform_openParentHamiltonianES_toTensorFromBlocks_gap_of_compact_all_lengths
    μ A hμ hA hS hSpan (by dsimp only [S]; omega) hK

end MPSTensor
