/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.CompactKernelGap
import TNLean.MPS.CanonicalForm.BlockSeparation.SharpBlocking
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockGroundSpaceContinuity
import TNLean.MPS.ParentHamiltonian.Continuity.BlockPeriodicGroundSpaceContinuity
import TNLean.MPS.ParentHamiltonian.Gap.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.FiniteRangeKnabeGap
import TNLean.MPS.ParentHamiltonian.Gap.BlockOpenGapAtSimultaneousInjectivity
import QICLean.Spectral.Perturbation.KernelGapPerturbation

/-!
# Compact uniform gaps for several simultaneously injective blocks

At a fixed simultaneous injectivity length, the joint local ground-space
projections vary continuously. A strict finite-range Knabe window at one
parameter therefore persists throughout a neighborhood. A finite subcover
of a compact parameter set gives a common positive gap for sufficiently
long rings. Continuity of the periodic block span treats the finitely many
remaining lengths, giving a gap for every ring containing the interaction.
A dimension bound supplies a common simultaneous injectivity length for
pairwise inequivalent normal blocks. The nonzero block weights do not enter
the local ground spaces and need not vary continuously.

This gives the compactness step of arXiv:1010.3732, Appendix A, through
finite-range Knabe windows. It applies to the source's two-site interaction
when the simultaneous injectivity length is one, as after the initial
blocking of the isometric deformation path.

**Scope restriction (common spanning length or sufficient range):**
arXiv:1010.3732, Appendix A, lines 2475--2580, treats a path of normal forms
with several blocks through Nachtergaele's estimate. The results here assume
one simultaneous spanning length \(S>0\) for the whole family and range
\(R\geq S+1\), or pairwise inequivalent normal blocks and range
\(R\geq3\max(\sum_jD_j,1)^5\). The source path satisfies the first
hypothesis with \(S=1\) after its initial blocking, which is proved in
`IsometricDeformation`; documented in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

open scoped Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- A strict finite-range open Knabe window for a block tensor persists on a
parameter neighborhood, giving one periodic gap at all sufficiently large
lengths. Source: arXiv:1010.3732, Appendix A, lines 2475--2580. -/
theorem eventually_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_strict_openGap
    {X : Type*} [TopologicalSpace X]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    {S R m : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) (hm : R ≤ m) {x₀ : X} {γ : ℝ}
    (hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ)
    (hgap : ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (d := d) (μ := μ x₀) (A x₀)) R
          (m + R - 1)).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 x₀, ∀ (N : ℕ) (hN : 2 * m ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction
            (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N).hamiltonian) z →
          z = 0 ∨ (δ : ℂ) ≤ z := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : ((R : ℝ) - 1) ^ 2 / (m : ℝ) < γ :=
    (div_lt_iff₀ hmpos).2 (by simpa only [mul_comm] using hnum)
  obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between hthreshold
  have hγpos : 0 < γ := by nlinarith [sq_nonneg ((R : ℝ) - 1)]
  let B := fun x => toTensorFromBlocks (d := d) (μ := μ x) (A x)
  have hProjR := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA R (fun x => wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega))
  have hProjW := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA (m + R - 1)
    (fun x => wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega))
  let e := (Matrix.toEuclideanCLM :
    Matrix (Cfg d (m + R - 1)) (Cfg d (m + R - 1)) ℂ ≃⋆ₐ[ℂ] _)
  have hH : Continuous fun x ↦ e (parentChainInteraction (B x) R (m + R - 1)).hamiltonian :=
    e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_hamiltonian_parentChainInteraction_family_of_groundProjection B hProjR)
  have hker := ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_wordTupleSpanTop
    (μ x₀) (A x₀) (hμ x₀) hS (hSpan x₀) hR (by omega : R ≤ m + R - 1)
  have hnear := ContinuousLinearMap.eventually_norm_gap_on_orthogonal
    (fun x ↦ e (parentChainInteraction (B x) R (m + R - 1)).hamiltonian)
    (fun x => groundSpaceES (B x) (m + R - 1)) hH.continuousAt hProjW.continuousAt
    (by rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
        exact groundSpaceES_le_ker_hamiltonian_parentChainInteraction (B x₀) R (m + R - 1))
    hγpos hγ'upper (by
      rw [← hker]
      exact (ManyBody.forall_hasEigenvalue_iff_norm
        (posSemidef_hamiltonian_parentChainInteraction (B x₀) R _)).mp hgap)
  have hnum' : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ' := by
    simpa only [mul_comm] using (div_lt_iff₀ hmpos).1 hγ'lower
  let δ : ℝ := ((m : ℝ) * γ' - ((R : ℝ) - 1) ^ 2) / ((m : ℝ) - R + 1)
  have hden : 0 < (m : ℝ) - R + 1 := by
    have hm' : (R : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  refine ⟨δ, div_pos (sub_pos.mpr hnum') hden, ?_⟩
  filter_upwards [hnear] with x hx N hN
  refine (hamiltonian_parentRingInteraction_gap_of_hamiltonian_parentChainInteraction_gap
    (B x) (R := R) (m := m) (by omega) hm hnum' ?_).2 N hN
  refine (ManyBody.forall_hasEigenvalue_iff_norm
    (posSemidef_hamiltonian_parentChainInteraction (B x) R _)).mpr ?_
  rw [ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_wordTupleSpanTop
    (μ x) (A x) (hμ x) hS (hSpan x) hR (by omega)]
  exact hx

/-- A compact continuous family of simultaneously injective block tensors has
one positive periodic parent-Hamiltonian gap at every sufficiently large
chain length. No finite-window gap or normalization is assumed.
Source: arXiv:1010.3732, Appendix A, lines 2475--2580. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_compact
    {X : Type*} [TopologicalSpace X]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ K, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction
            (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N).hamiltonian) z →
          z = 0 ∨ (δ : ℂ) ≤ z := by
  refine hK.exists_uniform_pos_nat_bounds (fun δ N₀ x ↦ ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction
            (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N).hamiltonian) z →
          z = 0 ∨ (δ : ℂ) ≤ z)
    (fun hle hgap N _ hN ↦ ManyBody.forall_hasEigenvalue_mono hle (hgap N hN))
    (fun hle hgap N _ hN ↦ hgap N (hle.trans hN)) fun x _ ↦ ?_
  obtain ⟨m, hm, γ, _hγ, hnum, hgap⟩ :=
    exists_strict_parentChainInteraction_toTensorFromBlocks_window_of_wordTupleSpanTop
      (μ x) (A x) (hμ x) hS (hSpan x) hR
  obtain ⟨δ, hδ, hnear⟩ :=
    eventually_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_strict_openGap
      μ A hμ hA hS hSpan hR hm hnum hgap
  exact ⟨δ, hδ, 2 * m, hnear.mono fun y hy N _ hN ↦ hy N hN⟩

/-- A compact continuous family of simultaneously injective block tensors has
one positive periodic gap valid for every ring containing the parent interaction.
No finite-window gap or normalization is assumed.
Source: arXiv:1010.3732, Appendix A, lines 2475--2580. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_all_lengths
    {X : Type*} [TopologicalSpace X]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ (N : ℕ) (hN : R ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction
            (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N).hamiltonian) z →
          z = 0 ∨ (δ : ℂ) ≤ z := by
  obtain ⟨δ₀, hδ₀, N₀, hlong⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_compact
      μ A hμ hA hS hSpan hR hK
  obtain ⟨δ, hδ, hgap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ => ∀ hN : R ≤ N, ∀ x ∈ K, haveI : NeZero N := ⟨by omega⟩;
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction
            (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N).hamiltonian) z →
          z = 0 ∨ (δ : ℂ) ≤ z)
    (fun N γ δ hle h hN x hx => ManyBody.forall_hasEigenvalue_mono hle (h hN x hx))
    (fun N => by
      by_cases hN : R ≤ N
      · exact
        (exists_uniform_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_wordTupleSpanTop
          μ A hμ hA hS hSpan hK hR hN).imp fun δ h ↦ ⟨h.1, fun _ ↦ h.2⟩
      · exact ⟨1, one_pos, fun h => (hN h).elim⟩)
    hδ₀ (fun N hN hN' x hx =>
      haveI : NeZero N := ⟨by omega⟩
      hlong x hx N hN)
  exact ⟨δ, hδ, fun x hx N hN => hgap N hN x hx⟩

omit [∀ j, NeZero (dim j)] in
/-- A compact continuous family of pairwise inequivalent normal blocks has a
positive periodic gap uniform in the parameter and every ring containing
an interaction of range at least \(3\max(\sum_jD_j,1)^5\).
A common simultaneous injectivity length is derived from the dimensions.
Source: arXiv:1010.3732, Appendix A, and arXiv:1606.00608, lines 317--345. -/
theorem exists_uniform_block_hamiltonian_parentRingInteraction_gap_of_compact_isNormalTensor
    {X : Type*} [TopologicalSpace X]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    (hNormal : ∀ x j, IsNormalTensor (A x j))
    (hDistinct : ∀ x, BlocksNotGaugePhaseEquiv (A x)) {R : ℕ}
    (hR : 3 * (max (∑ j, dim j) 1) ^ 5 ≤ R) {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ (N : ℕ) (hN : R ≤ N),
      haveI : NeZero N := NeZero.of_gt (lt_of_lt_of_le
        (by positivity : 0 < 3 * (max (∑ j, dim j) 1) ^ 5) (hR.trans hN));
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (parentRingInteraction
            (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N).hamiltonian) z →
          z = 0 ∨ (δ : ℂ) ≤ z := by
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
  exact exists_uniform_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_all_lengths
    μ A hμ hA hS hSpan (by dsimp only [S]; omega) hK

end MPSTensor
