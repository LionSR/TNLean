/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactGapBounds
import TNLean.MPS.ParentHamiltonian.BlockBoundaryTraceDuality
import TNLean.MPS.ParentHamiltonian.BlockWordSpanPropagation
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockWordSpan

/-!
# A common injectivity length for compact families of tensor blocks

For a continuous family of fixed-size tensor blocks, simultaneous word spanning
is open and persists at larger lengths whenever its initial length is positive.
Compactness therefore gives one positive spanning threshold without normalization
assumptions. Trace preservation allows an initial spanning length of zero, and
pairwise inequivalent normalized primitive blocks satisfy the pointwise spanning
hypothesis. Their positive fixed-point matrices need not vary continuously.

These results supply a finite-window ingredient in arXiv:1010.3732,
Appendix A, lines 2499–2503 and 2575–2578. They do not assert a spectral
gap uniform in chain length.
-/

open scoped Matrix Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Continuous fixed-size block families with positive-length simultaneous spanning at each
point of a compact set have one positive spanning threshold, valid at every larger length.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem exists_uniform_wordTupleSpanTop_of_compact
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) {K : Set X} (hK : IsCompact K)
    (hSpan : ∀ x ∈ K, ∃ L : ℕ, 0 < L ∧ WordTupleSpanTop (A x) L) :
    ∃ L : ℕ, 0 < L ∧ ∀ x ∈ K, ∀ n : ℕ, L ≤ n → WordTupleSpanTop (A x) n := by
  obtain ⟨_, _, N, hN⟩ := hK.exists_uniform_pos_nat_bounds
    (fun (_ : ℝ) N x => ∀ n : ℕ, N + 1 ≤ n → WordTupleSpanTop (A x) n)
    (fun _ h => h)
    (fun hle h n hn => h n ((Nat.add_le_add_right hle 1).trans hn))
    (by
      intro x hx
      obtain ⟨L, hL, hSpanL⟩ := hSpan x hx
      have hnear : ∀ᶠ y in 𝓝 x, WordTupleSpanTop (A y) L :=
        (isOpen_setOf_wordTupleSpanTop_family A hA L).mem_nhds hSpanL
      refine ⟨1, zero_lt_one, L, hnear.mono ?_⟩
      intro y hy n hn
      exact wordTupleSpanTop_of_ge_of_pos (A y) hy hL (by omega))
  exact ⟨N + 1, Nat.succ_pos N, hN⟩

/-- On a compact parameter set, pointwise simultaneous injectivity has one common threshold.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem exists_uniform_blockGroundSpaceMapES_injective_of_compact_wordTupleSpanTop
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) {S : Set X} (hS : IsCompact S)
    (hTP : ∀ x ∈ S, ∀ j, ∑ i, (A x j i)ᴴ * A x j i = 1)
    (hSpan : ∀ x ∈ S, ∃ L, WordTupleSpanTop (A x) L) :
    ∃ L : ℕ, ∀ x ∈ S, ∀ n : ℕ, L ≤ n →
      Function.Injective (blockGroundSpaceMapES (A x) n) := by
  obtain ⟨L, _, hL⟩ := exists_uniform_wordTupleSpanTop_of_compact A hA hS (by
    intro x hx
    obtain ⟨L, hSpanL⟩ := hSpan x hx
    exact ⟨L + 1, Nat.succ_pos L,
      wordTupleSpanTop_succ_of_tracePreserving (A x) hSpanL (hTP x hx)⟩)
  exact ⟨L, fun x hx n hn =>
    blockGroundSpaceMapES_injective_of_wordTupleSpanTop (A x) (hL x hx n hn)⟩

/-- A compact continuous family of inequivalent normalized primitive blocks admits one common
joint-boundary injectivity threshold. Fixed-point matrices need not vary continuously.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem exists_uniform_blockGroundSpaceMapES_injective_of_compact_isPrimitiveMPS
    {X : Type*} [TopologicalSpace X] [∀ j, NeZero (dim j)]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) {S : Set X} (hS : IsCompact S)
    (ρ : X → ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ x ∈ S, ∀ j, IsPrimitiveMPS (A x j) (ρ x j))
    (hρ : ∀ x ∈ S, ∀ j, (ρ x j).PosDef)
    (hDistinct : ∀ x ∈ S, ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A x j) (A x i)) :
    ∃ L : ℕ, ∀ x ∈ S, ∀ n : ℕ, L ≤ n →
      Function.Injective (blockGroundSpaceMapES (A x) n) := by
  apply exists_uniform_blockGroundSpaceMapES_injective_of_compact_wordTupleSpanTop
    A hA hS (fun x hx j => (hP x hx j).norm)
  intro x hx
  obtain ⟨L, hL⟩ := exists_eventually_wordTupleSpanTop_of_isPrimitiveMPS
    (A x) (ρ x) (hP x hx) (hρ x hx) (hDistinct x hx)
  exact ⟨L, hL L le_rfl⟩

end MPSTensor
