/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactGapBounds
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockWordSpan

/-!
# A common injectivity length for compact families of tensor blocks

For a continuous family of fixed-size tensor blocks, joint-boundary injectivity
is open. Under trace-preserving normalization it persists at larger lengths.
Compactness therefore turns pointwise simultaneous word spanning into one
common injectivity threshold. Pairwise inequivalent normalized primitive blocks
satisfy the pointwise spanning hypothesis. Their positive fixed-point matrices
need not vary continuously.

These results supply a finite-window ingredient in arXiv:1010.3732,
Appendix A, lines 2499–2503 and 2575–2578. They do not assert a spectral
gap uniform in chain length.
-/

open scoped Matrix Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

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
  obtain ⟨_, _, L, hL⟩ := hS.exists_uniform_pos_nat_bounds
    (fun (_ : ℝ) L x => x ∈ S → ∀ n : ℕ, L ≤ n →
      Function.Injective (blockGroundSpaceMapES (A x) n))
    (fun _ h => h)
    (fun hle h hx n hn => h hx n (hle.trans hn))
    (by
      intro x hx
      obtain ⟨L, hL⟩ := hSpan x hx
      have hInj := blockGroundSpaceMapES_injective_of_wordTupleSpanTop hL
      have hnear : ∀ᶠ y in 𝓝 x, Function.Injective (blockGroundSpaceMapES (A y) L) :=
        (isOpen_setOf_blockGroundSpaceMapES_injective_family A hA L).mem_nhds hInj
      refine ⟨1, zero_lt_one, L, hnear.mono ?_⟩
      intro y hy hyS n hn
      exact blockGroundSpaceMapES_injective_of_ge_of_tracePreserving
        (A y) hy (hTP y hyS) hn)
  exact ⟨L, fun x hx => hL x hx hx⟩

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
