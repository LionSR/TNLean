/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.BlockingQCA

/-!
# Nearest-neighbor propagation after site blocking

A finite original-lattice propagation neighborhood becomes nearest-neighbor after grouping more
sites than the absolute value of every displacement.  The carry-aware blocked neighborhood is then
contained in the integer interval `Finset.Icc (-1) 1`.

This only normalizes a finite propagation bound before applying the Schumacher--Werner structure
theorem.  It does not construct support algebras, finite-depth circuits, or an MPU standard form.

## Main results

* `SpinChain.blockedNeighborhood_subset_Icc_one` — a strict displacement bound gives only
  nearest-neighbor carries.
* `SpinChain.blockedNeighborhood_subset_Icc_one_of_sup` — the corresponding supremum criterion.
* `SpinChain.blockedNeighborhood_subset_Icc_one_sup_add_one` — the canonical block length.
* `SpinChain.PropagatesWithin.blocked_nearest_neighbor` — transport a bounded neighborhood to a
  nearest-neighbor propagation bound.
* `SpinChain.HasFinitePropagation.exists_blocked_nearest_neighbor` — every finite propagation bound
  becomes nearest-neighbor after a positive blocking.
* `SpinChain.IsQCA.exists_blocked_nearest_neighbor` — the same blocking preserves the QCA property.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, line 2308.
* Schumacher--Werner, quant-ph/0405174, Theorem 6.
-/

namespace SpinChain

/-- If every original displacement has absolute value strictly smaller than the block length, then
all carry-aware blocked displacements are nearest-neighbor displacements.

The statement also covers the empty neighborhood without an additional hypothesis. -/
lemma blockedNeighborhood_subset_Icc_one (L : ℕ) [NeZero L] (𝓝 : Finset ℤ)
    (h𝓝 : ∀ n ∈ 𝓝, Int.natAbs n < L) :
    blockedNeighborhood L 𝓝 ⊆ Finset.Icc (-1) 1 := by
  intro b hb
  rw [mem_blockedNeighborhood_iff_exists_eq] at hb
  obtain ⟨r, s, n, hn, hrs⟩ := hb
  have hnabs : |n| < (L : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h𝓝 n hn
  rw [abs_lt] at hnabs
  rw [Finset.mem_Icc]
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hr0 : (0 : ℤ) ≤ r := by exact_mod_cast r.zero_le
  have hrL : (r : ℤ) < L := by exact_mod_cast r.isLt
  have hs0 : (0 : ℤ) ≤ s := by exact_mod_cast s.zero_le
  have hsL : (s : ℤ) < L := by exact_mod_cast s.isLt
  constructor
  · by_contra hb
    have hb' : b ≤ -2 := by omega
    have hmul : b * (L : ℤ) ≤ -2 * L :=
      Int.mul_le_mul_of_nonneg_right hb' (le_of_lt hL)
    omega
  · by_contra hb
    have hb' : 2 ≤ b := by omega
    have hmul : 2 * (L : ℤ) ≤ b * L :=
      Int.mul_le_mul_of_nonneg_right hb' (le_of_lt hL)
    omega

/-- A strict bound on the supremum of the absolute displacements forces the carry-aware blocked
neighborhood to be nearest-neighbor. -/
lemma blockedNeighborhood_subset_Icc_one_of_sup (L : ℕ) [NeZero L] (𝓝 : Finset ℤ)
    (h𝓝 : 𝓝.sup Int.natAbs < L) :
    blockedNeighborhood L 𝓝 ⊆ Finset.Icc (-1) 1 :=
  blockedNeighborhood_subset_Icc_one L 𝓝 fun _ hn => lt_of_le_of_lt (Finset.le_sup hn) h𝓝

/-- Blocking by one more than the largest absolute displacement canonically makes the
carry-aware neighborhood nearest-neighbor.  For the empty neighborhood this chooses length one. -/
lemma blockedNeighborhood_subset_Icc_one_sup_add_one (𝓝 : Finset ℤ) :
    blockedNeighborhood (𝓝.sup Int.natAbs + 1) 𝓝 ⊆ Finset.Icc (-1) 1 := by
  let _ : NeZero (𝓝.sup Int.natAbs + 1) := ⟨Nat.succ_ne_zero _⟩
  exact blockedNeighborhood_subset_Icc_one_of_sup _ 𝓝 (Nat.lt_succ_self _)

namespace PropagatesWithin

/-- A propagation bound becomes nearest-neighbor after blocking by more than every absolute
original displacement. -/
lemma blocked_nearest_neighbor {d L : ℕ} [NeZero d] [NeZero L]
    {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d} {𝓝 : Finset ℤ}
    (hω : PropagatesWithin ω 𝓝) (h𝓝 : ∀ n ∈ 𝓝, Int.natAbs n < L) :
    PropagatesWithin (blockedAutomorphism d L ω) (Finset.Icc (-1) 1) :=
  hω.blocked.mono (blockedNeighborhood_subset_Icc_one L 𝓝 h𝓝)

end PropagatesWithin

namespace HasFinitePropagation

/-- Every finite forward propagation bound becomes nearest-neighbor after some positive site
blocking.  The witness is one more than the supremum of the absolute displacements. -/
theorem exists_blocked_nearest_neighbor {d : ℕ} [NeZero d]
    {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
    (hω : HasFinitePropagation ω) :
    ∃ (L : ℕ) (_ : NeZero L) (_ : 0 < L),
      PropagatesWithin (blockedAutomorphism d L ω) (Finset.Icc (-1) 1) := by
  obtain ⟨𝓝, h𝓝⟩ := hω
  let L := 𝓝.sup Int.natAbs + 1
  let _ : NeZero L := ⟨Nat.succ_ne_zero _⟩
  refine ⟨L, inferInstance, Nat.zero_lt_succ _, ?_⟩
  exact h𝓝.blocked.mono (blockedNeighborhood_subset_Icc_one_sup_add_one 𝓝)

end HasFinitePropagation

namespace IsQCA

/-- Every one-dimensional QCA becomes a nearest-neighbor QCA after some positive site blocking.

This packages propagation normalization and preservation of the QCA axioms. It does not
construct the Schumacher--Werner support algebras or circuit, nor an MPU standard form. -/
theorem exists_blocked_nearest_neighbor {d : ℕ} [NeZero d]
    {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
    (hω : IsQCA ω) :
    ∃ (L : ℕ) (_ : NeZero L) (_ : 0 < L),
      IsQCA (blockedAutomorphism d L ω) ∧
        PropagatesWithin (blockedAutomorphism d L ω) (Finset.Icc (-1) 1) := by
  obtain ⟨L, hL, hLpos, hprop⟩ := hω.hasFinitePropagation.exists_blocked_nearest_neighbor
  exact ⟨L, hL, hLpos, hω.blocked, hprop⟩

end IsQCA

end SpinChain
