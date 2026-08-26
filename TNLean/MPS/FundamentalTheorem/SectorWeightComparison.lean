/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.SectorDecomposition
import TNLean.MPS.Overlap.Basic
import QICLean.Algebra.ScalarPowerSumIdentity

import Mathlib.Data.Fintype.BigOperators

/-!
# Sector-weight comparison from BNT coefficient data

This module contains the coefficient comparison and power-sum arguments for
sector decompositions over a common BNT basis.  Eventual coefficient equality is
upgraded to equality of the sector-weight multisets by a geometric-sequence
extrapolation and the Newton identities.

In CPSV16, the relevant coefficient comparison is the equal-MPV corollary:
after the BNT sectors have been matched, the proof compares the
power sums of the copy weights in each matched sector
(`Papers/1606.00608/MPDO-22-12-17-2.tex`, Appendix MPV proof,
lines 1184--1188).  The finite power-sum rigidity input is the appendix
power-sum lemma at lines 1155--1163.  The geometric extrapolation in
`TNLean.MPS.SharedInfra.SectorDecomposition` is a formal strengthening needed
because the Lean coefficient identity is often
available eventually in the length parameter rather than at the first
`max{x_a,x_b}` positive exponents.

The main theorem below uses the unequal-cardinality finite-range power-sum
theorem directly, following the appendix power-sum lemma.  Without nonzero weights, positive
powers would only determine the nonzero submultiset.

## References

- [PGVWC07] Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- [CPSV16] Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2016),
  the appendix power-sum lemma, lines 1155--1163, and the equal-MPV corollary
  proof, lines 1184--1188.
- [CPSV21] Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected
  entangled pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021),
  arXiv:2011.12127.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ## Coefficient comparison from BNT linear independence -/

namespace SectorWeightData

variable {g : ℕ}

/-- If two nonzero finite weight families have equal power sums for all sufficiently
large exponents, then their power sums agree for every exponent.

This is the unequal-cardinality form used to recover copy counts. The proof
concatenates the two families with coefficients `+1` and `-1` and uses
`geom_sum_eventually_zero`. -/
lemma power_sums_eq_of_eventually_eq_hetero
    {m n : ℕ} (a : Fin m → ℂ) (b : Fin n → ℂ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    {M : ℕ}
    (hEv : ∀ N, M ≤ N → ∑ i, a i ^ N = ∑ i, b i ^ N) :
    ∀ k, ∑ i, a i ^ k = ∑ i, b i ^ k := by
  let w : Fin (m + n) → ℂ := Fin.append a b
  let coeffs : Fin (m + n) → ℂ := Fin.append (fun _ : Fin m => (1 : ℂ))
    (fun _ : Fin n => (-1 : ℂ))
  have hw : ∀ i, w i ≠ 0 :=
    fun i => Fin.addCases
      (fun j => by
        show w (Fin.castAdd n j) ≠ 0
        rw [show w (Fin.castAdd n j) = a j from Fin.append_left a b j]
        exact ha j)
      (fun j => by
        show w (Fin.natAdd m j) ≠ 0
        rw [show w (Fin.natAdd m j) = b j from Fin.append_right a b j]
        exact hb j)
      i
  have hDecomp : ∀ k,
      ∑ i, coeffs i * w i ^ k = (∑ i, a i ^ k) - (∑ i, b i ^ k) := by
    intro k
    simp only [coeffs, w, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      one_mul, neg_one_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  have hEvCombined : ∀ N, M ≤ N → ∑ i, coeffs i * w i ^ N = 0 := by
    intro N hN
    rw [hDecomp, sub_eq_zero]
    exact hEv N hN
  have hAll := geom_sum_eventually_zero w coeffs hw hEvCombined
  intro k
  have hk := hAll k
  rw [hDecomp] at hk
  exact sub_eq_zero.mp hk


end SectorWeightData

namespace SectorDecomposition

/-- Along every positive arithmetic subsequence, a sector coefficient cannot vanish at all
sufficiently large indices.

For a positive integer `p`, the subsequence is the geometric sum with nonzero bases
`(P.weight j q) ^ p`. Geometric extrapolation therefore reduces eventual vanishing to exponent
zero, where the sum is the positive number of copies in the sector.

This is the common-period coefficient input in the proof of arXiv:1708.00029,
theorem `thm:bd`, line 631. -/
lemma coeff_mul_not_eventually_zero (P : SectorDecomposition d)
    (p : ℕ) (hp : 0 < p) (j : Fin P.basisCount) :
    ¬ (∀ᶠ N in Filter.atTop, P.coeff (p * N) j = 0) := by
  classical
  obtain ⟨p₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  intro hEv
  rw [Filter.eventually_atTop] at hEv
  obtain ⟨M, hM⟩ := hEv
  have hAll : ∀ k,
      ∑ q : Fin (P.copies j), (1 : ℂ) * ((P.weight j q) ^ (p₀ + 1)) ^ k = 0 := by
    refine SectorWeightData.geom_sum_eventually_zero
      (w := fun q ↦ (P.weight j q) ^ (p₀ + 1)) (c := fun _ ↦ 1) (M := M) ?_ ?_
    · intro q
      exact pow_ne_zero (p₀ + 1) (P.weight_ne_zero j q)
    · intro N hN
      simpa [SectorDecomposition.coeff, SectorWeightData.coeff, pow_mul] using hM N hN
  have h0 := hAll 0
  have hcard :
      (∑ q : Fin (P.copies j), (1 : ℂ) * ((P.weight j q) ^ (p₀ + 1)) ^ 0) =
        (P.copies j : ℂ) := by
    simp
  rw [hcard] at h0
  exact (Nat.cast_ne_zero.mpr (P.copies_pos j).ne') h0

end SectorDecomposition

end MPSTensor
