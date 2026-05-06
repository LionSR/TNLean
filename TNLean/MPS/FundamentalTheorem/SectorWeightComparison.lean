/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.SharedInfra.SectorDecomposition
import TNLean.MPS.Overlap.Basic
import TNLean.Algebra.ScalarPowerSumIdentity

import Mathlib.Data.Fintype.BigOperators

/-!
# Sector-weight comparison from BNT coefficient data

This module contains the coefficient comparison and power-sum arguments for
sector decompositions over a common BNT basis.  Eventual coefficient equality is
upgraded to equality of the sector-weight multisets by a geometric-sequence
extrapolation and the Newton identities.

In arXiv:1606.00608, Theorem IV.13 and its appendix proof use positive diagonal
matrices whose traces enter the structure coefficients as power sums.  The
geometric extrapolation and Newton--Girard steps below are the finite-sequence
algebra needed to recover the weight lists from those power sums once the basis
blocks have been matched.

## References

- [PGVWC07] Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- [CPSV16] Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2016).
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

/-- **Eventual coefficient agreement from BNT linear independence.**

If two sector weight data `S` and `T` over the same basis produce the same total MPV
(expressed as equal linear combinations of basis MPVs at each system size), and the basis
is eventually linearly independent (the BNT property), then the coefficient arrays
`S.coeff N j` and `T.coeff N j` agree for all sufficiently large `N`.

This is the key step converting MPV equality into the algebraic statement needed for
Newton–Girard. -/
lemma coeff_eventually_eq_of_sameMPV
    {dim : Fin g → ℕ}
    (basis : (j : Fin g) → MPSTensor d (dim j))
    (S T : SectorWeightData g)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin g => mpvState (basis j) N))
    (hSame : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ j : Fin g, S.coeff N j * mpv (basis j) σ =
      ∑ j : Fin g, T.coeff N j * mpv (basis j) σ) :
    ∃ N0 : ℕ, ∀ N > N0, ∀ j : Fin g, S.coeff N j = T.coeff N j := by
  obtain ⟨N0, hLIN⟩ := hLI
  refine ⟨N0, fun N hN j => ?_⟩
  have hLI_N := hLIN N hN
  -- Express coefficient equality as equality of scalar-weighted MPV state sums.
  have hsums :
      ∑ j : Fin g, S.coeff N j • mpvState (basis j) N =
        ∑ j : Fin g, T.coeff N j • mpvState (basis j) N := by
    ext σ
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
               smul_eq_mul, mpvState, EuclideanSpace.equiv,
               PiLp.continuousLinearEquiv_symm_apply]
    exact hSame N σ
  -- Rewrite as a single sum of differences equal to zero.
  have hdiff : ∑ j : Fin g, (S.coeff N j - T.coeff N j) • mpvState (basis j) N = 0 := by
    simpa [Finset.sum_sub_distrib, sub_smul] using sub_eq_zero.mpr hsums
  -- Apply linear independence to conclude each coefficient difference is zero.
  have hzero := Fintype.linearIndependent_iff.mp hLI_N
    (fun j => S.coeff N j - T.coeff N j) hdiff
  exact sub_eq_zero.mp (hzero j)

/-- **Weight multiset recovery from equal multiplicities and power sums.**

If two sector weight data have the same multiplicities and their power sum coefficients
agree for every positive system size, then the sector weight multisets are equal for each
basis block. Uses `Fin.cast (hCopies j)` to align the two families over the same index type.

This is a direct application of Newton–Girard
(`Matrix.sum_pow_eq_implies_multiset_eq`). -/
lemma weight_multiset_eq_of_copies_eq_of_coeff_eq
    (S T : SectorWeightData g)
    (hCopies : ∀ j, S.copies j = T.copies j)
    (hCoeff : ∀ (k : ℕ), 0 < k → ∀ j : Fin g,
      S.coeff k j = T.coeff k j) :
    ∀ j : Fin g,
      Finset.univ.val.map (S.weight j) =
        Finset.univ.val.map (fun q => T.weight j (Fin.cast (hCopies j) q)) := by
  intro j
  apply Matrix.sum_pow_eq_implies_multiset_eq
  intro k hk
  have h := hCoeff k hk j
  simp only [SectorWeightData.coeff] at h
  convert h using 1
  exact Fintype.sum_equiv (Fin.castOrderIso (hCopies j)).toEquiv
    (fun q => (T.weight j (Fin.cast (hCopies j) q)) ^ k)
    (fun q => (T.weight j q) ^ k)
    (fun q => by simp [Fin.castOrderIso_apply])

/-! ### Extrapolation of power sum sequences

The connection between "eventually equal coefficients" (for `N > N₀`) and
"equal coefficients for every positive `k`" rests on a **telescoping induction**
on linear combinations of geometric sequences.

For a finite sum `N ↦ ∑ᵢ cᵢ · wᵢᴺ` with every `wᵢ` nonzero, vanishing for all
sufficiently large `N` forces vanishing for every exponent.  The proof subtracts
`w₀` times the equation at `N` from the equation at `N+1`, eliminating the first
base and reducing the number of terms.  The induction gives the shorter identity
for all exponents, and the original sequence then satisfies a geometric
recurrence whose value at the eventual-vanishing cutoff is zero.

Applying this to the signed union of two weight families converts eventual
equality of their power sums into equality at every positive exponent.
-/

/-- A linear combination of geometric sequences `∑ cᵢ wᵢᵏ` with all bases `wᵢ ≠ 0` that
vanishes for all `k ≥ M` vanishes identically.

See the section documentation above for the proof idea (telescoping induction). -/
lemma geom_sum_eventually_zero
    {n : ℕ} (w : Fin n → ℂ) (c : Fin n → ℂ)
    (hw : ∀ i, w i ≠ 0)
    {M : ℕ}
    (hEv : ∀ N, M ≤ N → ∑ i, c i * w i ^ N = 0) :
    ∀ k, ∑ i, c i * w i ^ k = 0 := by
  induction n with
  | zero => intro k; simp
  | succ n ih =>
    have hTailEv : ∀ N, M ≤ N →
        ∑ i : Fin n, c i.succ * (w i.succ - w 0) * w i.succ ^ N = 0 := by
      intro N hN
      have key : ∑ i : Fin (n + 1), c i * (w i - w 0) * w i ^ N = 0 := by
        have eq : ∑ i : Fin (n + 1), c i * (w i - w 0) * w i ^ N =
                  (∑ i, c i * w i ^ (N + 1)) - w 0 * (∑ i, c i * w i ^ N) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          congr 1; ext i; ring
        rw [eq, hEv (N + 1) (by omega), hEv N hN, mul_zero, sub_zero]
      rw [Fin.sum_univ_succ] at key
      simpa [sub_self] using key
    have hTailAll := ih _ _ (fun i => hw i.succ) hTailEv
    have hRec : ∀ k, (∑ i : Fin (n + 1), c i * w i ^ (k + 1)) =
                      w 0 * (∑ i : Fin (n + 1), c i * w i ^ k) := by
      intro k
      suffices h : (∑ i : Fin (n + 1), c i * w i ^ (k + 1)) -
                    w 0 * (∑ i : Fin (n + 1), c i * w i ^ k) = 0 from
        sub_eq_zero.mp h
      have eq : (∑ i : Fin (n + 1), c i * w i ^ (k + 1)) -
                 w 0 * (∑ i : Fin (n + 1), c i * w i ^ k) =
                ∑ i : Fin (n + 1), c i * (w i - w 0) * w i ^ k := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        congr 1; ext i; ring
      rw [eq, Fin.sum_univ_succ]
      simpa [sub_self] using hTailAll k
    have hGeom : ∀ k, (∑ i : Fin (n + 1), c i * w i ^ k) =
                        w 0 ^ k * (∑ i : Fin (n + 1), c i * w i ^ 0) := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk => rw [hRec, ihk, pow_succ]; ring
    have hS0 : (∑ i : Fin (n + 1), c i * w i ^ 0) = 0 := by
      have hSM := hEv M (le_refl M)
      have hGM := hGeom M
      rw [hSM] at hGM
      exact (mul_eq_zero.mp hGM.symm).resolve_left (pow_ne_zero M (hw 0))
    intro k
    rw [hGeom, hS0, mul_zero]

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

/-- If two equal-cardinality families of nonzero complex scalars have equal power sums for all
sufficiently large exponents, then their power sums agree for every exponent.

This is the equal-cardinality specialization of
`power_sums_eq_of_eventually_eq_hetero`. -/
lemma power_sums_eq_of_eventually_eq
    {m : ℕ} (a b : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    {M : ℕ}
    (hEv : ∀ N, M ≤ N → ∑ i, a i ^ N = ∑ i, b i ^ N) :
    ∀ k, ∑ i, a i ^ k = ∑ i, b i ^ k := by
  exact power_sums_eq_of_eventually_eq_hetero
    (m := m) (n := m) a b ha hb (M := M) hEv

/-- Eventual equality of coefficient power sums forces equality of multiplicities. -/
lemma copies_eq_of_eventually_coeff_eq
    (S T : SectorWeightData g)
    {N0 : ℕ}
    (hEv : ∀ N > N0, ∀ j : Fin g, S.coeff N j = T.coeff N j) :
    ∀ j : Fin g, S.copies j = T.copies j := by
  intro j
  have hEvj : ∀ N, N0 + 1 ≤ N →
      ∑ q : Fin (S.copies j), (S.weight j q) ^ N =
        ∑ q : Fin (T.copies j), (T.weight j q) ^ N := by
    intro N hN
    have h := hEv N (by omega) j
    simpa only [SectorWeightData.coeff] using h
  have h0 := power_sums_eq_of_eventually_eq_hetero
    (S.weight j) (T.weight j)
    (fun q => S.weight_ne_zero j q)
    (fun q => T.weight_ne_zero j q)
    (M := N0 + 1) hEvj 0
  exact (Nat.cast_injective (R := ℂ)) (by simpa using h0)

/-- Power-sum sequences from finite weight families that eventually agree also agree for all
positive exponents.

Proved by reducing to `power_sums_eq_of_eventually_eq` via a reindexing that uses
`hCopies` to align the two families over the same index type `Fin (S.copies j)`. -/
private lemma eventually_coeff_eq_implies_all_pos_eq
    (S T : SectorWeightData g)
    (hCopies : ∀ j, S.copies j = T.copies j)
    {N0 : ℕ}
    (hEv : ∀ N > N0, ∀ j : Fin g, S.coeff N j = T.coeff N j) :
    ∀ k : ℕ, 0 < k → ∀ j : Fin g, S.coeff k j = T.coeff k j := by
  intro k _ j
  set b : Fin (S.copies j) → ℂ := fun q => T.weight j (Fin.cast (hCopies j) q) with hb_def
  have hReindex : ∀ N, ∑ q : Fin (S.copies j), b q ^ N =
                        ∑ q : Fin (T.copies j), (T.weight j q) ^ N := by
    intro N
    exact Fintype.sum_equiv (Fin.castOrderIso (hCopies j)).toEquiv
      (fun q => b q ^ N) (fun q => (T.weight j q) ^ N)
      (fun q => by simp [hb_def, Fin.castOrderIso_apply])
  have hEvAB : ∀ N, N0 + 1 ≤ N →
      ∑ q : Fin (S.copies j), (S.weight j q) ^ N = ∑ q : Fin (S.copies j), b q ^ N := by
    intro N hN
    have h := hEv N (by omega) j
    simp only [SectorWeightData.coeff] at h
    rw [h, (hReindex N).symm]
  have hAll := power_sums_eq_of_eventually_eq (S.weight j) b
    (fun i => S.weight_ne_zero j i)
    (fun i => T.weight_ne_zero j (Fin.cast (hCopies j) i))
    hEvAB k
  simp only [SectorWeightData.coeff]
  exact hAll.trans (hReindex k)

/-- **Equal-case corollary: BNT linear independence + same multiplicities + equal total MPVs
→ equal sector weight multisets.**

BNT linear independence turns equality of the total matrix-product-vector
families into eventual equality of the sector coefficients.  The geometric
extrapolation above promotes eventual equality to equality of all positive
power sums, and Newton--Girard then recovers the weight multiset in each
sector once the copy counts have been aligned. -/
lemma weight_multiset_eq_of_sameMPV_bnt
    {dim : Fin g → ℕ}
    (basis : (j : Fin g) → MPSTensor d (dim j))
    (S T : SectorWeightData g)
    (hCopies : ∀ j, S.copies j = T.copies j)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin g => mpvState (basis j) N))
    (hSame : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ j : Fin g, S.coeff N j * mpv (basis j) σ =
      ∑ j : Fin g, T.coeff N j * mpv (basis j) σ) :
    ∀ j : Fin g,
      Finset.univ.val.map (S.weight j) =
        Finset.univ.val.map (fun q => T.weight j (Fin.cast (hCopies j) q)) := by
  obtain ⟨_, hCoeffEventuallyEq⟩ := coeff_eventually_eq_of_sameMPV basis S T hLI hSame
  have hCoeffAllPosEq := eventually_coeff_eq_implies_all_pos_eq S T hCopies hCoeffEventuallyEq
  exact weight_multiset_eq_of_copies_eq_of_coeff_eq S T hCopies hCoeffAllPosEq

/-- **BNT coefficient comparison recovers multiplicities and weight multisets.**

This variant does not assume matching copy counts. Eventual coefficient equality is
first extrapolated to exponent `0`, which recovers the cardinalities of the two
weight families, and then Newton--Girard recovers the multisets. -/
lemma exists_copies_eq_and_weight_multiset_eq_of_sameMPV_bnt
    {dim : Fin g → ℕ}
    (basis : (j : Fin g) → MPSTensor d (dim j))
    (S T : SectorWeightData g)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin g => mpvState (basis j) N))
    (hSame : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ j : Fin g, S.coeff N j * mpv (basis j) σ =
      ∑ j : Fin g, T.coeff N j * mpv (basis j) σ) :
    ∃ hCopies : ∀ j, S.copies j = T.copies j,
      ∀ j : Fin g,
        Finset.univ.val.map (S.weight j) =
          Finset.univ.val.map (fun q => T.weight j (Fin.cast (hCopies j) q)) := by
  obtain ⟨_, hCoeffEventuallyEq⟩ := coeff_eventually_eq_of_sameMPV basis S T hLI hSame
  let hCopies : ∀ j, S.copies j = T.copies j :=
    copies_eq_of_eventually_coeff_eq S T hCoeffEventuallyEq
  refine ⟨hCopies, ?_⟩
  have hCoeffAllPosEq := eventually_coeff_eq_implies_all_pos_eq S T hCopies hCoeffEventuallyEq
  exact weight_multiset_eq_of_copies_eq_of_coeff_eq S T hCopies hCoeffAllPosEq

end SectorWeightData

end MPSTensor
