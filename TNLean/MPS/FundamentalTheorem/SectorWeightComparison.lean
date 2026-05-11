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

The endpoint below uses the unequal-cardinality finite-range power-sum theorem
directly, as in the Appendix comparison.  Without nonzero weights, positive
powers would only determine the nonzero submultiset.

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

/-! ### Extrapolation of power-sum sequences

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

/-- Eventual equality of coefficient power sums forces equality of multiplicities and
weight multisets.

For each basis tensor, eventual equality is first extrapolated to all positive
exponents.  The finite-range unequal-cardinality power-sum theorem then gives the
copy count and the multiset of weights, using the nonzero-entry hypotheses carried
by `SectorWeightData`.  This is the formal counterpart of the Appendix power-sum
comparison in arXiv:1606.00608. -/
lemma copies_eq_and_weight_multiset_eq_of_eventually_coeff_eq
    (S T : SectorWeightData g)
    {N0 : ℕ}
    (hEv : ∀ N > N0, ∀ j : Fin g, S.coeff N j = T.coeff N j) :
    ∃ hCopies : ∀ j, S.copies j = T.copies j,
      ∀ j : Fin g,
        Finset.univ.val.map (S.weight j) =
          Finset.univ.val.map (fun q => T.weight j (Fin.cast (hCopies j) q)) := by
  have hPer :
      ∀ j : Fin g,
        ∃ hCopies : S.copies j = T.copies j,
          Finset.univ.val.map (S.weight j) =
            Finset.univ.val.map (fun q => T.weight j (Fin.cast hCopies q)) := by
    intro j
    have hEvj : ∀ N, N0 + 1 ≤ N →
        ∑ q : Fin (S.copies j), (S.weight j q) ^ N =
          ∑ q : Fin (T.copies j), (T.weight j q) ^ N := by
      intro N hN
      have h := hEv N (by omega) j
      simpa only [SectorWeightData.coeff] using h
    have hAll := power_sums_eq_of_eventually_eq_hetero
      (S.weight j) (T.weight j)
      (fun q => S.weight_ne_zero j q)
      (fun q => T.weight_ne_zero j q)
      (M := N0 + 1) hEvj
    obtain ⟨hCopies, hMultiset⟩ :=
      Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card
        (S.copies j) (T.copies j) (S.weight j) (T.weight j)
        (fun q => S.weight_ne_zero j q)
        (fun q => T.weight_ne_zero j q)
        (fun k hk _hkMax => hAll k)
    refine ⟨hCopies, ?_⟩
    have hReindex :
        Finset.univ.val.map (fun q : Fin (S.copies j) => T.weight j (Fin.cast hCopies q)) =
          Finset.univ.val.map (T.weight j) := by
      simpa [Multiset.map_map, Function.comp_def, Fin.castOrderIso_apply] using
        congrArg (Multiset.map (T.weight j))
          (Multiset.map_univ_val_equiv (Fin.castOrderIso hCopies).toEquiv)
    exact hMultiset.trans hReindex.symm
  let hCopies : ∀ j, S.copies j = T.copies j := fun j => (hPer j).choose
  refine ⟨hCopies, ?_⟩
  intro j
  exact (hPer j).choose_spec

/-- **BNT coefficient comparison recovers multiplicities and weight multisets.**

This variant does not assume matching copy counts. Eventual coefficient equality is
first extrapolated to all positive exponents. The unequal-cardinality finite-range
power-sum theorem then recovers both the copy counts and the multisets of weights. -/
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
  exact copies_eq_and_weight_multiset_eq_of_eventually_coeff_eq S T hCoeffEventuallyEq

end SectorWeightData

end MPSTensor
