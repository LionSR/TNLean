/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.SharedInfra.SectorDecomposition
import TNLean.MPS.BNT.Basic
import TNLean.Algebra.ScalarPowerSumIdentity

import Mathlib.Data.Fintype.BigOperators

/-!
# Sector decomposition comparison theorems

The shared multiplicity layer
`SectorWeightData` / `SectorDecomposition` now lives in
`TNLean.MPS.SharedInfra.SectorDecomposition`.

This file adds the higher-level equal-case Fundamental Theorem machinery:

* coefficient comparison from BNT linear independence,
* Newton–Girard recovery of sector-weight multisets,
* the combined equal-case corollaries used by the FT stack.

## References

- [PGVWC07] Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- [CPSV17] Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017).
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
theorem coeff_eventually_eq_of_sameMPV
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
theorem weight_multiset_eq_of_copies_eq_of_coeff_eq
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

The bridge between "eventually equal coefficients" (for `N > N₀`) and "all positive `k` equal
coefficients" rests on a **telescoping induction** on linear combinations of geometric
sequences.

**Key lemma** (`geom_sum_eventually_zero`): a finite linear combination
`N ↦ ∑ᵢ cᵢ · wᵢᴺ` with all bases `wᵢ ≠ 0` that vanishes for all `N ≥ M` vanishes
identically.

**Proof**: by induction on the number of terms `n`. Subtract `w₀` times the equation at `N`
from the equation at `N+1` to telescope out the `i = 0` term, reducing to a sum with `n − 1`
nonzero terms. By the inductive hypothesis this shorter sum vanishes for *all* `k`, giving the
recurrence `S(k+1) = w₀ · S(k)`, hence `S(k) = w₀ᵏ · S(0)`. Since `S(M) = 0` and
`w₀ᴹ ≠ 0`, we conclude `S(0) = 0`, so `S ≡ 0`.

The main lemma `eventually_coeff_eq_implies_all_pos_eq` reduces to this by concatenating the
two weight families (using `Fin.append`) with coefficients `+1` and `−1`.
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

/-- If two families of nonzero complex scalars have equal power sums for all sufficiently
large exponents, then their power sums agree for ALL exponents.

Reduces to `geom_sum_eventually_zero` by concatenating the two families with
coefficients `+1` and `−1`. -/
lemma power_sums_eq_of_eventually_eq
    {m : ℕ} (a b : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    {M : ℕ}
    (hEv : ∀ N, M ≤ N → ∑ i, a i ^ N = ∑ i, b i ^ N) :
    ∀ k, ∑ i, a i ^ k = ∑ i, b i ^ k := by
  let w : Fin (m + m) → ℂ := Fin.append a b
  let coeffs : Fin (m + m) → ℂ := Fin.append (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ))
  have hw : ∀ i, w i ≠ 0 :=
    fun i => Fin.addCases
      (fun j => by show w (Fin.castAdd m j) ≠ 0
                   rw [show w (Fin.castAdd m j) = a j from Fin.append_left a b j]; exact ha j)
      (fun j => by show w (Fin.natAdd m j) ≠ 0
                   rw [show w (Fin.natAdd m j) = b j from Fin.append_right a b j]; exact hb j)
      i
  have hDecomp : ∀ k, ∑ i, coeffs i * w i ^ k = (∑ i, a i ^ k) - (∑ i, b i ^ k) := by
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

This combines:
1. `coeff_eventually_eq_of_sameMPV`: BNT LI + equal MPVs → eventual coefficient equality.
2. Extrapolation (`eventually_coeff_eq_implies_all_pos_eq`): eventual equality →
   full equality for all positive `k` (telescoping induction on geometric sums).
3. `weight_multiset_eq_of_copies_eq_of_coeff_eq`: full coefficient equality + same
   multiplicities → equal weight multisets (Newton–Girard). -/
theorem weight_multiset_eq_of_sameMPV_bnt
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
  obtain ⟨N0, hCoeffEventuallyEq⟩ := coeff_eventually_eq_of_sameMPV basis S T hLI hSame
  have hCoeffAllPosEq := eventually_coeff_eq_implies_all_pos_eq S T hCopies hCoeffEventuallyEq
  exact weight_multiset_eq_of_copies_eq_of_coeff_eq S T hCopies hCoeffAllPosEq

end SectorWeightData

/-! ## Equal-case fundamental theorem for sector decompositions

The following theorems compose the MPV expansion formula
(`SectorDecomposition.mpv_toTensor_eq_sum_coeff`) with the weight multiset recovery theorem
(`SectorWeightData.weight_multiset_eq_of_sameMPV_bnt`) to obtain the strongest currently
available equal-case result for sector decompositions sharing a common BNT basis.

**What is proved**: if two sector decompositions over the same BNT basis with the same
multiplicities produce equal total MPVs, then the sector weight multisets are equal for each
basis block.

**What remains open**: global gauge equivalence of the assembled tensors. This would follow
from `fundamentalTheorem_proportionalMPV_CFBNT` (the proportional-case FT in `Full.lean`)
if one could additionally supply convergent decomposition coefficients with nonzero limits.
The sector decomposition coefficients `∑_q μ_{j,q}^N` are sums of geometric sequences that
may oscillate (unit-modulus terms), so coefficient convergence is not automatic and requires
either a dominant-weight hypothesis or an explicit normalization strategy.
-/

/-- **Equal-case FT for sector decompositions with shared BNT basis.**

If two sector decompositions built from the same BNT basis family, with the same
multiplicities, produce equal total MPVs (via `SameMPV₂`), then the sector weight
multisets are equal for each basis block.

This composes:
1. `SectorDecomposition.mpv_toTensor_eq_sum_coeff` (MPV expansion),
2. `SectorWeightData.coeff_eventually_eq_of_sameMPV` (BNT LI → eventual coefficient equality),
3. `eventually_coeff_eq_implies_all_pos_eq` (telescoping extrapolation),
4. `weight_multiset_eq_of_copies_eq_of_coeff_eq` (Newton–Girard). -/
theorem fundamentalTheorem_equalMPV_sectorDecomposition
    {d g : ℕ}
    {dim : Fin g → ℕ}
    (basis : (j : Fin g) → MPSTensor d (dim j))
    (S T : SectorWeightData g)
    (hCopies : ∀ j, S.copies j = T.copies j)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin g => mpvState (basis j) N))
    (hEqual : SameMPV₂
        (SectorDecomposition.mk g dim basis S).toTensor
        (SectorDecomposition.mk g dim basis T).toTensor) :
    ∀ j : Fin g,
      Finset.univ.val.map (S.weight j) =
        Finset.univ.val.map (fun q => T.weight j (Fin.cast (hCopies j) q)) := by
  apply SectorWeightData.weight_multiset_eq_of_sameMPV_bnt basis S T hCopies hLI
  intro N σ
  have hExpandS := (SectorDecomposition.mk g dim basis S).mpv_toTensor_eq_sum_coeff σ (N := N)
  have hExpandT := (SectorDecomposition.mk g dim basis T).mpv_toTensor_eq_sum_coeff σ (N := N)
  -- These are exactly the coefficient expansions for the two assembled tensors.
  calc ∑ j, S.coeff N j * mpv (basis j) σ
      = mpv (SectorDecomposition.mk g dim basis S).toTensor σ := hExpandS.symm
    _ = mpv (SectorDecomposition.mk g dim basis T).toTensor σ := hEqual N σ
    _ = ∑ j, T.coeff N j * mpv (basis j) σ := hExpandT

end MPSTensor
