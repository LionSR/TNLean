/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.SharedInfra.SectorDecomposition
import TNLean.MPS.BNT.Basic
import TNLean.MPS.BNT.PermutationRigidityPrimitive
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.Algebra.ScalarPowerSumIdentity

import Mathlib.Data.Fintype.BigOperators

/-!
# Sector decomposition comparison theorems

The shared multiplicity layer
`SectorWeightData` / `SectorDecomposition` now lives in
`TNLean.MPS.SharedInfra.SectorDecomposition`.

This file adds the higher-level equal-case Fundamental Theorem constructions:

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

/-- **Predicate asserting a sector decomposition's basis satisfies the BNT
linear-independence condition.**

`HasBNTSectorData P` asserts that the basis of the sector decomposition `P` is
a basis of normal tensors in the sense of Def. 4.2 of arXiv:2011.12127: for all
sufficiently large system sizes `N`, the MPV states `mpvState (P.basis j) N`
are linearly independent.  It is a `Prop`; no data is bundled.

This is exactly the linear-independence hypothesis consumed by the equal-case
sector comparison theorems in this file, i.e.
`fundamentalTheorem_equalMPV_sectorDecomposition` and the heterogeneous variants
introduced in PR #844.  It is the predicate tracked by issue #876 as the output
of a general BNT sector construction for the after-blocking canonical-form
reduction, and is the linear-independence hypothesis expected by the
after-blocking sector comparison of issue #877. -/
def HasBNTSectorData (P : SectorDecomposition d) : Prop :=
  ∃ N0 : ℕ, ∀ N > N0,
    LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N)

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

The connection between "eventually equal coefficients" (for `N > N₀`) and
"equal coefficients for every positive `k`" rests on a **telescoping induction**
on linear combinations of geometric sequences.

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
theorem copies_eq_of_eventually_coeff_eq
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
  obtain ⟨_, hCoeffEventuallyEq⟩ := coeff_eventually_eq_of_sameMPV basis S T hLI hSame
  have hCoeffAllPosEq := eventually_coeff_eq_implies_all_pos_eq S T hCopies hCoeffEventuallyEq
  exact weight_multiset_eq_of_copies_eq_of_coeff_eq S T hCopies hCoeffAllPosEq

/-- **BNT coefficient comparison recovers multiplicities and weight multisets.**

This variant does not assume matching copy counts. Eventual coefficient equality is
first extrapolated to exponent `0`, which recovers the cardinalities of the two
weight families, and then Newton--Girard recovers the multisets. -/
theorem exists_copies_eq_and_weight_multiset_eq_of_sameMPV_bnt
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

/-- **Phase matching and total MPV equality recover copy counts and sector weights.**

Assume two sector decompositions `P` and `Q` have basis blocks matched by a
permutation `perm`, and the matched basis MPVs differ by nonzero phase powers.
If the total tensors are `SameMPV₂` and the basis of `P` is eventually linearly
independent, then the copy counts are forced to agree. After absorbing the same
phases into the weights of `Q`, the per-basis sector weight multisets agree.

This is the coefficient-extraction part of the heterogeneous sector comparison:
copy alignment is not an input, but is recovered from the exponent-zero case of
the power-sum identity after eventual coefficient equality has been extrapolated
to all exponents. -/
theorem fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch_exists_copies
    (P Q : SectorDecomposition d)
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hPhase : ∀ j : Fin P.basisCount,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (perm j)) σ = ζ ^ N * mpv (P.basis j) σ)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  classical
  let ζFn : Fin P.basisCount → ℂ := fun j => (hPhase j).choose
  have hζ_ne : ∀ j : Fin P.basisCount, ζFn j ≠ 0 :=
    fun j => (hPhase j).choose_spec.1
  have hζ_mpv : ∀ (j : Fin P.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis (perm j)) σ = (ζFn j) ^ N * mpv (P.basis j) σ :=
    fun j N σ => (hPhase j).choose_spec.2 N σ
  let T : SectorWeightData P.basisCount := {
    copies := fun j => Q.copies (perm j)
    copies_pos := fun j => Q.copies_pos (perm j)
    weight := fun j q => ζFn j * Q.weight (perm j) q
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j) (Q.weight_ne_zero (perm j) q)
  }
  let Q' : SectorDecomposition d := {
    basisCount := P.basisCount
    basisDim := P.basisDim
    basis := P.basis
    sectors := T
  }
  have hTransport : SameMPV₂ Q'.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv Q'.toTensor σ
          = ∑ j : Fin P.basisCount,
              ∑ q : Fin (Q.copies (perm j)),
                (ζFn j * Q.weight (perm j) q) ^ N * mpv (P.basis j) σ := by
              simpa [Q', T] using Q'.mpv_toTensor_eq_sum_sectors (N := N) σ
      _ = ∑ j : Fin P.basisCount,
            ∑ q : Fin (Q.copies (perm j)),
              (Q.weight (perm j) q) ^ N * mpv (Q.basis (perm j)) σ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun q _ => ?_
            calc
              (ζFn j * Q.weight (perm j) q) ^ N * mpv (P.basis j) σ
                  = (Q.weight (perm j) q) ^ N * ((ζFn j) ^ N * mpv (P.basis j) σ) := by
                      rw [mul_pow]
                      ring
              _ = (Q.weight (perm j) q) ^ N * mpv (Q.basis (perm j)) σ := by
                      rw [hζ_mpv j N σ]
      _ = ∑ k : Fin Q.basisCount,
            ∑ q : Fin (Q.copies k),
              (Q.weight k q) ^ N * mpv (Q.basis k) σ := by
            let f : Fin P.basisCount → ℂ := fun j =>
              ∑ q : Fin (Q.copies (perm j)),
                (Q.weight (perm j) q) ^ N * mpv (Q.basis (perm j)) σ
            let g : Fin Q.basisCount → ℂ := fun k =>
              ∑ q : Fin (Q.copies k),
                (Q.weight k q) ^ N * mpv (Q.basis k) σ
            have hfg : ∀ j, f j = g (perm j) := by
              intro j
              rfl
            simpa [f, g] using (Fintype.sum_equiv perm f g hfg)
      _ = mpv Q.toTensor σ := by
            simpa using (Q.mpv_toTensor_eq_sum_sectors (N := N) σ).symm
  have hEqual' : SameMPV₂ P.toTensor Q'.toTensor := by
    intro N σ
    exact (hEqual N σ).trans (hTransport N σ).symm
  have hRecovered :
      ∃ hCopies' : ∀ j : Fin P.basisCount, P.sectors.copies j = T.copies j,
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map (fun q => T.weight j (Fin.cast (hCopies' j) q)) :=
    SectorWeightData.exists_copies_eq_and_weight_multiset_eq_of_sameMPV_bnt
      (basis := P.basis) (S := P.sectors) (T := T) hLI (by
        intro N σ
        have hExpandP := P.mpv_toTensor_eq_sum_coeff σ (N := N)
        have hExpandQ' := Q'.mpv_toTensor_eq_sum_coeff σ (N := N)
        calc ∑ j, P.sectors.coeff N j * mpv (P.basis j) σ
            = mpv P.toTensor σ := hExpandP.symm
          _ = mpv Q'.toTensor σ := hEqual' N σ
          _ = ∑ j, T.coeff N j * mpv (P.basis j) σ := hExpandQ')
  obtain ⟨hCopies', hMultiset⟩ := hRecovered
  let hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j) := fun j => by
    change P.sectors.copies j = T.copies j
    exact hCopies' j
  refine ⟨hCopies, ζFn, hζ_ne, ?_⟩
  intro j
  have hproof : hCopies' j = hCopies j := Subsingleton.elim _ _
  simpa [T, hproof] using hMultiset j

/-- **Heterogeneous sector comparison reduces to the shared-basis case after phase matching.**

Assume two sector decompositions `P` and `Q` have basis blocks matched by a permutation `perm`,
matching copy counts, and per-basis MPV relations
`mpv (Q.basis (perm j)) σ = ζ_j^N * mpv (P.basis j) σ`. If the total tensors are
`SameMPV₂`, then after absorbing the phases `ζ_j` into the sector weights on the `Q` side,
the per-basis sector weight multisets agree. -/
theorem fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch
    (P Q : SectorDecomposition d)
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j))
    (hPhase : ∀ j : Fin P.basisCount,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (perm j)) σ = ζ ^ N * mpv (P.basis j) σ)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ ζ : Fin P.basisCount → ℂ,
      (∀ j, ζ j ≠ 0) ∧
      ∀ j : Fin P.basisCount,
        Finset.univ.val.map (P.weight j) =
          Finset.univ.val.map
            (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨hCopies', ζ, hζ_ne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch_exists_copies
      P Q perm hPhase hLI hEqual
  refine ⟨ζ, hζ_ne, ?_⟩
  intro j
  have hproof : hCopies' j = hCopies j := Subsingleton.elim _ _
  simpa [hproof] using hMultiset j

/-- **Cast-compatible MPV scaling implies the phase-matched heterogeneous sector comparison.**

This theorem isolates the weaker data actually consumed by the
phase-absorption argument: after matching basis dimensions, each block pair
only needs a nonzero phase `ζ` relating the MPVs of the matched basis tensors. -/
theorem fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_mpvScaling_matched_basis
    (P Q : SectorDecomposition d)
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j))
    (hBasis : ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (perm j),
        ∃ ζ : ℂ, ζ ≠ 0 ∧
          ∀ (N : ℕ) (σ : Fin N → Fin d),
            mpv (Q.basis (perm j)) σ =
              ζ ^ N * mpv (cast (congr_arg (MPSTensor d) hdim) (P.basis j)) σ)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ ζ : Fin P.basisCount → ℂ,
      (∀ j, ζ j ≠ 0) ∧
      ∀ j : Fin P.basisCount,
        Finset.univ.val.map (P.weight j) =
          Finset.univ.val.map
            (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  have hPhase : ∀ j : Fin P.basisCount,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (perm j)) σ = ζ ^ N * mpv (P.basis j) σ := by
    intro j
    obtain ⟨hdim, ζ, hζne, hmpv⟩ := hBasis j
    refine ⟨ζ, hζne, ?_⟩
    intro N σ
    rw [hmpv N σ, mpv_cast_dim hdim (P.basis j) N σ]
  exact fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch
    P Q perm hCopies hPhase hLI hEqual

/-- **Gauge-phase matched sector bases imply the phase-matched heterogeneous sector comparison.**

This theorem states the MPV scaling relation obtained from blockwise
`GaugePhaseEquiv` and applies
`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_mpvScaling_matched_basis`.
Thus the remaining missing ingredients for the full heterogeneous BNT-sector
comparison are not the algebraic phase-absorption step below, but the
derivation of the basis/copy matching data from arbitrary `SameMPV₂` sector
decompositions. -/
theorem fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis
    (P Q : SectorDecomposition d)
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j))
    (hBasis : ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (perm j),
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
          (Q.basis (perm j)))
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ ζ : Fin P.basisCount → ℂ,
      (∀ j, ζ j ≠ 0) ∧
      ∀ j : Fin P.basisCount,
        Finset.univ.val.map (P.weight j) =
          Finset.univ.val.map
            (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  have hScaling : ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (perm j),
        ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (perm j)) σ =
            ζ ^ N * mpv (cast (congr_arg (MPSTensor d) hdim) (P.basis j)) σ := by
    intro j
    obtain ⟨hdim, hGPE⟩ := hBasis j
    obtain ⟨X, ζ, hζne, hX⟩ := hGPE
    refine ⟨hdim, ζ, hζne, ?_⟩
    intro N σ
    exact mpv_eq_pow_mul_of_gaugePhase _ _ X ζ hX N σ
  exact fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_mpvScaling_matched_basis
    P Q perm hCopies hScaling hLI hEqual

/-! ## Witness bundle for the heterogeneous sector comparison

The matched-basis theorems above consume the matching data as four separate
hypotheses (permutation, copy alignment, per-block dimension equality, and
per-block gauge-phase equivalence). The `SectorBasisMatching` structure
collects these as a single witness. A theorem deriving this witness from
`SameMPV₂` supplies the remaining step for the unconditional equal-case
Fundamental Theorem, following from the general basis-of-normal-tensors
construction; the final global Corollary IV.5 construction can then depend only
on this structure.
-/

/-- Basis matching before sector multiplicities have been recovered.

This structure captures the part of the heterogeneous BNT comparison supplied by
the overlap-dichotomy argument: a permutation of basis blocks, equality of their
bond dimensions, and gauge-phase equivalence of the matched blocks. It does not
include copy-count alignment; that alignment is recovered from total MPV equality
by `SectorBasisPreMatching.exists_sectorBasisMatching_of_sameMPV`. -/
structure SectorBasisPreMatching (P Q : SectorDecomposition d) where
  /-- Permutation matching basis indices of `P` and `Q`. -/
  perm : Fin P.basisCount ≃ Fin Q.basisCount
  /-- Matched basis blocks share the same bond dimension. -/
  dim_eq : ∀ j : Fin P.basisCount, P.basisDim j = Q.basisDim (perm j)
  /-- Matched basis blocks are gauge-phase equivalent after dimension transport. -/
  basis_equiv : ∀ j : Fin P.basisCount,
    GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) (dim_eq j)) (P.basis j))
      (Q.basis (perm j))

/-- Bundled witness data matching two sector decompositions block-by-block.

This structure collects the four pieces of data consumed by
`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`:

* a basis permutation,
* per-block multiplicity agreement,
* per-block bond-dimension equality, and
* per-block gauge-phase equivalence of the (dimension-transported) basis blocks.

Producing a `SectorBasisMatching P Q` from an arbitrary `SameMPV₂ P.toTensor
Q.toTensor` is the remaining combinatorial step in the Gap §1 closure
(see the remark in `blueprint/src/chapter/ch11_assembly.tex` and
arXiv:2011.12127 §IV.B–IV.C). Once that extraction is available, the
algebraic reduction runs purely through
`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching`. -/
structure SectorBasisMatching (P Q : SectorDecomposition d) where
  /-- Permutation matching basis indices of `P` and `Q`. -/
  perm : Fin P.basisCount ≃ Fin Q.basisCount
  /-- Matched basis blocks carry the same multiplicity. -/
  copies_eq : ∀ j : Fin P.basisCount, P.copies j = Q.copies (perm j)
  /-- Matched basis blocks share the same bond dimension. -/
  dim_eq : ∀ j : Fin P.basisCount, P.basisDim j = Q.basisDim (perm j)
  /-- Matched basis blocks are gauge-phase equivalent after dimension transport. -/
  basis_equiv : ∀ j : Fin P.basisCount,
    GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) (dim_eq j)) (P.basis j))
      (Q.basis (perm j))

private lemma sectorBasisMatchExists_of_fields
    {P Q : SectorDecomposition d}
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (dim_eq : ∀ j : Fin P.basisCount, P.basisDim j = Q.basisDim (perm j))
    (basis_equiv : ∀ j : Fin P.basisCount,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (dim_eq j)) (P.basis j))
        (Q.basis (perm j))) :
    ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (perm j),
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
          (Q.basis (perm j)) :=
  fun j => ⟨dim_eq j, basis_equiv j⟩

namespace SectorBasisMatching

variable {P Q : SectorDecomposition d}

/-- Reformulate the per-block data in the existential form consumed by
`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`. -/
lemma basis_match_exists (M : SectorBasisMatching P Q) :
    ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (M.perm j),
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
          (Q.basis (M.perm j)) :=
  sectorBasisMatchExists_of_fields M.perm M.dim_eq M.basis_equiv

/-- Build a `SectorBasisMatching` from a bijective index correspondence together with the
per-block copy / dimension / gauge-phase data.

This is the natural output shape of a general basis-of-normal-tensors matching extractor
(pending from #876): such an extractor delivers a function `f` on basis indices, a bijectivity
certificate, and per-index compatibility data. -/
noncomputable def ofBijective
    (f : Fin P.basisCount → Fin Q.basisCount)
    (hf : Function.Bijective f)
    (hCopies : ∀ j, P.copies j = Q.copies (f j))
    (hDim : ∀ j, P.basisDim j = Q.basisDim (f j))
    (hEquiv : ∀ j, GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) (hDim j)) (P.basis j)) (Q.basis (f j))) :
    SectorBasisMatching P Q where
  perm := Equiv.ofBijective f hf
  copies_eq := fun j => by
    change P.copies j = Q.copies (f j)
    exact hCopies j
  dim_eq := fun j => by
    change P.basisDim j = Q.basisDim (f j)
    exact hDim j
  basis_equiv := fun j => by
    change GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) (hDim j)) (P.basis j)) (Q.basis (f j))
    exact hEquiv j

end SectorBasisMatching

namespace SectorBasisPreMatching

variable {P Q : SectorDecomposition d}

/-- Reformulate pre-matching data in the existential form used by the matched-basis theorem. -/
lemma basis_match_exists (M : SectorBasisPreMatching P Q) :
    ∀ j : Fin P.basisCount,
      ∃ hdim : P.basisDim j = Q.basisDim (M.perm j),
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (P.basis j))
          (Q.basis (M.perm j)) :=
  sectorBasisMatchExists_of_fields M.perm M.dim_eq M.basis_equiv

/-- Gauge-phase pre-matching gives the MPV phase-scaling relation for each basis block. -/
lemma phase_match_exists (M : SectorBasisPreMatching P Q) :
    ∀ j : Fin P.basisCount,
      ∃ ζ : ℂ, ζ ≠ 0 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis (M.perm j)) σ = ζ ^ N * mpv (P.basis j) σ := by
  intro j
  obtain ⟨X, ζ, hζne, hX⟩ := M.basis_equiv j
  refine ⟨ζ, hζne, ?_⟩
  intro N σ
  rw [mpv_eq_pow_mul_of_gaugePhase _ _ X ζ hX N σ,
    mpv_cast_dim (M.dim_eq j) (P.basis j) N σ]

/-- Promote a basis pre-matching to a full sector basis matching.

The new information is the copy-count equality. It follows from total MPV equality
and BNT linear independence by recovering the exponent-zero power sums for the
matched sector coefficients. -/
theorem exists_sectorBasisMatching_of_sameMPV
    (M : SectorBasisPreMatching P Q)
    (hLI : HasBNTSectorData P)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ M' : SectorBasisMatching P Q, M'.perm = M.perm := by
  obtain ⟨hCopies, _ζ, _hζ_ne, _hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch_exists_copies
      P Q M.perm M.phase_match_exists hLI hEqual
  refine ⟨{
    perm := M.perm
    copies_eq := hCopies
    dim_eq := M.dim_eq
    basis_equiv := M.basis_equiv
  }, rfl⟩

end SectorBasisPreMatching

/-- **Heterogeneous sector comparison from a basis pre-matching.**

A pre-matching supplies the permutation, bond-dimension equalities, and
gauge-phase equivalences of the basis blocks. Total MPV equality and BNT linear
independence then recover the missing copy-count equalities and the phase-adjusted
sector weight multisets. -/
theorem fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_preMatching
    {P Q : SectorDecomposition d}
    (M : SectorBasisPreMatching P Q)
    (hLI : HasBNTSectorData P)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ hCopies : ∀ j : Fin P.basisCount, P.copies j = Q.copies (M.perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (M.perm j) (Fin.cast (hCopies j) q)) :=
  fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch_exists_copies
    P Q M.perm M.phase_match_exists hLI hEqual

/-- Single-family primitive overlap-orthogonality data for a sector basis.

This is the part of `SectorBasisOverlapSpanHypotheses` that can be checked one
sector decomposition at a time: positive basis dimensions, left-canonical
normalization, self-overlap convergence to `1`, and off-diagonal overlap
convergence to `0`. It intentionally omits one-site injectivity and the
finite-length span comparison between two different bases, because those are
separate inputs in the current Gap §1 route. -/
structure SectorBasisOverlapOrthoHypotheses (P : SectorDecomposition d) : Prop where
  /-- The basis blocks have nonzero bond dimension. -/
  dim_pos : ∀ j : Fin P.basisCount, 0 < P.basisDim j
  /-- The basis blocks are left-canonical. -/
  normalized :
    ∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1
  /-- Each basis block has self-overlap tending to one. -/
  self_overlap : ∀ j : Fin P.basisCount,
    Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
      Filter.atTop (nhds (1 : ℂ))
  /-- Distinct basis blocks have asymptotically zero overlap. -/
  off_overlap : ∀ i j : Fin P.basisCount, i ≠ j →
    Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
      Filter.atTop (nhds 0)

/-- Primitive overlap-rigidity hypotheses for two sector bases.

This structure collects the analytic inputs used by
`exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV`: nonzero bond
dimensions, injectivity, left-canonical normalization, asymptotic self/orthogonal
overlaps, and equality of the finite-length MPV spans. It deliberately does
not contain a permutation or copy alignment; those are produced by the overlap
rigidity theorem and the BNT coefficient comparison. -/
structure SectorBasisOverlapSpanHypotheses (P Q : SectorDecomposition d) : Prop where
  /-- The left basis blocks have nonzero bond dimension. -/
  left_dim_pos : ∀ j : Fin P.basisCount, 0 < P.basisDim j
  /-- The right basis blocks have nonzero bond dimension. -/
  right_dim_pos : ∀ k : Fin Q.basisCount, 0 < Q.basisDim k
  /-- The left basis blocks are injective. -/
  left_injective : ∀ j : Fin P.basisCount, IsInjective (P.basis j)
  /-- The right basis blocks are injective. -/
  right_injective : ∀ k : Fin Q.basisCount, IsInjective (Q.basis k)
  /-- The left basis blocks are left-canonical. -/
  left_normalized :
    ∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1
  /-- The right basis blocks are left-canonical. -/
  right_normalized :
    ∀ k : Fin Q.basisCount, (∑ i : Fin d, (Q.basis k i)ᴴ * (Q.basis k i)) = 1
  /-- Each left basis block has self-overlap tending to one. -/
  left_self_overlap : ∀ j : Fin P.basisCount,
    Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
      Filter.atTop (nhds (1 : ℂ))
  /-- Distinct left basis blocks have asymptotically zero overlap. -/
  left_off_overlap : ∀ i j : Fin P.basisCount, i ≠ j →
    Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
      Filter.atTop (nhds 0)
  /-- Each right basis block has self-overlap tending to one. -/
  right_self_overlap : ∀ k : Fin Q.basisCount,
    Filter.Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis k) N)
      Filter.atTop (nhds (1 : ℂ))
  /-- Distinct right basis blocks have asymptotically zero overlap. -/
  right_off_overlap : ∀ k l : Fin Q.basisCount, k ≠ l →
    Filter.Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis l) N)
      Filter.atTop (nhds 0)
  /-- The finite-length spans of the two sector bases agree. -/
  span_eq : ∀ N,
    Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
      mpvState (d := d) (P.basis j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
      mpvState (d := d) (Q.basis k) N))

namespace SectorBasisOverlapOrthoHypotheses

variable {P Q : SectorDecomposition d}

/-- Combine the single-family overlap-orthogonality data for two sector bases
with the remaining one-site injectivity and finite-length span comparison inputs
needed by the primitive overlap-rigidity theorem. -/
theorem to_overlapSpan
    (HP : SectorBasisOverlapOrthoHypotheses P)
    (HQ : SectorBasisOverlapOrthoHypotheses Q)
    (hP_inj : ∀ j : Fin P.basisCount, IsInjective (P.basis j))
    (hQ_inj : ∀ k : Fin Q.basisCount, IsInjective (Q.basis k))
    (hspan : ∀ N,
      Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
        mpvState (d := d) (P.basis j) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
        mpvState (d := d) (Q.basis k) N))) :
    SectorBasisOverlapSpanHypotheses P Q where
  left_dim_pos := HP.dim_pos
  right_dim_pos := HQ.dim_pos
  left_injective := hP_inj
  right_injective := hQ_inj
  left_normalized := HP.normalized
  right_normalized := HQ.normalized
  left_self_overlap := HP.self_overlap
  left_off_overlap := HP.off_overlap
  right_self_overlap := HQ.self_overlap
  right_off_overlap := HQ.off_overlap
  span_eq := hspan

end SectorBasisOverlapOrthoHypotheses

/-- Produce a sector basis matching from the primitive overlap-rigidity hypotheses.

The overlap-rigidity theorem gives the basis permutation, dimension equalities,
and gauge-phase equivalences. The preceding pre-matching result then recovers
the sector copy-count alignment from total MPV equality. -/
theorem exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV
    (P Q : SectorDecomposition d)
    [∀ j : Fin P.basisCount, NeZero (P.basisDim j)]
    [∀ k : Fin Q.basisCount, NeZero (Q.basisDim k)]
    (hP_inj : ∀ j, IsInjective (P.basis j))
    (hQ_inj : ∀ k, IsInjective (Q.basis k))
    (hP_norm : ∀ j, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1)
    (hQ_norm : ∀ k, (∑ i : Fin d, (Q.basis k i)ᴴ * (Q.basis k i)) = 1)
    (hP_self : ∀ j,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
        Filter.atTop (nhds (1 : ℂ)))
    (hP_off : ∀ i j, i ≠ j →
      Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
        Filter.atTop (nhds 0))
    (hQ_self : ∀ k,
      Filter.Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis k) N)
        Filter.atTop (nhds (1 : ℂ)))
    (hQ_off : ∀ k l, k ≠ l →
      Filter.Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis l) N)
        Filter.atTop (nhds 0))
    (hspan : ∀ N,
      Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
        mpvState (d := d) (P.basis j) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
        mpvState (d := d) (Q.basis k) N)))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    Nonempty (SectorBasisMatching P Q) := by
  obtain ⟨_hCount, perm, hBasis⟩ :=
    exists_eq_numBlocks_and_equiv_gaugePhase_of_overlapOrtho
      (A := P.basis) (B := Q.basis)
      hP_inj hQ_inj hP_norm hQ_norm hP_self hP_off hQ_self hQ_off hspan
  let M₀ : SectorBasisPreMatching P Q := {
    perm := perm
    dim_eq := fun j => (hBasis j).choose
    basis_equiv := fun j => (hBasis j).choose_spec
  }
  have hLI : HasBNTSectorData P := by
    have hEventually := eventually_linearIndependent_of_overlap_tendsto_orthonormal
      P.basis hP_self hP_off
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hEventually
    exact ⟨N0, fun N hN => hN0 N (le_of_lt hN)⟩
  obtain ⟨M, _hperm⟩ := M₀.exists_sectorBasisMatching_of_sameMPV hLI hEqual
  exact ⟨M⟩

namespace SectorBasisOverlapSpanHypotheses

variable {P Q : SectorDecomposition d}

/-- Convert the bundled primitive overlap-rigidity hypotheses into a sector basis
matching. The produced witness is not part of the hypotheses: it is obtained by
`exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV`. -/
theorem exists_sectorBasisMatching
    (H : SectorBasisOverlapSpanHypotheses P Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    Nonempty (SectorBasisMatching P Q) := by
  letI : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j => ⟨Nat.ne_of_gt (H.left_dim_pos j)⟩
  letI : ∀ k : Fin Q.basisCount, NeZero (Q.basisDim k) :=
    fun k => ⟨Nat.ne_of_gt (H.right_dim_pos k)⟩
  exact exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV P Q
    H.left_injective H.right_injective H.left_normalized H.right_normalized
    H.left_self_overlap H.left_off_overlap H.right_self_overlap H.right_off_overlap
    H.span_eq hEqual

end SectorBasisOverlapSpanHypotheses

/-- **Heterogeneous sector comparison via a bundled basis matching witness.**

Corollary of `fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`
obtained by supplying the matching data in bundled form as a `SectorBasisMatching`. Once a
theorem constructs a `SectorBasisMatching P Q` from arbitrary `SameMPV₂ P.toTensor
Q.toTensor` (the remaining combinatorial step, following from the general
basis-of-normal-tensors construction in #876), this result completes the Gap §1
heterogeneous sector comparison with the matching data gathered into a single argument. -/
theorem fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching
    {P Q : SectorDecomposition d}
    (M : SectorBasisMatching P Q)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (P.basis j) N))
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ ζ : Fin P.basisCount → ℂ,
      (∀ j, ζ j ≠ 0) ∧
      ∀ j : Fin P.basisCount,
        Finset.univ.val.map (P.weight j) =
          Finset.univ.val.map
            (fun q => ζ j * Q.weight (M.perm j) (Fin.cast (M.copies_eq j) q)) :=
  fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis
    P Q M.perm M.copies_eq M.basis_match_exists hLI hEqual

end MPSTensor
