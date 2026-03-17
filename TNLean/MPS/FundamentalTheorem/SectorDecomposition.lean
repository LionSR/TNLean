/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.BNT.Basic
import TNLean.Algebra.ScalarPowerSumIdentity

import Mathlib.Data.Fintype.BigOperators

/-!
# Sector decomposition with per-copy weights for the equal-case fundamental theorem

This file formalizes the **multiplicity layer** of the MPS fundamental theorem.

## Mathematical background

In the canonical form for matrix product states, the total tensor decomposes into a weighted
block-diagonal sum over a *basis of normal tensors* (BNT) `A_j`.  In the original treatment
of [PGVWC07, §III], each distinct BNT block appears exactly once.  The review [CPSV21, §IV]
and the detailed analysis in [CPSV17, §2.3 + Appendix A] refine this by tracking
**multiplicities**: each basis block `A_j` may appear `r_j` times with distinct sector weights
`μ_{j,q}` (`q = 1, …, r_j`), so the MPV coefficient of `A_j` at system size `N` is the
power sum `∑_q (μ_{j,q})^N`.

The equal-case corollary of the fundamental theorem ([CPSV21, Corollary IV.5] /
[CPSV17, §2.3]) compares two such decompositions.  After matching basis blocks via the
proportional-case theorem ([CPSV17, Theorem 4.4]), one obtains power-sum identities
`∑_q (μ_{j,q}^A)^k = ∑_q (μ_{j,q}^B)^k` for each `j` and all positive `k`.  The paper's
Lemma `Lem:app_simple` (Newton's identities on symmetric functions) then recovers equality
of the weight multisets.

## Relationship to `IsCanonicalFormBNT`

The existing `IsCanonicalFormBNT` predicate models the **merged case** where each basis block
appears once (i.e., all `r_j = 1`).  This file's `SectorWeightData` / `SectorDecomposition`
layer faithfully tracks the per-copy multiplicity structure, complementing the merged
interface without modifying it.

## Related results in other formalizations

The Newton–Girard / power-sum recovery step is a classical result; our
`Matrix.sum_pow_eq_implies_multiset_eq` (in `ScalarPowerSumIdentity.lean`) formalizes it via
the companion matrix approach.  The extrapolation lemma (`geom_sum_eventually_zero`) — that
an eventually-vanishing linear combination of geometric sequences is identically zero — is
standard but does not appear to have a direct Mathlib counterpart; we prove it by induction
with a telescoping argument.

## Main definitions

* `SectorWeightData`: multiplicities `copies j = r_j`, sector weights `weight j q = μ_{j,q}`,
  positivity of the multiplicities, and nonvanishing of all sector weights.
* `SectorDecomposition`: a basis family together with the sector weight data.
* `SectorDecomposition.toTensor`: the flattened block-diagonal tensor obtained by reusing
  `toTensorFromBlocks` after flattening `(j, q)` to a single block index.
* `SectorDecomposition.coeff`: the coefficient `coeff N j = ∑_q (μ_{j,q})^N`.

## Main theorems

* `SectorDecomposition.mpv_toTensor_eq_sum_coeff`: the decomposition formula
  `mpv(total) = ∑_j coeff(N,j) * mpv(A_j)` ([CPSV21, Eq. (IV.26)]).

* `SectorWeightData.coeff_eventually_eq_of_sameMPV`: equal MPVs + BNT linear independence →
  eventual coefficient agreement.

* `SectorWeightData.weight_multiset_eq_of_copies_eq_of_coeff_eq`: equal multiplicities +
  equal power sums for all positive k → equal weight multisets
  (Newton–Girard / [CPSV17, Lemma Lem:app_simple]).

* `SectorWeightData.weight_multiset_eq_of_sameMPV_bnt`: combined equal-case corollary
  ([CPSV21, Corollary IV.5]), connecting BNT linear independence and equal MPVs to sector
  weight multiset equality.

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

/--
Sector multiplicity and weight data over a family of basis blocks.

`copies j` is the multiplicity `r_j` of basis block `j`, while `weight j q` is the sector
weight `μ_{j,q}` attached to the `q`-th copy.
-/
structure SectorWeightData (g : ℕ) where
  /-- The multiplicity `r_j` of the basis block `j`. -/
  copies : Fin g → ℕ
  /-- Each basis block occurs at least once. -/
  copies_pos : ∀ j, 0 < copies j
  /-- The sector weight `μ_{j,q}` attached to the `q`-th copy of basis block `j`. -/
  weight : (j : Fin g) → Fin (copies j) → ℂ
  /-- All sector weights are nonzero. -/
  weight_ne_zero : ∀ j q, weight j q ≠ 0

namespace SectorWeightData

variable {g : ℕ}

/-- The coefficient `coeff N j = ∑_q (μ_{j,q})^N`. -/
noncomputable def coeff (S : SectorWeightData g) (N : ℕ) (j : Fin g) : ℂ :=
  ∑ q : Fin (S.copies j), (S.weight j q) ^ N

end SectorWeightData

/--
A sector decomposition: a basis of normal tensors together with per-copy sector weight data.

This bundles the basis-block family `A_j` with the multiplicity and weight structure
`SectorWeightData`.
-/
structure SectorDecomposition (d : ℕ) where
  /-- Number of basis blocks `A_j`. -/
  basisCount : ℕ
  /-- Bond dimension of each basis block. -/
  basisDim : Fin basisCount → ℕ
  /-- The basis-block family `A_j`. -/
  basis : (j : Fin basisCount) → MPSTensor d (basisDim j)
  /-- Multiplicities and sector weights lying over the basis blocks. -/
  sectors : SectorWeightData basisCount

namespace SectorDecomposition

/-- The multiplicity `r_j` of the basis block `j`. -/
abbrev copies (P : SectorDecomposition d) : Fin P.basisCount → ℕ :=
  P.sectors.copies

/-- Positivity of the multiplicities. -/
abbrev copies_pos (P : SectorDecomposition d) : ∀ j, 0 < P.copies j :=
  P.sectors.copies_pos

/-- The sector weight `μ_{j,q}`. -/
abbrev weight (P : SectorDecomposition d) : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ :=
  P.sectors.weight

/-- Nonvanishing of the sector weights. -/
abbrev weight_ne_zero (P : SectorDecomposition d) : ∀ j q, P.weight j q ≠ 0 :=
  P.sectors.weight_ne_zero

/-- The coefficient `coeff N j = ∑_q (μ_{j,q})^N`. -/
noncomputable def coeff (P : SectorDecomposition d) (N : ℕ) (j : Fin P.basisCount) : ℂ :=
  P.sectors.coeff N j

/-- Total number of sectors after flattening the pairs `(j, q)`. -/
def totalCopies (P : SectorDecomposition d) : ℕ :=
  ∑ j : Fin P.basisCount, P.copies j

/-- Flatten the sector index `(j, q)` to a single `Fin totalCopies` index. -/
noncomputable def flatIndexEquiv (P : SectorDecomposition d) :
    ((j : Fin P.basisCount) × Fin (P.copies j)) ≃ Fin P.totalCopies :=
  finSigmaFinEquiv

/-- Bond dimension of the flattened sector block indexed by `s`. -/
noncomputable def flatDim (P : SectorDecomposition d) : Fin P.totalCopies → ℕ :=
  fun s ↦ P.basisDim (P.flatIndexEquiv.symm s).1

/-- Weight of the flattened sector block indexed by `s`. -/
noncomputable def flatWeight (P : SectorDecomposition d) : Fin P.totalCopies → ℂ :=
  fun s ↦ P.weight (P.flatIndexEquiv.symm s).1 (P.flatIndexEquiv.symm s).2

/-- Basis tensor carried by the flattened sector block indexed by `s`. -/
noncomputable def flatBasis (P : SectorDecomposition d) :
    (s : Fin P.totalCopies) → MPSTensor d (P.flatDim s) :=
  fun s ↦ P.basis (P.flatIndexEquiv.symm s).1

/-- Total bond dimension of the flattened block-diagonal tensor. -/
noncomputable def totalDim (P : SectorDecomposition d) : ℕ :=
  ∑ s : Fin P.totalCopies, P.flatDim s

/--
The total tensor, obtained by flattening `(j, q)` and applying `toTensorFromBlocks`.
-/
noncomputable def toTensor (P : SectorDecomposition d) : MPSTensor d P.totalDim :=
  toTensorFromBlocks (d := d) (μ := P.flatWeight) P.flatBasis

/-- `toTensor` is `toTensorFromBlocks` for the flattened sector data. -/
theorem toTensor_eq_toTensorFromBlocks_flat (P : SectorDecomposition d) :
    P.toTensor = toTensorFromBlocks (d := d) (μ := P.flatWeight) P.flatBasis :=
  rfl

/-- Every flattened sector weight is nonzero. -/
theorem flatWeight_ne_zero (P : SectorDecomposition d) (s : Fin P.totalCopies) :
    P.flatWeight s ≠ 0 := by
  simpa [SectorDecomposition.flatWeight] using
    P.weight_ne_zero (P.flatIndexEquiv.symm s).1 (P.flatIndexEquiv.symm s).2

/--
Intermediate expansion: first sum over the basis index `j`, then over its copies `q`.
-/
theorem mpv_toTensor_eq_sum_sectors (P : SectorDecomposition d) {N : ℕ}
    (σ : Fin N → Fin d) :
    mpv P.toTensor σ =
      ∑ j : Fin P.basisCount, ∑ q : Fin (P.copies j),
        (P.weight j q) ^ N * mpv (P.basis j) σ := by
  classical
  let e : ((j : Fin P.basisCount) × Fin (P.copies j)) ≃ Fin P.totalCopies :=
    P.flatIndexEquiv
  calc
    mpv P.toTensor σ
      = ∑ s : Fin P.totalCopies, (P.flatWeight s) ^ N * mpv (P.flatBasis s) σ := by
          simpa [SectorDecomposition.toTensor, smul_eq_mul] using
            (mpv_toTensorFromBlocks_eq_sum (d := d) (μ := P.flatWeight)
              (A := P.flatBasis) (σ := σ))
    _ = ∑ x : ((j : Fin P.basisCount) × Fin (P.copies j)),
          (P.weight x.1 x.2) ^ N * mpv (P.basis x.1) σ := by
          calc
            ∑ s : Fin P.totalCopies, (P.flatWeight s) ^ N * mpv (P.flatBasis s) σ
              = ∑ s : Fin P.totalCopies,
                  (P.weight (e.symm s).1 (e.symm s).2) ^ N *
                    mpv (P.basis (e.symm s).1) σ := by
                      simp [SectorDecomposition.flatWeight, SectorDecomposition.flatBasis, e]
            _ = ∑ x : ((j : Fin P.basisCount) × Fin (P.copies j)),
                  (P.weight x.1 x.2) ^ N * mpv (P.basis x.1) σ := by
                      let f : ((j : Fin P.basisCount) × Fin (P.copies j)) → ℂ :=
                        fun x ↦ (P.weight x.1 x.2) ^ N * mpv (P.basis x.1) σ
                      let g : Fin P.totalCopies → ℂ :=
                        fun s ↦ (P.weight (e.symm s).1 (e.symm s).2) ^ N *
                          mpv (P.basis (e.symm s).1) σ
                      have hfg : ∀ x, f x = g (e x) := by
                        intro x
                        simpa [f, g] using (congrArg
                          (fun y : ((j : Fin P.basisCount) × Fin (P.copies j)) ↦
                            (P.weight y.1 y.2) ^ N * mpv (P.basis y.1) σ)
                          (e.symm_apply_apply x)).symm
                      simpa [f, g] using (Fintype.sum_equiv e f g hfg).symm
    _ = ∑ j : Fin P.basisCount, ∑ q : Fin (P.copies j),
          (P.weight j q) ^ N * mpv (P.basis j) σ := by
          simpa using (Fintype.sum_sigma' fun j q ↦
            (P.weight j q) ^ N * mpv (P.basis j) σ)

/--
Decomposition formula: the MPV of the assembled tensor expands with coefficients
`coeff N j = ∑_q (μ_{j,q})^N` against the basis MPVs.
-/
theorem mpv_toTensor_eq_sum_coeff (P : SectorDecomposition d) {N : ℕ}
    (σ : Fin N → Fin d) :
    mpv P.toTensor σ =
      ∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ := by
  calc
    mpv P.toTensor σ
      = ∑ j : Fin P.basisCount, ∑ q : Fin (P.copies j),
          (P.weight j q) ^ N * mpv (P.basis j) σ :=
        P.mpv_toTensor_eq_sum_sectors σ
    _ = ∑ j : Fin P.basisCount,
          (∑ q : Fin (P.copies j), (P.weight j q) ^ N) * mpv (P.basis j) σ := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact (Finset.sum_mul Finset.univ
            (fun q : Fin (P.copies j) ↦ (P.weight j q) ^ N)
            (mpv (P.basis j) σ)).symm
    _ = ∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ := by
          simp [SectorDecomposition.coeff, SectorWeightData.coeff]

end SectorDecomposition

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
  obtain ⟨N0, hN0⟩ := coeff_eventually_eq_of_sameMPV basis S T hLI hSame
  have hAll := eventually_coeff_eq_implies_all_pos_eq S T hCopies hN0
  exact weight_multiset_eq_of_copies_eq_of_coeff_eq S T hCopies hAll

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
  have hP := (SectorDecomposition.mk g dim basis S).mpv_toTensor_eq_sum_coeff σ (N := N)
  have hQ := (SectorDecomposition.mk g dim basis T).mpv_toTensor_eq_sum_coeff σ (N := N)
  -- hP and hQ unfold to the coefficient expansion; the goal is definitionally equivalent
  calc ∑ j, S.coeff N j * mpv (basis j) σ
      = mpv (SectorDecomposition.mk g dim basis S).toTensor σ := hP.symm
    _ = mpv (SectorDecomposition.mk g dim basis T).toTensor σ := hEqual N σ
    _ = ∑ j, T.coeff N j * mpv (basis j) σ := hQ

end MPSTensor
