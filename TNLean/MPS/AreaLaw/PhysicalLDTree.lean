/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AdjacentIntervalMerge
import TNLean.MPS.AreaLaw.BalancedIntervalTree
import TNLean.MPS.AreaLaw.DyadicIntervalLowDensityFamily
import TNLean.MPS.AreaLaw.FullIntervalViability

/-!
# A merge tree of viable spaces for a low-density spectrum

The original nearest-neighbour Hamiltonian determines one improving family
on every interval, before the tree and every window. A balanced recursion
keeps the full local space at short leaves. At a long node it tensors the
two child spaces and takes the images under the family of that node.
The window shrinks by the buffer `3 * w` at each level: a node whose length
is at most `4 * ell * 2 ^ k` is `3/200`-viable for the original low-energy
window of width `etaLD - 3 * w * k` above the ground energy. The root is
therefore close to the window shortened by `3 * w * clog₂ L`.

This is the per-level viability induction of ALVV, arXiv:1602.08828v2,
Theorem `t:alg2`, lines 1869–1878, built from the improving families of
Theorem `t:aisgapless`, lines 1027–1041, under Assumption (LD),
lines 281–284. The source buffer `w = μ / (3 log n)` and the condition
`η₁ ≥ 2μ / log n` correspond to the hypothesis `3 * w * (k + 1) ≤ etaLD`.

**Scope restriction (merge tree without sampling or trimming):** Long nodes
retain the full family image of the merged space. No random sampling,
collective trimming, dimension bound, final refinement or MPS bound of the
nodes is asserted, and the hidden constant depends on the fixed bandwidth
`etaLD`; the local dimension satisfies `q ≥ 2`. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

set_option maxHeartbeats 800000 in
-- The interval families retain dependent physical configuration coordinates.
/-- The original nearest-neighbour Hamiltonian determines one family of
`D ^ 2` operators on every interval such that the balanced merge tree,
whose long nodes take the family images of the merged child spaces, is
`3/200`-viable at every node for the original low-energy window shortened
by `3 * w` per level. A node of length at most `4 * ell * 2 ^ k` has the
window `etaLD - 3 * w * k`, provided `3 * w * (k + 1) ≤ etaLD`; the root
space is then close to the window `etaLD - 3 * w * clog₂ L`. The constant
precedes every physical datum. ALVV, arXiv:1602.08828v2, Theorem `t:alg2`,
lines 1869–1878, with the families of Theorem `t:aisgapless`,
lines 1027–1041, and the fixed bandwidth of Assumption (LD), lines 281–284. -/
theorem exists_physical_ld_interval_tree (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      let g := min w 1
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      ∃ _hell : 21 ≤ ell,
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      let width := 4 * ell
      let hwidth : 1 ≤ width := by omega
      ∃ A : ∀ p r : ℕ, Fin (D ^ 2) → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L p r → Fin q),
      let operation : IntervalMergeOperation L q := fun p k r hpk hkr S1 S2 ↦
        ⨆ i : Fin (D ^ 2),
          (adjacentIntervalMerge L q p k r hpk hkr S1 S2).map (A p r i).toLinearMap
      (∀ k p r : ℕ, p ≤ r → r ≤ L → r - p ≤ width * 2 ^ k →
        3 * w * ((k : ℝ) + 1) ≤ etaLD →
        Submodule.IsViable (3 / 200 : ℝ) (balancedIntervalSpace operation width hwidth p r)
          ((G (etaLD - 3 * w * k)).map
            (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)) ∧
      (3 * w * ((Nat.clog 2 L : ℝ) + 1) ≤ etaLD →
        Submodule.IsCloseTo (3 / 200 : ℝ)
          (nativeFullIntervalSpace L q (balancedIntervalSpace operation width hwidth 0 L))
          (G (etaLD - 3 * w * Nat.clog 2 L))) := by
  classical
  obtain ⟨C, hC, hCeta, hfamily⟩ :=
    exists_fixed_bandwidth_interval_dyadic_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m w hq hqm hw g u ell D h hs h0 h1 config H hRaw G
  let : Nonempty (Fin L → Fin q) := config
  have hm0 : m * 2 ^ 0 = m := by rw [pow_zero, mul_one]
  have hfamily' (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) := by
    have hfam := hfamily L q m p r 0 w hq hqm hpr hrL hw h hs h0 h1
    rw [hm0] at hfam
    exact hfam
  obtain ⟨hell, hlogD, -⟩ := hfamily' 0 0 le_rfl (Nat.zero_le L)
  refine ⟨hell, hlogD, ?_⟩
  intro width hwidth
  have hD : (1 : ℝ) ≤ (D : ℝ) ^ 12 := by
    have hbase : 1 ≤ m * ell ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (pow_ne_zero 2 (by omega)))
    exact one_le_pow₀ (by exact_mod_cast Nat.one_le_pow _ _ hbase)
  -- The interval families, transported to the region coordinates of the tree.
  have hlocal : ∀ p r : ℕ, ∃ A : Fin (D ^ 2) →
      EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L p r → Fin q),
      p ≤ r → r ≤ L → ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
      ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
        Submodule.IsCloseTo (1 / 200) (G eta) Thi ∧
        Submodule.IsCloseTo (1 / 200) Tlo (G (eta - 3 * w)) ∧
        0 < Delta ∧ Delta ≤ 1 / 100000 ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (delta : ℝ),
          Submodule.IsViable delta S (Thi.map
            (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) →
          delta < 1 →
          Submodule.IsViable (Delta / (1 - delta) ^ 2)
            (⨆ i : Fin (D ^ 2), S.map (A i).toLinearMap) (Tlo.map
              (Entropy.regionTensorCoordinates q
                (interval L p r)).toLinearEquiv.toLinearMap) := by
    intro p r
    by_cases hJ : p ≤ r ∧ r ≤ L
    · obtain ⟨-, -, A, hA⟩ := hfamily' p r hJ.1 hJ.2
      refine ⟨A, fun _ _ eta hbuffer heta ↦ ?_⟩
      obtain ⟨Tlo, Thi, Delta, -, hupper, hlower, hDelta, htrade, himprove⟩ :=
        hA eta hbuffer heta
      refine ⟨Tlo, Thi, Delta, hupper.of_le (by norm_num), ?_, hDelta, ?_, ?_⟩
      · have hcut : minEigenvalue hRaw + eta - 3 * w = minEigenvalue hRaw + (eta - 3 * w) := by
          ring
        simpa only [G, hcut] using hlower.of_le (by norm_num)
      · nlinarith only [hD, hDelta, htrade]
      · intro S delta hS hdelta
        rw [Entropy.regionTensorCoordinates_eq_exteriorFirst] at hS ⊢
        exact (himprove S delta hS hdelta).2
    · exact ⟨0, fun hpr hrL ↦ absurd ⟨hpr, hrL⟩ hJ⟩
  choose A hA using hlocal
  refine ⟨A, ?_⟩
  intro operation
  let P := fun (p r : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) ↦
    ∀ k : ℕ, r - p ≤ width * 2 ^ k → 3 * w * ((k : ℝ) + 1) ≤ etaLD →
      Submodule.IsViable (3 / 200 : ℝ) S
        ((G (etaLD - 3 * w * k)).map
          (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)
  have htree : ∀ p r : ℕ, p ≤ r → r ≤ L →
      P p r (balancedIntervalSpace operation width hwidth p r) := by
    apply balancedIntervalSpace_invariant_of_midpoint operation hwidth P
    · intro p r _hpr _hrL _hshort k _hk _hkw
      exact Submodule.isViable_top _ (by norm_num) _
    · intro p r hpk hkr hrL hlong S1 S2 hS1 hS2 k hk hkw
      cases k with
      | zero =>
        rw [pow_zero, mul_one] at hk
        omega
      | succ k =>
        have hk2 : r - p ≤ 2 * (width * 2 ^ k) := by
          rw [pow_succ] at hk
          linarith only [hk]
        have hkw' : 3 * w * ((k : ℝ) + 1 + 1) ≤ etaLD := by
          simpa only [Nat.cast_succ] using hkw
        have hkwc : 3 * w * ((k : ℝ) + 1) ≤ etaLD := by
          nlinarith only [hkw', hw]
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have h1 := hS1 k (by generalize width * 2 ^ k = X at hk2 ⊢; omega) hkwc
        have h2 := hS2 k (by generalize width * 2 ^ k = X at hk2 ⊢; omega) hkwc
        obtain ⟨Tlo, Thi, Delta, hupper, hlower, hDelta, hDelta1, himprove⟩ :=
          hA p r (hpk.trans hkr) hrL (etaLD - 3 * w * k)
            (by nlinarith only [hkw']) (by nlinarith only [hw, hk0])
        let RC := Entropy.regionTensorCoordinates q (interval L p r)
        have hmerge := isViable_adjacentIntervalMerge hpk hkr (G (etaLD - 3 * w * k))
          S1 S2 h1 h2
        have hupperMap : Submodule.IsCloseTo (1 / 200)
            ((G (etaLD - 3 * w * k)).map RC.toLinearEquiv.toLinearMap)
            (Thi.map RC.toLinearEquiv.toLinearMap) :=
          (Submodule.isCloseTo_map_iff RC).mpr hupper
        have hmergeHi : Submodule.IsViable (2 * ((3 / 200 + 3 / 200) + 1 / 200))
            (adjacentIntervalMerge L q p (p + (r - p) / 2) r hpk hkr S1 S2)
            (Thi.map RC.toLinearEquiv.toLinearMap) :=
          Submodule.IsCloseTo.trans hmerge hupperMap (by norm_num)
        have hgrow := himprove _ _ hmergeHi (by norm_num)
        have hlowerMap : Submodule.IsCloseTo (1 / 200)
            (Tlo.map RC.toLinearEquiv.toLinearMap)
            ((G (etaLD - 3 * w * k - 3 * w)).map RC.toLinearEquiv.toLinearMap) :=
          (Submodule.isCloseTo_map_iff RC).mpr hlower
        have hfinal := Submodule.IsCloseTo.trans hgrow hlowerMap (by positivity)
        have hcut : etaLD - 3 * w * k - 3 * w = etaLD - 3 * w * ((k + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hcut] at hfinal
        have hsmall : Delta / (1 - 2 * ((3 / 200 + 3 / 200) + 1 / 200 : ℝ)) ^ 2 ≤ 1 / 400 := by
          rw [div_le_iff₀ (by norm_num)]
          nlinarith only [hDelta1]
        exact Submodule.IsCloseTo.of_le hfinal (by linarith only [hsmall])
  refine ⟨fun k p r hpr hrL hk hkw ↦ htree p r hpr hrL k hk hkw, ?_⟩
  intro hroot
  have hlen : L - 0 ≤ width * 2 ^ Nat.clog 2 L := by
    have hpow := Nat.le_pow_clog (by norm_num : 1 < 2) L
    have hmul : 2 ^ Nat.clog 2 L ≤ width * 2 ^ Nat.clog 2 L :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  exact (isViable_fullInterval_iff_isCloseTo _ _).mp
    (htree 0 L (Nat.zero_le L) le_rfl (Nat.clog 2 L) hlen hroot)

end TNLean.MPS.AreaLaw
