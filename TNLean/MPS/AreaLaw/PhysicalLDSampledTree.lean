/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalLDTree

/-!
# The sampled merge tree for a low-density spectrum at its root

The root conclusion of the low-density sampled tree: the root is close to
the window shortened by `3w · clog₂ L` and consists of matrix product states.
This is the instance of the general tree theorem with that conclusion.

This supports ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878.

**Scope restriction (modified tree and fixed bandwidth):** The tree has full
leaves and one final trim per node, and the existence of successful samples is
asserted rather than a success probability; see
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The original nearest-neighbour Hamiltonian determines, on every long
interval, one low-density family of at most `D ^ 2` operators, chosen before
the tree, the window and the sampling size. For a buffer `w` with
`3w (clog₂ L + 1) ≤ etaLD` there is one reference bond `Dref` and, for every
failure parameter `beta`, an actual balanced tree whose long nodes are
literal sampled word images followed by collective trims at the threshold
`xi`. Every node `[p, r)` is `3/200`-viable for the original window
`etaLD - 3w · clog₂ (r - p)`, has dimension at most `count = D^6 s^3`, and is
spanned by at most `count` recorded vectors of controlled Schmidt rank.
The root is `3/200`-close to the window `etaLD - 3w · clog₂ L`, and each of
its vectors is a matrix product state of bond dimension
`10^6 Dref^2 (L + 1) count^2`. ALVV, arXiv:1602.08828v2, Theorem `t:alg2`,
lines 1869–1878, with Theorem `t:alg1`, lines 1777–1817, and the families
of Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_physical_ld_sampled_interval_tree (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      let mi := 4 * m
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
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
      let rG := Module.finrank ℂ (G etaLD)
      ∃ _hell : 21 ≤ ell,
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      let width := 4 * ell
      let hwidth : 1 ≤ width := by omega
      let target := fun p r : ℕ ↦ G (etaLD - 3 * w * Nat.clog 2 (r - p))
      ∃ (N : LongIntervalIndex L width → ℕ)
        (F : ∀ J : LongIntervalIndex L width,
          Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
            EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        (∀ J, N J ≤ D ^ 2) ∧
        (3 * w * ((Nat.clog 2 L : ℝ) + 1) ≤ etaLD →
        ∃ Dref : ℕ, 1 ≤ Dref ∧
        let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
        ∀ beta : ℝ, 0 < beta → beta < 1 →
        let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
        let s := Nat.ceil (4096 * (rG : ℝ) * A)
        let count := D ^ 6 * s ^ 3
        (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧
        ∃ operation : IntervalMergeOperation L q,
          (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
            k = J.val.1 + (J.val.2 - J.val.1) / 2 →
            ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
              (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
            Submodule.IsViable (3 / 200 : ℝ) S1
              ((target J.val.1 k).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
            Submodule.IsViable (3 / 200 : ℝ) S2
              ((target k J.val.2).map (Entropy.regionTensorCoordinates q
                (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
            Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
            ∃ U : Matrix.unitaryGroup
              (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
                J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
              operation J.val.1 k J.val.2 hpk hkr S1 S2 =
                sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
                  (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
          (∀ p r : ℕ, p ≤ r → r ≤ L →
            let S := balancedIntervalSpace operation width hwidth p r
            Submodule.IsViable (3 / 200 : ℝ) S
              ((target p r).map (Entropy.regionTensorCoordinates q
                (interval L p r)).toLinearEquiv.toLinearMap) ∧
            Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S) ∧
          let S0 := balancedIntervalSpace operation width hwidth 0 L
          Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0)
            (G (etaLD - 3 * w * Nat.clog 2 L)) ∧
          ∀ v ∈ S0, IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
            (fullIntervalRead L q v)) :=
  exists_physical_ld_sampled_interval_tree_of_clause etaLD hLD
    (fun L q m w hq h h0 count Dref S0 ↦
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0)
          (G (etaLD - 3 * w * Nat.clog 2 L)) ∧
        ∀ v ∈ S0, IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
          (fullIntervalRead L q v))
    (by
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hclose _ hMPS
      exact ⟨hclose, hMPS⟩)

end TNLean.MPS.AreaLaw
