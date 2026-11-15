/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.BalancedRegionalEnergy
import TNLean.MPS.AreaLaw.BalancedIntervalMergeClosure
import TNLean.MPS.AreaLaw.CanonicalIntervalSamplingOperation

/-!
# Energy estimates on the actual successful sampled root subtree

The actual sampled root and its listed descendants are the only spaces
assumed viable. The same targets and operator families then determine one
scalar energy function, with attained minima at used short leaves and
literal raw compressed updates at used long nodes. No viability or raw
update is asserted at overlapping intervals outside this root subtree.

This is a corrected conditional auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and line 1807.
**Scope restriction (fixed family and actual joint success):** The calibrated
target and word certificates precede the sampling choices; joint viability
is required only for the actual root subtree. The family is hard-clipped,
not identified with literal soft Generate, and no running time is asserted.
See `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- The actual sampled root subtree acquires scalar energy estimates from
its joint original-ground viability and the same fixed target/family
certificates. All used callbacks are derived from the physical soft word
energy theorem. No energy, minimum, callback or all-overlap viability is
supplied. Corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and line 1807. -/
theorem exists_canonical_interval_root_energy_assignment {L q ell D s : ℕ}
    (hq : 0 < q) (hell : 21 ≤ ell) (hD : 2 ≤ D)
    (hcount : 50 * ell ^ 2 ≤ D) (hsample : 1 ≤ s)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (T : LongIntervalIndex L (4 * ell) →
      Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (N : LongIntervalIndex L (4 * ell) → ℕ)
    (F : ∀ J : LongIntervalIndex L (4 * ell),
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let Delta := 1 / (200000 * (D : ℝ) ^ 12)
    let loss := Delta / (1 - (1 / 4 : ℝ)) ^ 2
    (∀ J : LongIntervalIndex L (4 * ell),
      Module.finrank ℂ (T J) = Module.finrank ℂ G ∧ Submodule.IsCloseTo tau G (T J) ∧
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        Submodule.IsViable (1 / 4 : ℝ) S ((T J).map
          (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) →
        let grow := ⨆ word : Fin 1 → Fin (N J),
          S.map ((List.ofFn (fun j ↦ F J (word j))).prod : _ →ₗ[ℂ] _)
        Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
          Submodule.IsViable loss grow ((T J).map
            (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) →
    ∀ (xi : ℝ) (U : IntervalSamplingChoices L q) (p0 r0 : ℕ), p0 ≤ r0 → r0 ≤ L →
    let hwidth : 1 ≤ 4 * ell := by omega
    let operation := canonicalIntervalSamplingOperation D s N F xi U
    (Submodule.IsViable (3 / 200 : ℝ)
      (balancedIntervalSpace operation (4 * ell) hwidth p0 r0)
      (G.map (Entropy.regionTensorCoordinates q (interval L p0 r0)).toLinearEquiv.toLinearMap) ∧
      ∀ I ∈ balancedIntervalMergeList (4 * ell) hwidth p0 r0,
        Submodule.IsViable (3 / 200 : ℝ)
          (balancedIntervalSpace operation (4 * ell) hwidth I.1 I.2)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L I.1 I.2)).toLinearEquiv.toLinearMap)) →
    ∃ estimate : ℕ → ℕ → ℝ,
      IsRegionalLowerEnergyEstimate h p0 r0 (49 / 16) (estimate p0 r0) ∧
      (r0 - p0 ≤ 4 * ell → IsRegionalLowerEnergyEstimate h p0 r0 0 (estimate p0 r0)) ∧
      ∀ J : LongIntervalIndex L (4 * ell),
        J.val ∈ balancedIntervalMergeList (4 * ell) hwidth p0 r0 →
        let l := J.val.1
        let r := J.val.2
        let k := l + (r - l) / 2
        let hpk : l ≤ k := by dsimp only [k]; omega
        let hkr : k ≤ r := by dsimp only [k]; omega
        IsRegionalLowerEnergyEstimate h l r (49 / 16) (estimate l r) ∧
        (k - l ≤ 4 * ell → IsRegionalLowerEnergyEstimate h l k 0 (estimate l k)) ∧
        (r - k ≤ 4 * ell → IsRegionalLowerEnergyEstimate h k r 0 (estimate k r)) ∧
        IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell) hq hpk hkr h (F J)
          (balancedIntervalSpace operation (4 * ell) hwidth l k)
          (balancedIntervalSpace operation (4 * ell) hwidth k r)
          (estimate l k) (estimate k r) (estimate l r) := by
  classical
  intro config H hH G a tau Delta loss htargets xi U p0 r0 hp0r0 hr0L
    hwidth operation hjoint
  let : Nonempty (Fin L → Fin q) := config
  let rootList := balancedIntervalMergeList (4 * ell) hwidth p0 r0
  apply exists_balanced_root_regional_energy_assignment hq hwidth h hs h0 h1 N F
    operation p0 r0 hp0r0 hr0L
  intro J hJ l r k hpk hkr
  have hlong : 4 * ell < r - l := J.property.2.2
  have hdescendant (K : ℕ × ℕ)
      (hK : K ∈ balancedIntervalMergeList (4 * ell) hwidth l k ∨
        K ∈ balancedIntervalMergeList (4 * ell) hwidth k r) : K ∈ rootList := by
    apply mem_balancedIntervalMergeList_trans (4 * ell) hwidth hJ
    rw [balancedIntervalMergeList, dite_eq_right (by omega : ¬r - l ≤ 4 * ell)]
    simp only [List.mem_append, List.mem_singleton]
    tauto
  have hviable (a b : ℕ)
      (hcontained : 4 * ell < b - a → (a, b) ∈ rootList) :
      Submodule.IsViable (3 / 200 : ℝ)
        (balancedIntervalSpace operation (4 * ell) hwidth a b)
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap) := by
    by_cases hshort : b - a ≤ 4 * ell
    · rw [balancedIntervalSpace_of_short operation hwidth hshort]
      exact Submodule.isViable_top _ (by norm_num) _
    · exact hjoint.2 (a, b) (hcontained (by omega))
  have hS1 := hviable l k (fun hchild ↦
    hdescendant (l, k) (Or.inl (self_mem_balancedIntervalMergeList _ hwidth l k hchild)))
  have hS2 := hviable k r (fun hchild ↦
    hdescendant (k, r) (Or.inr (self_mem_balancedIntervalMergeList _ hwidth k r hchild)))
  obtain ⟨hdimT, hGT, hword⟩ := htargets J
  exact exists_soft_word_node_energy_update hq (by omega : l ≤ l + ell)
    (by omega : l + ell ≤ r - ell) (Nat.sub_le _ _) J.property.2.1
    (by omega : l + ell - l ≤ 2 * ell) (by omega : r - (r - ell) ≤ 2 * ell)
    hell hD hcount hsample h hs h0 h1 (T J) (F J) hdimT hGT hword k hpk hkr
    (balancedIntervalSpace operation (4 * ell) hwidth l k)
    (balancedIntervalSpace operation (4 * ell) hwidth k r) hS1 hS2

end TNLean.MPS.AreaLaw.ALVV
