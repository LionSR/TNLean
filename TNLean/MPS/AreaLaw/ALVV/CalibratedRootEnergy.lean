/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.PhysicalDGRootEnergyAssignment
import TNLean.MPS.AreaLaw.CanonicalIntervalTreeSuccessEvent

/-!
# Root energy estimates from calibrated operator words

The original spectral minimum and a calibrated word family determine one
energy function on a successful canonical root subtree. This auxiliary
concerns the tree before final filtering and Ritz extraction.

Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631 and 1807.
**Scope restriction (calibrated hard-clipped family):** The family and its
word bounds are supplied, and viability is required on the actual root
subtree. This is an auxiliary to the physical construction, not literal
soft Generate; see `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A calibrated word family and joint viability on the actual canonical
root subtree determine one energy function, before any terminal refinement.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631 and 1807. -/
theorem exists_canonical_root_energy_of_calibrated_words {L q ell D s : ℕ}
    (hq : 0 < q) (hell : 21 ≤ ell) (hD2 : 2 ≤ D) (hsample : 1 ≤ s)
    (hDdef : D = (max q 50 * ell ^ 2) ^ (22 * ell))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (mu gamma : ℝ) (hgamma : 0 < gamma) (hwidth : 1 ≤ 4 * ell)
    (T : LongIntervalIndex L (4 * ell) →
      Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (N : LongIntervalIndex L (4 * ell) → ℕ)
    (F : ∀ J : LongIntervalIndex L (4 * ell),
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) :
    let H := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let tau := (3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)) ^ 2 / 1048576
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    (∀ J, Module.finrank ℂ (T J) = Module.finrank ℂ G ∧
      Submodule.IsCloseTo tau G (T J) ∧
      ∀ (power : ℕ)
        (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
        (delta : ℝ),
        Submodule.IsViable delta S ((T J).map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → delta < 1 →
        let grow := ⨆ word : Fin power → Fin (N J),
          S.map ((List.ofFn (fun j ↦ F J (word j))).prod : _ →ₗ[ℂ] _)
        Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
          Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
            ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) →
    ∀ (xi : ℝ) (seed : IntervalSamplingChoices L q),
      seed ∈ canonicalIntervalSamplingTreeGood D s hwidth N F xi G (3 / 200 : ℝ) 0 L →
    ∃ estimate : ℕ → ℕ → ℝ,
      ALVV.IsRegionalLowerEnergyEstimate h 0 L (49 / 16) (estimate 0 L) ∧
      (L - 0 ≤ (4 * ell) →
        ALVV.IsRegionalLowerEnergyEstimate h 0 L 0 (estimate 0 L)) ∧
      (∀ J : LongIntervalIndex L (4 * ell),
        J.val ∈ balancedIntervalMergeList (4 * ell) hwidth 0 L →
        let l := J.val.1
        let r := J.val.2
        let k := l + (r - l) / 2
        let hpk : l ≤ k := Nat.le_add_right l ((r - l) / 2)
        let hkr : k ≤ r :=
          (Nat.add_le_add_left (Nat.div_le_self (r - l) 2) l).trans_eq
            (Nat.add_sub_of_le J.property.1)
        ALVV.IsRegionalLowerEnergyEstimate h l r (49 / 16) (estimate l r) ∧
        (k - l ≤ (4 * ell) → ALVV.IsRegionalLowerEnergyEstimate h l k 0 (estimate l k)) ∧
        (r - k ≤ (4 * ell) → ALVV.IsRegionalLowerEnergyEstimate h k r 0 (estimate k r)) ∧
        ALVV.IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell)
          hq hpk hkr h (F J)
          (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
            (4 * ell) hwidth l k)
          (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
            (4 * ell) hwidth k r)
          (estimate l k) (estimate k r) (estimate l r)) := by
  classical
  intro H hH hmu hgap G tau Delta htargets xi seed hgood
  let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  have hmin : minEigenvalue hH = mu := by
    apply le_antisymm
    · obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
      simpa only [hj] using minEigenvalue_le hH j
    · apply Finset.le_min'
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with heq | hle
      · exact heq.ge
      · exact (le_add_of_nonneg_right hgamma.le).trans hle
  have hcount : 50 * ell ^ 2 ≤ D := by
    have hm : 50 ≤ max q 50 := Nat.le_max_right q 50
    have hell1 : 1 ≤ ell := (by decide : 1 ≤ 21).trans hell
    have he : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell hell1
    have hbase : 1 ≤ max q 50 * ell ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul ((by decide : 1 ≤ 50).trans hm) he
    calc
      50 * ell ^ 2 ≤ max q 50 * ell ^ 2 := Nat.mul_le_mul_right (ell ^ 2) hm
      _ ≤ (max q 50 * ell ^ 2) ^ (22 * ell) :=
        le_self_pow hbase (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hell1))
      _ = D := hDdef.symm
  let Gmin := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues
    (minEigenvalue hH)
  have htargetEq : Gmin = G :=
    congrArg (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues) hmin
  have henergyTargets (J : LongIntervalIndex L (4 * ell)) :
      Module.finrank ℂ (T J) = Module.finrank ℂ Gmin ∧
      Submodule.IsCloseTo tau Gmin (T J) ∧
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        Submodule.IsViable (1 / 4 : ℝ) S ((T J).map
          (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) →
        let grow := ⨆ word : Fin 1 → Fin (N J),
          S.map ((List.ofFn (fun j ↦ F J (word j))).prod : _ →ₗ[ℂ] _)
        Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
          Submodule.IsViable ((1 / (200000 * (D : ℝ) ^ 12)) / (1 - (1 / 4 : ℝ)) ^ 2)
            grow ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) := by
    obtain ⟨hdim, hGT, hwords⟩ := htargets J
    have hdimEq : Module.finrank ℂ Gmin = Module.finrank ℂ G :=
      congrArg (fun V : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) ↦
        Module.finrank ℂ V) htargetEq
    have hdimMin : Module.finrank ℂ (T J) = Module.finrank ℂ Gmin :=
      hdim.trans hdimEq.symm
    have hGTMin := Eq.mpr (congrArg (fun V ↦ Submodule.IsCloseTo tau V (T J))
      htargetEq) hGT
    refine ⟨hdimMin, hGTMin, ?_⟩
    intro S hS
    simpa only [pow_one, Delta, div_div] using hwords 1 S (1 / 4) hS (by norm_num)
  have hgoodMin : seed ∈
      canonicalIntervalSamplingTreeGood D s hwidth N F xi Gmin (3 / 200 : ℝ) 0 L :=
    Eq.mpr (congrArg (fun V ↦ seed ∈
      canonicalIntervalSamplingTreeGood D s hwidth N F xi V (3 / 200 : ℝ) 0 L)
      htargetEq) hgood
  obtain ⟨estimate, hrootEnergy, hshortEnergy, hnodesEnergy⟩ :=
    ALVV.exists_canonical_interval_root_energy_assignment
      hq hell hD2 hcount hsample h hsupp h0 h1 T N F henergyTargets
      xi seed 0 L (Nat.zero_le L) le_rfl hgoodMin
  exact ⟨estimate, hrootEnergy, hshortEnergy, hnodesEnergy⟩

end TNLean.MPS.AreaLaw
