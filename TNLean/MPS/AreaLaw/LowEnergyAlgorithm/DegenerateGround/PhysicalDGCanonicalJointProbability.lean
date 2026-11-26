/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalIntervalSamplingTree
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IndependentIntervalProbability
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGCanonicalParentFailure
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IntervalSamplingChoices
import QICLean.Analysis.Parameter.ViableNodeParameters

/-!
# Joint success for the actual physical sampled tree

One collection of physical clipped targets and improving families is
chosen before the radius, all children and the global product Haar seed.
The existing balanced recursion, with literal interleaved collective
trimming at every parent, is viable simultaneously at its root and all
of its internal intervals except on a set of measure at most
(L-1)/(L+1)^2. Its size bounds hold for every seed, including failures.
Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817.

**Scope restriction (block leaves, fixed failure scale and capped gap):**
The leaves have at most four window lengths; the estimate retains
min(gamma,1), the hard-clipped family and the fixed scale (L+1)^(-2).
Only descendants of the specified full-chain root are asserted viable.
Runtime and the soft-Hamiltonian energy procedure are separate results.
See `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (assignment and integer rounds):** The construction uses the
current-space assignment and larger integer round count documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_physical_dg_canonical_interval_sampling_data`: one physical family for
  the actual sampled tree and every history.
-/

open ManyBody (interval)
open MeasureTheory

section PhysicalDGCanonicalSamplingData

/-!
## One physical family for the actual sampled tree and every history

The physical canonical-parent construction chooses one common reference
and a target and operator family for each long interval before all radii,
children and global seeds. The same data give unconditional dimensions and
recorded ranks for every space of the existing balanced recursion and the
true local failure bound. Source: ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817.

**Scope restriction (block leaves, fixed failure scale and capped gap):**
The width is four window lengths, the failure scale is (L+1)^(-2), and
the quantitative dependence retains min(gamma,1). The family acts through
the actual hard-clipped Hamiltonian. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (assignment and integer rounds):** Every parent uses the
literal current-space iteration and larger integer round count documented
in `docs/paper-gaps/alvv16_approximation_parameters.tex`. Joint tree
probability and runtime remain separate assertions.
-/

open scoped TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The original chain chooses one collection of actual targets and
families before all global seeds. Its actual sampled tree has the common
size bounds on every history, while each long parent retains its true
uniform failure estimate under viable bounded children. -/
theorem exists_physical_dg_canonical_interval_sampling_data :
    ∃ Ctail C Kref : ℝ, 21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let m := max q 50
    let w := 1 + Real.log (rG : ℝ) + 2 * Real.log ((L : ℝ) + 1)
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g) + Real.log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let s := Nat.ceil (4096 * (rG : ℝ) * (Real.log (D : ℝ) + w))
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let epsilon := 200 * tau
    let t := Ctail * (1 + Real.log (1 / g) + Real.log (1 / tau))
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 0 < a ∧ a ≤ 1 / 100 ∧
      0 < epsilon ∧ epsilon ≤ 1 ∧ 21 ≤ t ∧
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤ epsilon * g / 1000000 ∧
      (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let bref := 16 + Real.log (1 / g) + Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / tau)
    ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      (∀ z ∈ U, IsOpenMPS L q (rG ^ 2 * B) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * B
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width,
    ∃ (T : LongIntervalIndex L width →
        Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      (∀ J, Module.finrank ℂ (T J) = rG ∧
        Submodule.IsCloseTo tau (T J) G ∧ Submodule.IsCloseTo tau G (T J) ∧
        Submodule.IsCloseTo (4 * tau) (T J) U ∧
        Submodule.IsCloseTo (4 * tau) U (T J) ∧
        (∀ (power : ℕ)
          (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))) (delta : ℝ),
          Submodule.IsViable delta S
            ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ w : Fin power → Fin (N J),
            S.map ((List.ofFn (fun j ↦ F J (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
            Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
              ((T J).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap))) ∧
      ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
      (∀ (seed : IntervalSamplingChoices L q) (p r : ℕ), p ≤ r → r ≤ L →
        let S := balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
          width hwidth p r
        Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S) ∧
      ∀ (J : LongIntervalIndex L width) (k : ℕ)
        (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      Module.finrank ℂ S1 ≤ D ^ 6 * s ^ 3 →
      Module.finrank ℂ S2 ≤ D ^ 6 * s ^ 3 →
      Submodule.IsViable (3 / 200 : ℝ) S1
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        (G.map (Entropy.regionTensorCoordinates q
          (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
      let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2
      let beta : ℝ := 1 / ((L : ℝ) + 1) ^ 2
      let Bad := {U : Matrix.rankUnitaryProduct
          (Fintype.card (interval L J.val.1 J.val.2 → Fin q)) |
        ¬ Submodule.IsViable (3 / 200 : ℝ)
          (canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s (F J) xi W U)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)}
      MeasurableSet Bad ∧
        Matrix.rankUnitaryHaar (Fintype.card (interval L J.val.1 J.val.2 → Fin q)) Bad ≤
          ENNReal.ofReal beta := by
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfamily⟩ :=
    exists_physical_dg_canonical_interval_parent_failure
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Uref, hdimU, hUMPS, hxiMax, hinterval⟩ :=
    hfamily L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  change 21 ≤ ell at hell
  change 2 ≤ D at hD
  change 1 ≤ s at hs
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, Uref, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  have hwidth : 1 ≤ width := by dsimp only [width]; omega
  refine ⟨hwidth, ?_⟩
  have hfamilies := fun J : LongIntervalIndex L width ↦
    hinterval J.val.1 J.val.2 J.property.1 J.property.2.1 J.property.2.2
  choose T N F hN hdimT hTG hGT hTU hUT hwords hEvents using hfamilies
  clear hfamily hinterval
  refine ⟨T, N, F, hN, ?_, ?_⟩
  · intro J
    exact ⟨hdimT J, hTG J, hGT J, hTU J, hUT J, hwords J⟩
  · intro xi hxi hxiMax
    have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
    have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr hG
    have hq : 1 ≤ q := (by decide : 1 ≤ 2).trans
      (hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu))
    have hDref : 1 ≤ Dref := by
      simpa only [Dref, one_mul] using Nat.mul_le_mul (Nat.one_le_pow 2 rG hrG) hB
    have hDrefR : (1 : ℝ) ≤ Dref := by exact_mod_cast hDref
    have hroot : 1 ≤ Real.sqrt ((L : ℝ) + 1) :=
      Real.one_le_sqrt.mpr (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
    have hden : 1 ≤ 256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1) :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hDrefR) hroot
    have hxiMax1 : xiMax ≤ 1 := by
      dsimp only [xiMax]
      apply (div_le_one (lt_of_lt_of_le zero_lt_one hden)).mpr
      exact haSmall.trans ((by norm_num : (1 / 100 : ℝ) ≤ 1).trans hden)
    have hleaf : q ^ width ≤ D ^ 6 * s ^ 3 :=
      Nat.viable_tree_leaf_count_le (Nat.le_max_left q 50) (by omega) (by omega) hs
    refine ⟨?_, ?_⟩
    · intro seed p r hpr hrL
      exact canonicalIntervalSamplingTree_profile hwidth hq hD hs N F hN hxi
        (hxiMax.trans hxiMax1) hleaf seed p r hpr hrL
    · intro J k hpk hkr S1 S2 hd1 hd2 hS1 hS2
      exact (hEvents J xi hxi hxiMax).2 k hpk hkr S1 S2 hd1 hd2 hS1 hS2

end TNLean.MPS.AreaLaw

end PhysicalDGCanonicalSamplingData

section PhysicalDGCanonicalJointProbability

open scoped ENNReal TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Actual physical targets and families precede all global seeds. For
every admissible common radius, their literal sampled tree has unconditional
size bounds and a Borel joint viability event for the original full ground
space. Its failure probability is at most (L-1)/(L+1)^2. The retained
reference and word certificates are those of the same single physical
construction. Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1777–1817. -/
theorem exists_physical_dg_canonical_tree_joint_probability :
    ∃ Ctail C Kref : ℝ, 21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let m := max q 50
    let w := 1 + Real.log (rG : ℝ) + 2 * Real.log ((L : ℝ) + 1)
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g) + Real.log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let s := Nat.ceil (4096 * (rG : ℝ) * (Real.log (D : ℝ) + w))
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let epsilon := 200 * tau
    let t := Ctail * (1 + Real.log (1 / g) + Real.log (1 / tau))
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 0 < a ∧ a ≤ 1 / 100 ∧
      0 < epsilon ∧ epsilon ≤ 1 ∧ 21 ≤ t ∧
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤ epsilon * g / 1000000 ∧
      (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let bref := 16 + Real.log (1 / g) + Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / tau)
    ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      (∀ z ∈ U, IsOpenMPS L q (rG ^ 2 * B) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * B
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width,
    ∃ (T : LongIntervalIndex L width →
        Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      (∀ J, Module.finrank ℂ (T J) = rG ∧
        Submodule.IsCloseTo tau (T J) G ∧ Submodule.IsCloseTo tau G (T J) ∧
        Submodule.IsCloseTo (4 * tau) (T J) U ∧
        Submodule.IsCloseTo (4 * tau) U (T J) ∧
        (∀ (power : ℕ)
          (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))) (delta : ℝ),
          Submodule.IsViable delta S
            ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ w : Fin power → Fin (N J),
            S.map ((List.ofFn (fun j ↦ F J (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
            Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
              ((T J).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap))) ∧
      ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
      (∀ (seed : IntervalSamplingChoices L q) (p r : ℕ), p ≤ r → r ≤ L →
        let S := balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
          width hwidth p r
        Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S) ∧
      let Good := canonicalIntervalSamplingTreeGood D s hwidth N F xi G
        (3 / 200 : ℝ) 0 L
      let failureBound : ℝ≥0∞ := ((L - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2)
      MeasurableSet Good ∧
        intervalSamplingMeasure L q Goodᶜ ≤ failureBound ∧
        1 - failureBound ≤ intervalSamplingMeasure L q Good := by
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfamily⟩ :=
    exists_physical_dg_canonical_interval_sampling_data
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Uref, hdimU, hUMPS, hxiMax, hwidth, T, N, F, hN, htargets, hxi⟩ :=
    hfamily L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  clear hfamily
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, Uref, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  refine ⟨hwidth, T, N, F, hN, htargets, ?_⟩
  intro xi hxi0 hxiMax'
  obtain ⟨hprofile, hparents⟩ := hxi xi hxi0 hxiMax'
  refine ⟨hprofile, ?_⟩
  intro Good failureBound
  have hGood : MeasurableSet Good :=
    measurableSet_canonicalIntervalSamplingTreeGood D s hwidth N F xi G
      (3 / 200 : ℝ) 0 L (Nat.zero_le L) le_rfl
  have hfailure : intervalSamplingMeasure L q Goodᶜ ≤ failureBound := by
    change intervalSamplingMeasure L q
      {seed | ¬(Submodule.IsViable (3 / 200 : ℝ)
        (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
          width hwidth 0 L)
        (G.map (Entropy.regionTensorCoordinates q (interval L 0 L)).toLinearEquiv.toLinearMap) ∧
        ∀ J ∈ balancedIntervalMergeList width hwidth 0 L,
          Submodule.IsViable (3 / 200 : ℝ)
            (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
              width hwidth J.1 J.2)
            (G.map (Entropy.regionTensorCoordinates q
              (interval L J.1 J.2)).toLinearEquiv.toLinearMap))} ≤ _
    apply intervalSamplingMeasure_canonical_tree_joint_failure_le
      D s hwidth N F xi G (3 / 200 : ℝ) (by norm_num)
      (ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2)) 0 L (Nat.zero_le L) le_rfl
    intro p r hpr hrL hlong seed k hpk hkr J S1 S2 hS1 hS2
    exact (hparents J k hpk hkr S1 S2
      (hprofile seed p k hpk (hkr.trans hrL)).1
      (hprofile seed k r hkr hrL).1 hS1 hS2).2
  have hcomplement : intervalSamplingMeasure L q Good =
      1 - intervalSamplingMeasure L q Goodᶜ := by
    simpa only [compl_compl, measure_univ] using
      (measure_compl hGood.compl (measure_ne_top (intervalSamplingMeasure L q) Goodᶜ))
  refine ⟨hGood, hfailure, ?_⟩
  rw [hcomplement]
  exact tsub_le_tsub_left hfailure 1

end TNLean.MPS.AreaLaw

end PhysicalDGCanonicalJointProbability
