/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGCanonicalSamplingData
import TNLean.MPS.AreaLaw.CanonicalIntervalTreeSuccessEvent
import TNLean.MPS.AreaLaw.CanonicalIntervalJointProbability

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
-/

open MeasureTheory
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
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
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
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Uref, hdimU, hUMPS, hxiMax, hwidth, T, N, F, hN, htargets, hxi⟩ :=
    hfamily L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
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
