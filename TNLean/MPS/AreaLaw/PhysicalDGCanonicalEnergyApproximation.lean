/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGCanonicalApproximation
import TNLean.MPS.AreaLaw.ALVV.CalibratedRootEnergy

/-!
# Energy and Ritz output from one successful sampled tree

One family is selected before accuracy and seeds. For every successful seed,
its original canonical root subtree carries a single scalar energy function.
The same root is then refined literally, and its actual Ritz space has the
prescribed dimension, two-sided closeness and uniform polynomial MPS bond.
The energy function belongs to the original tree, not to the refined space.

Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631 and 1777–1817.
**Local fix (same-family energy and normalized final gain):** The energy
updates use the corrected compressed minimum minus three and the final
refinement uses its normalized raw-filter gain. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex` and
`docs/paper-gaps/alvv16_final_filter_gain.tex`.
**Scope restriction (physical construction and coarse polynomial bound):**
Block leaves, hard-clipped families, capped gap and larger integer parent
counts are retained as in `docs/paper-gaps/alvv16_approximation_parameters.tex`.
No measurable Ritz-basis selection or running time is asserted.
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The same selected family supplies the probability bound, the energy
function on every successful root subtree, and the literal final Ritz/MPS
output. The energy function is chosen once per successful seed, before all
vectors in the Ritz space. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817, with the corrected energy estimate of line 1807. -/
theorem exists_physical_dg_canonical_ritz_polynomial_approximation_with_energy :
    ∃ Ctail Cscale Ktree Kfinal : ℝ,
    21 ≤ Ctail ∧ 21 ≤ Cscale ∧ 0 < Ktree ∧ 0 < Kfinal ∧
    ∀ (q : ℕ) (gamma : ℝ), 0 < gamma →
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    ∀ (L : ℕ),
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu : ℝ),
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
    let ell := Nat.ceil (Cscale * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
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
    ∃ Btree : ℕ, 1 ≤ Btree ∧
      Real.log (Btree : ℝ) ≤
        Ktree * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ Utree : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ Utree = rG ∧
      (∀ z ∈ Utree, IsOpenMPS L q (rG ^ 2 * Btree) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * Btree
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width, ∃ hq : 0 < q,
    ∃ (T : LongIntervalIndex L width →
        Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      (∀ J, Module.finrank ℂ (T J) = rG ∧
        Submodule.IsCloseTo tau (T J) G ∧ Submodule.IsCloseTo tau G (T J) ∧
        Submodule.IsCloseTo (4 * tau) (T J) Utree ∧
        Submodule.IsCloseTo (4 * tau) Utree (T J) ∧
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
      let Dtree := Dref * Nat.ceil (1 / a)
      let A := ‖H‖ - mu
      let c := gamma / A
      let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
      ∀ eta : ℝ, 0 < eta →
      let rho := eta * gamma / (2 * A + eta * gamma)
      let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
      let epsilonFinal := c ^ 2 * rho / 32768
      let bfinal := 16 + Real.log (1 / g) +
        Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonFinal)
      ∃ Bfinal : ℕ, 1 ≤ Bfinal ∧
        Real.log (Bfinal : ℝ) ≤
          Kfinal * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bfinal ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log bfinal) ∧
      let b := rG ^ 2 * Bfinal
      let Dcommon := max Dtree b
      let Nfinal := Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))
      let xi := 1 / (1000 * ((Dcommon * Nfinal : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
      ∃ Ufinal : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ Ufinal = rG ∧
        Submodule.IsCloseTo epsilonFinal Ufinal G ∧ Submodule.IsCloseTo epsilonFinal G Ufinal ∧
        (∀ z ∈ Ufinal, IsOpenMPS L q b (fun x ↦ z x)) ∧
        0 < xi ∧ xi ≤ xiMax ∧
        Real.sqrt ((L : ℝ) * (rG : ℝ) * (b : ℝ)) * xi <
          eta / (10000 * (D : ℝ) ^ 12) ∧
      (∀ (seed : IntervalSamplingChoices L q) (p r : ℕ), p ≤ r → r ≤ L →
        let S := balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
          width hwidth p r
        Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S) ∧
      let Good := canonicalIntervalSamplingTreeGood D s hwidth N F xi G (3 / 200 : ℝ) 0 L
      let failureBound : ℝ≥0∞ := ((L - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2)
      MeasurableSet Good ∧ intervalSamplingMeasure L q Goodᶜ ≤ failureBound ∧
        1 - failureBound ≤ intervalSamplingMeasure L q Good ∧
      let Bout : ℕ := 1000000 * (Dcommon * Nfinal) ^ 2 * (L + 1) * (D ^ 6 * s ^ 3) ^ 2
      (Bout : ℝ) ≤ C * (((L : ℝ) + 1) * ((rG : ℝ) + 1) * (1 + 1 / eta)) ^ k ∧
      ∀ seed ∈ Good,
        ∃ estimate : ℕ → ℕ → ℝ,
          ALVV.IsRegionalLowerEnergyEstimate h 0 L (49 / 16) (estimate 0 L) ∧
          (L - 0 ≤ width →
            ALVV.IsRegionalLowerEnergyEstimate h 0 L 0 (estimate 0 L)) ∧
          (∀ J : LongIntervalIndex L width,
            J.val ∈ balancedIntervalMergeList width hwidth 0 L →
            let l := J.val.1
            let r := J.val.2
            let k := l + (r - l) / 2
            let hpk : l ≤ k := Nat.le_add_right l ((r - l) / 2)
            let hkr : k ≤ r :=
              (Nat.add_le_add_left (Nat.div_le_self (r - l) 2) l).trans_eq
                (Nat.add_sub_of_le J.property.1)
            ALVV.IsRegionalLowerEnergyEstimate h l r (49 / 16) (estimate l r) ∧
            (k - l ≤ width → ALVV.IsRegionalLowerEnergyEstimate h l k 0 (estimate l k)) ∧
            (r - k ≤ width → ALVV.IsRegionalLowerEnergyEstimate h k r 0 (estimate k r)) ∧
            ALVV.IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell)
              hq hpk hkr h (F J)
              (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
                width hwidth l k)
              (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
                width hwidth k r)
              (estimate l k) (estimate k r) (estimate l r)) ∧
        let S0 := balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
          width hwidth 0 L
        let W0 := nativeFullIntervalSpace L q S0
        Submodule.IsCloseTo (3 / 200 : ℝ) W0 G ∧
          (∀ z ∈ W0, IsOpenMPS L q Bout (fun x ↦ z x)) ∧
        let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
        let W := nativeFullIntervalSpace L q S
        let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
        0 < n ∧ Submodule.IsCloseTo rho W G ∧ Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          R ≤ W ∧ Module.finrank ℂ R = rG ∧
          Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
          ∀ z ∈ R, IsOpenMPS L q Bout (fun x ↦ z x) := by
  classical
  obtain ⟨Ctail, Cscale, Ktree, Kfinal, hCtail, hCscale, hKtree, hKfinal, hmain⟩ :=
    exists_physical_dg_canonical_ritz_polynomial_approximation
  refine ⟨Ctail, Cscale, Ktree, Kfinal, hCtail, hCscale, hKtree, hKfinal, ?_⟩
  intro q gamma hgamma
  obtain ⟨C, hC, k, hmain⟩ := hmain q gamma hgamma
  refine ⟨C, hC, k, ?_⟩
  intro L h hsupp h0 h1 mu nu H hH hmu hnu hmunu hgap G rG
    g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD2, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    Btree, hBtree, hlogBtree, Utree, hdimUtree, hUtreeMPS, hxiMax,
    hwidth, T, N, F, hN, htargets, haccuracy⟩ :=
    hmain L h hsupp h0 h1 mu nu hmu hnu hmunu hgap
  change 21 ≤ ell at hell
  change 2 ≤ D at hD2
  change 1 ≤ s at hs
  have hq : 0 < q := lt_of_lt_of_le (by decide : 0 < 2)
    (hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu))
  refine ⟨hell, hD2, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨Btree, hBtree, hlogBtree, Utree, hdimUtree, hUtreeMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  refine ⟨hwidth, hq, T, N, F, hN, htargets, ?_⟩
  have henergy := exists_canonical_root_energy_of_calibrated_words
    (L := L) (q := q) (ell := ell) (D := D) (s := s) hq hell hD2 hs rfl
    h hsupp h0 h1 mu gamma hgamma hwidth T N F hmu hgap
    (fun J ↦ ⟨(htargets J).1, (htargets J).2.2.1, (htargets J).2.2.2.2.2⟩)
  intro Dtree A c Kraw eta heta rho n epsilonFinal bfinal
  obtain ⟨Bfinal, hBfinal, hlogBfinal, Ufinal, hdimUfinal, hUG, hGU, hUfinalMPS,
    hxi, hxiTree, hxiSource, hprofile, hGoodMeasurable, hfailure, hsuccess,
    hbond, hterminal⟩ := haccuracy eta heta
  refine ⟨Bfinal, hBfinal, hlogBfinal, ?_⟩
  intro b Dcommon Nfinal xi
  refine ⟨Ufinal, hdimUfinal, hUG, hGU, hUfinalMPS, hxi, hxiTree, hxiSource,
    hprofile, ?_⟩
  intro Good failureBound
  refine ⟨hGoodMeasurable, hfailure, hsuccess, ?_⟩
  intro Bout
  refine ⟨hbond, ?_⟩
  intro seed hgood
  obtain ⟨estimate, hrootEnergy, hshortEnergy, hnodesEnergy⟩ := henergy xi seed hgood
  refine ⟨estimate, hrootEnergy, hshortEnergy, hnodesEnergy, ?_⟩
  dsimp only [Bout, xi, Nfinal, Dcommon, b, n, rho, Kraw, c, A,
    Dtree, Dref, a, s, D, width, ell, v, w, m, g, rG, G, H]
  exact hterminal seed hgood

end TNLean.MPS.AreaLaw
