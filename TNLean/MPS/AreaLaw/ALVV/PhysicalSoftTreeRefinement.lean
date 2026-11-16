/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.PhysicalSoftResampling
import TNLean.MPS.AreaLaw.PhysicalSameRootPolynomialRefinement
import TNLean.MPS.AreaLaw.FullIntervalViability

/-!
# Refinement from the successful root of the physical resampling tree

The final refinement of the source's algorithm is applied to the actual root of the physical
soft resampling tree. On the joint success event, of probability at least `1 - 1/(L+1)^2`,
the root is `3/200`-viable for the ground space, so the literal filter-and-trim refinement of
that same root and its Ritz extraction give a subspace of the dimension of the ground space,
mutually `η/2`-close to it, all of whose vectors are matrix product states of bond dimension
`Bscale · count²`. The refinement data precede every seed, the count is polynomial in the
chain length and the ground-space dimension, and `Bscale` is polynomial in these and `1/η`.

Supporting ALVV, arXiv:1602.08828v2, Theorem `t:alg1` and its proof, lines 1777--1818.

**Scope restriction (reference gap dependence):** the refinement constants use the capped gap;
see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
**Local fix (normalized gain):** the refinement iterate is the corrected raw filter of
`docs/paper-gaps/alvv16_final_filter_gain.tex`. No running time and no printed parameter
choice is asserted.
-/

open MeasureTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- **The refined Ritz output of the successful physical root.** For a primitive gapped chain,
the physical soft families on the actual resampling tree have a measurable joint success event
of failure probability at most `1/(L+1)^2`. For every `η > 0` there are refinement data, chosen
before every seed, such that on that event the literal refinement of the same actual root and
its Ritz extraction give a subspace of the dimension of the ground space, mutually `η/2`-close
to it, consisting of matrix product states of bond dimension `Bscale · count²`, where `count` is
at most `Ccount ((L+1)(r+1))²` and `Bscale ≤ C ((L+1)(r+1)(1+1/η))^k`. Supporting ALVV,
arXiv:1602.08828v2, Theorem `t:alg1` and its proof, lines 1777--1818. -/
theorem exists_physical_soft_tree_refined_ritz_approximation
    (q : ℕ) (hq : 2 ≤ q) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ u Ccount : ℕ, 2 ≤ u ∧ 1 ≤ Ccount ∧ ∃ K : ℕ, 1 ≤ K ∧ ∃ C : ℝ, 0 < C ∧ ∃ kexp : ℕ,
    let ell := u ^ 8
    let m := u ^ 10
    let k := u ^ 16
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let width := 4 * ell
    ∀ (L : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu : ℝ),
    let H := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rho := Module.finrank ℂ G
    let threshold := K * (rho + 1) * (L + 2) ^ 2
    let rounds := q * L
    let count := max (q ^ width) (D ^ 2 * threshold)
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    ∃ xiInit : ℝ, 0 < xiInit ∧
    ∃ hwidth : 1 ≤ width,
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      let thresholdFamily := fun _ : LongIntervalIndex L width ↦ threshold
      let Good := canonicalIntervalResamplingGood D rounds hwidth thresholdFamily N F xiInit G 0 L
      MeasurableSet Good ∧
      intervalResamplingMeasure L q rounds Goodᶜ ≤ ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2) ∧
      count ≤ Ccount * ((L + 1) * (rho + 1)) ^ 2 ∧
      ∀ eta : ℝ, 0 < eta →
      let Z := ((L : ℝ) + 1) * ((rho : ℝ) + 1) * (1 + 1 / eta)
      ∃ (roundsRef : ℕ) (xiRef : ℝ) (Bscale : ℕ), 0 < xiRef ∧ (Bscale : ℝ) ≤ C * Z ^ kexp ∧
        ∀ U ∈ Good,
          let S0 := balancedIntervalSpace (canonicalIntervalResamplingOperation
            D rounds thresholdFamily N F xiInit U) width hwidth 0 L
          let S := fullIntervalFilterTrimIterate L q Kraw xiRef S0 roundsRef
          let W := nativeFullIntervalSpace L q S
          let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rho
          Module.finrank ℂ S ≤ count ∧ R ≤ W ∧ Module.finrank ℂ R = rho ∧
            Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
            ∀ v ∈ R, IsOpenMPS L q (Bscale * count ^ 2) (fun x ↦ v x) := by
  classical
  obtain ⟨u, K, Ccount, hu, hK, hCcount, hrest⟩ :=
    exists_physical_soft_resampling_tree q hq gamma hgamma
  obtain ⟨C, hC, kexp, href⟩ :=
    exists_physical_same_root_polynomial_refinement q 1 (by omega) le_rfl gamma hgamma
  refine ⟨u, Ccount, hu, hCcount, K, hK, C, hC, kexp, ?_⟩
  intro ell m k D width L h hs h0 h1 mu H hH hmu hgap G rho threshold rounds count Kraw
  obtain ⟨_hD, _hM, _htau, _htau1, _hprec, _hprec1, _htfloor, _hTfloor, _hT0, _hO, _hR,
    _hDelta, _heps, _hrev, _hSmall, _Cxi, _hCxi, _Pxi, hall⟩ := hrest
  obtain ⟨xiInit, hxi, _hxi1, _hinv, hwidth, N, F, _hFam, hGood, hprob, _hshort, hcount,
    hsize, _henergy⟩ := hall L h hs h0 h1 mu hmu hgap
  refine ⟨xiInit, hxi, hwidth, N, F, hGood, hprob, hcount, ?_⟩
  intro eta heta Z
  obtain ⟨roundsRef, xiRef, Bscale, hxiRef, hB, hout⟩ := href L h hs h0 h1 mu hmu hgap eta heta
  refine ⟨roundsRef, xiRef, Bscale, hxiRef, hB, ?_⟩
  intro U hU
  have hroot := (hsize U 0 L (Nat.zero_le L) le_rfl).1
  have hclose := (isViable_fullInterval_iff_isCloseTo _ G).mp hU.1
  exact hout count _ hroot hclose

end TNLean.MPS.AreaLaw.ALVV
