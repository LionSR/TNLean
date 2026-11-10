/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalTrimmingMPS
import TNLean.MPS.AreaLaw.PhysicalDGFilterIteration
import TNLean.MPS.AreaLaw.PhysicalDGReferenceSpace
import QICLean.Analysis.ViableRefinementParameters
import QICLean.Analysis.RitzGroundSpaceCloseness

/-!
# Automatic common-reference refinement of the same candidate

The physical reference and positive threshold are chosen before every
initial candidate. They fit both the original tree threshold and the
strict source threshold inequality. The terminal space is a literal
raw-filter-and-trim iterate of the given candidate, and its actual
compressed Ritz space approximates the original full ground space.
Its MPS bound follows from the recorded terminal trimming vectors,
including the additional spanning-family factor.

This is a parameter-selection and refinement auxiliary for ALVV,
arXiv:1602.08828v2, `eq:algo-xi-dg`, lines 1800–1805, and final refinement,
lines 1809–1817. The initial-candidate hypothesis is discharged by the
actual common-radius tree in the subsequent composition.

**Scope restriction (reference gap dependence):** The reference estimate
uses `min gamma 1`; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
No adaptive sampling probability or running time is asserted.

**Local fix (normalized gain):** The literal raw-filter iterates use the
corrected recurrence recorded in `docs/paper-gaps/alvv16_final_filter_gain.tex`.
The printed iteration count is not identified with this accuracy choice.
-/

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual physical reference and threshold can be chosen before any
initial candidate. A candidate already close to the original full ground
space is refined by literal raw-filter-and-trim iterates, and the actual
Ritz extraction from that same terminal space has the prescribed accuracy.
The initial-candidate premise belongs to this auxiliary, not to the final
physical tree construction. Supporting ALVV, arXiv:1602.08828v2,
`eq:algo-xi-dg`, lines 1800–1805, and `t:alg1`, lines 1809–1817. -/
theorem exists_physical_dg_automatic_same_candidate_refinement :
    ∃ Kref : ℝ, 0 < Kref ∧ ∀ (L q : ℕ),
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
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let A := ‖H‖ - mu
    let c := gamma / A
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    ∀ (Dtree Dfilter : ℕ), 1 ≤ Dtree → 1 ≤ Dfilter →
    ∀ eta : ℝ, 0 < eta →
    let rho := eta * gamma / (2 * A + eta * gamma)
    let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
    let epsilonRef := c ^ 2 * rho / 32768
    let bref := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
    ∃ B : ℕ, 1 ≤ B ∧
    Real.log (B : ℝ) ≤
      Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log bref) ∧
    let b := rG ^ 2 * B
    let Dcommon := max Dtree b
    let N := Nat.ceil (100 * (Dfilter : ℝ) ^ 12 / (c * rho))
    let xi := 1 / (1000 * ((Dcommon * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      Submodule.IsCloseTo epsilonRef U G ∧ Submodule.IsCloseTo epsilonRef G U ∧
      (∀ v ∈ U, IsOpenMPS L q b (fun x ↦ v x)) ∧
      0 < xi ∧
      xi ≤ 1 / (1000 * (Dtree : ℝ) * Real.sqrt ((L : ℝ) + 1)) ∧
      Real.sqrt ((L : ℝ) * (rG : ℝ) * (b : ℝ)) * xi <
        eta / (10000 * (Dfilter : ℝ) ^ 12) ∧
      ∀ (count : ℕ) (S0 : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
      Module.finrank ℂ S0 ≤ count →
      Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0) G →
      let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
      let W := nativeFullIntervalSpace L q S
      let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
      0 < n ∧ Submodule.IsCloseTo rho W G ∧ Module.finrank ℂ S ≤ count ∧
        R ≤ W ∧ Module.finrank ℂ R = rG ∧
        Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
        ∀ v ∈ R, IsOpenMPS L q
          (1000000 * (Dcommon * N) ^ 2 * (L + 1) * count ^ 2) (fun x ↦ v x) := by
  classical
  obtain ⟨Kref, hKref, hreference⟩ := exists_physical_dg_isOpenMPS_reference_subspace
  refine ⟨Kref, hKref, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u A c Kraw Dtree Dfilter hDtree hDfilter eta heta rho n epsilonRef bref
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  obtain ⟨_hM, hA, _hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec h h0 mu nu gamma hgamma hmu hnu hmunu hgap
  change 0 < A at hA
  change gamma / A ≤ 1 at hc1
  have hgammaA : gamma ≤ A := (div_le_one hA).mp hc1
  obtain ⟨hc, _hc1', hrho, hrho1, _hrhoEta, hpEta, hepsilon, hepsilonSmall,
    hepsilonBudget, henergy⟩ := Real.viable_refinement_error_parameters hgamma hgammaA heta
  have hepsilon1 : epsilonRef ≤ 1 := hepsilonSmall.trans (by norm_num)
  obtain ⟨B, hB, hlogB, U, hdimU, hUG, hGU, hUMPS⟩ :=
    hreference L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilonRef hepsilon hepsilon1
  refine ⟨B, hB, hlogB, ?_⟩
  intro b Dcommon N xi
  have hrb : rG ≤ b := by
    have hsquare : rG ≤ rG ^ 2 := by
      simpa only [mul_one, pow_two] using Nat.mul_le_mul_left rG hrG
    exact hsquare.trans (by simpa only [mul_one] using Nat.mul_le_mul_left (rG ^ 2) hB)
  have hb : 1 ≤ b := hrG.trans hrb
  obtain ⟨hN, hDN, hxi, hxiTree, hxiBudget, hxiSource⟩ :=
    Real.viable_refinement_radius_parameters (L := L) hrG hrb hDtree hDfilter
      (mul_pos hc hrho) hpEta
  refine ⟨U, hdimU, hUG, hGU, hUMPS, hxi, hxiTree, hxiSource, ?_⟩
  intro count S0 hdimS0 hcloseS0
  have hxiBudget' : xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (b ^ 2 : ℕ)) ≤ c * rho / 48 := by
    simpa only [Nat.cast_pow] using hxiBudget
  obtain ⟨hn, hcloseW, hdimS, _hrecorded⟩ :=
    physical_dg_filterTrimIterate_ceil_log_isCloseTo h h0 mu nu gamma hgamma
      hmu hnu hmunu hgap b hb U epsilonRef rho xi (3 / 200)
      hepsilon.le hrho hrho1.le hxi (by norm_num) (by norm_num)
      hGU hUG hUMPS hepsilonBudget hxiBudget' S0 hcloseS0
  let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
  let W := nativeFullIntervalSpace L q S
  let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
  have hspan := isIntervalSpanWithRankBound_fullIntervalFilterTrimIterate_succ
    hxi Kraw S0 hdimS0 (Nat.ceil (4 / c * Real.log (1 / rho)))
  have hWmps : ∀ v ∈ W, IsOpenMPS L q
      (1000000 * (Dcommon * N) ^ 2 * (L + 1) * count ^ 2) (fun x ↦ v x) := by
    intro v hv
    exact isOpenMPS_of_mem_nativeFullIntervalSpace_of_trimming_rank_bound hDN hspan hv
  obtain ⟨hRle, hdimR, hGR, hRG⟩ :=
    hH.ritzSubspace_isCloseTo_ground_of_isCloseTo W hgamma hmu hgap hrho.le hrho1 hcloseW
  have herror : (‖H‖ - mu) * rho / (1 - rho) / gamma = eta / 2 := by
    rw [henergy]
    field_simp
  rw [herror] at hGR hRG
  exact ⟨hn, hcloseW, hdimS.trans hdimS0, hRle, hdimR, hGR, hRG,
    fun v hv ↦ hWmps v (hRle hv)⟩

end TNLean.MPS.AreaLaw
