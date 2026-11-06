/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalFilterTrimming
import QICLean.Analysis.GroundSpaceAffineFilter

/-!
# The physical full-ground filter at the same root

The filter is constructed from the actual positive chain Hamiltonian, its
original ground energy and its operator norm. The two actual distinct
spectral values and the original global gap determine its positive
normalization and complementary contraction. The complete ground space
is retained, with no uniqueness assumption or gap cap.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1620–1643,
and the final refinement in `t:alg1`, lines 1809–1817. The reference and
trimming threshold remain explicit in the one-step auxiliary; their automatic
choice and the repeated iteration are separate.

**Local fix (normalized gain):** The normalized error estimate replaces
the printed raw multiplicative overlap gain. The actual image and trim
spaces equal those obtained from the printed unnormalized filter; see
`docs/paper-gaps/alvv16_final_filter_gain.tex`.
-/

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem fullIntervalFilterTrimStep_smul {L q : ℕ} {a : ℂ} (ha : a ≠ 0)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
    (xi : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    fullIntervalFilterTrimStep L q (a • K) xi S = fullIntervalFilterTrimStep L q K xi S := by
  have hfilter : fullIntervalFilter L q (a • K) = a • fullIntervalFilter L q K := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [fullIntervalFilter_apply, smul_apply, map_smul]
  have himage : S.map (fullIntervalFilter L q (a • K)).toLinearMap =
      S.map (fullIntervalFilter L q K).toLinearMap := by
    rw [hfilter]
    exact Submodule.map_smul (fullIntervalFilter L q K).toLinearMap S a ha
  exact congrArg (fun V : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)) ↦
    intervalTrimSubspace L q 0 L xi (fun i ↦ ((stdOrthonormalBasis ℂ V) i : _))) himage

/-- Multiplying the actual affine filter by its nonzero ground-energy
normalization leaves every full-interval filter-and-trim space unchanged.
The standard basis and trim are those of the same image subspace.
Supporting ALVV, arXiv:1602.08828v2, final filter, lines 1620–1643. -/
theorem fullIntervalFilterTrimStep_normalized_affine_eq_raw
    {L q : ℕ} (H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (mu M : ℝ) (hM : M ≠ 0) (hden : M - mu ≠ 0)
    (xi : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    fullIntervalFilterTrimStep L q
      (Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        ((M - mu)⁻¹ • (M • 1 - H))) xi S =
      fullIntervalFilterTrimStep L q
        (Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - M⁻¹ • H)) xi S := by
  have hnormal : 1 - mu / M ≠ 0 := by
    rw [← div_self hM, ← sub_div]
    exact div_ne_zero hden hM
  rw [← Matrix.normalized_affine_filter_eq_smul_raw H mu M hM,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [map_smul]
  exact fullIntervalFilterTrimStep_smul (Complex.ofReal_ne_zero.mpr (inv_ne_zero hnormal)) _ xi S

/-- The actual positive chain supplies a normalized filter for its original
full degenerate ground space. The physical two-value spectral convention
makes the normalization positive. Supporting ALVV, arXiv:1602.08828v2,
hypothesis (DG), lines 275–279, and final filter, lines 1620–1643. -/
theorem physical_dg_normalized_ground_filter_spec
    {L q : ℕ} (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (mu nu gamma : ℝ) (hgamma : 0 < gamma) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let M := ‖H‖
    let K := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      ((M - mu)⁻¹ • (M • 1 - H))
    let c := gamma / (M - mu)
    0 < M ∧ 0 < M - mu ∧ 0 < c ∧ c ≤ 1 ∧
      (∀ x ∈ G, K x = x) ∧
      (∀ x ∈ Gᗮ, K x ∈ Gᗮ) ∧
      ∀ x ∈ Gᗮ, ‖K x‖ ^ 2 ≤ (1 - c) * ‖x‖ ^ 2 := by
  intro H hH hmu hnu hmunu hgap G M K c
  have hupper : ∀ z ∈ spectrum ℝ H, z ≤ M := by
    apply (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp
    exact IsSelfAdjoint.le_algebraMap_norm_self H hH.isSelfAdjoint
  have hE1 : mu + gamma ≤ M := by
    rcases hgap nu hnu with heq | hexc
    · exact False.elim (ne_of_gt hmunu heq)
    · exact hexc.trans (hupper nu hnu)
  have hden : 0 < M - mu := by linarith [hupper nu hnu]
  have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg
    (show 0 ≤ H from Finset.sum_nonneg fun i _ ↦ h0 i) hmu
  have hM : 0 < M := by linarith
  have hspectrum : ∀ z ∈ spectrum ℝ H, z = mu ∨ z ∈ Set.Icc (mu + gamma) M := by
    intro z hz
    exact (hgap z hz).elim Or.inl (fun he ↦ Or.inr ⟨he, hupper z hz⟩)
  have hspec := hH.normalized_affine_ground_filter_spec
    (by linarith : mu < mu + gamma) hE1 hspectrum
  have hrate : (mu + gamma - mu) / (M - mu) = c := by
    dsimp only [c]
    congr 1
    ring
  rw [hrate] at hspec
  exact ⟨hM, hden, hspec⟩

/-- One actual physical filter and collective trim of the given root
obeys the stable recurrence for the original full ground space. The
printed raw filter produces exactly the same image and trimmed spaces as
its nonzero ground-normalized multiple. The filter and its contraction
are derived from the actual Hamiltonian;
the common reference and numerical trimming budgets are explicit inputs.
Supporting ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1809–1817. -/
theorem isCloseTo_nativeFullIntervalSpace_filterTrimStep_of_physical_dg
    {L q : ℕ} (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (mu nu gamma : ℝ) (hgamma : 0 < gamma) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let M := ‖H‖
    let K := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - M⁻¹ • H)
    let c := gamma / (M - mu)
    ∀ (D : ℕ), 1 ≤ D →
    ∀ (U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (epsilon eta xi delta : ℝ),
    0 ≤ epsilon → 0 < xi → 0 ≤ delta → delta ≤ 1 / 2 →
    Submodule.IsCloseTo epsilon G U → Submodule.IsCloseTo epsilon U G →
    (∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x)) →
    epsilon ≤ c ^ 2 * eta / 1024 →
    xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)) ≤ c * eta / 48 →
    ∀ (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
    Submodule.IsCloseTo delta (nativeFullIntervalSpace L q S) G →
    Submodule.IsCloseTo ((1 - c / 4) * delta + c * eta / 8)
      (nativeFullIntervalSpace L q (fullIntervalFilterTrimStep L q K xi S)) G := by
  intro H hH hmu hnu hmunu hgap G M K c D hD U epsilon eta xi delta
    hepsilon hxi hdelta0 hdelta hGU hUG hU hepsilonBudget hxiBudget S hS
  let Kn := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    ((M - mu)⁻¹ • (M • 1 - H))
  obtain ⟨hM, hden, hc, hc1, hfix, hKGo, hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec h h0 mu nu gamma hgamma
      hmu hnu hmunu hgap
  have hnext := isCloseTo_nativeFullIntervalSpace_filterTrimStep hD hxi hc hc1
    hdelta0 hdelta hepsilon Kn (fun x hx ↦ by rw [hfix x hx]; exact hx) hKGo
    (fun x hx ↦ by rw [hfix x hx]) hhigh hGU hUG hU hepsilonBudget hxiBudget S hS
  dsimp only [Kn] at hnext
  rw [fullIntervalFilterTrimStep_normalized_affine_eq_raw H mu M hM.ne' hden.ne' xi S] at hnext
  exact hnext

end TNLean.MPS.AreaLaw
