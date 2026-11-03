/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGSharpApproximation
import TNLean.MPS.AreaLaw.NormalizedSequentialApproximation
import QICLean.Analysis.LogRankRounding
import QICLean.Analysis.ViableSubspaceEntropy
import QICLean.Channel.MaximalOverlap

/-!
# One physical matrix product approximant at all cuts

Fixed-cut normalized approximants control the discarded spectral mass of the
original marginals. The output vector is the single sequential truncation
onto their leading eigenspaces, followed by normalization. This supports the
global matrix product state conclusion of ALVV, arXiv:1602.08828v2,
Theorem 4.9, source lines 1080–1086.

**Local fix (parameter choice):** The independent scales are documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Scope restriction (gap dependence):** The bound uses `min gamma 1`.
Comparison with the printed quantitative dependence is for `0 < gamma ≤ 1`;
the larger-gap comparison remains in the same note.

The distinct spectral values express Assumption (DG) of the source,
lines 275–279, which requires a second smallest eigenvalue.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Every original ground vector has one normalized open-boundary matrix
product approximant with simultaneous bond control at all cuts. The factor
beyond the ground-space dimension is chosen before the vector. The proof
constructs one sequential projection product and then normalizes it.
Supporting ALVV, arXiv:1602.08828v2, Theorem 4.9, global conclusion,
source lines 1080–1086. -/
theorem exists_physical_dg_normalized_isOpenMPS_approximation :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ),
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let b := 16 + Real.log (1 / g) + Real.log (16 * ((L : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin L → Fin q)), ψ ∈ G → ‖ψ‖ = 1 →
      ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
        IsOpenMPS L q (Module.finrank ℂ G * B) (fun x ↦ Φ x) ∧
        1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  obtain ⟨K, hK, hfixed⟩ := exists_physical_dg_interval_normalized_approximation
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  intro L q h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G g u
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hg1 : g ≤ 1 := min_le_right gamma 1
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  intro delta hdelta hdelta1 b
  let deltaCut := delta / (16 * ((L : ℝ) + 1))
  have hden : 0 < 16 * ((L : ℝ) + 1) := by positivity
  have hcut : 0 < deltaCut := div_pos hdelta hden
  have hcut1 : deltaCut ≤ 1 := by
    apply (div_le_iff₀ hden).2
    have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith only [hdelta1, hL]
  have hrecip : 1 / deltaCut = 16 * ((L : ℝ) + 1) / delta := by
    dsimp only [deltaCut]
    field_simp
  have hb : 16 ≤ b := by
    have hlogcut := Real.log_nonneg ((one_le_div hcut).2 hcut1)
    rw [hrecip] at hlogcut
    dsimp only [b]
    linarith only [hlogg, hlogcut]
  let F := u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u
  have hbase : 1 ≤ u ^ 3 / g := (le_div_iff₀ hg).2 (by
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
    linarith only [hu3, hg1])
  have hroot : 0 ≤ (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by positivity
  have hsum : 1 ≤ u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u := by
    linarith only [hbase, hroot]
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by linarith only [hb])
  have hF : 1 ≤ F := hsum
  have hPone : 1 ≤ 1 + Real.log b := by linarith only [hlogb]
  have hFP : 1 ≤ F * (1 + Real.log b) := by
    simpa only [one_mul] using
      (mul_le_mul hF hPone (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hF))
  let E := K * F * (1 + Real.log b)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg hK.le (zero_le_one.trans hF))
    (zero_le_one.trans hPone)
  let B : ℕ := ⌈Real.exp E⌉₊
  obtain ⟨hB, hlogB⟩ := Real.log_ceil_exp_le_add_one E hE
  refine ⟨B, hB, ?_, ?_⟩
  · change Real.log (B : ℝ) ≤ (K + 1) * F * (1 + Real.log b)
    change Real.log (B : ℝ) ≤ E + 1 at hlogB
    dsimp only [E] at hlogB
    nlinarith only [hlogB, hFP]
  · intro ψ hψG hψ
    have htail : ∀ k ∈ Finset.Ico 1 L,
        1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
          (leftBlock L k) ψ).kyFanNorm (Module.finrank ℂ G * B) ≤
            delta / (8 * ((L : ℝ) + 1)) := by
      intro k hk
      have hkL : k ≤ L := (Finset.mem_Ico.mp hk).2.le
      obtain ⟨φ, hφ, hoverlap, hlogrank⟩ :=
        hfixed L q 0 k (Nat.zero_le k) hkL h hs h0 h1 mu nu gamma hgamma
          hmu hnu hmunu hgap deltaCut hcut hcut1 ψ hψG hψ
      rw [hrecip] at hlogrank
      have hregional := one_sub_regional_kyFanNorm_le_twice_error
        (interval L 0 k) ψ φ hφ deltaCut hcut1 (Module.finrank ℂ G * B)
        (Nat.le_mul_ceil_exp_of_log_le hrG E hlogrank) hoverlap
      rw [leftBlock_eq_interval]
      convert hregional using 1
      dsimp only [deltaCut]
      field_simp; ring
    exact exists_unit_mps_of_uniform_prefix_mass ψ hψ (Module.finrank ℂ G * B)
      delta hdelta hdelta1 htail

end TNLean.MPS.AreaLaw
