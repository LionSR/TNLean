/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGReferenceSpace
import QICLean.Analysis.ViableSubspaceOrder

/-!
# An original-ground reference, including flat spectra

The reference used for ALVV collective trimming is constructed from the original
physical ground space. A distinct excited energy is needed only to invoke the
existing area-law approximation. If the Hamiltonian has flat spectrum, its ground
space is the whole space and is its own exact reference.

This is an auxiliary to ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805.
No reference is taken from a sampled tree or its output.

**Scope restriction (gap dependence):** The quantitative profile uses the clipped
gap `min gamma 1`; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- A reference for the original full ground space with the usual logarithmic
matrix product bond bound. The flat-spectrum case is included, without requiring
an excited energy as an additional hypothesis. Supporting ALVV,
arXiv:1602.08828v2, `t:alg1`, lines 1801–1805. -/
theorem exists_physical_ground_isOpenMPS_reference_subspace :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ), 1 ≤ q →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      let b := 16 + Real.log (1 / g) +
        Real.log (32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo epsilon U G ∧ Submodule.IsCloseTo epsilon G U ∧
        ∀ v ∈ U, IsOpenMPS L q (r ^ 2 * B) (fun x ↦ v x) := by
  classical
  obtain ⟨K, hK, href⟩ := exists_physical_dg_isOpenMPS_reference_subspace
  refine ⟨K, hK, ?_⟩
  intro L q hq h hs h0 h1 mu gamma hgamma H hH hmu hgap G r g u
    epsilon hepsilon hepsilon1 b
  by_cases hnonflat : ∃ nu ∈ spectrum ℝ H, mu < nu
  · obtain ⟨nu, hnu, hmunu⟩ := hnonflat
    exact href L q h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilon hepsilon hepsilon1
  · have heig (i) : hH.eigenvalues i = mu := by
      rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with hi | hi
      · exact hi
      · exact False.elim (hnonflat ⟨_, hH.eigenvalues_mem_spectrum_real i,
          by linarith only [hi, hgamma]⟩)
    have hGtop : G = ⊤ := by
      apply top_unique
      intro v _
      apply (Submodule.mem_spectralSpanLE_iff _ _ _ _).mpr
      intro i hi
      simp only [heig i, lt_self_iff_false] at hi
    have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
      (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hg : 0 < g := lt_min hgamma (by norm_num)
    have hlogg : 0 ≤ Real.log (1 / g) :=
      Real.log_nonneg ((one_le_div hg).2 (min_le_right gamma 1))
    have hu : 0 ≤ u := by
      have hlogq := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
      dsimp only [u]
      linarith only [hlogq, hlogg]
    have hb : 1 ≤ b := by
      have hratio : 1 ≤ 32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon := by
        apply (one_le_div hepsilon).2
        nlinarith only [hrR, (Nat.cast_nonneg L : (0 : ℝ) ≤ L), hepsilon1]
      have hlog := Real.log_nonneg hratio
      dsimp only [b]
      linarith only [hlogg, hlog]
    have hcost : 0 ≤ K *
        (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) := by
      have hlogb := Real.log_nonneg hb
      positivity
    refine ⟨1, le_rfl, ?_, G, rfl,
      Submodule.isCloseTo_of_le hepsilon.le le_rfl,
      Submodule.isCloseTo_of_le hepsilon.le le_rfl, ?_⟩
    · simpa only [Nat.cast_one, Real.log_one] using hcost
    · intro v _
      apply (isOpenMPS_iff_internal_cutMatrix_rank_le v).mpr
      intro k _ _
      calc
        (cutMatrix v k).rank ≤
            Fintype.card ((w : {w : Fin L // w ∈ leftBlock L k}) → Fin q) :=
          Matrix.rank_le_card_height _
        _ = q ^ Fintype.card {w : Fin L // w ∈ leftBlock L k} := by simp
        _ ≤ q ^ L := Nat.pow_le_pow_right hq (by
          simpa using Fintype.card_subtype_le (fun w : Fin L ↦ w ∈ leftBlock L k))
        _ = r := by
          change q ^ L = Module.finrank ℂ G
          rw [hGtop]
          simp
        _ ≤ r ^ 2 * 1 := by nlinarith only [hr]

end TNLean.MPS.AreaLaw
