/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.SequentialTruncation
import QICLean.Analysis.UnitNormalizationDistance
import QICLean.Analysis.ViableSubspaceEntropy
import QICLean.Channel.MaximalOverlap

/-!
# One normalized sequential MPS from actual marginal tails

The existing regional overlap-to-tail and sequential approximation proofs
are moved unchanged from PhysicalDGGlobalApproximation. They require only
actual vectors, their marginal spectra and missing-mass bounds. No spectral
gap or independent area law is used. The same helpers can therefore serve
both the gapped and buffered low-energy approximations.

The construction projects onto the leading marginal eigenspaces in sequence
and normalizes the one resulting vector. It supports ALVV,
arXiv:1602.08828v2, fixed-cut to global approximation at lines 1080–1086
and the low-density conclusion at lines 1096–1105.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- The left block of `k` sites is the interval `[0, k)`. -/
theorem leftBlock_eq_interval (L k : ℕ) : leftBlock L k = interval L 0 k := by
  ext i
  simp


/-- The actual normalized regional rank approximant controls the original
marginal's missing leading mass. The coordinate map is constructed internally.
This is the Ky Fan step in ALVV, arXiv:1602.08828v2, proof of Theorem 4.9,
source lines 1080–1086. -/
theorem one_sub_regional_kyFanNorm_le_twice_error
    {L q : ℕ} (J : Finset (Fin L))
    (ψ φ : EuclideanSpace ℂ (Fin L → Fin q)) (hφ : ‖φ‖ = 1)
    (delta : ℝ) (hdelta1 : delta ≤ 1) (D : ℕ) :
    let beta := fun _ : Fin L ↦ Fin q
    let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
      (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
      (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
    let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm
    Matrix.schmidtRank (WithLp.ofLp (e φ)) ≤ D →
    1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ →
    1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) J ψ).kyFanNorm D ≤
      2 * delta := by
  intro beta tau U Phi Tm e hrank hoverlap
  have hφe : ‖e φ‖ = 1 := by simpa only [LinearIsometryEquiv.norm_map] using hφ
  have hinner : ‖⟪e ψ, e φ⟫_ℂ‖ = ‖⟪φ, ψ⟫_ℂ‖ := by
    rw [e.inner_map_map, norm_inner_symm]
  have hmass := Matrix.normSq_inner_le_kyFanNorm (e ψ) (e φ) hφe D hrank
  rw [hinner] at hmass
  have hactual : Matrix.schmidtCoeffMatrix (WithLp.ofLp (e ψ)) *
      (Matrix.schmidtCoeffMatrix (WithLp.ofLp (e ψ)))ᴴ = Entropy.regionState J ψ :=
    (Submodule.actualRegionSplit_marginal_and_entropy (n := fun _ : Fin L ↦ q) J ψ).1
  have hmass' : ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ≤
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) J ψ).kyFanNorm D := by
    simpa only [hactual] using hmass
  have hsquare := pow_le_pow_left₀ (by linarith only [hdelta1] : 0 ≤ 1 - delta) hoverlap 2
  nlinarith only [hsquare, hmass', sq_nonneg delta]

/-- Uniform missing marginal mass gives one normalized sequential matrix
product state, rather than a collection of cut-dependent vectors. Auxiliary
to ALVV, arXiv:1602.08828v2, Theorem 4.9, source line 1086; the product estimate
is Verstraete--Cirac Proposition 7.1 in the one-dimensional note. -/
theorem exists_unit_mps_of_uniform_prefix_mass
    {L q : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
    (D : ℕ) (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htail : ∀ k ∈ Finset.Ico 1 L,
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm D ≤ delta / (8 * ((L : ℝ) + 1))) :
    ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
      IsOpenMPS L q D (fun x ↦ Φ x) ∧ 1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ ∧
      ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  have hLpos : 0 < (L : ℝ) + 1 := by positivity
  have hcard : ((Finset.Ico 1 L).card : ℝ) ≤ (L : ℝ) + 1 := by
    exact_mod_cast (show (Finset.Ico 1 L).card ≤ L + 1 by rw [Nat.card_Ico]; omega)
  have hsum : (∑ k ∈ Finset.Ico 1 L,
      (1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm D)) ≤ delta / 8 := by
    calc
      _ ≤ (Finset.Ico 1 L).card • (delta / (8 * ((L : ℝ) + 1))) :=
        Finset.sum_le_card_nsmul _ _ _ htail
      _ = ((Finset.Ico 1 L).card : ℝ) * (delta / (8 * ((L : ℝ) + 1))) := by
        rw [nsmul_eq_mul]
      _ ≤ ((L : ℝ) + 1) * (delta / (8 * ((L : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = delta / 8 := by field_simp
  let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
    (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
      (leftBlock L k) ψ).leadingEigenprojection D
  let Φ0 := sequentialTruncation P (L - 1) ψ
  have hmps0 : IsOpenMPS L q D (fun x ↦ Φ0 x) :=
    (isOpenMPS_sequentialTruncation_leadingEigenprojection ψ hψ D).1
  have herr : ‖Φ0 - ψ‖ ^ 2 ≤ delta / 8 :=
    (norm_sequentialTruncation_leadingEigenprojection_sub_sq_le ψ hψ D).trans hsum
  have hdistlt : ‖Φ0 - ψ‖ < 1 := by nlinarith only [herr, hdelta1, norm_nonneg (Φ0 - ψ)]
  have hpos : 0 < ‖Φ0‖ := by
    have hn := norm_sub_norm_le ψ Φ0
    rw [hψ, norm_sub_rev] at hn
    linarith only [hn, hdistlt]
  let Φ : EuclideanSpace ℂ (Fin L → Fin q) := (‖Φ0‖ : ℂ)⁻¹ • Φ0
  have hΦ : ‖Φ‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) (norm_pos_iff.mp hpos)
  have hdist : ‖Φ - ψ‖ ≤ 2 * ‖Φ0 - ψ‖ :=
    norm_inv_norm_smul_sub_le_two_mul hψ (norm_pos_iff.mp hpos)
  have hsq : ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    nlinarith only [hs, herr]
  have hoverlap : 1 - delta ≤ ‖⟪Φ, ψ⟫_ℂ‖ := by
    have heq := norm_sub_sq (𝕜 := ℂ) Φ ψ
    simp only [hΦ, hψ, one_pow, RCLike.re_to_complex] at heq
    have hre := Complex.re_le_norm (⟪Φ, ψ⟫_ℂ)
    nlinarith only [heq, hre, hsq, hdelta]
  exact ⟨Φ, hΦ, hmps0.smul (‖Φ0‖ : ℂ)⁻¹, hoverlap, hsq⟩

end TNLean.MPS.AreaLaw
