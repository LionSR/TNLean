/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGGlobalApproximation
import TNLean.MPS.AreaLaw.MPSReferenceSpace

/-!
# A physical ground-space reference for collective trimming

Apply the global matrix product approximation to a genuine orthonormal
basis of the full ground space, at accuracy `epsilon / (2*r)`.
Their fixed span has dimension `r`, is mutually `epsilon`-close to the
original ground space, and every vector in the span has an exact bond
bound `r^2*B`. This supplies the reference-space step in ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805.
The viable-space merge construction is a separate result. The sharp
coefficient-one entropy theorem concerns the original ground space.

**Scope restriction (gap dependence):** The quantitative bound uses
`min gamma 1`; comparison with the printed inverse-gap rate is established
for `0 < gamma ≤ 1`. See
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- A fixed nearby reference subspace for the full physical ground space has
one exact matrix product bond bound for every vector. The original ground
basis and its approximants are constructed internally. The per-basis global
accuracy is `epsilon/(2*r)`, giving a total squared error at most `epsilon/4`.
This supports the use of the area law in collective trimming in ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805; no merge-tree
construction or entropy bound for the whole reference space is asserted. -/
theorem exists_physical_dg_isOpenMPS_reference_subspace :
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
  obtain ⟨K, hK, hglobal⟩ := exists_physical_dg_normalized_isOpenMPS_approximation
  refine ⟨K, hK, ?_⟩
  intro L q h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G r g u
    epsilon hepsilon hepsilon1 b
  have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr hG
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith only [hrR]
  let deltaBasis := epsilon / (2 * (r : ℝ))
  have hdelta : 0 < deltaBasis := by dsimp only [deltaBasis]; positivity
  have hdelta1 : deltaBasis ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (r : ℝ))).2
    linarith only [hepsilon1, hrR]
  obtain ⟨B, hB, hlogB, hvectors⟩ :=
    hglobal L q h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      deltaBasis hdelta hdelta1
  have hratio : 16 * ((L : ℝ) + 1) / deltaBasis =
      32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon := by
    dsimp only [deltaBasis]
    field_simp [ne_of_gt hepsilon, ne_of_gt hr0]; ring
  rw [hratio] at hlogB
  let basis : OrthonormalBasis (Fin r) ℂ G := stdOrthonormalBasis ℂ G
  have hunit (i : Fin r) : ‖(basis i : EuclideanSpace ℂ (Fin L → Fin q))‖ = 1 := by
    rw [Submodule.norm_coe]
    exact basis.norm_eq_one i
  choose phi _hphiUnit hphiMPS _hphiOverlap hphiError using
    fun i : Fin r ↦ hvectors (basis i) (basis i).property (hunit i)
  have hsum : ∑ i : Fin r,
      ‖phi i - (basis i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤ epsilon / 4 := by
    calc
      _ ≤ ∑ _i : Fin r, deltaBasis / 2 := Finset.sum_le_sum fun i _ ↦ hphiError i
      _ = (r : ℝ) * (deltaBasis / 2) := by simp only [Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = epsilon / 4 := by
        dsimp only [deltaBasis]
        field_simp [ne_of_gt hr0]; ring
  obtain ⟨U, hdim, hUG, hGU, hUMPS⟩ :=
    exists_reference_subspace_of_isOpenMPS_basis_approximations G basis phi epsilon
      hepsilon.le hepsilon1 hsum hphiMPS
  refine ⟨B, hB, hlogB, U, hdim, hUG, hGU, ?_⟩
  intro v hv
  simpa only [r, pow_two, mul_assoc] using hUMPS v hv

end TNLean.MPS.AreaLaw
