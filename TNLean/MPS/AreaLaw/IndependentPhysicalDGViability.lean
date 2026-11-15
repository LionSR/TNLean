/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IndependentPhysicalDGPower

/-!
# Physical improving families at independent scales

The actual clipped polynomial family is applied to the physical low cluster
with independent threshold and window scales. The numerical filter condition
is explicit; spectral bases, supported tensor factors and the original ground
space are constructed from the nearest-neighbour terms. This supports ALVV,
arXiv:1602.08828v2, Corollary 4.6 and Theorem 4.9, source line 1080.

**Local fix (closed spectral cutoffs):** The full original ground space is
retained as documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
-/

open scoped BigOperators Kronecker TensorProduct ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The actual long-interval polynomial family improves every viable subspace
at the independently chosen threshold and window length. The scalar filter
bound is a numerical condition; no rank, overlap, tensor or spectral-basis
hypothesis is supplied. Auxiliary to ALVV, arXiv:1602.08828v2,
Corollary 4.6 and the proof of Theorem 4.9, source line 1080. -/
theorem exists_independent_long_middle_actual_dg_family :
    ∀ (m q ell : ℕ) (t g epsilon Delta : ℝ), 2 ≤ q → q ≤ m →
      1 ≤ ell → 21 ≤ t → 0 < g → g ≤ 1 → 0 < epsilon → epsilon ≤ 1 →
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤
        epsilon * g / 1000000 →
      (∀ R : ℝ, 0 < R → R ≤ 3 * t + 4 * (ell : ℝ) →
        (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R))) ^ 2 ≤ Delta) →
      let D : ℕ := (m * ell ^ 2) ^ (22 * ell)
      ∀ (L p r : ℕ), p ≤ r → r ≤ L → 4 * ell < r - p →
      let Jtarget := interval L p r
      let β := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv β Jtarget).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration β Jtargetᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration β Jtarget) ℂ)).repr
      let Tcoord := U.trans Phi.symm
      let Tm := Tcoord.trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration β Jtargetᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration β Jtarget)))
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      mu ∈ spectrum ℝ H →
      (∀ x ∈ spectrum ℝ H, x = mu ∨ mu + g ≤ x) →
      ∃ (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
        (F : Fin (D ^ 2) → EuclideanSpace ℂ (Jtarget → Fin q) →L[ℂ]
          EuclideanSpace ℂ (Jtarget → Fin q)),
        Submodule.IsCloseTo (epsilon / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (epsilon / 200 : ℝ) G T ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ (Jtarget → Fin q))) (δ : ℝ),
          Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ (Jtarget → Fin q))
            (F := EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)) δ S
            (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
              (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)))) → δ < 1 →
          let grow := ⨆ i : Fin (D ^ 2), S.map (F i : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
            Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ (Jtarget → Fin q))
              (F := EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q))
              (Delta / (1 - δ) ^ 2) grow
              (T.map (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ]
                (EuclideanSpace ℂ (Jtarget → Fin q) ⊗[ℂ]
                  EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q)))) := by
  classical
  intro m q ell t g epsilon Delta hq hqm hell ht hg hg1 hepsilon hepsilon1 htail hfilter
    D L p r hpr hrL hlong Jtarget β tau U Phi Tcoord Tm h hs h0 h1 mu H hH G hmu hgap
  obtain ⟨T, N, CW, hN, hTG, hGT, hdim, hpower⟩ :=
    exists_independent_long_middle_actual_dg_word_family m q ell t g epsilon Delta
      hq hqm hell ht hg hg1 hepsilon hepsilon1 htail hfilter
      L p r hpr hrL hlong h hs h0 h1 mu hmu hgap
  obtain ⟨_f, F, _hF, _hzero, hspan⟩ :=
    Submodule.exists_clm_family_extension_of_card_le
      (by simpa only [Fintype.card_fin] using hN) CW
  refine ⟨T, F, hTG, hGT, hdim, ?_⟩
  intro S δ hS hδ grow
  obtain ⟨hdimension, hviable⟩ := hpower 1 S δ hS hδ
  have hwordspan :
      (⨆ w : Fin 1 → Fin N,
        S.map (List.ofFn (fun j ↦ CW (w j))).prod.toLinearMap) =
      ⨆ i : Fin N, S.map (CW i).toLinearMap := by
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    exact (show Function.Surjective (fun w : Fin 1 → Fin N ↦ w 0) from
      fun i ↦ ⟨fun _ ↦ i, rfl⟩).iSup_comp
        (fun i : Fin N ↦ S.map (CW i).toLinearMap)
  rw [hwordspan] at hdimension hviable
  constructor
  · change Module.finrank ℂ
        (↥((⨆ i : Fin (D ^ 2), S.map (F i).toLinearMap) :
          Submodule ℂ (EuclideanSpace ℂ (Jtarget → Fin q)))) ≤
        D ^ 2 * Module.finrank ℂ S
    rw [hspan S]
    simpa only [pow_one] using hdimension
  · change Submodule.IsViable (𝕜 := ℂ)
      (E := EuclideanSpace ℂ (Jtarget → Fin q))
      (F := EuclideanSpace ℂ (↥(Jtargetᶜ) → Fin q))
      (Delta / (1 - δ) ^ 2)
      (⨆ i : Fin (D ^ 2), S.map (F i).toLinearMap)
      (T.map Tm.toLinearEquiv.toLinearMap)
    rw [hspan S]
    simpa only [pow_one] using hviable
end TNLean.MPS.AreaLaw
