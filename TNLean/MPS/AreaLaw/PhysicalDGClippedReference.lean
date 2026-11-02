/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGReferenceSpace

/-!
# One physical reference for all nearby clipped targets

An original-ground-space reference is chosen at the same small accuracy
as the original-to-clipped comparison. It then controls every nearby
clipped target, in both directions, before the interval is chosen. The
clipping error and reference error are separate inputs to the triangle
estimate; neither is replaced by a fixed constant.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and the reference argument, lines 1801–1805.
The actual clipped targets must still be constructed with the stated
accuracy by the physical truncation estimate.

**Scope restriction (reference gap dependence):** The reference rank bound
uses `min gamma 1`; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
No physical cutoff calibration or adaptive probability is asserted here.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- One actual physical MPS reference controls every target mutually close
to the original full ground space at the prescribed small accuracy. It is
chosen before all such targets and retains one all-span MPS bound. The
original-to-clipped accuracy must be separately derived in the physical
application. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670, and lines 1801–1805. -/
theorem exists_physical_dg_common_reference_for_clipped_targets :
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
      ∀ a : ℝ, 0 < a → a ≤ 1 →
      let tau := a ^ 2 / 1048576
      let b := 16 + Real.log (1 / g) +
        Real.log (32 * (r : ℝ) * ((L : ℝ) + 1) / tau)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo tau U G ∧ Submodule.IsCloseTo tau G U ∧
        (∀ v ∈ U, IsOpenMPS L q (r ^ 2 * B) (fun x ↦ v x)) ∧
        4 * tau ≤ a ^ 2 / 16384 ∧
        ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
          Submodule.IsCloseTo tau G T → Submodule.IsCloseTo tau T G →
          Submodule.IsCloseTo (4 * tau) T U ∧ Submodule.IsCloseTo (4 * tau) U T := by
  classical
  obtain ⟨K, hK, hreference⟩ := exists_physical_dg_isOpenMPS_reference_subspace
  refine ⟨K, hK, ?_⟩
  intro L q h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G r g u a ha ha1 tau b
  have htau : 0 < tau := by dsimp only [tau]; positivity
  have htau1 : tau ≤ 1 := by
    have haSq : a ^ 2 ≤ 1 := by nlinarith
    dsimp only [tau]
    linarith
  obtain ⟨B, hB, hlogB, U, hdimU, hUG, hGU, hUMPS⟩ :=
    hreference L q h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap tau htau htau1
  refine ⟨B, hB, hlogB, U, hdimU, hUG, hGU, hUMPS, ?_, ?_⟩
  · dsimp only [tau]
    nlinarith [sq_nonneg a]
  · intro T hGT hTG
    constructor
    · exact (hTG.trans hGU htau.le).of_le (by linarith)
    · exact (hUG.trans hGT htau.le).of_le (by linarith)

end TNLean.MPS.AreaLaw
