/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ProjectivePathInvariance

/-!
# Cohomology along an invertible virtual projective path

The virtual symmetry matrices obtained from an injective matrix product
tensor need not be unitary before choosing a canonical form. Their
continuity and invertibility nevertheless imply that their factor system
cannot change cohomology class at a fixed positive bond dimension.

This is the fixed-dimension virtual argument in Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2, lines 1000–1047. It does not deduce a
continuous virtual family from a physical Hamiltonian path, and does not
treat changes of the minimal bond dimension. The continuous virtual family
is constructed from a continuous fixed-dimension injective tensor family
with exact on-site symmetry in `GlobalVirtualGauge.lean`.

**Scope restriction (fixed bond dimension):** The endpoint invariance
theorem assumes a continuous virtual family of a fixed positive dimension.
It supplies the determinant argument in the separation proof. The passage
from an independent exact MPS ground-state path to compatible continuous
tensor and virtual data, including the changing-support case in Appendix C,
remains to be proved. The distinction
between this MPS argument and arbitrary Hamiltonian paths is recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

namespace MPSTensor

open scoped Matrix

/-- A continuous family of invertible projective matrices has continuous
factor systems. An entry of the product with the adjugate extracts each
factor without choosing a continuous gauge. Source: arXiv:1010.3732,
Section II.F.2, lines 1000–1029. -/
theorem continuous_projectiveFactor_of_invertibleMatrixPath
    {G : Type} [Group G] {D : ℕ} (hD : 0 < D)
    (V : unitInterval → G → Matrix (Fin D) (Fin D) ℂ)
    (ω : unitInterval → G → G → Units ℂ)
    (hV : ∀ g, Continuous fun t => V t g)
    (hdet : ∀ t g, (V t g).det ≠ 0)
    (hmul : ∀ t g h, V t g * V t h = (ω t g h : ℂ) • V t (g * h))
    (g h : G) : Continuous fun t => (ω t g h : ℂ) := by
  let i : Fin D := ⟨0, hD⟩
  have hformula (t : unitInterval) :
      (ω t g h : ℂ) =
        (((V t g * V t h) * (V t (g * h)).adjugate) i i) /
          (V t (g * h)).det := by
    rw [hmul t g h, Matrix.smul_mul, Matrix.mul_adjugate]
    simp [Matrix.smul_apply, hdet]
  have hc : Continuous fun t =>
      (((V t g * V t h) * (V t (g * h)).adjugate) i i) /
        (V t (g * h)).det :=
    ((((hV g).matrix_mul (hV h)).matrix_mul
      (hV (g * h)).matrix_adjugate).matrix_elem i i).div
        (hV (g * h)).matrix_det (fun t => hdet t (g * h))
  exact hc.congr (fun t => (hformula t).symm)

/-- A continuous family of invertible projective matrices of fixed positive
dimension has cohomologous endpoint factor systems. Unitarity is not
required, and continuity is required only in the path parameter, separately
for each group element. Source: arXiv:1010.3732, Section II.F.2,
lines 1000–1063. The virtual family is obtained from fixed-dimension
injective tensor paths in `GlobalVirtualGauge.lean`; the passage from an
independent exact MPS ground-state path remains a separate question. -/
theorem invertible_projectivePath_factor_endpoints_cohomologous
    {G : Type} [Group G] {D : ℕ} (hD : 0 < D)
    (V : unitInterval → G → Matrix (Fin D) (Fin D) ℂ)
    (ω : unitInterval → TNLean.Algebra.ScalarCocycle G)
    (hV : ∀ g, Continuous fun t => V t g)
    (hdet : ∀ t g, (V t g).det ≠ 0)
    (hmul : ∀ t g h, V t g * V t h = (ω t g h : ℂ) • V t (g * h)) :
    (ω 1).CohomologousTo (ω 0) := by
  have hdetMul (t : unitInterval) (g h : G) :
      (V t g).det * (V t h).det =
        (ω t g h : ℂ) ^ D * (V t (g * h)).det := by
    have heq := congrArg Matrix.det (hmul t g h)
    simpa only [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin] using heq
  exact projectiveFactor_endpoints_cohomologous_of_det_path hD ω
    (fun t g => (V t g).det)
    (continuous_projectiveFactor_of_invertibleMatrixPath hD V ω hV hdet hmul)
    (fun g => (hV g).matrix_det) hdet hdetMul

end MPSTensor
