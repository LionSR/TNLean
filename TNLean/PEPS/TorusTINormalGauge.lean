import TNLean.PEPS.TorusOrientationGauge
import TNLean.PEPS.TorusEdgeGauge

/-!
# The translation-invariant gauge family on the torus

This file assembles the translationally invariant gauge reduction of the normal PEPS Fundamental
Theorem on the discrete torus (arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498).  A
translation-invariant tensor has orientation-uniform bond dimensions
(`torusUniformBondDim_of_translationInvariant`); on a torus every edge is interior, so the
per-edge gauge of the edge blocking is available at every edge
(`TNLean/PEPS/TorusEdgeGauge.lean`), and translation invariance carries the reference blocking
datum to every edge of each orientation class (`TNLean/PEPS/TorusBlockingData.lean`).  The
assembly into one horizontal and one vertical matrix, up to per-edge scalars, is the
orientation-uniform selection `isTorusOrientationUniformGaugeFamilyModScalar_of_classAgreement`.

The one genuinely remaining input is the **per-edge class agreement**: that each per-edge gauge
agrees, up to a nonzero scalar, with the reference orientation matrix transported to that edge.
This is the source's *"X and Y are unique up to a multiplicative constant"* across an orientation
class, derived from the per-edge uniqueness (`edgeGauge_unique_scalar`) together with the
transfer-map covariance under translation.  Establishing that covariance from the
blocked-region-weight covariance (`regionBlockedWeight_transport`) is the residual obligation
recorded as obligation 6 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`; this capstone
takes the per-edge agreement as a hypothesis and discharges the assembly above it.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1449--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The translation-invariant gauge family on the torus, up to per-edge scalars.**

For a translation-invariant tensor `A`, with reference horizontal and vertical matrices `Xh`,
`Xv` chosen at a reference edge of each orientation class, a per-edge gauge family `X` that
agrees on every horizontal (vertical) edge with `Xh` (`Xv`) transported to that edge up to a
nonzero scalar is orientation uniform up to scalars: it is described by the single horizontal
matrix `Xh` and the single vertical matrix `Xv`, with the per-edge scalars the residual
multiplicative freedom.

The orientation-uniform bond dimensions come from translation invariance
(`torusUniformBondDim_of_translationInvariant`); the per-edge agreement hypotheses `hH`, `hV`
are the class-agreement input, the residual obligation recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, obligation 6.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isTorusOrientationUniformGaugeFamilyModScalar_of_translationInvariant
    {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A)
    (X : (e : Edge (torusGraph width height)) →
      GL (Fin (A.bondDim e)) ℂ)
    (Xh : GL (Fin (A.bondDim (torusRightEdge 0))) ℂ)
    (Xv : GL (Fin (A.bondDim (torusUpEdge 0))) ℂ)
    (cH cV : Edge (torusGraph width height) → ℂˣ)
    (hH : ∀ (e : Edge (torusGraph width height)) (he : IsHorizontalTorusEdge e),
      (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
        (cH e : ℂ) • (glReindex
          ((torusUniformBondDim_of_translationInvariant hA).horizontal he).symm Xh :
          Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ))
    (hV : ∀ (e : Edge (torusGraph width height)) (he : IsVerticalTorusEdge e),
      (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
        (cV e : ℂ) • (glReindex
          ((torusUniformBondDim_of_translationInvariant hA).vertical he).symm Xv :
          Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)) :
    IsTorusOrientationUniformGaugeFamilyModScalar
      (torusUniformBondDim_of_translationInvariant hA) X :=
  isTorusOrientationUniformGaugeFamilyModScalar_of_classAgreement
    (torusUniformBondDim_of_translationInvariant hA) X Xh Xv cH cV hH hV

end PEPS
end TNLean
