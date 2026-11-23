/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.ScaledNormality
import TNLean.MPS.Tensor.Gauge.GaugeUniqueness
import TNLean.MPS.Tensor.GroundSpace.ChainGroundSpace
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonianBasic
import TNLean.MPS.Transfer.Irreducible.PerronGauge
import TNLean.MPS.Transfer.Primitivity.Equivalence

/-!
# The normalized primitive gauge of a normal tensor

A normal tensor need not be trace preserving, and its transfer map need not have
spectral radius one.  Both normalizations are taken "without loss of generality"
by the sources: Nachtergaele, arXiv:cond-mat/9410110, rewrites the generalized
valence-bond construction so that equations (3.2a) and (3.2b) hold (lines
1394--1435), and Pérez-García, Verstraete, Wolf, and Cirac, arXiv:quant-ph/0608197,
open the proof of Theorem 4, the translation-invariant canonical form
(statement lines 742--761, proof lines 765--770), by assuming that the spectral
radius of the transfer map is one and gauging by the square root of a positive
fixed point.

This file performs that step. From a normal tensor \(A\) it produces a positive
scalar \(\zeta\), a virtual gauge \(X\), and the rescaled gauged tensor
\(B^i=\zeta\,XA^iX^{-1}\) which carries the trace-preserving normalization
\(\sum_i (B^i)^\dagger B^i=\mathbb 1\) together with a positive definite fixed
point of its transfer map: exactly the data bundled by the complementary
transfer-map gap predicate.  Rescaling and gauging leave the local MPS spaces,
the parent interaction, and the periodic chain ground spaces untouched.

## Main results

* `MPSTensor.exists_hasComplementaryFixedPointGap_gauge_of_isNormal`: the normalized primitive
  gauge of a normal tensor.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines
  1394--1435.
* D. Pérez-García, F. Verstraete, M. Wolf, J. I. Cirac, arXiv:quant-ph/0608197,
  Theorem 4, lines 742--770.
* M. Sanz, D. Pérez-García, M. Wolf, J. I. Cirac, arXiv:0909.5347,
  Proposition 3.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **The normalized primitive gauge of a normal tensor.**

For a normal tensor \(A\) there are a nonzero scalar \(\zeta\), a virtual gauge,
and a matrix \(\rho>0\) such that the rescaled gauged tensor \(B\) satisfies
\(\sum_i (B^i)^\dagger B^i=\mathbb 1\) and has \(\rho\) as the distinguished
fixed point of a complementary transfer-map gap.  The matrix product vectors of
\(B\) are those of \(A\) rescaled by \(\zeta^N\), and the local MPS spaces, the
parent interactions, and the periodic chain ground spaces of \(A\) and \(B\)
coincide.

This is the step taken without loss of generality at
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435, and at
arXiv:quant-ph/0608197, Theorem 4, proof lines 765--770: rescale
so that the transfer map has spectral radius one and gauge by the square root of
a positive fixed point.  The gauge here is built from the Perron eigenvector of
the adjoint transfer map, giving the trace-preserving orientation, which is what
conditions 1 and 2 of that theorem (statement lines 752--758) become after the
further gauge by the square root of the matrix \(\Lambda\) appearing in
condition 2.

Normality supplies the irreducibility that the Perron--Frobenius eigenvector
requires, through the direction of arXiv:0909.5347, Proposition 3, that imposes
no normalization on the tensor, and it survives both the rescaling and the
gauge; the trace-preserving representative is therefore normal as well, and the
full equivalence of Proposition 3, which does assume the trace-preserving
normalization, returns the complementary transfer-map gap with a positive
definite fixed point. -/
theorem exists_hasComplementaryFixedPointGap_gauge_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) :
    ∃ (B : MPSTensor d D) (ζ : ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      ζ ≠ 0 ∧
      GaugeEquiv (ζ • A) B ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) ∧
      Kraus.HasComplementaryFixedPointGap B ρ ∧ ρ.PosDef ∧
      (∀ L : ℕ, groundSpace A L = groundSpace B L) ∧
      (∀ L : ℕ, parentInteraction A L = parentInteraction B L) ∧
      (∀ L N : ℕ, chainGroundSpace A L N = chainGroundSpace B L N) := by
  classical
  have hIrr : Kraus.IsIrreducibleFamily (d := d) (D := D) A :=
    isIrreducibleFamily_of_isNormal A hA
  obtain ⟨B, r, σ, _hσ, hr, _hBdef, hBnorm, hBgauge⟩ :=
    exists_tp_data_of_irreducible A hIrr (exists_apply_ne_zero_of_isNormal hA)
  set ζ : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ) with hζ_def
  have hζ : ζ ≠ 0 := by
    have hsqrt : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
    simpa [hζ_def] using inv_ne_zero hsqrt
  have hgauge : GaugeEquiv (ζ • A) B := hBgauge
  have hNormalScaled : Kraus.IsNormal (ζ • A) := (isNormal_smul_iff hζ A).2 hA
  have hNormalB : Kraus.IsNormal B := isNormal_of_gaugeEquiv hNormalScaled hgauge
  obtain ⟨ρ, hPrim, hρ⟩ :=
    exists_hasComplementaryFixedPointGap_posDef_of_isNormal B hBnorm hNormalB
  have hGS : ∀ L : ℕ, groundSpace A L = groundSpace B L := by
    intro L
    rw [← groundSpace_smul_eq A ζ hζ L]
    exact hgauge.groundSpace_eq L
  refine ⟨B, ζ, ρ, hζ, hgauge, ?_, hPrim, hρ, hGS, ?_, ?_⟩
  · intro N τ
    rw [← hgauge.sameMPV N τ]
    simp only [mpv, coeff]
    change Matrix.trace (Kraus.evalWord (fun i => ζ • A i) (List.ofFn τ)) = _
    rw [Kraus.evalWord_smul]
    simp [List.length_ofFn, Matrix.trace_smul]
  · exact fun L => parentInteraction_eq_of_groundSpace_eq (hGS L)
  · exact fun L N => chainGroundSpace_eq_of_groundSpace_eq (hGS L)

end MPSTensor
