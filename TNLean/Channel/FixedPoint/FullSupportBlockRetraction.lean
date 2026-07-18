/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.AbstractAlgebra
import TNLean.Channel.FixedPoint.MeanErgodicAdjoint
import TNLean.Channel.PositiveConditionalExpectationDirectSum

/-!
# Block form of the adjoint fixed-point projection on full support

Let $T$ be positive and trace preserving, suppose that $T^*$ satisfies the
Schwarz inequality, and suppose that $T$ has a positive-definite fixed point.
The trace adjoint of the mean-ergodic projection of $T$ is then a positive
retraction onto the fixed-point star-algebra of $T^*$.  Wolf's classification
of positive retractions therefore gives its weighted partial-trace block form.

This is the full-support part of the proof of Wolf's Theorem 6.14.  Taking the
trace adjoint of the resulting formula identifies the fixed points of $T$;
the general theorem also requires restriction to the support of a
maximum-rank fixed point and the adjoining of the complementary zero block.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
  Equations (1.40), (6.63); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1483--1494.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder Kronecker

noncomputable section

variable {D : ℕ}

/-- **Weighted block form of the adjoint Cesàro projection on full support.**

Let $T:M_D(\mathbb C)\to M_D(\mathbb C)$ be positive and trace preserving,
suppose that $T^*$ satisfies the Schwarz inequality, and let $\rho>0$ satisfy
$T(\rho)=\rho$.  Then the trace adjoint $P_T^*$ of the mean-ergodic projection
is a positive retraction onto $\operatorname{Fix}(T^*)$, and hence has the
weighted partial-trace form of Wolf, Equation (1.40).

This is the full-support retraction step in the proof of Wolf's Theorem 6.14,
local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines
1483--1492.

**Scope restriction (full support):** The general theorem first restricts to
the support of a maximum-rank fixed point and later adjoins its orthogonal
complement as the zero block.  Here the fixed point is assumed positive
definite on the ambient space.  The support reduction and zero-block
construction are documented in
`docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`. -/
theorem IsPositiveMap.exists_block_densities_of_adjoint_meanErgodicProjection
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : T ρ = ρ) :
    let Pstar := Matrix.traceAdjointMap
      (LinearMap.meanErgodicProjection (𝕜 := ℂ)
        (E := Matrix (Fin D) (Fin D) ℂ) T
        (hT.hasBoundedOrbits_of_tracePreserving hTP))
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ A : Matrix (Fin D) (Fin D) ℂ,
          Matrix.traceAdjointMap T A = A ↔
            ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
              star U * A * U = Matrix.reindex e e
                (Matrix.blockDiagonal' fun k ↦
                  (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k)) ∧
        (∀ k, (σ k).PosSemidef) ∧ (∀ k, (σ k).trace = 1) ∧
        ∀ A, Pstar A = U * Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦
            (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
              Matrix.partialTraceLeft
                (((σ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
                  Matrix.directSumBlockCompression (m := m) (d := d) k
                    (Matrix.reindex e.symm e.symm (star U * A * U)))) * star U := by
  dsimp only
  let E := Matrix.traceAdjointMap T
  have hEpos : IsPositiveMap E := hT.traceAdjointMap
  have hEone : E 1 = 1 := by
    simpa only [E] using isTracePreservingMap_iff_traceAdjointMap_one.mp hTP
  have hEschwarz : IsSchwarzMap E := by
    simpa only [E] using hSchwarz
  have hρfix' : Matrix.traceAdjointMap E ρ = ρ := by
    dsimp only [E]
    rw [Matrix.traceAdjointMap_traceAdjointMap, hρfix]
  let S := SchwarzMap.fixedPointsStarSubalgebra E hEpos hEone hEschwarz hρ hρfix'
  have hRetraction :=
    hT.traceAdjoint_meanErgodicProjection_isPositiveUnitalRetraction hTP
  dsimp only at hRetraction
  obtain ⟨hPpos, _, hPidemp, _, hPfixed⟩ := hRetraction
  have hRange (A : Matrix (Fin D) (Fin D) ℂ) :
      Matrix.traceAdjointMap
          (LinearMap.meanErgodicProjection T
            (hT.hasBoundedOrbits_of_tracePreserving hTP)) A ∈ S := by
    dsimp only [S]
    rw [SchwarzMap.mem_fixedPointsStarSubalgebra]
    exact (hPfixed _).mp (hPidemp A)
  have hFix (A : Matrix (Fin D) (Fin D) ℂ) (hA : A ∈ S) :
      Matrix.traceAdjointMap
          (LinearMap.meanErgodicProjection T
            (hT.hasBoundedOrbits_of_tracePreserving hTP)) A = A := by
    dsimp only [S] at hA
    rw [SchwarzMap.mem_fixedPointsStarSubalgebra] at hA
    exact (hPfixed A).mpr hA
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, hBlock, hσpos, hσtrace, hFormula⟩ :=
    S.exists_block_densities_of_positive_retraction
      (Matrix.traceAdjointMap
        (LinearMap.meanErgodicProjection T
          (hT.hasBoundedOrbits_of_tracePreserving hTP)))
      hPpos hRange hFix
  refine ⟨K, d, m, e, U, σ, hU, hd, hm, ?_, hσpos, hσtrace, hFormula⟩
  intro A
  rw [← hBlock A]
  dsimp only [S]
  rw [SchwarzMap.mem_fixedPointsStarSubalgebra]
