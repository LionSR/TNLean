/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.DependentBlockDiagonal
import TNLean.Channel.FixedPoint.FullSupportBlockRetraction

/-!
# Density-block form of the full-support fixed points

Suppose that a positive trace-preserving map has a positive-definite fixed
point and that its trace adjoint satisfies the Schwarz inequality.  The
adjoint Cesàro projection has the weighted partial-trace form supplied by the
preceding full-support fixed-point decomposition.  Taking its adjoint with
respect to the trace pairing gives the density-block formula for the original
Cesàro projection and identifies its range with the fixed points of the
original map.

Each summand is indexed by the product of the multiplicity index and the
matrix-factor index.  Thus the left partial trace is over the multiplicity
factor, and the Schrödinger-picture summand has the form
$\sigma_k\otimes M_{d_k}(\mathbb C)$.

## Main results

* `IsPositiveMap.exists_block_densities_of_meanErgodicProjection_with_adjoint`:
  the full-support density-block form in the same coordinates as the
  trace-adjoint fixed-point algebra.
* `IsPositiveMap.exists_block_densities_of_meanErgodicProjection`: the
  corresponding Schrödinger-picture statement.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.5,
  Equation (1.40), Theorem 6.14, and Equation (6.63); local sources
  `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 536--570,
  and `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1483--1494.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder Kronecker
open Matrix Finset BigOperators

noncomputable section

namespace Matrix

private theorem trace_density_blockMap_mul_eq
    {K : ℕ} {m d : Fin K → ℕ}
    (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (A B : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
      ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ) :
    Matrix.trace
        ((Matrix.blockDiagonal' fun k ↦
          σ k ⊗ₖ Matrix.partialTraceLeft
            (Matrix.directSumBlockCompression (m := m) (d := d) k B)) * A) =
      Matrix.trace
        (B * (Matrix.blockDiagonal' fun k ↦
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
            Matrix.partialTraceLeft
              (((σ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
                Matrix.directSumBlockCompression (m := m) (d := d) k A))) := by
  classical
  rw [Matrix.trace_blockDiagonal'_mul]
  rw [Matrix.trace_mul_comm, Matrix.trace_blockDiagonal'_mul]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = Matrix.trace
        (Matrix.directSumBlockCompression (m := m) (d := d) k B *
          ((1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
            Matrix.partialTraceLeft
              (((σ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
                Matrix.directSumBlockCompression (m := m) (d := d) k A))) :=
      trace_kronecker_partialTraceLeft_mul_eq (σ k)
        (Matrix.directSumBlockCompression (m := m) (d := d) k A)
        (Matrix.directSumBlockCompression (m := m) (d := d) k B)
    _ = _ := Matrix.trace_mul_comm _ _

end Matrix

variable {D : ℕ}

/-- **Density-block form of the Cesàro projection on full support.**

Let $T:M_D(\mathbb C)\to M_D(\mathbb C)$ be positive and trace preserving,
suppose that $T^*$ satisfies the Schwarz inequality, and let $\rho>0$ satisfy
$T(\rho)=\rho$.  Then the mean-ergodic projection has the block form
\[
  P_T(B)=U\left(\bigoplus_k
    \sigma_k\otimes\operatorname{tr}_{m_k}((U^*BU)_{kk})\right)U^*,
\]
and its range, which equals $\operatorname{Fix}(T)$, is
$U(\bigoplus_k \sigma_k\otimes M_{d_k}(\mathbb C))U^*$.

This is the trace-adjoint calculation in Wolf, Equation (1.40), used in the
proof of Theorem 6.14 and Equation (6.63); local sources
`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 536--570,
and `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1483--1494.

**Scope restriction (full support):** The fixed point is positive definite on
the ambient space.  The subsequent maximal-support reduction and the
complementary zero summand are completed in
`TNLean.Channel.FixedPoint.WolfTheorem614`; their construction is recorded in
`docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`.

**Convention (factor order):** Wolf writes the algebra and density factors in
the opposite order.  Each summand is indexed by
`Fin (m k) × Fin (d k)`, so `Matrix.partialTraceLeft` traces the multiplicity
factor and the density block is $\sigma_k\otimes M_{d_k}(\mathbb C)$. -/
theorem IsPositiveMap.exists_block_densities_of_meanErgodicProjection_with_adjoint
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : T ρ = ρ) :
    let P := LinearMap.meanErgodicProjection (𝕜 := ℂ)
      (E := Matrix (Fin D) (Fin D) ℂ) T
      (hT.hasBoundedOrbits_of_tracePreserving hTP)
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ A : Matrix (Fin D) (Fin D) ℂ,
          Matrix.traceAdjointMap T A = A ↔
            ∃ Y : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
              star U * A * U = Matrix.reindex e e
                (Matrix.blockDiagonal' fun k ↦
                  (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ Y k)) ∧
        (∀ k, (σ k).PosSemidef) ∧ (∀ k, (σ k).trace = 1) ∧
        (∀ B, P B = U * Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦
            σ k ⊗ₖ Matrix.partialTraceLeft
              (Matrix.directSumBlockCompression (m := m) (d := d) k
                (Matrix.reindex e.symm e.symm (star U * B * U)))) * star U) ∧
        ∀ B, T B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
  dsimp only
  let P := LinearMap.meanErgodicProjection (𝕜 := ℂ)
    (E := Matrix (Fin D) (Fin D) ℂ) T
    (hT.hasBoundedOrbits_of_tracePreserving hTP)
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, hBlock, hσpos, hσtrace, hFormula⟩ :=
    hT.exists_block_densities_of_adjoint_meanErgodicProjection hTP hSchwarz hρ hρfix
  have hPFormula : ∀ B, P B = U * Matrix.reindex e e
      (Matrix.blockDiagonal' fun k ↦
        σ k ⊗ₖ Matrix.partialTraceLeft
          (Matrix.directSumBlockCompression (m := m) (d := d) k
            (Matrix.reindex e.symm e.symm (star U * B * U)))) * star U := by
    intro B
    let Φ := Matrix.unitaryReindexLinearEquiv e U hU
    let F : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ →
        Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ :=
      fun A ↦ Matrix.blockDiagonal' fun k ↦
        (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
          Matrix.partialTraceLeft
            (((σ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
              Matrix.directSumBlockCompression (m := m) (d := d) k A)
    let G : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ →
        Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ :=
      fun B ↦ Matrix.blockDiagonal' fun k ↦
        σ k ⊗ₖ Matrix.partialTraceLeft
          (Matrix.directSumBlockCompression (m := m) (d := d) k B)
    change P B = _
    rw [show U * Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦
            σ k ⊗ₖ Matrix.partialTraceLeft
              (Matrix.directSumBlockCompression (m := m) (d := d) k
                (Matrix.reindex e.symm e.symm (star U * B * U)))) * star U =
        Φ.symm (G (Φ B)) by
      simp only [Φ, G, Matrix.unitaryReindexLinearEquiv_apply,
        Matrix.unitaryReindexLinearEquiv_symm_apply]]
    refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
      (M := P B - Φ.symm (G (Φ B)))).1 ?_)
    intro A
    rw [Matrix.sub_mul, Matrix.trace_sub]
    apply sub_eq_zero.mpr
    have hPdouble : Matrix.traceAdjointMap (Matrix.traceAdjointMap P) B = P B :=
      LinearMap.congr_fun (Matrix.traceAdjointMap_traceAdjointMap P) B
    calc
      Matrix.trace (P B * A) =
          Matrix.trace (Matrix.traceAdjointMap (Matrix.traceAdjointMap P) B * A) := by
        rw [hPdouble]
      _ = Matrix.trace (B * Matrix.traceAdjointMap P A) :=
        Matrix.trace_traceAdjointMap_mul (Matrix.traceAdjointMap P) B A
      _ = Matrix.trace (B * Φ.symm (F (Φ A))) := by
        rw [hFormula A]
        simp only [Φ, F, Matrix.unitaryReindexLinearEquiv_apply,
          Matrix.unitaryReindexLinearEquiv_symm_apply]
      _ = Matrix.trace (Φ.symm (F (Φ A)) * B) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (F (Φ A) * Φ B) :=
        Matrix.trace_unitaryReindexLinearEquiv_symm_mul e U hU _ _
      _ = Matrix.trace (Φ B * F (Φ A)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (G (Φ B) * Φ A) := by
        exact (Matrix.trace_density_blockMap_mul_eq σ (Φ A) (Φ B)).symm
      _ = Matrix.trace (Φ.symm (G (Φ B)) * A) :=
        (Matrix.trace_unitaryReindexLinearEquiv_symm_mul e U hU _ _).symm
  refine ⟨K, d, m, e, U, σ, hU, hd, hm, hBlock, hσpos, hσtrace, hPFormula, ?_⟩
  intro B
  let Φ := Matrix.unitaryReindexLinearEquiv e U hU
  let G : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
        ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ →
      Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
        ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ :=
    fun B ↦ Matrix.blockDiagonal' fun k ↦
      σ k ⊗ₖ Matrix.partialTraceLeft
        (Matrix.directSumBlockCompression (m := m) (d := d) k B)
  rw [← hT.meanErgodicProjection_apply_eq_self_iff_of_tracePreserving hTP B]
  constructor
  · intro hPB
    refine ⟨fun k ↦ Matrix.partialTraceLeft
      (Matrix.directSumBlockCompression (m := m) (d := d) k (Φ B)), ?_⟩
    have hpcoord : P B = Φ.symm (G (Φ B)) := by
      simpa only [Φ, G, Matrix.unitaryReindexLinearEquiv_apply,
        Matrix.unitaryReindexLinearEquiv_symm_apply] using hPFormula B
    have hcoord : Φ B = G (Φ B) := by
      apply Φ.symm.injective
      rw [LinearEquiv.symm_apply_apply]
      exact hPB.symm.trans hpcoord
    calc
      star U * B * U = Matrix.reindex e e (Φ B) := by
        ext i j
        simp [Φ]
      _ = Matrix.reindex e e (G (Φ B)) := congrArg (Matrix.reindex e e) hcoord
      _ = _ := by rfl
  · rintro ⟨X, hX⟩
    have hcoord : Φ B = Matrix.blockDiagonal' (fun k ↦ σ k ⊗ₖ X k) := by
      rw [Matrix.unitaryReindexLinearEquiv_apply, hX]
      ext i j
      simp
    have hG : G (Φ B) = Φ B := by
      rw [hcoord]
      simp only [G]
      congr 1
      funext k
      have hcomp : Matrix.directSumBlockCompression (m := m) (d := d) k
            (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ X j) = σ k ⊗ₖ X k := by
        ext i j
        simp [Matrix.directSumBlockCompression, Matrix.blockDiagonal'_apply_eq]
      rw [hcomp, Matrix.partialTraceLeft_kronecker, hσtrace]
      simp
    calc
      P B = Φ.symm (G (Φ B)) := by
        simpa only [Φ, G, Matrix.unitaryReindexLinearEquiv_apply,
          Matrix.unitaryReindexLinearEquiv_symm_apply] using hPFormula B
      _ = Φ.symm (Φ B) := by rw [hG]
      _ = B := Φ.symm_apply_apply B

/-- **Schrödinger fixed-point blocks in the coordinates of the adjoint algebra.**

This is the Schrödinger-picture projection of
`IsPositiveMap.exists_block_densities_of_meanErgodicProjection_with_adjoint`.
It retains the established API for clients that do not need the simultaneous
trace-adjoint fixed-point characterization. -/
theorem IsPositiveMap.exists_block_densities_of_meanErgodicProjection
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : T ρ = ρ) :
    let P := LinearMap.meanErgodicProjection (𝕜 := ℂ)
      (E := Matrix (Fin D) (Fin D) ℂ) T
      (hT.hasBoundedOrbits_of_tracePreserving hTP)
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (σ k).PosSemidef) ∧ (∀ k, (σ k).trace = 1) ∧
        (∀ B, P B = U * Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦
            σ k ⊗ₖ Matrix.partialTraceLeft
              (Matrix.directSumBlockCompression (m := m) (d := d) k
                (Matrix.reindex e.symm e.symm (star U * B * U)))) * star U) ∧
        ∀ B, T B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
  dsimp only
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, -, hσpos, hσtrace, hFormula, hFixed⟩ :=
    hT.exists_block_densities_of_meanErgodicProjection_with_adjoint
      hTP hSchwarz hρ hρfix
  exact ⟨K, d, m, e, U, σ, hU, hd, hm, hσpos, hσtrace, hFormula, hFixed⟩
