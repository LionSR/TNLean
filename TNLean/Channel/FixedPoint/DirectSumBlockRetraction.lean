/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TraceReindex
import TNLean.Channel.FixedPoint.DirectSumExtension
import TNLean.Channel.FixedPoint.TraceAdjointDensityBlocks

/-!
# Density-block form for fixed points on finite sums of matrix algebras

The canonical full-matrix extension of a map on a finite direct sum may be
reindexed by a finite equivalence and then classified by the full-support
fixed-point theorem. This file carries out that last change of coordinates and
returns the density-block description to the original direct-sum index space.

This is the fixed-point step used in arXiv:1606.00608, Appendix C.4,
lines 1980--1995. The channel hypotheses for the particular transported sector
maps are separate from the result proved here.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators Kronecker

noncomputable section

namespace Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α]
variable [Fintype β] [DecidableEq β]

/-- Conjugate a matrix endomorphism by the simultaneous reindexing of its row
and column coordinates. -/
noncomputable def reindexEndomorphism (e : α ≃ β)
    (T : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) :
    Matrix β β ℂ →ₗ[ℂ] Matrix β β ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ e e).conj T

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp]
theorem reindexEndomorphism_apply (e : α ≃ β)
    (T : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) (A : Matrix β β ℂ) :
    reindexEndomorphism e T A =
      Matrix.reindex e e (T (Matrix.reindex e.symm e.symm A)) := by
  rfl

omit [DecidableEq α] [DecidableEq β] in
private theorem trace_reindex_mul (e : α ≃ β) (A : Matrix α α ℂ)
    (B : Matrix β β ℂ) :
    (Matrix.reindex e e A * B).trace =
      (A * Matrix.reindex e.symm e.symm B).trace := by
  have hB : B = Matrix.reindex e e (Matrix.reindex e.symm e.symm B) := by
    simpa only [Matrix.coe_reindexLinearEquiv,
      Matrix.symm_reindexLinearEquiv] using
      (Matrix.reindexLinearEquiv ℂ ℂ e e).apply_symm_apply B |>.symm
  have hmul : Matrix.reindex e e A *
      Matrix.reindex e e (Matrix.reindex e.symm e.symm B) =
      Matrix.reindex e e (A * Matrix.reindex e.symm e.symm B) := by
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ e e e A _
  calc
    (Matrix.reindex e e A * B).trace =
        (Matrix.reindex e e A *
          Matrix.reindex e e (Matrix.reindex e.symm e.symm B)).trace := by
      exact congrArg Matrix.trace (congrArg (Matrix.reindex e e A * ·) hB)
    _ = (Matrix.reindex e e
          (A * Matrix.reindex e.symm e.symm B)).trace := by rw [hmul]
    _ = (A * Matrix.reindex e.symm e.symm B).trace := Matrix.trace_reindex e _

omit [DecidableEq α] [DecidableEq β] in
private theorem reindex_conjugation (e : α ≃ β)
    (U A : Matrix α α ℂ) :
    Matrix.reindex e e (star U * A * U) =
      star (Matrix.reindex e e U) * Matrix.reindex e e A *
        Matrix.reindex e e U := by
  have hstar : Matrix.reindex e e (star U) =
      star (Matrix.reindex e e U) := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  calc
    Matrix.reindex e e (star U * A * U) =
        Matrix.reindex e e (star U * A) * Matrix.reindex e e U :=
      (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e (star U * A) U).symm
    _ = (Matrix.reindex e e (star U) * Matrix.reindex e e A) *
        Matrix.reindex e e U := by
      exact congrArg (· * Matrix.reindex e e U)
        (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e (star U) A).symm
    _ = _ := by rw [hstar]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
private theorem reindex_symm_reindex (e : α ≃ β) (A : Matrix α α ℂ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
  simpa only [Matrix.coe_reindexLinearEquiv,
    Matrix.symm_reindexLinearEquiv] using
    (Matrix.reindexLinearEquiv ℂ ℂ e e).symm_apply_apply A

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
private theorem reindex_reindex {γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    (A : Matrix α α ℂ) :
    Matrix.reindex f f (Matrix.reindex e e A) =
      Matrix.reindex (e.trans f) (e.trans f) A := by
  rfl

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Positivity is invariant under a simultaneous change of the matrix index
set. -/
theorem IsPositiveMap.reindexEndomorphism
    {T : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ} (hT : IsPositiveMap T)
    (e : α ≃ β) : IsPositiveMap (reindexEndomorphism e T) := by
  intro A hA
  rw [reindexEndomorphism_apply]
  exact (hT _ (hA.submatrix e)).submatrix e.symm

omit [DecidableEq α] [DecidableEq β] in
/-- Trace preservation is invariant under a simultaneous change of the matrix
index set. -/
theorem IsTracePreservingMap.reindexEndomorphism
    {T : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hT : IsTracePreservingMap T) (e : α ≃ β) :
    IsTracePreservingMap (reindexEndomorphism e T) := by
  intro A
  rw [reindexEndomorphism_apply, Matrix.trace_reindex, hT, Matrix.trace_reindex]

omit [DecidableEq α] [DecidableEq β] in
/-- The trace adjoint commutes with simultaneous reindexing of matrix
coordinates. -/
theorem traceAdjointMap_reindexEndomorphism (e : α ≃ β)
    (T : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) :
    Matrix.traceAdjointMap (reindexEndomorphism e T) =
      reindexEndomorphism e (Matrix.traceAdjointMap T) := by
  apply LinearMap.ext
  intro A
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  calc
    (Matrix.traceAdjointMap (reindexEndomorphism e T) A * B).trace =
        (A * reindexEndomorphism e T B).trace :=
      Matrix.trace_traceAdjointMap_mul _ _ _
    _ = (Matrix.reindex e.symm e.symm A *
          T (Matrix.reindex e.symm e.symm B)).trace := by
      rw [reindexEndomorphism_apply]
      rw [Matrix.trace_mul_comm, trace_reindex_mul, Matrix.trace_mul_comm]
    _ = (Matrix.traceAdjointMap T (Matrix.reindex e.symm e.symm A) *
          Matrix.reindex e.symm e.symm B).trace :=
      (Matrix.trace_traceAdjointMap_mul _ _ _).symm
    _ = (reindexEndomorphism e (Matrix.traceAdjointMap T) A * B).trace := by
      rw [reindexEndomorphism_apply]
      rw [trace_reindex_mul]

omit [DecidableEq α] [DecidableEq β] in
/-- The Schwarz inequality is invariant under a simultaneous change of the
matrix index set. -/
theorem IsSchwarzMap.reindexEndomorphism
    {T : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ} (hT : IsSchwarzMap T)
    (e : α ≃ β) : IsSchwarzMap (reindexEndomorphism e T) := by
  intro A
  let Φ := Matrix.reindexLinearEquiv ℂ ℂ e e
  have h := hT (Φ.symm A)
  have h' : (Φ (T ((Φ.symm A)ᴴ * Φ.symm A) -
      T (Φ.symm A)ᴴ * T (Φ.symm A))).PosSemidef := by
    exact h.submatrix e.symm
  have hstar : Φ.symm Aᴴ = (Φ.symm A)ᴴ := by
    simp only [Φ, Matrix.symm_reindexLinearEquiv,
      Matrix.coe_reindexLinearEquiv, Matrix.conjTranspose_reindex]
  have hmul : Φ.symm (Aᴴ * A) = (Φ.symm A)ᴴ * Φ.symm A := by
    calc
      Φ.symm (Aᴴ * A) = Φ.symm Aᴴ * Φ.symm A := by
        exact (Matrix.reindexLinearEquiv_mul ℂ ℂ
          e.symm e.symm e.symm Aᴴ A).symm
      _ = (Φ.symm A)ᴴ * Φ.symm A := by rw [hstar]
  change (Φ (T (Φ.symm (Aᴴ * A))) -
    Φ (T (Φ.symm Aᴴ)) * Φ (T (Φ.symm A))).PosSemidef
  rw [hmul, hstar]
  have hprod : Φ (T (Φ.symm A)ᴴ * T (Φ.symm A)) =
      Φ (T (Φ.symm A)ᴴ) * Φ (T (Φ.symm A)) := by
    exact (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e _ _).symm
  rw [map_sub, hprod] at h'
  exact h'

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Positive definiteness is invariant under a simultaneous change of the
matrix index set. -/
theorem PosDef.reindex (e : α ≃ β) {A : Matrix α α ℂ} (hA : A.PosDef) :
    (Matrix.reindex e e A).PosDef :=
  hA.submatrix e.symm.injective

end Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]

/-- **Density-block form for fixed points on a finite direct sum.**

Let `T` be a positive map of a finite sum of full matrix algebras that
preserves the total trace. If the direct-sum trace adjoint satisfies the
Schwarz inequality and `T` has a positive-definite fixed family, then its
fixed points have the density-block form obtained from Wolf's Theorem 6.14.

This is the finite-index classification step used in arXiv:1606.00608,
Appendix C.4, lines 1980--1995. The hypotheses for the particular sector map
in that argument are not asserted here.

**Scope restriction (full support):** The fixed family is positive definite on
every summand. The maximal-support reduction and complementary zero summand
for a full matrix algebra are completed in
`TNLean.Channel.FixedPoint.WolfTheorem614`; the present direct-sum theorem
retains its explicit full-support hypothesis. See
`docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`. -/
theorem IsPositiveDirectSumMap.exists_block_densities_of_fixedPoints
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsPositiveDirectSumMap T)
    (hTP : IsTracePreservingDirectSumMap T)
    (hSchwarz : IsSchwarzDirectSumMap (Matrix.directSumTraceAdjointMap T))
    {ρ : ∀ k, Matrix (n k) (n k) ℂ} (hρ : ∀ k, (ρ k).PosDef)
    (hρfix : T ρ = ρ) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ ((k : ι) × n k))
      (U : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup ((k : ι) × n k) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (σ k).PosSemidef) ∧ (∀ k, (σ k).trace = 1) ∧
        ∀ A, T A = A ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * directSumDiagonalEmbedding A * U =
              Matrix.reindex e e
                (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
  let s := (k : ι) × n k
  let efin : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let TExt := directSumExtension T
  let TFin := reindexEndomorphism efin TExt
  let ρExt := directSumDiagonalEmbedding ρ
  let ρFin := Matrix.reindex efin efin ρExt
  have hTFin : IsPositiveMap TFin := by
    exact IsPositiveMap.reindexEndomorphism
      hT.directSumExtension_isPositiveMap efin
  have hTPFin : IsTracePreservingMap TFin := by
    exact IsTracePreservingMap.reindexEndomorphism
      hTP.directSumExtension_isTracePreservingMap efin
  have hSchwarzExt : IsSchwarzMap (Matrix.traceAdjointMap TExt) := by
    exact hSchwarz.traceAdjointMap_directSumExtension_isSchwarzMap hT
  have hSchwarzFin : IsSchwarzMap (Matrix.traceAdjointMap TFin) := by
    rw [traceAdjointMap_reindexEndomorphism]
    exact IsSchwarzMap.reindexEndomorphism hSchwarzExt efin
  have hρExt : ρExt.PosDef := directSumDiagonalEmbedding_posDef hρ
  have hρFin : ρFin.PosDef := hρExt.reindex efin
  have hρExtFix : TExt ρExt = ρExt := by
    exact (directSumExtension_embedding_eq_self_iff T ρ).2 hρfix
  have hρFinFix : TFin ρFin = ρFin := by
    let Φ := Matrix.reindexLinearEquiv ℂ ℂ efin efin
    change Φ (TExt (Φ.symm (Φ ρExt))) = Φ ρExt
    rw [Φ.symm_apply_apply, hρExtFix]
  obtain ⟨K, d, m, eClass, UFin, σ, hUFin, hd, hm, hσpos, hσtrace,
      _, hfixed⟩ :=
    hTFin.exists_block_densities_of_meanErgodicProjection
      hTPFin hSchwarzFin hρFin hρFinFix
  let U := Matrix.reindex efin.symm efin.symm UFin
  let e := eClass.trans efin.symm
  have hU : U ∈ Matrix.unitaryGroup s ℂ := by
    rw [Matrix.mem_unitaryGroup_iff'] at hUFin ⊢
    have hstar : star U = Matrix.reindex efin.symm efin.symm (star UFin) := by
      simp only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
    rw [hstar]
    have hmul : Matrix.reindex efin.symm efin.symm (star UFin) *
        Matrix.reindex efin.symm efin.symm UFin =
        Matrix.reindex efin.symm efin.symm (star UFin * UFin) := by
      exact Matrix.reindexLinearEquiv_mul ℂ ℂ
        efin.symm efin.symm efin.symm _ _
    rw [hmul, hUFin]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · have heij : efin i ≠ efin j := fun h ↦ hij (efin.injective h)
      simp [hij, heij]
  refine ⟨K, d, m, e, U, σ, hU, hd, hm, hσpos, hσtrace, ?_⟩
  intro A
  rw [← directSumExtension_embedding_eq_self_iff T A]
  have hcoord : TExt (directSumDiagonalEmbedding A) =
        directSumDiagonalEmbedding A ↔
      TFin (Matrix.reindex efin efin (directSumDiagonalEmbedding A)) =
        Matrix.reindex efin efin (directSumDiagonalEmbedding A) := by
    let Φ := Matrix.reindexLinearEquiv ℂ ℂ efin efin
    change TExt (directSumDiagonalEmbedding A) = directSumDiagonalEmbedding A ↔
      Φ (TExt (Φ.symm (Φ (directSumDiagonalEmbedding A)))) =
        Φ (directSumDiagonalEmbedding A)
    rw [Φ.symm_apply_apply]
    exact Φ.injective.eq_iff.symm
  rw [hcoord, hfixed]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    calc
      star U * directSumDiagonalEmbedding A * U =
          Matrix.reindex efin.symm efin.symm
            (star UFin * Matrix.reindex efin efin
              (directSumDiagonalEmbedding A) * UFin) := by
        dsimp only [U]
        rw [reindex_conjugation]
        rw [reindex_symm_reindex]
      _ = Matrix.reindex efin.symm efin.symm
          (Matrix.reindex eClass eClass
            (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)) := by rw [hX]
      _ = Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
        exact reindex_reindex eClass efin.symm _
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    have hUback : Matrix.reindex efin efin U = UFin := by
      dsimp only [U]
      simpa only [Equiv.symm_symm] using
        reindex_symm_reindex efin.symm UFin
    calc
      star UFin * Matrix.reindex efin efin
          (directSumDiagonalEmbedding A) * UFin =
          Matrix.reindex efin efin
            (star U * directSumDiagonalEmbedding A * U) := by
        rw [reindex_conjugation]
        rw [hUback]
      _ = Matrix.reindex efin efin
          (Matrix.reindex e e
            (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)) := by rw [hX]
      _ = Matrix.reindex eClass eClass
          (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
        rw [reindex_reindex]
        congr 1
        ext x
        simp [e]

end Matrix
