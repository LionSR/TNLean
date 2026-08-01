/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.DirectSumExtension
import TNLean.Channel.KrausCPTP

/-!
# Kraus maps between finite sums of matrix algebras

A linear map between two finite sums of full matrix algebras has a canonical
extension between the full matrix algebras on the corresponding direct sums:
retain the diagonal input blocks, apply the original map, and embed the output
as a block-diagonal matrix. This extension commutes with composition.

Complete positivity of a map between the finite sums is expressed by a Kraus
representation of this canonical extension. Consequently, complete positivity
is preserved by composition. For a trace-preserving endomorphism, complete
positivity also gives the Schwarz inequality for its trace adjoint.

These facts supply the finite-direct-sum part of the argument in
arXiv:1606.00608, Appendix C.4, lines 1974--1995. The Kraus representations of
the particular transported vertical-sector maps are separate.

## Main definitions

* `Matrix.directSumMapExtension`: the canonical full-matrix extension of a map
  between two finite sums of matrix algebras.
* `Matrix.IsKrausDirectSumMap`: complete positivity through this extension.
* `Matrix.IsKrausDirectSumMap.map_posSemidef`: complete positivity preserves
  positive-semidefinite families.
-/

open scoped Matrix MatrixOrder ComplexOrder

noncomputable section

namespace Matrix

variable {ι κ τ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype τ] [DecidableEq τ]
variable {n : ι → Type*} {m : κ → Type*} {p : τ → Type*}
variable [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
variable [∀ l, Fintype (p l)] [∀ l, DecidableEq (p l)]

/-- Extend a linear map between finite sums of matrix algebras to the full
matrix algebras on the two direct sums. The extension first retains the
diagonal input blocks and then embeds the output as a block-diagonal matrix.

This is the full-matrix form of the maps between \(\mathcal A_1\) and
\(\mathcal A_2\) in arXiv:1606.00608, Appendix C.4, lines 1974--1995. -/
noncomputable def directSumMapExtension
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)) :
    Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ →ₗ[ℂ]
      Matrix ((j : κ) × m j) ((j : κ) × m j) ℂ :=
  directSumDiagonalEmbedding.comp (T.comp directSumDiagonalCompression)

omit [Fintype ι] [DecidableEq ι] [Fintype κ]
    [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    [(j : κ) → Fintype (m j)] [(j : κ) → DecidableEq (m j)] in
@[simp]
theorem directSumMapExtension_apply
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (A : Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ) :
    directSumMapExtension T A =
      directSumDiagonalEmbedding (T (directSumDiagonalCompression A)) :=
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ]
    [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]
    [(j : κ) → Fintype (m j)] [(j : κ) → DecidableEq (m j)]
    [(l : τ) → Fintype (p l)] [(l : τ) → DecidableEq (p l)] in
/-- Canonical full-matrix extension commutes with composition of maps between
finite sums of matrix algebras. -/
theorem directSumMapExtension_comp
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (S : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ l, Matrix (p l) (p l) ℂ)) :
    directSumMapExtension (S.comp T) =
      (directSumMapExtension S).comp (directSumMapExtension T) := by
  apply LinearMap.ext
  intro A
  change directSumDiagonalEmbedding (S (T (directSumDiagonalCompression A))) =
    directSumDiagonalEmbedding
      (S (directSumDiagonalCompression
        (directSumDiagonalEmbedding (T (directSumDiagonalCompression A)))))
  rw [directSumDiagonalCompression_embedding]

/-- A map between finite sums of full matrix algebras is completely positive when its
canonical full-matrix extension admits a Kraus representation. -/
def IsKrausDirectSumMap
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)) : Prop :=
  IsKrausCP (directSumMapExtension T)

/-- A completely positive map between finite sums of full matrix algebras
sends every positive-semidefinite family to a positive-semidefinite family. -/
theorem IsKrausDirectSumMap.map_posSemidef
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    (hT : IsKrausDirectSumMap T)
    {A : ∀ i, Matrix (n i) (n i) ℂ}
    (hA : ∀ i, (A i).PosSemidef) (j : κ) :
    (T A j).PosSemidef := by
  have hExt :
      (directSumMapExtension T (directSumDiagonalEmbedding A)).PosSemidef :=
    IsKrausCP.map_posSemidef hT (directSumDiagonalEmbedding_posSemidef hA)
  have hj := directSumDiagonalCompression_posSemidef hExt j
  simpa only [directSumMapExtension_apply,
    directSumDiagonalCompression_embedding] using hj

/-- Composition preserves complete positivity for maps between finite sums of
full matrix algebras. -/
theorem IsKrausDirectSumMap.comp
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    {S : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ l, Matrix (p l) (p l) ℂ)}
    (hT : IsKrausDirectSumMap T) (hS : IsKrausDirectSumMap S) :
    IsKrausDirectSumMap (S.comp T) := by
  rw [IsKrausDirectSumMap, directSumMapExtension_comp]
  exact isKrausCP_comp hT hS

section PiMap

variable {q : ι → Type*}
variable [∀ i, Fintype (q i)] [∀ i, DecidableEq (q i)]

/-- A coordinatewise family of completely positive maps determines a completely positive map
between the corresponding finite sums of matrix algebras. -/
theorem isKrausDirectSumMap_piMap
    (T : ∀ i, Matrix (n i) (n i) ℂ →ₗ[ℂ] Matrix (q i) (q i) ℂ)
    (hT : ∀ i, IsKrausCP (T i)) :
    IsKrausDirectSumMap (LinearMap.piMap T) := by
  classical
  choose r A hA using hT
  change IsKrausCP (directSumMapExtension (LinearMap.piMap T))
  rw [show directSumMapExtension (LinearMap.piMap T) = controlledKrausMap r A by
    apply LinearMap.ext
    intro X
    ext ⟨i, b⟩ ⟨j, c⟩
    by_cases hij : i = j
    · subst j
      rw [directSumMapExtension_apply, directSumDiagonalEmbedding_apply,
        Matrix.blockDiagonal'_apply_eq, controlledKrausMap_sameBlock_apply]
      exact congrFun (congrFun (hA i (X.submatrix (Sigma.mk i) (Sigma.mk i))) b) c
    · rw [directSumMapExtension_apply, directSumDiagonalEmbedding_apply,
        Matrix.blockDiagonal'_apply_ne _ _ _ hij,
        controlledKrausMap_apply_of_ne _ _ _ hij]]
  exact rectangularKrausMap_isKrausCP _

end PiMap

omit [Fintype ι] [(i : ι) → Fintype (n i)]
    [(i : ι) → DecidableEq (n i)] in
/-- For an endomorphism of one finite direct sum, the extension between two
finite sums agrees with the canonical endomorphism extension. -/
theorem directSumMapExtension_self
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)) :
    directSumMapExtension T = directSumExtension T :=
  rfl

omit [(i : ι) → DecidableEq (n i)] in
/-- If the canonical full-matrix extension satisfies the Schwarz inequality,
then the original map satisfies the inequality in every direct summand. -/
theorem isSchwarzDirectSumMap_of_directSumExtension_isSchwarzMap
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)}
    (hT : IsSchwarzMap (directSumExtension T)) :
    IsSchwarzDirectSumMap T := by
  intro A i
  have h := hT (directSumDiagonalEmbedding A)
  have hstar : (directSumDiagonalEmbedding A)ᴴ =
      directSumDiagonalEmbedding (fun l ↦ (A l)ᴴ) :=
    (directSumDiagonalEmbedding_conjTranspose A).symm
  have hprod : (directSumDiagonalEmbedding A)ᴴ *
      directSumDiagonalEmbedding A =
        directSumDiagonalEmbedding (fun l ↦ (A l)ᴴ * A l) := by
    rw [hstar, ← directSumDiagonalEmbedding_mul]
    rfl
  rw [hprod, hstar] at h
  simp only [directSumExtension_apply,
    directSumDiagonalCompression_embedding] at h
  rw [← directSumDiagonalEmbedding_mul, ← map_sub] at h
  have hi := directSumDiagonalCompression_posSemidef h i
  simpa only [directSumDiagonalCompression_embedding, Pi.sub_apply,
    Pi.mul_apply] using hi

/-- The trace adjoint of a trace-preserving completely positive endomorphism
of a finite sum of matrix algebras satisfies the Schwarz inequality in every
summand.

This is the direct-sum Kadison--Schwarz implication used for the transported
composites in arXiv:1606.00608, Appendix C.4, lines 1980--1995. -/
theorem IsKrausDirectSumMap.directSumTraceAdjointMap_isSchwarz
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)}
    (hT : IsKrausDirectSumMap T)
    (hTP : IsTracePreservingDirectSumMap T) :
    IsSchwarzDirectSumMap (directSumTraceAdjointMap T) := by
  have hCP : IsCPMap (directSumExtension T) := by
    change IsKrausCP (directSumExtension T)
    rw [← directSumMapExtension_self]
    exact hT
  have h2 : Is2PositiveMap
      (Matrix.traceAdjointMap (directSumExtension T)) :=
    (hCP.isNPositiveMap 2).traceAdjointMap
  have hUnital : KadisonSchwarz.IsUnitalMap
      (Matrix.traceAdjointMap (directSumExtension T)) := by
    change Matrix.traceAdjointMap (directSumExtension T) 1 = 1
    refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
      (M := Matrix.traceAdjointMap (directSumExtension T) 1 - 1)).1 ?_)
    intro X
    simp only [Matrix.sub_mul, Matrix.trace_sub,
      Matrix.trace_traceAdjointMap_mul, Matrix.one_mul]
    exact sub_eq_zero.mpr
      (hTP.directSumExtension_isTracePreservingMap X)
  have hSchwarz : IsSchwarzMap
      (Matrix.traceAdjointMap (directSumExtension T)) := by
    intro X
    have hPos := h2.isPositiveMap
    simpa only [hPos.map_conjTranspose X] using
      kadison_schwarz_2positive
        (Matrix.traceAdjointMap (directSumExtension T)) h2 hUnital X
  rw [traceAdjointMap_directSumExtension] at hSchwarz
  exact isSchwarzDirectSumMap_of_directSumExtension_isSchwarzMap hSchwarz

end Matrix
