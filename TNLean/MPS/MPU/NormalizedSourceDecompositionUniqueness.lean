/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceDecompositionUniqueness

/-!
# Unitary comparison of normalized source decompositions

FBC25, arXiv:2502.20257, Lemma `lem:deco` (lines 1052–1066) gives reciprocal
positive rescalings and unitary comparisons between two source decompositions.
When both second-cut left factors are isometries, the positive rescaling is one.
This corollary states that additional normalization explicitly; it is not a
replacement for the unrestricted decomposition lemma.
-/

open scoped Matrix BigOperators
open Matrix

private theorem real_smul_isometry_eq_one
    {α β : Type*} [Fintype α] [DecidableEq β] [Nonempty β]
    (A : Matrix α β ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hA : A.IsIsometry) (hδA : ((δ : ℂ) • A).IsIsometry) : δ = 1 := by
  have hA' : Aᴴ * A = 1 := hA
  have hδA' : (((δ : ℂ) • A)ᴴ) * ((δ : ℂ) • A) = 1 := hδA
  have hmat : ((δ : ℂ) * star (δ : ℂ)) • (1 : Matrix β β ℂ) = 1 := by
    simpa only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hA'] using hδA'
  let b : β := Classical.choice ‹Nonempty β›
  have hcomplex : (δ : ℂ) * star (δ : ℂ) = 1 := by
    have h := congrArg (fun M : Matrix β β ℂ => M b b) hmat
    simpa [Matrix.smul_apply] using h
  have hreal : δ * δ = 1 := by
    apply Complex.ofReal_injective
    simpa using hcomplex
  nlinarith

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

/-- Two source decompositions whose second-cut left factors are isometries differ
by unitary matrices, without scalar rescaling.

This is a normalized corollary of FBC25, arXiv:2502.20257, Lemma `lem:deco`
(lines 1052–1066). The factorization and one-sided-inverse hypotheses are those
of `exists_reciprocal_unitary_source_gauges`. Only the unitarity of the two
literal source $u$ contractions is needed. The two isometry hypotheses eliminate
the reciprocal positive scalar; no canonical form, weighted normalization, or
physical-adjoint simplicity is assumed. -/
theorem exists_unitary_source_gauges_of_isometric_second_factors
    {X₁ Xt₁ : Matrix (Fin d × Fin D) (Fin r[U]) ℂ}
    {Y₁ Yt₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ}
    {X₂ Xt₂ : Matrix (Fin D × Fin d) (Fin ℓ[U]) ℂ}
    {Y₂ Yt₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ}
    {Lt₁ : Matrix (Fin r[U]) (Fin d × Fin D) ℂ}
    {R₁ : Matrix (Fin D × Fin d) (Fin r[U]) ℂ}
    {Lt₂ : Matrix (Fin ℓ[U]) (Fin D × Fin d) ℂ}
    {R₂ : Matrix (Fin d × Fin D) (Fin ℓ[U]) ℂ}
    (hfac₁ : X₁ * Y₁ = sourceCutM₁ U)
    (hfact₁ : Xt₁ * Yt₁ = sourceCutM₁ U)
    (hfac₂ : X₂ * Y₂ = sourceCutM₂ U)
    (hfact₂ : Xt₂ * Yt₂ = sourceCutM₂ U)
    (hleft₁ : Lt₁ * Xt₁ = 1) (hright₁ : Y₁ * R₁ = 1)
    (hleft₂ : Lt₂ * Xt₂ = 1) (hright₂ : Y₂ * R₂ = 1)
    (hu : Matrix.IsUnitaryBetween
      (fun ((l, r) : Fin ℓ[U] × Fin r[U]) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D, Y₂ l (p, β) * Y₁ r (β, q)))
    (hut : Matrix.IsUnitaryBetween
      (fun ((l, r) : Fin ℓ[U] × Fin r[U]) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D, Yt₂ l (p, β) * Yt₁ r (β, q)))
    (hX₂ : X₂.IsIsometry) (hXt₂ : Xt₂.IsIsometry) :
    ∃ (W₁ : Matrix.unitaryGroup (Fin r[U]) ℂ)
      (W₂ : Matrix.unitaryGroup (Fin ℓ[U]) ℂ),
      Xt₁ = X₁ * (W₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) ∧
      Yt₁ = star (W₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * Y₁ ∧
      Xt₂ = X₂ * (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) ∧
      Yt₂ = star (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * Y₂ := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, 1, ?_, ?_, ?_, ?_⟩
    · ext ⟨i, _⟩ _
      exact Fin.elim0 i
    · ext _ ⟨_, i⟩
      exact Fin.elim0 i
    · ext ⟨_, i⟩ _
      exact Fin.elim0 i
    · ext _ ⟨i, _⟩
      exact Fin.elim0 i
  have hcard := hu.1.card_le _
  have hdpos : 0 < Fintype.card (Fin d × Fin d) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨⟨0, Nat.pos_of_ne_zero hd⟩, ⟨0, Nat.pos_of_ne_zero hd⟩⟩⟩
  have hpos : 0 < Fintype.card (Fin ℓ[U] × Fin r[U]) :=
    lt_of_lt_of_le hdpos hcard
  obtain ⟨l, r⟩ := Fintype.card_pos_iff.mp hpos
  have : Nonempty (Fin ℓ[U]) := ⟨l⟩
  obtain ⟨δ, hδ, W₁, W₂, hXt₁, hYt₁, hXt₂eq, hYt₂, _⟩ :=
    exists_reciprocal_unitary_source_gauges
      hfac₁ hfact₁ hfac₂ hfact₂ hleft₁ hright₁ hleft₂ hright₂ hu hut
  have hW₂ : (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ).IsIsometry := W₂.2.1
  have hprod : (X₂ * (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)).IsIsometry :=
    Matrix.IsIsometry.mul X₂ (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) hX₂ hW₂
  have hscaled : ((δ : ℂ) • (X₂ * (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ))).IsIsometry :=
    hXt₂eq ▸ hXt₂
  have hδone : δ = 1 :=
    real_smul_isometry_eq_one _ δ hδ hprod hscaled
  refine ⟨W₁, W₂, ?_, ?_, ?_, ?_⟩
  · simpa [hδone] using hXt₁
  · simpa [hδone] using hYt₁
  · simpa [hδone] using hXt₂eq
  · simpa [hδone] using hYt₂

end MPOTensor

