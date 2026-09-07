/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import TNLean.Algebra.FinSumPermutation
import TNLean.Algebra.UnitaryKroneckerComparison
import TNLean.MPS.MPU.SourceCuts

/-!
# Uniqueness of the raw source decompositions

FBC25, arXiv:2502.20257, Lemma `lem:deco` (main.tex lines 1052--1066).
The factors are raw matrices on the actual source cuts, not normalized
`SourceFactors` records. Only the unitarity of the two literal $u$ contractions
from clause (b) is used; the unitarity of $v$ is unused. Thus the result has
weaker premises, and applies in particular to the decompositions in the source.
No positive-physical-dimension, clause (c), canonical-form, or weighted
normalization hypothesis is needed; when `d = 0`, the source-cut ranks are zero
and the raw physical matrix equalities are vacuous.
-/

open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

/-- Transport of the raw source $u$ contraction under left multiplication of
its two factors (FBC25, `lem:deco`, lines 1052--1066). The row order is
$\ell\times r$, so the comparison operator is $K_2\otimes K_1$. -/
theorem sourceU_contraction_transport
    {Y₁ Yt₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ}
    {Y₂ Yt₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ}
    {K₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ}
    {K₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ}
    (hY₁ : Yt₁ = K₁ * Y₁) (hY₂ : Yt₂ = K₂ * Y₂) :
    (fun ((l, r) : Fin ℓ[U] × Fin r[U]) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D, Yt₂ l (p, β) * Yt₁ r (β, q)) =
      ((K₂ ⊗ₖ K₁) * Matrix.of
        (fun (l, r) (p, q) ↦ ∑ β : Fin D, Y₂ l (p, β) * Y₁ r (β, q)) :
          Matrix (Fin ℓ[U] × Fin r[U]) (Fin d × Fin d) ℂ) := by
  classical
  subst Yt₁ Yt₂
  ext ⟨l, r⟩ ⟨p, q⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  refine Finset.sum_congr₂ fun l' _ r' _ ↦ ?_
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- Reciprocal unitary gauges for two raw factorizations of the source cuts.

FBC25, arXiv:2502.20257, Lemma `lem:deco` (lines 1052--1066). Only the
$u$ part of clause (b) is required: $v$ unitarity is unused, so these weaker
premises give a stronger result applying to the source. Chosen left inverses
of the tilde $X$ factors and right inverses of the original $Y$ factors suffice.
In positive physical dimension the two unitary contractions force both ranks to
be nonempty internally. In dimension zero, the source cuts have rank zero and
identity gauges with scalar one satisfy the vacuous raw matrix equalities.

The source scalars are $\delta_1=\delta^{-1}$ and $\delta_2=\delta$;
the final equality is exactly $\delta_1\delta_2=1$. The gauges have the
source orientation, with their adjoints acting on the $Y$ factors. -/
theorem exists_reciprocal_unitary_source_gauges
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
        ∑ β : Fin D, Yt₂ l (p, β) * Yt₁ r (β, q))) :
    ∃ (δ : ℝ) (_ : 0 < δ) (W₁ : Matrix.unitaryGroup (Fin r[U]) ℂ)
      (W₂ : Matrix.unitaryGroup (Fin ℓ[U]) ℂ),
      Xt₁ = (δ : ℂ)⁻¹ • (X₁ * (W₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ)) ∧
      Yt₁ = (δ : ℂ) • (star (W₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * Y₁) ∧
      Xt₂ = (δ : ℂ) • (X₂ * (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)) ∧
      Yt₂ = (δ : ℂ)⁻¹ • (star (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * Y₂) ∧
      (δ : ℂ)⁻¹ * (δ : ℂ) = 1 := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, by norm_num, 1, 1, ?_, ?_, ?_, ?_, ?_⟩
    · ext ⟨i, _⟩ _
      exact Fin.elim0 i
    · ext _ ⟨_, i⟩
      exact Fin.elim0 i
    · ext ⟨_, i⟩ _
      exact Fin.elim0 i
    · ext _ ⟨i, _⟩
      exact Fin.elim0 i
    · norm_num
  have hcard := hu.1.card_le _
  have hdpos : 0 < Fintype.card (Fin d × Fin d) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨⟨0, Nat.pos_of_ne_zero hd⟩, ⟨0, Nat.pos_of_ne_zero hd⟩⟩⟩
  have hpos : 0 < Fintype.card (Fin ℓ[U] × Fin r[U]) :=
    lt_of_lt_of_le hdpos hcard
  obtain ⟨l, r⟩ := Fintype.card_pos_iff.mp hpos
  have : Nonempty (Fin r[U]) := ⟨r⟩
  have : Nonempty (Fin ℓ[U]) := ⟨l⟩
  obtain ⟨_, hX₁, hY₁⟩ := Matrix.factorization_comparison_of_one_sided_inverses
    (hfac₁.trans hfact₁.symm) hleft₁ hright₁
  obtain ⟨_, hX₂, hY₂⟩ := Matrix.factorization_comparison_of_one_sided_inverses
    (hfac₂.trans hfact₂.symm) hleft₂ hright₂
  rw [sourceU_contraction_transport hY₁ hY₂] at hut
  have hK := Matrix.IsUnitaryBetween.of_mul_right _ _ hu hut
  have hswap := hK.reindex _ (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  have hK' : ((Lt₁ * X₁) ⊗ₖ (Lt₂ * X₂)).IsUnitaryBetween := by
    convert hswap using 1
    ext ⟨r, l⟩ ⟨r', l'⟩
    simp [Matrix.reindex_apply, mul_comm]
  exact Matrix.exists_reciprocal_unitary_gauges_of_comparison
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp hK') hX₁ hY₁ hX₂ hY₂

end MPOTensor
