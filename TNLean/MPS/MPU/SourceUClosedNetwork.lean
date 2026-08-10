/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MatchingContractions
import TNLean.MPS.MPU.SourceUBoundary

/-!
# Closed source-u networks

This file gives two exact closed-network formulas used in the proof of
`lemuisometry` from arXiv:1703.09188, lines 545--557. The first writes an
ordinary source-u Gram entry as an output-first double-layer letter whose
remaining bond is closed by the second-cut range projector. The second writes
the normalized `(K+2)`-site output-tail contraction as a trace of two retained
output-first letters followed by the Kth normalized-diagonal power.

The retained output pair `q` is unstarred and `p` is starred. Doubled bonds are
ordered `(ket, bra)`. These formulas do not identify the two closed networks,
insert a rank-one tail projector, or assert an ambient coisometry.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- The weighted first-cut projector acts identically on the first source cut. -/
private theorem sourceX₁_range_weighted_sourceCutM₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceX₁ U ρ hρ * (sourceX₁ U ρ hρ)ᴴ *
        sourceWeight (d := d) ρ * sourceCutM₁ U = sourceCutM₁ U := by
  rw [show sourceX₁ U ρ hρ * (sourceX₁ U ρ hρ)ᴴ *
      sourceWeight (d := d) ρ * sourceCutM₁ U =
      sourceX₁ U ρ hρ * ((sourceX₁ U ρ hρ)ᴴ *
        sourceWeight (d := d) ρ * sourceCutM₁ U) by
    simp only [Matrix.mul_assoc]]
  rw [← sourceY₁_eq_sourceX₁_conjTranspose_mul_weight_mul_sourceCutM₁ U ρ hρ]
  exact (sourceCutM₁_eq_sourceX₁_mul_sourceY₁ U ρ hρ).symm

/-- The weighted cut recovery identifies the Gram of `Y₁` with the weighted raw cut Gram. -/
private theorem sourceY₁_conjTranspose_mul_self
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    (sourceY₁ U ρ hρ)ᴴ * sourceY₁ U ρ hρ =
      (sourceCutM₁ U)ᴴ * sourceWeight (d := d) ρ * sourceCutM₁ U := by
  rw [sourceY₁_eq_sourceX₁_conjTranspose_mul_weight_mul_sourceCutM₁ U ρ hρ,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    (sourceWeight_posDef (d := d) hρ).isHermitian.eq]
  have hrange : sourceX₁ U ρ hρ * ((sourceX₁ U ρ hρ)ᴴ *
      (sourceWeight (d := d) ρ * sourceCutM₁ U)) = sourceCutM₁ U := by
    simpa only [Matrix.mul_assoc] using
      sourceX₁_range_weighted_sourceCutM₁ U ρ hρ
  simp only [Matrix.mul_assoc, hrange]

/-- Exact closed cut-projector formula for the ordinary source-u Gram entry. -/
private theorem sourceU_gram_eq_closed_cut
    {d D : ℕ} (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (p q : Fin d × Fin d) :
    (∑ lr : Fin ℓ[U] × Fin r[U],
      sourceU U ρ hρ lr q * star (sourceU U ρ hρ lr p)) =
      ∑ β : Fin D, ∑ δ : Fin D,
        ((sourceCutM₁ U)ᴴ * sourceWeight (d := d) ρ * sourceCutM₁ U)
            (p.1, δ) (q.1, β) *
          (sourceX₂ U * (sourceX₂ U)ᴴ) (β, q.2) (δ, p.2) := by
  classical
  rw [Fintype.sum_prod_type]
  change (∑ l : Fin ℓ[U], ∑ r : Fin r[U],
    (∑ β : Fin D, sourceY₁ U ρ hρ r (q.1, β) * sourceX₂ U (β, q.2) l) *
      star (∑ δ : Fin D,
        sourceY₁ U ρ hρ r (p.1, δ) * sourceX₂ U (δ, p.2) l)) = _
  simp_rw [star_sum, star_mul]
  simp_rw [Finset.sum_mul_sum]
  rw [← sourceY₁_conjTranspose_mul_self U ρ hρ]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul_sum]
  have hreorder (l : Fin ℓ[U]) (r : Fin r[U]) (β δ : Fin D) :
      sourceY₁ U ρ hρ r (q.1, β) * sourceX₂ U (β, q.2) l *
          (star (sourceX₂ U (δ, p.2) l) *
            star (sourceY₁ U ρ hρ r (p.1, δ))) =
        star (sourceY₁ U ρ hρ r (p.1, δ)) * sourceY₁ U ρ hρ r (q.1, β) *
          (sourceX₂ U (β, q.2) l * star (sourceX₂ U (δ, p.2) l)) := by
    ring
  simp_rw [← hreorder]
  let f := fun (l : Fin ℓ[U]) (r : Fin r[U]) (β δ : Fin D) ↦
    sourceY₁ U ρ hρ r (q.1, β) * sourceX₂ U (β, q.2) l *
      (star (sourceX₂ U (δ, p.2) l) *
        star (sourceY₁ U ρ hρ r (p.1, δ)))
  change (∑ l, ∑ r, ∑ β, ∑ δ, f l r β δ) =
    ∑ β, ∑ δ, ∑ r, ∑ l, f l r β δ
  calc
    _ = ∑ l, ∑ β, ∑ r, ∑ δ, f l r β δ := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = ∑ β, ∑ l, ∑ r, ∑ δ, f l r β δ := Finset.sum_comm
    _ = ∑ β, ∑ l, ∑ δ, ∑ r, f l r β δ := by
      apply Finset.sum_congr rfl
      intro β _
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = ∑ β, ∑ δ, ∑ l, ∑ r, f l r β δ := by
      apply Finset.sum_congr rfl
      intro β _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro β _
      apply Finset.sum_congr rfl
      intro δ _
      exact Finset.sum_comm

/-- The source-u Gram as one output-first double-layer letter closed by the
weighted left boundary and the range projector of the second source cut.
The doubled bonds have order `(ket, bra)`.

Source: arXiv:1703.09188, equation `uUnitary`, lines 545--556. -/
theorem sourceU_gram_apply_eq_closed_output_letter
    {d D : ℕ} (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (p q : Fin d × Fin d) :
    (∑ lr : Fin ℓ[U] × Fin r[U],
      sourceU U ρ hρ lr q * star (sourceU U ρ hρ lr p)) =
      ∑ β : Fin D, ∑ δ : Fin D, ∑ γ : Fin D, ∑ α : Fin D,
        ρ α γ *
          doubleLayerTensor (physicalAdjointTensor U) q.1 p.1
            (finProdFinEquiv (γ, α)) (finProdFinEquiv (β, δ)) *
          (sourceX₂ U * (sourceX₂ U)ᴴ) (β, q.2) (δ, p.2) := by
  rw [sourceU_gram_eq_closed_cut U ρ hρ p q]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro δ _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sourceWeight,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type,
    sourceCutM₁_apply,
    doubleLayerTensor_physicalAdjointTensor_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A normalized diagonal power is the normalized sum of diagonal open words. -/
private theorem normalizedDiagonal_pow_eq_sum_evalWord
    [NeZero d] (W : MPOTensor d D) (K : ℕ) :
    normalizedDiagonal W ^ K =
      ((d : ℂ)⁻¹) ^ K •
        ∑ τ : Fin K → Fin d, evalWord W (List.ofFn τ) (List.ofFn τ) := by
  classical
  simp only [normalizedDiagonal, contractPhysical, Matrix.one_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    evalWord_ofFn]
  rw [smul_pow]
  congr 1
  simpa [List.ofFn_const] using
    (List.prod_ofFn_sum (fun _ : Fin K ↦ fun i : Fin d ↦ W i i))

/-- The normalized output-tail contraction is a fully closed output-first
double-layer trace, with retained letters in `(q,p)` order.

Source: arXiv:1703.09188, equation `uUnitary`, lines 550--556. -/
theorem normalized_mpo_output_tail_eq_closed_doubleLayer_trace
    [NeZero d] (U : MPOTensor d D) (K : ℕ) (p q : Fin d × Fin d) :
    ((d : ℂ)⁻¹) ^ K *
        ∑ τ : Fin K → Fin d, ∑ η : Fin (K + 2) → Fin d,
          mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) η *
            star (mpo U (K + 2)
              ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ)) η) =
      Matrix.trace
        (doubleLayerTensor (physicalAdjointTensor U) q.1 p.1 *
          doubleLayerTensor (physicalAdjointTensor U) q.2 p.2 *
            normalizedDiagonal (doubleLayerTensor (physicalAdjointTensor U)) ^ K) := by
  classical
  let W := doubleLayerTensor (physicalAdjointTensor U)
  have hη (σ τ : Fin (K + 2) → Fin d) :
      (∑ η : Fin (K + 2) → Fin d,
        mpo U (K + 2) σ η * star (mpo U (K + 2) τ η)) =
        mpo W (K + 2) σ τ := by
    have h := congrArg (fun M ↦ M σ τ)
      (mpo_doubleLayerTensor (physicalAdjointTensor U) (K + 2))
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      mpo_physicalAdjointTensor, star_star] at h
    exact h.symm
  simp_rw [hη]
  have hword (τ : Fin K → Fin d) :
      mpo W (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))
          ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ)) =
        Matrix.trace (W q.1 p.1 * W q.2 p.2 *
          evalWord W (List.ofFn τ) (List.ofFn τ)) := by
    rw [mpo_apply, mpoMatrixEntry]
    simp only [finAddTwoArrowEquiv_symm_apply, List.ofFn_succ, evalWord_cons,
      Fin.cons_zero, Fin.cons_succ]
    rw [← Matrix.mul_assoc]
  simp_rw [hword]
  change ((d : ℂ)⁻¹) ^ K *
      ∑ τ : Fin K → Fin d,
        Matrix.trace (W q.1 p.1 * W q.2 p.2 *
          evalWord W (List.ofFn τ) (List.ofFn τ)) =
    Matrix.trace (W q.1 p.1 * W q.2 p.2 * normalizedDiagonal W ^ K)
  rw [normalizedDiagonal_pow_eq_sum_evalWord W K]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_sum, Matrix.trace_sum]

end MPOTensor
