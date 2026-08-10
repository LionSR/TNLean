/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.DoubleLayerContraction
import TNLean.MPS.MPU.MatchingContractions
import TNLean.MPS.MPU.SourceUOpenTail

/-!
# Forward open-tail packaging for the source tensor u

This file packages the forward kernel occurring inside the complete source-$u$
network in arXiv:1703.09188, Figure `II_uUnitary.png` and Lemma
`lemuisometry` (lines 536--557). The normalized internal sum is an output-first
double-layer letter followed by a power of its normalized diagonal. It also
records the two source-cut range projections used when moving the cut in the
closed network.

No declaration identifies the ambient open-tail coefficient with the identity
or asserts an ambient coisometry. In particular, the range projections below
apply only to the source-cut matrices $M_1$ and $M_2$.

**Local fix (range-restricted graphical contraction):** the source diagram
is read as a contraction of the complete external network, not as an ambient
matrix identity. This clarification and the remaining closed-network
obligation are recorded in
`docs/paper-gaps/mpu_sourceu_range_restriction.tex`.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

private lemma sum_rotate_five {A B C D E R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [AddCommMonoid R] (f : A → B → C → D → E → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, f a b c d e := by
  let equiv : ((((A × B) × C) × D) × E) ≃ ((((D × E) × A) × B) × C) := {
    toFun := fun x ↦ ((((x.1.2, x.2), x.1.1.1.1), x.1.1.1.2), x.1.1.2)
    invFun := fun x ↦ ((((x.1.1.2, x.1.2), x.2), x.1.1.1.1), x.1.1.1.2)
    left_inv := by rintro ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩; rfl
    right_inv := by rintro ⟨⟨⟨⟨d, e⟩, a⟩, b⟩, c⟩; rfl
  }
  have h := Fintype.sum_equiv equiv
    (fun x ↦ f x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2)
    (fun x ↦ f x.1.1.2 x.1.2 x.2 x.1.1.1.1 x.1.1.1.2)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

/-- The normalized forward kernel before applying the outer $X_1$ and $X_2$
factors. It contains exactly one factor $d^{-K}$.

Source: arXiv:1703.09188, equation `uUnitary`, lines 545--556. -/
noncomputable def sourceUForwardKernel (K : ℕ) (i i' : Fin d)
    (β β' α α' : Fin D) : ℂ :=
  ((d : ℂ)⁻¹) ^ K *
    ∑ τ : Fin K → Fin d, ∑ ζ : Fin K → Fin d, ∑ j₂ : Fin d,
      (U i j₂ * evalWord U (List.ofFn τ) (List.ofFn ζ)) β α *
        star ((U i' j₂ * evalWord U (List.ofFn τ) (List.ofFn ζ)) β' α')

/-- An entry of the $K$th normalized output-layer diagonal is the normalized
sum over a common output word and an arbitrary contracted input word.

Source: arXiv:1703.09188, Figure `II_uUnitary.png` and equation `uUnitary`,
lines 545--556. -/
theorem normalizedDiagonal_outputLayer_pow_apply [NeZero d]
    (K : ℕ) (γ γ' α α' : Fin D) :
    (normalizedDiagonal (doubleLayerTensor (physicalAdjointTensor U)) ^ K)
        (finProdFinEquiv (γ, γ')) (finProdFinEquiv (α, α')) =
      ((d : ℂ)⁻¹) ^ K * ∑ τ : Fin K → Fin d, ∑ ζ : Fin K → Fin d,
        evalWord U (List.ofFn τ) (List.ofFn ζ) γ α *
          star (evalWord U (List.ofFn τ) (List.ofFn ζ) γ' α') := by
  classical
  rw [← normalizedDiagonal_blockTensor K]
  simp only [normalizedDiagonal, contractPhysical, Matrix.one_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    blockTensor_apply, Matrix.smul_apply, smul_eq_mul]
  have hdim : (MPSTensor.blockPhysDim d K : ℂ)⁻¹ = ((d : ℂ)⁻¹) ^ K := by
    rw [MPSTensor.blockPhysDim_eq_pow, Nat.cast_pow, inv_pow]
  rw [hdim]
  congr 1
  have hsum := (MPSTensor.decodeBlockEquiv d K).sum_comp
    (fun τ ↦ evalWord (doubleLayerTensor (physicalAdjointTensor U))
      (List.ofFn τ) (List.ofFn τ))
  simp only [MPSTensor.decodeBlockEquiv_apply] at hsum
  simp only [MPSTensor.wordOfBlock]
  rw [hsum]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro τ _
  rw [doubleLayerTensor, evalWord_mulTensor]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.sum_apply, Matrix.kronecker_apply]
  apply Finset.sum_congr rfl
  intro ζ _
  rw [evalWord_physicalAdjointTensor, evalWord_physicalAdjointTensor]
  · change star (star (evalWord U (List.ofFn τ) (List.ofFn ζ) γ α)) *
        star (evalWord U (List.ofFn τ) (List.ofFn ζ) γ' α') = _
    rw [star_star]
  · simp
  · simp

/-- The forward internal sum is an output-first double-layer letter followed
by the $K$th power of its normalized diagonal.

The unstarred bond component precedes the starred component in both doubled
bond indices. This is the forward, rather than conjugate-transpose-reversed,
chain needed inside the complete source-$u$ network.

Source: arXiv:1703.09188, Figure `II_uUnitary.png` and equation `uUnitary`,
lines 545--556. -/
theorem sourceUForwardKernel_eq_outputLayer_mul_normalizedDiagonal_pow
    [NeZero d] (K : ℕ) (i i' : Fin d) (β β' α α' : Fin D) :
    sourceUForwardKernel U K i i' β β' α α' =
      (doubleLayerTensor (physicalAdjointTensor U) i i' *
        normalizedDiagonal (doubleLayerTensor (physicalAdjointTensor U)) ^ K)
          (finProdFinEquiv (β, β')) (finProdFinEquiv (α, α')) := by
  classical
  unfold sourceUForwardKernel
  rw [Matrix.mul_apply, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp_rw [normalizedDiagonal_outputLayer_pow_apply U K]
  simp only [doubleLayerTensor_physicalAdjointTensor_apply, Matrix.mul_apply,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [sum_rotate_five, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro γ' _
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro ζ _
  apply Finset.sum_congr rfl
  intro j₂ _
  ring

/-- The weighted $X_1X_1^\dagger$ projection fixes the first source-cut
matrix. This is a range identity on $M_1$, not an ambient coisometry.

Source: arXiv:1703.09188, equations `SVDforms2`, `Y1Y1X1X1`, and `X1X2b`,
lines 479--528. -/
theorem sourceX₁_mul_conjTranspose_mul_weight_mul_sourceCutM₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceX₁ U ρ hρ * (sourceX₁ U ρ hρ)ᴴ * sourceWeight (d := d) ρ *
        sourceCutM₁ U = sourceCutM₁ U := by
  calc
    _ = sourceX₁ U ρ hρ *
        ((sourceX₁ U ρ hρ)ᴴ * sourceWeight (d := d) ρ * sourceCutM₁ U) := by
      simp only [Matrix.mul_assoc]
    _ = sourceX₁ U ρ hρ * sourceY₁ U ρ hρ := by
      rw [sourceY₁_eq_sourceX₁_conjTranspose_mul_weight_mul_sourceCutM₁]
    _ = _ := (sourceCutM₁_eq_sourceX₁_mul_sourceY₁ U ρ hρ).symm

/-- The $X_2X_2^\dagger$ projection fixes the second source-cut matrix. This
is a range identity on $M_2$, not the false ambient equation
$X_2X_2^\dagger=1$.

Source: arXiv:1703.09188, equations `SVDforms2`, `Y1Y1X1X1`, and `X1X2b`,
lines 479--528. -/
theorem sourceX₂_mul_conjTranspose_mul_sourceCutM₂ :
    sourceX₂ U * (sourceX₂ U)ᴴ * sourceCutM₂ U = sourceCutM₂ U := by
  rw [Matrix.mul_assoc, ← sourceY₂_eq_sourceX₂_conjTranspose_mul_sourceCutM₂]
  exact (sourceCutM₂_eq_sourceX₂_mul_sourceY₂ U).symm

/-- Expanding both periodic MPO entries through $X_1$, the source tensor $u$,
$X_2$, and the forward open tail gives the normalized source-$u$ metric. MPU
output coisometry evaluates this complete expression to the retained physical
Kronecker delta. The entry indexed by $q$ is unstarred and the entry indexed by
$p$ is starred. The theorem evaluates the displayed expansion directly; it
does not fold the sum through the separately defined open-tail coefficient
or identify the ordinary Gram matrix `sourceUᴴ * sourceU`.

Source: arXiv:1703.09188, Figure `II_uUnitary.png`, equation `uUnitary`, and
Lemma `lemuisometry`, lines 536--557. -/
theorem IsMPU.normalized_sourceU_openTail_metric [NeZero d]
    {U : MPOTensor d D} (hU : IsMPU U)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (K : ℕ)
    (p q : Fin d × Fin d) :
    ((d : ℂ)⁻¹) ^ K *
        ∑ τ : Fin K → Fin d, ∑ j : Fin d × Fin d, ∑ ζ : Fin K → Fin d,
          (∑ α : Fin D, ∑ r : Fin r[U], ∑ l : Fin ℓ[U],
            ∑ β : Fin D, ∑ i : Fin d,
              sourceX₁ U ρ hρ (α, j.1) r * sourceU U ρ hρ (l, r) q *
                star (sourceX₂ U (β, i) l) *
                  (U i j.2 * evalWord U (List.ofFn τ) (List.ofFn ζ)) β α) *
          star (∑ α' : Fin D, ∑ r' : Fin r[U], ∑ l' : Fin ℓ[U],
            ∑ β' : Fin D, ∑ i' : Fin d,
              sourceX₁ U ρ hρ (α', j.1) r' * sourceU U ρ hρ (l', r') p *
                star (sourceX₂ U (β', i') l') *
                  (U i' j.2 * evalWord U (List.ofFn τ) (List.ofFn ζ)) β' α') =
      if p = q then 1 else 0 := by
  classical
  simp_rw [← mpo_finAddTwo_eq_sum_sourceX₁_sourceU_sourceX₂_openTail
    U ρ hρ K q, ← mpo_finAddTwo_eq_sum_sourceX₁_sourceU_sourceX₂_openTail
    U ρ hρ K p]
  have hreindex (τ : Fin K → Fin d) :
      (∑ j : Fin d × Fin d, ∑ ζ : Fin K → Fin d,
        mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))
            ((finAddTwoArrowEquiv (Fin d) K).symm (j, ζ)) *
          star (mpo U (K + 2)
            ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))
            ((finAddTwoArrowEquiv (Fin d) K).symm (j, ζ)))) =
        ∑ η : Fin (K + 2) → Fin d,
          mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) η *
            star (mpo U (K + 2)
              ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ)) η) := by
    let f : (Fin d × Fin d) × (Fin K → Fin d) → ℂ := fun x ↦
      mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ))
          ((finAddTwoArrowEquiv (Fin d) K).symm x) *
        star (mpo U (K + 2)
          ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))
          ((finAddTwoArrowEquiv (Fin d) K).symm x))
    calc
      _ = ∑ x, f x := (Fintype.sum_prod_type f).symm
      _ = _ := (finAddTwoArrowEquiv (Fin d) K).symm.sum_comp
        (fun η : Fin (K + 2) → Fin d ↦
          mpo U (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) η *
            star (mpo U (K + 2)
              ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ)) η))
  rw [← hU.normalized_mpo_tail_coisometry K p q]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  exact hreindex τ

end MPOTensor
