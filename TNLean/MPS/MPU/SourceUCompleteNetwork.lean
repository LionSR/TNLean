/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MatchingContractions
import TNLean.MPS.MPU.SourceVIsometry

/-!
# The complete network for the paper source gate u

This file follows the contraction in CPSV17 Lemma `lemuisometry`.  The source
gate is the staggered contraction \(u=Y_2\mathbin{-}Y_1\).  Its Gram matrix is
first expanded into the literal reflected--direct four-tensor network in
Figure `II_uUnitary.png`; the retained physical legs are not included in the
simple interior block.

Source: arXiv:1703.09188, equations `X1X2b`, `uu`, and `uUnitary`, and Lemma
`lemuisometry` (lines 487--557).
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

private lemma sum_rotate_four {A B C P R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [AddCommMonoid R]
    (f : A → B → C → P → R) :
    (∑ a, ∑ b, ∑ c, ∑ p, f a b c p) =
      ∑ c, ∑ p, ∑ b, ∑ a, f a b c p := by
  let e : (((A × B) × C) × P) ≃ (((C × P) × B) × A) :=
    { toFun := fun x ↦ (((x.1.2, x.2), x.1.1.2), x.1.1.1)
      invFun := fun x ↦ (((x.2, x.1.2), x.1.1.1), x.1.1.2)
      left_inv := by rintro ⟨⟨⟨a, b⟩, c⟩, p⟩; rfl
      right_inv := by rintro ⟨⟨⟨c, p⟩, b⟩, a⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1.1 x.1.1.2 x.1.2 x.2)
    (fun x ↦ f x.2 x.1.2 x.1.1.1 x.1.1.2)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

namespace SourceFactors

/-- The tensor product \(Y_1\otimes Y_2\) for supplied source factors, in the
paper's dotted/solid source-bond order `(r,l)`.

Source: CPSV17 equations `uu` and `uUnitary` (lines 532--557). -/
private noncomputable def sourceYTensor {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) :
    Matrix (Fin r[U] × Fin ℓ[U])
      ((Fin d × Fin D) × (Fin d × Fin D)) ℂ :=
  S.Y₁ ⊗ₖ S.Y₂

@[simp] private theorem sourceYTensor_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (r : Fin r[U]) (l : Fin ℓ[U])
    (x₁ x₂ : Fin d × Fin D) :
    sourceYTensor U S (r, l) (x₁, x₂) = S.Y₁ r x₁ * S.Y₂ l x₂ := rfl

/-- The paper gate \(u=Y_2\mathbin{-}Y_1\) is the diagonal virtual
contraction of `sourceYTensor`, with the physical and source-bond orders
displayed explicitly.

Source: CPSV17 equation `uu` and Figure `II_umatrix.png` (lines 532--543). -/
private theorem sourceU_eq_diagonal_sourceYTensor
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (l : Fin ℓ[U]) (r : Fin r[U]) (i₁ i₂ : Fin d) :
    sourceU U S (l, r) (i₁, i₂) =
      ∑ β : Fin D, sourceYTensor U S (r, l) ((i₂, β), (i₁, β)) := by
  apply Finset.sum_congr rfl
  intro β _
  simp only [sourceYTensor_apply]
  ring

private theorem Y₁_gram_eq_weighted_sourceCutM₁_gram
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (p q : Fin d) (a b : Fin D) :
    (∑ r : Fin r[U], star (S.Y₁ r (p, a)) * S.Y₁ r (q, b)) =
      ∑ α : Fin D, ∑ α' : Fin D, ∑ j : Fin d,
        star (U p j α a) * ρ α α' * U q j α' b := by
  have hgram : S.Y₁ᴴ * S.Y₁ =
      (sourceCutM₁ U)ᴴ * sourceWeight (d := d) ρ * sourceCutM₁ U := by
    calc
      S.Y₁ᴴ * S.Y₁ =
          S.Y₁ᴴ * (S.X₁ᴴ * sourceWeight (d := d) ρ * S.X₁) * S.Y₁ := by
        rw [S.X₁_weighted_isometry]
        simp
      _ = (S.X₁ * S.Y₁)ᴴ * sourceWeight (d := d) ρ *
          (S.X₁ * S.Y₁) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [← S.sourceCutM₁_eq]
  have hentry := congrArg (fun M ↦ M (p, a) (q, b)) hgram
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sourceWeight,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sourceCutM₁_apply,
    Fintype.sum_prod_type] at hentry
  simp_rw [Finset.sum_mul] at hentry
  conv_rhs at hentry => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm] at hentry
  exact hentry

private theorem Y₂_gram_eq_rotated_sourceCutM₂_gram
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (p q : Fin d) (a b : Fin D) :
    (∑ l : Fin ℓ[U], star (S.Y₂ l (p, a)) * S.Y₂ l (q, b)) =
      ∑ β : Fin D, ∑ j : Fin d,
        star (U j p β a) * U j q β b := by
  have hgram : S.Y₂ᴴ * S.Y₂ = (sourceCutM₂ U)ᴴ * sourceCutM₂ U := by
    calc
      S.Y₂ᴴ * S.Y₂ = S.Y₂ᴴ * (S.X₂ᴴ * S.X₂) * S.Y₂ := by
        rw [show S.X₂ᴴ * S.X₂ = 1 by exact S.X₂_isometry]
        simp
      _ = (S.X₂ * S.Y₂)ᴴ * (S.X₂ * S.Y₂) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [← S.sourceCutM₂_eq]
  have hentry := congrArg (fun M ↦ M (p, a) (q, b)) hgram
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, sourceCutM₂_apply] at hentry
  exact hentry

/-- Complete expansion of the supplied \(Y_1\otimes Y_2\) Gram entry into
four local tensor entries.  The first cut retains the source weight, and the
second cut uses only the column-isometry normalization of \(X_2\).

Source: CPSV17 equations `X1X2b` and `uUnitary` (lines 487--557). -/
private theorem sourceYTensor_gram_eq_four_u_weighted
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (p q : Fin d × Fin d) (a b : Fin D × Fin D) :
    (∑ t : Fin r[U] × Fin ℓ[U],
      star (sourceYTensor U S t ((p.1, a.1), (p.2, a.2))) *
        sourceYTensor U S t ((q.1, b.1), (q.2, b.2))) =
      ∑ α : Fin D, ∑ α' : Fin D, ∑ β : Fin D,
      ∑ j₁ : Fin d, ∑ j₂ : Fin d,
        star (U p.1 j₁ α a.1) * ρ α α' * U q.1 j₁ α' b.1 *
          (star (U j₂ p.2 β a.2) * U j₂ q.2 β b.2) := by
  rw [Fintype.sum_prod_type]
  simp only [sourceYTensor_apply, star_mul]
  calc
    _ = (∑ r : Fin r[U], star (S.Y₁ r (p.1, a.1)) *
          S.Y₁ r (q.1, b.1)) *
        (∑ l : Fin ℓ[U], star (S.Y₂ l (p.2, a.2)) *
          S.Y₂ l (q.2, b.2)) := by
      simp_rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = (∑ α : Fin D, ∑ α' : Fin D, ∑ j₁ : Fin d,
          star (U p.1 j₁ α a.1) * ρ α α' * U q.1 j₁ α' b.1) *
        (∑ β : Fin D, ∑ j₂ : Fin d,
          star (U j₂ p.2 β a.2) * U j₂ q.2 β b.2) := by
      rw [Y₁_gram_eq_weighted_sourceCutM₁_gram,
        Y₂_gram_eq_rotated_sourceCutM₂_gram]
    _ = _ := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      conv_lhs => arg 2; ext α; arg 2; ext α'; rw [Finset.sum_comm]

/-- The Gram matrix of the corrected paper gate \(u=Y_2\mathbin{-}Y_1\) is
the literal staggered reflected--direct four-\(\mathcal U\) network.  The pair
`p` is starred and `q` is unstarred.

The first retained physical coordinate belongs to the direct input layer;
the second belongs to the reflected output layer.  No mixed \(Y_1\)--\(X_2\)
kernel or ambient source-factor coisometry is used.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557).
-/
theorem sourceU_gram_eq_staggered_four_u
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (p q : Fin d × Fin d) :
    (∑ lr, sourceU U S lr q * star (sourceU U S lr p)) =
      ∑ β : Fin D, ∑ β' : Fin D, ∑ α : Fin D, ∑ α' : Fin D,
      ∑ γ : Fin D, ∑ j₁ : Fin d, ∑ j₂ : Fin d,
        star (U p.2 j₁ α β) * ρ α α' * U q.2 j₁ α' β' *
          (star (U j₂ p.1 γ β) * U j₂ q.1 γ β') := by
  classical
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  rw [Fintype.sum_prod_type]
  simp_rw [sourceU_eq_diagonal_sourceYTensor, star_sum]
  simp_rw [Finset.sum_mul_sum]
  let f := fun (l : Fin ℓ[U]) (r : Fin r[U]) (β β' : Fin D) ↦
    sourceYTensor U S (r, l) ((q₂, β), (q₁, β)) *
      star (sourceYTensor U S (r, l) ((p₂, β'), (p₁, β')))
  change (∑ l, ∑ r, ∑ β, ∑ β', f l r β β') = _
  calc
    _ = ∑ β, ∑ β', ∑ r, ∑ l,
        star (sourceYTensor U S (r, l) ((p₂, β'), (p₁, β'))) *
          sourceYTensor U S (r, l) ((q₂, β), (q₁, β)) := by
      rw [sum_rotate_four]
      apply Finset.sum_congr rfl
      intro β _
      apply Finset.sum_congr rfl
      intro β' _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro l _
      simp only [f]
      ring
    _ = ∑ β, ∑ β', ∑ α, ∑ α', ∑ γ, ∑ j₁, ∑ j₂,
        star (U p₂ j₁ α β') * ρ α α' * U q₂ j₁ α' β *
          (star (U j₂ p₁ γ β') * U j₂ q₁ γ β) := by
      apply Finset.sum_congr rfl
      intro β _
      apply Finset.sum_congr rfl
      intro β' _
      rw [← sourceYTensor_gram_eq_four_u_weighted U S
        (p₂, p₁) (q₂, q₁) (β', β') (β, β),
        Fintype.sum_prod_type]
    _ = _ := by
      rw [Finset.sum_comm]

end SourceFactors

/-- The normalized input-tail contraction is the closed direct double-layer
network with two retained input letters followed by the (K)-site interior.
The retained pair `p` is starred and `q` is unstarred.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557).
-/
theorem normalized_mpo_input_tail_eq_closed_doubleLayer_trace
    [NeZero d] (U : MPOTensor d D) (K : ℕ) (p q : Fin d × Fin d) :
    ((d : ℂ)⁻¹) ^ K *
        ∑ τ : Fin K → Fin d, ∑ η : Fin (K + 2) → Fin d,
          star (mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))) *
          mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) =
      Matrix.trace
        (doubleLayerTensor U p.1 q.1 * doubleLayerTensor U p.2 q.2 *
          normalizedDiagonal (doubleLayerTensor U) ^ K) := by
  classical
  let W := doubleLayerTensor U
  have hη (σ τ : Fin (K + 2) → Fin d) :
      (∑ η : Fin (K + 2) → Fin d,
        star (mpo U (K + 2) η σ) * mpo U (K + 2) η τ) =
        mpo W (K + 2) σ τ := by
    have h := congrArg (fun M ↦ M σ τ) (mpo_doubleLayerTensor U (K + 2))
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    exact h.symm
  simp_rw [hη]
  have hword (τ : Fin K → Fin d) :
      mpo W (K + 2) ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))
          ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) =
        Matrix.trace (W p.1 q.1 * W p.2 q.2 *
          evalWord W (List.ofFn τ) (List.ofFn τ)) := by
    rw [mpo_apply, mpoMatrixEntry]
    simp only [finAddTwoArrowEquiv_symm_apply, List.ofFn_succ, evalWord_cons,
      Fin.cons_zero, Fin.cons_succ]
    rw [← Matrix.mul_assoc]
  simp_rw [hword]
  change ((d : ℂ)⁻¹) ^ K *
      ∑ τ : Fin K → Fin d,
        Matrix.trace (W p.1 q.1 * W p.2 q.2 *
          evalWord W (List.ofFn τ) (List.ofFn τ)) =
    Matrix.trace (W p.1 q.1 * W p.2 q.2 * normalizedDiagonal W ^ K)
  rw [normalizedDiagonal_pow_eq_sum_evalWord W K]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_sum, Matrix.trace_sum]

end MPOTensor
