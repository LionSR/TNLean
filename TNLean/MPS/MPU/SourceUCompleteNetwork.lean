/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.MPS.MPU.MatchingContractions
import TNLean.MPS.MPU.SourceVIsometry

/-!
# The complete network for the paper source gate u

This file follows the contraction in CPSV17 Lemma `lemuisometry`.  The source
gate is the staggered contraction \(u=Y_2\mathbin{-}Y_1\).  Its Gram matrix is
first expanded into the literal reflected--direct four-tensor network in
Figure `II_uUnitary.png`.  The network is then closed against a fixed pair
\(E^K=|\rho)(\Phi|\), while the two retained one-site letters remain outside
the \(K\)-site interior.  The normalized input tail gives \(u^\dagger u=\Id\)
and \(d^2\le r\ell\).

The closing theorems in the `SourceFactors` namespace are generic: they take
arbitrary supplied source factors for an arbitrary positive weight together
with the stabilized fixed pair \(E^K=|\rho)(\Phi|\), and assume nothing else
about \(\mathcal U\).  Lemma `lemuisometry` itself is stated for an MPU in
canonical form II, where the diagonal positive weight and the stabilized power
are both recorded by the convention.  In that convention, \(\rho\) is diagonal
with positive weights; see `Papers/1703.09188/paper_v2.tex` at lines 269--280
and line 495.  Diagonality is load-bearing in the coordinate proof: column
stacking makes the Gram closure insert \(|\rho^{\mathsf T})(\Phi|\), while
stabilization supplies \(|\rho)(\Phi|\), and the two agree because
\(\rho^{\mathsf T}=\rho\).  The generic theorems keep `SourceFactors U ρ` built
from the printed weight, expose the convention as `ρ.IsDiag`, and use only
`ρ.IsSymm` for the algebraic trace closure.  The column-stacking orientation is
recorded in `docs/paper-gaps/mpu_source_cut_orientation.tex`.

Source: arXiv:1703.09188, equations `Erightleft`, `X1X2b`, `uu`, and
`uUnitary`, and Lemma `lemuisometry` (lines 269--280 and 487--557).
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- The tensor product \(Y_1\otimes Y_2\) for supplied source factors, in the
paper's dotted/solid source-bond order `(r,l)`.

Source: CPSV17 equations `uu` and `uUnitary` (lines 532--557). -/
private noncomputable def sourceYTensor {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) :
    Matrix (Fin r[U] × Fin ℓ[U])
      ((Fin D × Fin d) × (Fin d × Fin D)) ℂ :=
  S.Y₁ ⊗ₖ S.Y₂

@[simp] private theorem sourceYTensor_apply {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (r : Fin r[U]) (l : Fin ℓ[U])
    (x₁ : Fin D × Fin d) (x₂ : Fin d × Fin D) :
    sourceYTensor U S (r, l) (x₁, x₂) = S.Y₁ r x₁ * S.Y₂ l x₂ := rfl

/-- The paper gate \(u=Y_2\mathbin{-}Y_1\) is the diagonal virtual
contraction of `sourceYTensor`, with the physical and source-bond orders
displayed explicitly.

Source: CPSV17 equation `uu` and Figure `II_umatrix.png` (lines 532--543). -/
private theorem sourceU_eq_diagonal_sourceYTensor
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (l : Fin ℓ[U]) (r : Fin r[U]) (i₁ i₂ : Fin d) :
    sourceU U S (l, r) (i₁, i₂) =
      ∑ β : Fin D, sourceYTensor U S (r, l) ((β, i₂), (i₁, β)) := by
  apply Finset.sum_congr rfl
  intro β _
  simp only [sourceYTensor_apply]
  ring

private theorem Y₁_gram_eq_weighted_sourceCutM₁_gram
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (p q : Fin d) (a b : Fin D) :
    (∑ r : Fin r[U], star (S.Y₁ r (a, p)) * S.Y₁ r (b, q)) =
      ∑ β : Fin D, ∑ β' : Fin D, ∑ i : Fin d,
        star (U i p a β) * ρ β β' * U i q b β' := by
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
  have hentry := congrArg (fun M ↦ M (a, p) (b, q)) hgram
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sourceWeight,
    Matrix.kronecker_apply, sourceCutM₁_apply, Fintype.sum_prod_type] at hentry
  conv_rhs at hentry =>
    simp [Matrix.one_apply]
    arg 2
    ext i
    arg 2
    ext β'
    rw [Finset.sum_mul]
  calc
    (∑ r : Fin r[U], star (S.Y₁ r (a, p)) * S.Y₁ r (b, q)) =
        ∑ i : Fin d, ∑ β' : Fin D, ∑ β : Fin D,
          star (U i p a β) * ρ β β' * U i q b β' := hentry
    _ = ∑ β : Fin D, ∑ β' : Fin D, ∑ i : Fin d,
          star (U i p a β) * ρ β β' * U i q b β' := by
      rw [Fintype.sum_reverse_three]

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
      star (sourceYTensor U S t ((a.1, p.1), (p.2, a.2))) *
        sourceYTensor U S t ((b.1, q.1), (q.2, b.2))) =
      ∑ β : Fin D, ∑ β' : Fin D, ∑ γ : Fin D,
      ∑ j₁ : Fin d, ∑ j₂ : Fin d,
        star (U j₁ p.1 a.1 β) * ρ β β' * U j₁ q.1 b.1 β' *
          (star (U j₂ p.2 γ a.2) * U j₂ q.2 γ b.2) := by
  rw [Fintype.sum_prod_type]
  simp only [sourceYTensor_apply, star_mul]
  calc
    _ = (∑ r : Fin r[U], star (S.Y₁ r (a.1, p.1)) *
          S.Y₁ r (b.1, q.1)) *
        (∑ l : Fin ℓ[U], star (S.Y₂ l (p.2, a.2)) *
          S.Y₂ l (q.2, b.2)) := by
      simp_rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = (∑ β : Fin D, ∑ β' : Fin D, ∑ j₁ : Fin d,
          star (U j₁ p.1 a.1 β) * ρ β β' * U j₁ q.1 b.1 β') *
        (∑ γ : Fin D, ∑ j₂ : Fin d,
          star (U j₂ p.2 γ a.2) * U j₂ q.2 γ b.2) := by
      rw [Y₁_gram_eq_weighted_sourceCutM₁_gram,
        Y₂_gram_eq_rotated_sourceCutM₂_gram]
    _ = _ := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      conv_lhs => arg 2; ext β; arg 2; ext β'; rw [Finset.sum_comm]

/-- The Gram matrix of the paper gate \(u=Y_2\mathbin{-}Y_1\) is
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
      ∑ α : Fin D, ∑ α' : Fin D, ∑ β : Fin D, ∑ β' : Fin D,
      ∑ γ : Fin D, ∑ j₁ : Fin d, ∑ j₂ : Fin d,
        star (U j₁ p.2 α β) * ρ β β' * U j₁ q.2 α' β' *
          (star (U j₂ p.1 γ α) * U j₂ q.1 γ α') := by
  classical
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  rw [Fintype.sum_prod_type]
  simp_rw [sourceU_eq_diagonal_sourceYTensor, star_sum]
  simp_rw [Finset.sum_mul_sum]
  let f := fun (l : Fin ℓ[U]) (r : Fin r[U]) (α' α : Fin D) ↦
    sourceYTensor U S (r, l) ((α', q₂), (q₁, α')) *
      star (sourceYTensor U S (r, l) ((α, p₂), (p₁, α)))
  change (∑ l, ∑ r, ∑ α', ∑ α, f l r α' α) = _
  calc
    _ = ∑ α, ∑ α', ∑ l, ∑ r,
        star (sourceYTensor U S (r, l) ((α, p₂), (p₁, α))) *
          sourceYTensor U S (r, l) ((α', q₂), (q₁, α')) := by
      rw [Fintype.sum_last_first_four]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro α' _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro r _
      simp only [f]
      ring
    _ = ∑ α, ∑ α', ∑ r, ∑ l,
        star (sourceYTensor U S (r, l) ((α, p₂), (p₁, α))) *
          sourceYTensor U S (r, l) ((α', q₂), (q₁, α')) := by
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro α' _
      rw [Finset.sum_comm]
    _ = ∑ α, ∑ α', ∑ β, ∑ β', ∑ γ, ∑ j₁, ∑ j₂,
        star (U j₁ p₂ α β) * ρ β β' * U j₁ q₂ α' β' *
          (star (U j₂ p₁ γ α) * U j₂ q₁ γ α') := by
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro α' _
      rw [← sourceYTensor_gram_eq_four_u_weighted U S
        (p₂, p₁) (q₂, q₁) (α, α) (α', α'),
        Fintype.sum_prod_type]
    _ = _ := rfl

/-- The Gram matrix of the paper gate \(u=Y_2\mathbin{-}Y_1\) closes to a
fixed-pair trace of two double-layer letters.  The source weight enters as
\(\rho^{\mathsf T}\) because `Matrix.vec` uses the column-stacking coordinates
fixed by `finProdFinEquiv`.  The pair `p` is starred and `q` is unstarred.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557).
-/
theorem sourceU_gram_eq_transpose_fixed_pair_trace
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (p q : Fin d × Fin d) :
    (∑ lr, sourceU U S lr q * star (sourceU U S lr p)) =
      Matrix.trace
        (doubleLayerTensor U p.2 q.2 *
          Matrix.vecMulVec
            (fun x ↦ ρ.transpose.vec (finProdFinEquiv.symm x))
            (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec
              (finProdFinEquiv.symm x)) *
          doubleLayerTensor U p.1 q.1) := by
  classical
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  have hentry (a b : Fin D) :
      (doubleLayerTensor U p₂ q₂ *
          Matrix.vecMulVec
            (fun x ↦ ρ.transpose.vec (finProdFinEquiv.symm x))
            (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec
              (finProdFinEquiv.symm x)) *
          doubleLayerTensor U p₁ q₁)
          (finProdFinEquiv (a, b)) (finProdFinEquiv (a, b)) =
        ∑ β : Fin D, ∑ β' : Fin D, ∑ γ : Fin D,
        ∑ j₁ : Fin d, ∑ j₂ : Fin d,
          star (U j₁ p₂ a β) * U j₁ q₂ b β' * ρ β β' *
            (star (U j₂ p₁ γ a) * U j₂ q₁ γ b) := by
    simpa only [Matrix.transpose_apply] using
      doubleLayerTensor_rankOne_mul_apply_four_u U ρ.transpose
        (p₂, p₁) (q₂, q₁) (a, a) (b, b)
  have htrace :
      Matrix.trace
          (doubleLayerTensor U p₂ q₂ *
            Matrix.vecMulVec
              (fun x ↦ ρ.transpose.vec (finProdFinEquiv.symm x))
              (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec
                (finProdFinEquiv.symm x)) *
            doubleLayerTensor U p₁ q₁) =
        ∑ a : Fin D, ∑ b : Fin D, ∑ β : Fin D, ∑ β' : Fin D,
        ∑ γ : Fin D, ∑ j₁ : Fin d, ∑ j₂ : Fin d,
          star (U j₁ p₂ a β) * U j₁ q₂ b β' * ρ β β' *
            (star (U j₂ p₁ γ a) * U j₂ q₁ γ b) := by
    unfold Matrix.trace
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact hentry a b
  rw [sourceU_gram_eq_staggered_four_u, htrace]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro β' _
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro j₁ _
  apply Finset.sum_congr rfl
  intro j₂ _
  ring

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

namespace SourceFactors

/-- For a symmetric supplied source weight, the source-$u$ Gram matrix is the
closed direct double-layer trace for any matching fixed pair.  The source
factors remain those constructed from `ρ`; the pair `p` is starred and `q` is
unstarred.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557),
with the fixed point in the diagonal coordinates of lines 269--280. -/
theorem sourceU_gram_eq_closed_doubleLayer_trace_of_isSymm
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (hρ : ρ.IsSymm) (K : ℕ)
    (hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec (fun x ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)))
    (p q : Fin d × Fin d) :
    (∑ lr, sourceU U S lr q * star (sourceU U S lr p)) =
      Matrix.trace
        (doubleLayerTensor U p.1 q.1 * doubleLayerTensor U p.2 q.2 *
          normalizedDiagonal (doubleLayerTensor U) ^ K) := by
  rw [sourceU_gram_eq_transpose_fixed_pair_trace, hρ.eq, ← hK]
  exact Matrix.trace_mul_cycle _ _ _

/-- For the source's diagonal fixed point satisfying \(E^K=|\rho)(\Phi|\), the
source-$u$ Gram matrix is the normalized input-first contraction with one
length-$K$ interior and two retained one-site endpoints.  The pair `p` is
starred and `q` is unstarred.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557),
with the fixed point in the diagonal coordinates of lines 269--280. -/
theorem sourceU_gram_eq_normalized_input_tail [NeZero d]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (hρdiag : ρ.IsDiag)
    (K : ℕ)
    (hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec (fun x ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)))
    (p q : Fin d × Fin d) :
    (∑ lr, sourceU U S lr q * star (sourceU U S lr p)) =
      ((d : ℂ)⁻¹) ^ K *
        ∑ τ : Fin K → Fin d, ∑ η : Fin (K + 2) → Fin d,
          star (mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))) *
          mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) := by
  rw [normalized_mpo_input_tail_eq_closed_doubleLayer_trace]
  exact sourceU_gram_eq_closed_doubleLayer_trace_of_isSymm U S hρdiag.isSymm K hK p q

/-- For supplied source factors and a diagonal fixed pair, the paper gate
\(u=Y_2\mathbin{-}Y_1\) of an MPU tensor is an isometry.

Source: CPSV17 Lemma `lemuisometry` (lines 545--557), with the fixed point in
the diagonal coordinates of lines 269--280. -/
theorem sourceU_isIsometry_of_isMPU [NeZero d] (hU : IsMPU U)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (hρdiag : ρ.IsDiag)
    (K : ℕ)
    (hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec (fun x ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))) :
    (sourceU U S).IsIsometry := by
  change (sourceU U S)ᴴ * sourceU U S = 1
  ext p q
  have h := sourceU_gram_eq_normalized_input_tail U S hρdiag K hK p q
  rw [hU.normalized_mpo_tail_isometry] at h
  rw [Matrix.mul_apply, Matrix.one_apply, ← h]
  exact Finset.sum_congr rfl fun lr _ ↦ by
    rw [Matrix.conjTranspose_apply, mul_comm]

/-- The rank consequence of the supplied-fixed-pair source-$u$ isometry:
\(d^2\le r\ell\).

Source: CPSV17 Lemma `lemuisometry` (lines 545--557). -/
theorem mul_self_le_rightRank_mul_leftRank_of_isMPU [NeZero d] (hU : IsMPU U)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (hρdiag : ρ.IsDiag)
    (K : ℕ)
    (hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec (fun x ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))) :
    d * d ≤ r[U] * ℓ[U] := by
  have h := Matrix.IsIsometry.card_le _ (sourceU_isIsometry_of_isMPU U hU S hρdiag K hK)
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm ℓ[U]] using h

end SourceFactors

variable {U} in
/-- Lemma `lemuisometry` under the source's standing convention: the compact-SVD
paper gate $u=Y_2\mathbin{-}Y_1$ of an MPU in canonical form II is an isometry.

The diagonal positive ambient fixed point, the stabilized rank-one power, and
the nonzero physical dimension are recorded by the convention, so none of them
is supplied as a separate hypothesis.

Source: CPSV17 Lemma `lemuisometry` (lines 545--557), with the fixed point in
the diagonal coordinates of `Erightleft` (lines 269--280). -/
theorem IsMPUCanonicalFormII.sourceU_isIsometry
    (hU : IsMPUCanonicalFormII U) :
    (sourceU U hU.ρ hU.ρ_posDef).IsIsometry :=
  have := hU.neZero_phys
  SourceFactors.sourceU_isIsometry_of_isMPU U hU.isMPU
    (sourceFactors U hU.ρ hU.ρ_posDef) hU.ρ_isDiag _
    hU.normalizedDiagonal_pow_eq_vecMulVec

variable {U} in
/-- The rank consequence of Lemma `lemuisometry` under the standing
canonical-form-II convention: $d^2\le r\ell$.

Source: CPSV17 Lemma `lemuisometry` (lines 545--557). -/
theorem IsMPUCanonicalFormII.mul_self_le_rightRank_mul_leftRank
    (hU : IsMPUCanonicalFormII U) :
    d * d ≤ r[U] * ℓ[U] := by
  have h := Matrix.IsIsometry.card_le _ hU.sourceU_isIsometry
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm ℓ[U]] using h

end MPOTensor
