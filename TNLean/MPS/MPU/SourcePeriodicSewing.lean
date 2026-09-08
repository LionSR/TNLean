/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceCuts

/-!
# Raw periodic sewing of two source-cut arcs

Let $U$ be a tensor with raw factorizations of its two source cuts through
independent spaces $\mathrm{Fin}(r)$ and $\mathrm{Fin}(\ell)$.
Split two distinct marked sites $a,b$ on a periodic word in order $(a,p,b,q)$,
where $p$ and $q$ contain $n$ and $m$ sites. The two open contractions are
$B_n=X_1\mathbin{-}U[p,p']\mathbin{-}X_2$ and
$A_m=Y_2\mathbin{-}U[q,q']\mathbin{-}Y_1$.
Their shared rank indices sew to the ordinary periodic trace. The second arc
runs from $b$ to $a$, with rank order $(\ell,r)$; neither word is reversed.

This is raw local algebra for the tensor-network sewing referred to in
arXiv:2502.20257, `main.tex` lines 5486–5487, using its source decompositions
at lines 5390–5432. It assumes only the two cut factorizations, not canonicality,
simplicity, normalization, unitarity, or a phase relation.

The ring has $n+m+2$ sites, including two distinct marked sites even when
$n=m=0$. The arcs have lengths $n+2$ and $m+2$ and overlap at both marked
sites. In particular, this is not a claim that the second arc has length
$(n+m+2)-(n+2)$, nor a proof of the phase-bearing operator identity `eq:UUU`.
-/

open scoped Matrix

namespace MPOTensor

variable {d D r l : ℕ} (U : MPOTensor d D)

/-- The raw $Y_2$--word--$Y_1$ contraction with row order $(l,(q,r))$.
Source: the local sewing step associated with arXiv:2502.20257, lines 5486–5487.
Its boundary order is the complementary arc from the second marked site to the first. -/
noncomputable def sourcePeriodicArcA
    (Y₁ : Matrix (Fin r) (Fin D × Fin d) ℂ)
    (Y₂ : Matrix (Fin l) (Fin d × Fin D) ℂ) (N : ℕ) :
    Matrix (Fin l × ((Fin N → Fin d) × Fin r))
      (Fin d × ((Fin N → Fin d) × Fin d)) ℂ :=
  fun (s, p, t) (a, q, b) ↦ ∑ α : Fin D, ∑ β : Fin D,
    Y₂ s (a, α) * evalWord U (List.ofFn p) (List.ofFn q) α β * Y₁ t (β, b)

/-- The raw $X_1$--word--$X_2$ contraction with column order $(r,(p',l))$.
Source: the local sewing step associated with arXiv:2502.20257, lines 5486–5487. -/
noncomputable def sourcePeriodicArcB
    (X₁ : Matrix (Fin d × Fin D) (Fin r) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin l) ℂ) (N : ℕ) :
    Matrix (Fin d × ((Fin N → Fin d) × Fin d))
      (Fin r × ((Fin N → Fin d) × Fin l)) ℂ :=
  fun (a, p, b) (t, q, s) ↦ ∑ α : Fin D, ∑ β : Fin D,
    X₁ (a, α) t * evalWord U (List.ofFn p) (List.ofFn q) α β * X₂ (β, b) s

/-- Splitting the two marked tensors by their respective source cuts and regrouping
the periodic trace sews the two arcs. Only the raw factorizations are required.
Source: arXiv:2502.20257, source decompositions at lines 5390–5432 and the
local tensor-network sewing referred to at lines 5486–5487. -/
theorem trace_two_marked_evalWord_eq_sourcePeriodic_sewing
    (X₁ : Matrix (Fin d × Fin D) (Fin r) ℂ)
    (Y₁ : Matrix (Fin r) (Fin D × Fin d) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin l) ℂ)
    (Y₂ : Matrix (Fin l) (Fin d × Fin D) ℂ)
    (hcut₁ : sourceCutM₁ U = X₁ * Y₁) (hcut₂ : sourceCutM₂ U = X₂ * Y₂)
    {n m : ℕ} (a a' b b' : Fin d)
    (p p' : Fin n → Fin d) (q q' : Fin m → Fin d) :
    (U a a' * evalWord U (List.ofFn p) (List.ofFn p') * U b b' *
      evalWord U (List.ofFn q) (List.ofFn q')).trace =
      ∑ t : Fin r, ∑ s : Fin l,
        sourcePeriodicArcB U X₁ X₂ n (a, p, b) (t, p', s) *
          sourcePeriodicArcA U Y₁ Y₂ m (s, q, t) (b', q', a') := by
  let C : Matrix (Fin r) (Fin D) ℂ := fun t α ↦ X₁ (a, α) t
  let H : Matrix (Fin D) (Fin r) ℂ := fun δ t ↦ Y₁ t (δ, a')
  let E : Matrix (Fin D) (Fin l) ℂ := fun β s ↦ X₂ (β, b) s
  let F : Matrix (Fin l) (Fin D) ℂ := fun s γ ↦ Y₂ s (b', γ)
  let P := evalWord U (List.ofFn p) (List.ofFn p')
  let Q := evalWord U (List.ofFn q) (List.ofFn q')
  have ha : U a a' = H * C := by
    ext δ α
    change U a a' δ α = ∑ t : Fin r, Y₁ t (δ, a') * X₁ (a, α) t
    have h := congrArg (fun M ↦ M (a, α) (δ, a')) hcut₁
    simpa only [sourceCutM₁_apply, Matrix.mul_apply, mul_comm] using h
  have hb : U b b' = E * F := by
    ext β γ
    exact congrArg (fun M ↦ M (β, b) (b', γ)) hcut₂
  have hB (t : Fin r) (s : Fin l) :
      sourcePeriodicArcB U X₁ X₂ n (a, p, b) (t, p', s) = (C * P * E) t s := by
    simp only [sourcePeriodicArcB, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hA (s : Fin l) (t : Fin r) :
      sourcePeriodicArcA U Y₁ Y₂ m (s, q, t) (b', q', a') = (F * Q * H) s t := by
    simp only [sourcePeriodicArcA, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  change (U a a' * P * U b b' * Q).trace = _
  rw [ha, hb]
  calc
    _ = (H * (C * P * E * F * Q)).trace := by simp only [Matrix.mul_assoc]
    _ = ((C * P * E * F * Q) * H).trace := Matrix.trace_mul_comm _ _
    _ = ((C * P * E) * (F * Q * H)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hB, hA]

/-- The exact periodic MPO entry in site order $(a,p,b,q)$ is the raw sewn contraction.
The size is $n+(m+1)+1=n+m+2$, not the sum of two disjoint endpoint-inclusive arc lengths.
Source: the local sewing referred to in arXiv:2502.20257, lines 5486–5487;
this is an entry identity, not the phase-bearing operator equation `eq:UUU`. -/
theorem mpo_two_marked_entry_eq_sourcePeriodic_sewing
    (X₁ : Matrix (Fin d × Fin D) (Fin r) ℂ)
    (Y₁ : Matrix (Fin r) (Fin D × Fin d) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin l) ℂ)
    (Y₂ : Matrix (Fin l) (Fin d × Fin D) ℂ)
    (hcut₁ : sourceCutM₁ U = X₁ * Y₁) (hcut₂ : sourceCutM₂ U = X₂ * Y₂)
    {n m : ℕ} (a a' b b' : Fin d)
    (p p' : Fin n → Fin d) (q q' : Fin m → Fin d) :
    mpo U (n + (m + 1) + 1)
      (Fin.cons a (Fin.append p (Fin.cons b q)))
      (Fin.cons a' (Fin.append p' (Fin.cons b' q'))) =
      ∑ t : Fin r, ∑ s : Fin l,
        sourcePeriodicArcB U X₁ X₂ n (a, p, b) (t, p', s) *
          sourcePeriodicArcA U Y₁ Y₂ m (s, q, t) (b', q', a') := by
  rw [mpo_apply, mpoMatrixEntry, List.ofFn_cons, List.ofFn_cons,
    List.ofFn_fin_append, List.ofFn_fin_append, evalWord_cons,
    evalWord_append U (List.ofFn p) (List.ofFn p') _ _ (by simp),
    List.ofFn_cons, List.ofFn_cons, evalWord_cons]
  simpa only [Matrix.mul_assoc] using
    trace_two_marked_evalWord_eq_sourcePeriodic_sewing U X₁ Y₁ X₂ Y₂ hcut₁ hcut₂
      a a' b b' p p' q q'

end MPOTensor
