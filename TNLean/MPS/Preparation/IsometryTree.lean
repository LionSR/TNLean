/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryKronecker
import TNLean.MPS.Core.Blocking

/-!
# Binary trees of isometries with unequal physical leaves

A tree of coarse depth `h` has `2^h` physical leaves. Each leaf is an isometry from a
fixed virtual space `ℂ^χ` to at most `R` consecutive physical sites. Each binary vertex
has its own isometry `ℂ^χ → ℂ^χ ⊗ ℂ^χ`; the two descendants may contain different
numbers of physical sites. Its matrix is the tensor product of its descendants followed
by this vertex isometry. Every such tree is an isometry.

The fixed bound `R` is part of the type, so enlarging the chain cannot silently enlarge
a leaf. This is the unequal-block version of the isometry layers in arXiv:2307.01696,
eq. (16) and the paragraph "Connection to MERA". There is one finest layer in addition
to the coarse depth; a top disentangler contributes one further layer.
-/

open Matrix MPSTensor
open scoped BigOperators Kronecker

namespace MPSPreparation

/-- A binary tree with `h` coarse layers, fixed virtual dimension `χ`, and physical leaves
of positive lengths at most `R`. Vertex isometries may depend on the vertex.

Source: arXiv:2307.01696, eq. (16) and the paragraph "Connection to MERA". -/
inductive IsometryTree (d χ R : ℕ) : ℕ → ℕ → Type
  | leaf {n : ℕ} (V : Matrix ((Fin n → Fin d)) (Fin χ) ℂ) (hV : V.IsIsometry)
      (hn : 0 < n) (hR : n ≤ R) : IsometryTree d χ R 0 n
  | fork {h n₁ n₂ : ℕ} (left : IsometryTree d χ R h n₁)
      (right : IsometryTree d χ R h n₂)
      (W : Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ) (hW : W.IsIsometry) :
      IsometryTree d χ R (h + 1) (n₁ + n₂)

namespace IsometryTree

variable {d χ R h n n₁ n₂ : ℕ}

private noncomputable def pairIndexEquiv (χ : ℕ) :
    Fin (blockPhysDim χ 2) ≃ Fin χ × Fin χ :=
  (decodeBlockEquiv χ 2).trans (piFinTwoEquiv fun _ => Fin χ)

private noncomputable def joinMatrix (L : Matrix ((Fin n₁ → Fin d)) (Fin χ) ℂ)
    (R : Matrix ((Fin n₂ → Fin d)) (Fin χ) ℂ) :
    Matrix ((Fin (n₁ + n₂) → Fin d)) (Fin (blockPhysDim χ 2)) ℂ :=
  Matrix.reindex (Fin.appendEquiv n₁ n₂) (pairIndexEquiv χ).symm (L ⊗ₖ R)

private theorem isIsometry_joinMatrix {L : Matrix ((Fin n₁ → Fin d)) (Fin χ) ℂ}
    {R : Matrix ((Fin n₂ → Fin d)) (Fin χ) ℂ} (hL : L.IsIsometry) (hR : R.IsIsometry) :
    (joinMatrix L R).IsIsometry :=
  Matrix.IsIsometry.reindex _ (Matrix.IsIsometry.kronecker L R hL hR)
    (Fin.appendEquiv n₁ n₂) (pairIndexEquiv χ).symm

/-- The contraction of the tree, from its root virtual space to its physical sites. -/
noncomputable def matrix : {h n : ℕ} → IsometryTree d χ R h n →
    Matrix ((Fin n → Fin d)) (Fin χ) ℂ
  | _, _, .leaf V _ _ _ => V
  | _, _, .fork left right W _ => joinMatrix left.matrix right.matrix * W

/-- Contracting a tree of isometries gives an isometry. -/
theorem isIsometry_matrix (T : IsometryTree d χ R h n) : T.matrix.IsIsometry := by
  induction T with
  | leaf V hV _ _ => exact hV
  | fork left right W hW ih₁ ih₂ =>
    exact Matrix.IsIsometry.mul _ W (isIsometry_joinMatrix ih₁ ih₂) hW

/-- At a binary vertex, sum over its two virtual outputs and multiply the two
physical descendant amplitudes. -/
theorem matrix_fork_apply (left : IsometryTree d χ R h n₁)
    (right : IsometryTree d χ R h n₂)
    (W : Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ) (hW : W.IsIsometry)
    (τ : (Fin (n₁ + n₂) → Fin d)) (x : Fin χ) :
    (fork left right W hW).matrix τ x =
      ∑ e, left.matrix (fun i => τ (Fin.castAdd n₂ i)) (decodeBlock χ 2 e 0) *
        right.matrix (fun i => τ (Fin.natAdd n₁ i)) (decodeBlock χ 2 e 1) * W e x := by
  rfl

/-- Relabel the physical length by an equality, leaving all vertex tensors unchanged. -/
def cast {n' : ℕ} (hn : n = n') (T : IsometryTree d χ R h n) :
    IsometryTree d χ R h n' := hn ▸ T

@[simp] theorem matrix_cast {n' : ℕ} (hn : n = n') (T : IsometryTree d χ R h n)
    (τ : (Fin n' → Fin d)) (x : Fin χ) :
    (T.cast hn).matrix τ x = T.matrix (fun i => τ (Fin.cast hn i)) x := by
  subst n'
  rfl

end IsometryTree
end MPSPreparation
