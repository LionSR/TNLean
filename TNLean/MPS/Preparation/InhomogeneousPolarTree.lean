/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.IsometricPolarMerge
import TNLean.MPS.Preparation.MixedSequentialFactorization
import TNLean.MPS.Preparation.PolarUniqueness

/-!
# Exact polar trees for site-dependent chains

The physical matrix of an actual concatenated chain factors through the tensor product
of independently chosen child ranges. Recursive isometric polar completion therefore gives
a tree for every site-dependent chain on any feasible binary geometry. All virtual spaces
have dimension `D²`; tensors and merge maps may depend on the interval. No injectivity or
common coordinate support is assumed.

This proves the algebraic tree step of the inhomogeneous extension of arXiv:2307.01696,
eq. (16). It does not compile the position-dependent tree into measurement rounds, specify
the source's sequence class, or derive a uniform approximation rate for that class.
-/

open Matrix MPSTensor MPSChainTensor
open scoped BigOperators

namespace MPSPreparation

variable {d D n₁ n₂ : ℕ}

/-- Contract the common virtual bond of two compressed interval maps. This is the actual
matrix-product contraction, before taking the polar factor at a parent vertex.
Source: the interval-dependent form of arXiv:2307.01696, eq. (16). -/
noncomputable def chainPairMerge
    (P Q : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) :
    Matrix (Fin (blockPhysDim (D * D) 2)) (Fin (D * D)) ℂ := fun e x =>
  ∑ γ : Fin D,
    P (decodeBlock (D * D) 2 e 0)
      ((virtualPairEquiv D).symm ((virtualPairEquiv D x).1, γ)) *
    Q (decodeBlock (D * D) 2 e 1)
      ((virtualPairEquiv D).symm (γ, (virtualPairEquiv D x).2))

private theorem sum_decodeBlock_two {χ : ℕ} (f : Fin χ → Fin χ → ℂ) :
    (∑ e : Fin (blockPhysDim χ 2), f (decodeBlock χ 2 e 0) (decodeBlock χ 2 e 1)) =
      ∑ u, ∑ v, f u v := by
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (IsometryTree.pairIndexEquiv χ)
      (fun e => f (decodeBlock χ 2 e 0) (decodeBlock χ 2 e 1))
      (fun p => f p.1 p.2) (fun _ => rfl))

/-- The concatenated physical matrix factors through the two child physical maps whenever
the child matrices do. The remainder is the contraction of the two child remainders.
Source: the matrix-product identity underlying arXiv:2307.01696, eq. (16). -/
theorem chainPairMatrix_append_eq_joinMatrix_mul
    (A : MPSChainTensor d D n₁) (B : MPSChainTensor d D n₂)
    (X : Matrix (Fin n₁ → Fin d) (Fin (D * D)) ℂ)
    (Y : Matrix (Fin n₂ → Fin d) (Fin (D * D)) ℂ)
    (P Q : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
    (hA : chainPairMatrix A = X * P) (hB : chainPairMatrix B = Y * Q) :
    chainPairMatrix (Fin.append A B) = IsometryTree.joinMatrix X Y * chainPairMerge P Q := by
  classical
  ext σ x
  obtain ⟨⟨σ₁, σ₂⟩, rfl⟩ := (Fin.appendEquiv n₁ n₂).surjective σ
  have hleft (γ : Fin D) :
      eval A σ₁ (virtualPairEquiv D x).1 γ =
        ∑ u, X σ₁ u * P u ((virtualPairEquiv D).symm ((virtualPairEquiv D x).1, γ)) := by
    simpa only [chainPairMatrix, Matrix.of_apply, Equiv.apply_symm_apply, Matrix.mul_apply]
      using congrFun₂ hA σ₁ ((virtualPairEquiv D).symm ((virtualPairEquiv D x).1, γ))
  have hright (γ : Fin D) :
      eval B σ₂ γ (virtualPairEquiv D x).2 =
        ∑ v, Y σ₂ v * Q v ((virtualPairEquiv D).symm (γ, (virtualPairEquiv D x).2)) := by
    simpa only [chainPairMatrix, Matrix.of_apply, Equiv.apply_symm_apply, Matrix.mul_apply]
      using congrFun₂ hB σ₂ ((virtualPairEquiv D).symm (γ, (virtualPairEquiv D x).2))
  change eval (Fin.append A B) (Fin.append σ₁ σ₂)
      (virtualPairEquiv D x).1 (virtualPairEquiv D x).2 = _
  rw [eval_append, Matrix.mul_apply]
  simp only [Matrix.mul_apply, IsometryTree.joinMatrix_apply, Fin.append_left,
    Fin.append_right, chainPairMerge]
  let f (u v : Fin (D * D)) : ℂ := X σ₁ u * Y σ₂ v *
    ∑ γ : Fin D,
      P u ((virtualPairEquiv D).symm ((virtualPairEquiv D x).1, γ)) *
      Q v ((virtualPairEquiv D).symm (γ, (virtualPairEquiv D x).2))
  change (∑ γ : Fin D,
      eval A σ₁ (virtualPairEquiv D x).1 γ * eval B σ₂ γ (virtualPairEquiv D x).2) =
    ∑ e, f (decodeBlock (D * D) 2 e 0) (decodeBlock (D * D) 2 e 1)
  rw [sum_decodeBlock_two f]
  dsimp only [f]
  simp_rw [hleft, hright, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- Independently completed child polar maps admit an isometric merge for their actual
concatenated chain. The parent is not assumed to lie in the child ranges: that fact follows
from the matrix-product contraction. Source: arXiv:2307.01696, eq. (16). -/
theorem exists_isometry_chainPairMatrix_append (hD : 0 < D)
    (A : MPSChainTensor d D n₁) (B : MPSChainTensor d D n₂)
    (X : Matrix (Fin n₁ → Fin d) (Fin (D * D)) ℂ)
    (Y : Matrix (Fin n₂ → Fin d) (Fin (D * D)) ℂ)
    (hX : X.IsIsometry) (hY : Y.IsIsometry)
    (hA : X * polarPos (chainPairMatrix A) = chainPairMatrix A)
    (hB : Y * polarPos (chainPairMatrix B) = chainPairMatrix B) :
    ∃ W : Matrix (Fin (blockPhysDim (D * D) 2)) (Fin (D * D)) ℂ,
      W.IsIsometry ∧ (IsometryTree.joinMatrix X Y * W) *
        polarPos (chainPairMatrix (Fin.append A B)) = chainPairMatrix (Fin.append A B) := by
  have hfactor := chainPairMatrix_append_eq_joinMatrix_mul A B X Y
    (polarPos (chainPairMatrix A)) (polarPos (chainPairMatrix B)) hA.symm hB.symm
  obtain ⟨W, hW, hparent⟩ := exists_isometry_binaryPolarMerge (Nat.mul_pos hD hD)
    X Y hX hY (chainPairMerge (polarPos (chainPairMatrix A)) (polarPos (chainPairMatrix B)))
  rw [← hfactor] at hparent
  exact ⟨W, hW, hparent⟩

/-- Every site-dependent chain has an exact isometric polar tree on any feasible binary
geometry. A template supplies the geometry and certifies that each leaf has room for `D²`
orthogonal columns; none of its gates or tensors need agree with the target chain.
The new tree uses interval-dependent maps and agrees with the canonical polar isometry on
its support. Source: the algebraic tree step in arXiv:2307.01696, eq. (16).

This is a factorization theorem, not a measurement-depth theorem. -/
theorem exists_isometryTree_mul_polarPos_eq {R h n : ℕ} (hD : 0 < D)
    (T : IsometryTree d (D * D) R h n) (A : MPSChainTensor d D n) :
    ∃ U : IsometryTree d (D * D) R h n,
      U.matrix * polarPos (chainPairMatrix A) = chainPairMatrix A ∧
      U.matrix * polarSupport (chainPairMatrix A) = polarIso (chainPairMatrix A) := by
  classical
  suffices hex : ∃ U : IsometryTree d (D * D) R h n,
      U.matrix * polarPos (chainPairMatrix A) = chainPairMatrix A by
    obtain ⟨U, hU⟩ := hex
    exact ⟨U, hU, Matrix.mul_polarSupport_eq_polarIso_of_mul_polarPos_eq hU⟩
  induction T generalizing A with
  | leaf V hV hn hR =>
    obtain ⟨X, hX, hXP⟩ := Matrix.exists_isometry_mul_polarPos_eq (chainPairMatrix A)
      (Matrix.IsIsometry.card_le V hV)
    exact ⟨.leaf X hX hn hR, hXP⟩
  | @fork h n₁ n₂ left right W hW ih₁ ih₂ =>
    let A₁ : MPSChainTensor d D n₁ := fun i => A (Fin.castAdd n₂ i)
    let A₂ : MPSChainTensor d D n₂ := fun i => A (Fin.natAdd n₁ i)
    obtain ⟨U₁, hU₁⟩ := ih₁ A₁
    obtain ⟨U₂, hU₂⟩ := ih₂ A₂
    have hA : Fin.append A₁ A₂ = A := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [A₁, A₂]
    obtain ⟨W', hW', hparent⟩ := exists_isometry_chainPairMatrix_append hD A₁ A₂
      U₁.matrix U₂.matrix U₁.isIsometry_matrix U₂.isIsometry_matrix hU₁ hU₂
    refine ⟨.fork U₁ U₂ W' hW', ?_⟩
    change (IsometryTree.joinMatrix U₁.matrix U₂.matrix * W') *
      polarPos (chainPairMatrix A) = chainPairMatrix A
    simpa only [hA] using hparent

/-- A balanced binary geometry exists whenever every leaf can hold the virtual space.
The leaf length and all virtual dimensions are independent of the tree height. -/
theorem IsometryTree.nonempty_of_leaf_dimension (d χ s : ℕ) (hs : 0 < s)
    (hχ : 0 < χ) (hdim : χ ≤ d ^ s) (h : ℕ) :
    Nonempty (IsometryTree d χ s h (s * 2 ^ h)) := by
  classical
  have hleaf : Fintype.card (Fin χ) ≤ Fintype.card (Fin s → Fin d) := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using hdim
  obtain ⟨V, hV, _⟩ := Matrix.exists_isometry_mul_polarPos_eq
    (0 : Matrix (Fin s → Fin d) (Fin χ) ℂ) hleaf
  have hmerge : Fintype.card (Fin χ) ≤ Fintype.card (Fin (blockPhysDim χ 2)) := by
    simpa only [Fintype.card_fin, blockPhysDim_eq_pow, pow_two] using
      Nat.le_mul_of_pos_right χ hχ
  obtain ⟨W, hW, _⟩ := Matrix.exists_isometry_mul_polarPos_eq
    (0 : Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ) hmerge
  induction h with
  | zero => exact ⟨(.leaf V hV hs le_rfl).cast (by simp)⟩
  | succ h ih =>
    obtain ⟨T⟩ := ih
    exact ⟨(.fork T T W hW).cast (by rw [pow_succ]; ring)⟩

/-- Every site-dependent chain on `s 2^h` sites has an exact polar tree of height `h`
with leaves of at most `s` sites, provided `d^s ≥ D²`. This is an algebraic factorization;
no approximation class or uniform decay rate is assumed, and no measurement protocol is
asserted. Source: the interval-dependent tree underlying arXiv:2307.01696, eq. (16). -/
theorem exists_isometryTree_chainPairMatrix {s h : ℕ} (hD : 0 < D) (hs : 0 < s)
    (hdim : D * D ≤ d ^ s) (A : MPSChainTensor d D (s * 2 ^ h)) :
    ∃ T : IsometryTree d (D * D) s h (s * 2 ^ h),
      T.matrix * polarPos (chainPairMatrix A) = chainPairMatrix A ∧
      T.matrix * polarSupport (chainPairMatrix A) = polarIso (chainPairMatrix A) := by
  obtain ⟨T⟩ := IsometryTree.nonempty_of_leaf_dimension d (D * D) s hs
    (Nat.mul_pos hD hD) hdim h
  exact exists_isometryTree_mul_polarPos_eq hD T A

end MPSPreparation
