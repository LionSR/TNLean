/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OBCMinimalPrefixBasis
import TNLean.MPS.Preparation.PhysicalCutGramRecurrences
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Physical ranks of a prescribed faithful canonical OBC tensor

The canonical density recursion identifies the actual prefix Gram with
its supplied bond density. The row normalization identifies every actual
suffix Gram with the identity. Faithfulness therefore makes every
prescribed bond minimal for the represented physical state. The argument
retains the original rectangular site matrices and does not replace the
representation by a newly constructed canonical one.

Source: PGVWC07, arXiv:quant-ph/0608197, conditions 1--3 of Theorem
thm:OBC-Vidal, MPSarchive.tex lines 431--458, and the prescribed OBC
canonical window in Theorem 8, lines 1139--1169.
-/

open Matrix MPSPreparation
open scoped BigOperators ComplexOrder

namespace OBCChainTensor

variable {d Q N : ℕ} (B : OBCChainTensor d Q N)

/-- The original physical prefix factors satisfy the canonical Gram
recursion before any density is supplied.
Source: PGVWC07, Theorem thm:OBC-Vidal, condition 2, lines 444--456. -/
theorem physicalPrefixMatrix_gram_step (p : Fin N) :
    ∑ i, (B.tensor p i)ᴴ *
      ((physicalPrefixMatrix B p.castSucc)ᴴ * physicalPrefixMatrix B p.castSucc) *
      B.tensor p i = (physicalPrefixMatrix B p.succ)ᴴ * physicalPrefixMatrix B p.succ := by
  exact prefixGram_eq_sum_of_extendCutPrefix p.isLt (physicalPrefixMatrix B p.castSucc)
    (physicalPrefixMatrix B p.succ) (B.tensor p) (physicalPrefixMatrix_step B p)

/-- The actual prefix Gram at the scalar left boundary is the identity.
Source: PGVWC07, Theorem thm:OBC-Vidal, condition 3, lines 449--456. -/
theorem physicalPrefixMatrix_zero_gram :
    (physicalPrefixMatrix B 0)ᴴ * physicalPrefixMatrix B 0 = 1 := by
  classical
  let : IsEmpty {s : Fin N // s.val < 0} := ⟨fun s ↦ Nat.not_lt_zero _ s.property⟩
  let : Unique (Fin (B.bondDim 0)) := Equiv.unique (finCongr B.left_dim)
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, physicalPrefixMatrix_zero]

/-- The supplied canonical densities are the actual physical prefix
Grams, derived from their source recursion and scalar initial boundary.
Source: PGVWC07, Theorem thm:OBC-Vidal, conditions 2--3, lines 444--456. -/
theorem physicalPrefixMatrix_gram_eq_density
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (k : Fin (N + 1)) : (physicalPrefixMatrix B k)ᴴ * physicalPrefixMatrix B k = Λ k := by
  refine Fin.induction ?_ (fun p ih ↦ ?_) k
  · exact (physicalPrefixMatrix_zero_gram B).trans hzero.symm
  · rw [← physicalPrefixMatrix_gram_step B p, ih, hstep]

/-- The actual suffix factors recurse by the original first site matrix.
Source: PGVWC07, the OBC contraction in lines 419--429. -/
theorem physicalSuffixMatrix_step (p : Fin N) (i : Fin d)
    (v : CutSuffixConfig d N (p.val + 1)) (a : Fin (B.bondDim p.castSucc)) :
    physicalSuffixMatrix B p.castSucc a (extendCutSuffix p.val i v) =
      (B.tensor p i * physicalSuffixMatrix B p.succ) a v := by
  classical
  have hlen : N - p.val = (N - (p.val + 1)) + 1 := by have := p.isLt; omega
  have hword :
      List.ofFn (fun q : Fin (N - p.val) ↦
        B.zeroPad ⟨p.val + q.val, by have := q.isLt; omega⟩
          (extendCutSuffix p.val i v
            ⟨⟨p.val + q.val, by have := q.isLt; omega⟩, Nat.le_add_right _ _⟩)) =
        B.zeroPad p i :: List.ofFn (fun q : Fin (N - (p.val + 1)) ↦
          B.zeroPad ⟨p.val + 1 + q.val, by have := q.isLt; omega⟩
            (v ⟨⟨p.val + 1 + q.val, by have := q.isLt; omega⟩,
              Nat.le_add_right _ _⟩)) := by
    rw [List.ofFn_congr hlen, List.ofFn_succ]
    apply congrArg₂ List.cons
    · simp only [Fin.val_cast, Fin.val_zero, Nat.add_zero, extendCutSuffix,
        Nat.not_succ_le_self, dite_false]
      rfl
    · apply congrArg List.ofFn
      funext q
      simp only [Fin.val_cast, Fin.val_succ]
      congr 1
      · exact Fin.ext (by omega)
      · simp only [extendCutSuffix,
          show p.val + 1 ≤ p.val + (q.val + 1) by omega, dite_true]
        apply congrArg v
        exact Subtype.ext (Fin.ext (by omega))
  change (List.ofFn _).prod (Fin.castLE (B.bondDim_le p.castSucc) a)
    ⟨0, B.bondBound_pos⟩ = _
  rw [hword, List.prod_cons, Matrix.mul_apply]
  rw [Fin.sum_castLE_extend_zero _ (B.bondDim_le p.succ)]
  apply Finset.sum_congr rfl
  intro γ _
  split_ifs with hγ
  · rw [Matrix.zeroPad_apply_of_lt _ a.isLt hγ]
    rfl
  · rw [Matrix.zeroPad_apply_eq_zero _ (by intro h; exact hγ h.2),
      zero_mul]

/-- The actual suffix factor at the scalar right endpoint has every
entry equal to one. Source: PGVWC07, scalar OBC boundaries, lines 419--429. -/
theorem physicalSuffixMatrix_last (a : Fin (B.bondDim (Fin.last N)))
    (v : CutSuffixConfig d N N) : physicalSuffixMatrix B (Fin.last N) a v = 1 := by
  have ha : a.val = 0 := by have := a.isLt; rw [B.right_dim] at this; omega
  simp only [physicalSuffixMatrix, Fin.val_last, Nat.sub_self, List.ofFn_zero,
    List.prod_nil, Matrix.one_apply]
  exact if_pos (Fin.ext ha)

/-- The actual suffix Grams satisfy the backward canonical recursion.
Source: PGVWC07, Theorem thm:OBC-Vidal, condition 1, lines 444--456. -/
theorem physicalSuffixMatrix_gram_step (p : Fin N) :
    physicalSuffixMatrix B p.castSucc * (physicalSuffixMatrix B p.castSucc)ᴴ =
      ∑ i, B.tensor p i *
        (physicalSuffixMatrix B p.succ * (physicalSuffixMatrix B p.succ)ᴴ) *
          (B.tensor p i)ᴴ := by
  exact suffixGram_eq_sum_of_extendCutSuffix p.isLt (physicalSuffixMatrix B p.castSucc)
    (physicalSuffixMatrix B p.succ) (B.tensor p)
    (fun i v q ↦ physicalSuffixMatrix_step B p i v q)

/-- Row normalization forces every original physical suffix factor to
be row-coisometric. Source: PGVWC07, condition 1 and scalar right boundary
of Theorem thm:OBC-Vidal, lines 444--456. -/
theorem physicalSuffixMatrix_coisometry
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (k : Fin (N + 1)) : physicalSuffixMatrix B k * (physicalSuffixMatrix B k)ᴴ = 1 := by
  classical
  refine Fin.reverseInduction ?_ (fun p ih ↦ ?_) k
  · let : IsEmpty {s : Fin N // N ≤ s.val} := ⟨fun s ↦ by have := s.val.isLt; omega⟩
    let : Unique (Fin (B.bondDim (Fin.last N))) := Equiv.unique (finCongr B.right_dim)
    ext q r
    have hqr : q = r := Subsingleton.elim _ _
    subst r
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, physicalSuffixMatrix_last]
  · rw [physicalSuffixMatrix_gram_step B p, ih]
    simpa only [Matrix.mul_one] using hrow p

/-- Every bond of the prescribed faithful canonical OBC representation
is the actual physical cut rank. All rank information is derived from
its source density and row-normalization equations.
Source: PGVWC07, Theorem thm:OBC-Vidal, conditions 1--3, lines 444--458. -/
theorem bondDim_eq_cutCoefficientRank_of_canonical
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef)
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (k : Fin (N + 1)) : B.bondDim k = cutCoefficientRank B.coeff k.val := by
  classical
  let F := physicalPrefixMatrix B k
  let G := physicalSuffixMatrix B k
  have hGram : Fᴴ * F = Λ k := physicalPrefixMatrix_gram_eq_density B Λ hzero hstep k
  have hinj : Function.Injective F.mulVec := by
    intro x y hxy
    apply (hfaithful k).mulVec_injective
    simpa only [Matrix.mulVec_mulVec, hGram] using congrArg (Fᴴ).mulVec hxy
  have hli : LinearIndependent ℂ F.col := Matrix.mulVec_injective_iff.mp hinj
  have hRankF : F.rank = B.bondDim k := by
    have h := (show LinearIndependent ℂ Fᵀ.row from hli).rank_matrix
    simpa only [Matrix.rank_transpose, Fintype.card_fin] using h
  have hrecover : cutCoefficientMatrix B.coeff k.val * Gᴴ = F := by
    rw [cutCoefficientMatrix_eq_physicalPrefix_mul_suffix B k, Matrix.mul_assoc,
      physicalSuffixMatrix_coisometry B hrow k, Matrix.mul_one]
  apply le_antisymm
  · rw [← hRankF, ← hrecover]
    exact Matrix.rank_mul_le_left _ _
  · rw [cutCoefficientRank_eq_cutRank _ (Nat.lt_succ_iff.mp k.isLt)]
    exact B.cutRank_coeff_le k

/-- Faithfulness of the final canonical density proves that the actual
represented vector is nonzero. No nonvanishing premise is supplied.
Source: PGVWC07, Theorem thm:OBC-Vidal, conditions 2--3, lines 444--456. -/
theorem coeff_ne_zero_of_faithful_density
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef) : B.coeff ≠ 0 := by
  classical
  intro hcoeff
  have hF : physicalPrefixMatrix B (Fin.last N) = 0 := by
    ext u q
    rw [physicalPrefixMatrix_last, hcoeff]
    rfl
  have hΛ : Λ (Fin.last N) = 0 := by
    rw [← physicalPrefixMatrix_gram_eq_density B Λ hzero hstep (Fin.last N), hF,
      Matrix.conjTranspose_zero, Matrix.zero_mul]
  let : Nonempty (Fin (B.bondDim (Fin.last N))) := ⟨⟨0, by rw [B.right_dim]; omega⟩⟩
  have hunit := (hfaithful (Fin.last N)).isUnit
  rw [hΛ] at hunit
  exact not_isUnit_zero hunit

/-- Changing only a verified common upper bound retains every original
bond space and rectangular site matrix.
Source: PGVWC07, OBC bond bounds in lines 419--429 and 456--458. -/
def withBondBound {R : ℕ} (hbound : ∀ k, B.bondDim k ≤ R) : OBCChainTensor d R N where
  bondDim := B.bondDim
  bondDim_le := hbound
  left_dim := B.left_dim
  right_dim := B.right_dim
  tensor := B.tensor

/-- Replacing the common upper bound leaves the original rectangular
site matrices definitionally unchanged.
Source: PGVWC07, OBC tensor data, lines 419--429. -/
@[simp] theorem withBondBound_tensor {R : ℕ} (hbound : ∀ k, B.bondDim k ≤ R)
    (p : Fin N) (i : Fin d) : (withBondBound B hbound).tensor p i = B.tensor p i := rfl

/-- Replacing only the common upper bound retains the exact coefficient
vector because its actual dependent virtual-path sum is unchanged.
Source: PGVWC07, OBC contraction, lines 419--429. -/
@[simp] theorem withBondBound_coeff {R : ℕ} (hbound : ∀ k, B.bondDim k ≤ R) :
    (withBondBound B hbound).coeff = B.coeff := rfl

end OBCChainTensor
