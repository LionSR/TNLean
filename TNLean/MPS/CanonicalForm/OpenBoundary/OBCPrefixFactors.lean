/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationCuts
import TNLean.MPS.CanonicalForm.OpenBoundary.OBCCanonicalConfigurations
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationFactorization
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Actual prefix factors of an arbitrary open-boundary representation

The physical prefix matrix is the actual product of the original site
matrices, restricted to the current virtual bond. Its adjacent-cut
recursion uses those original rectangular matrices. Every physical cut
coefficient column lies in its range, by the actual open-chain contraction.

Source: PGVWC07, arXiv:quant-ph/0608197, free-OBC and its local rectangular
maps, lines 461--522.

## Rectangular maps from every OBC representation to the physical cut bases

The physical cut column space is contained in the range of the original
prefix contraction. Thus every chosen minimal cut basis lifts through
that prefix matrix. A left inverse of the minimal prefix gives the reverse
map, their product is the identity on the minimal bond, and adjacent
physical prefix recursions prove the local rectangular site formula.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem free-OBC and
Eq. eq.lem.II.9, lines 461--522.
-/

open ManyBody (interval cutMatrix cutRank RegionConfig ComplConfig)

section

open Matrix
open scoped BigOperators

namespace OBCChainTensor

open MPSPreparation

variable {d D N : ℕ} (B : OBCChainTensor d D N)

private def prefixProduct (k : Fin (N + 1)) (u : RegionConfig (fun _ : Fin N ↦ Fin d)
    (interval N 0 k.val)) :
    Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun p : Fin k.val ↦ B.zeroPad (Fin.castLE (Nat.lt_succ_iff.mp k.isLt) p)
    (u ⟨Fin.castLE (Nat.lt_succ_iff.mp k.isLt) p, mem_interval_zero_iff.mpr p.isLt⟩)).prod

/-- The actual physical prefix matrix of the supplied representation,
with columns indexed by its original virtual bond.
Source: PGVWC07, free-OBC, lines 461--522. -/
def physicalPrefixMatrix (k : Fin (N + 1)) :
    Matrix (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k.val)) (Fin (B.bondDim k)) ℂ :=
  fun u a ↦ prefixProduct B k u ⟨0, B.bondBound_pos⟩ (Fin.castLE (B.bondDim_le k) a)

private theorem prefixProduct_outside (k : Fin (N + 1))
    (u : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k.val)) (γ : Fin D) (hγ : B.bondDim k ≤
        γ.val) :
    prefixProduct B k u ⟨0, B.bondBound_pos⟩ γ = 0 := by
  classical
  rcases k with ⟨k, hk⟩
  cases k with
  | zero =>
      have hγ0 : γ.val ≠ 0 := by
        have h := B.left_dim
        change B.bondDim 0 ≤ γ.val at hγ
        rw [h] at hγ
        omega
      simp only [prefixProduct, List.ofFn_zero, List.prod_nil]
      exact Matrix.one_apply_ne (fun h ↦ hγ0 (Fin.ext_iff.mp h).symm)
  | succ k =>
      rw [prefixProduct, List.ofFn_succ', List.prod_concat, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro β _
      apply mul_eq_zero_of_right
      apply Matrix.zeroPad_apply_eq_zero
      intro hlt
      have heq : (Fin.castLE (Nat.lt_succ_iff.mp hk) (Fin.last k)).succ =
          (⟨k + 1, hk⟩ : Fin (N + 1)) := Fin.ext rfl
      have hcol := hlt.2
      change γ.val < B.bondDim _ at hcol
      rw [heq] at hcol
      exact (not_lt_of_ge hγ) hcol

private theorem prefixProduct_step (p : Fin N) (u : RegionConfig (fun _ : Fin N ↦ Fin d)
    (interval N 0 p.val)) (i : Fin d) :
    prefixProduct B p.succ (extendCutPrefix p.val u i) =
      prefixProduct B p.castSucc u * B.zeroPad p i := by
  classical
  rw [prefixProduct, List.ofFn_succ', List.prod_concat]
  apply congrArg₂ (· * ·)
  · apply congrArg List.prod
    apply congrArg List.ofFn
    funext q
    simp only [extendCutPrefix, Fin.val_castLE, Fin.val_castSucc, q.isLt, dite_true]
    rfl
  · simp only [extendCutPrefix, Fin.val_castLE, Fin.val_last, Nat.lt_irrefl, dite_false]
    rfl

/-- The actual arbitrary-representation prefix factors propagate by the
original site matrices. Source: PGVWC07, free-OBC, local maps in
lines 475--486 and the factorization proof in lines 490--522. -/
theorem physicalPrefixMatrix_step (p : Fin N) (u : RegionConfig (fun _ : Fin N ↦ Fin d)
    (interval N 0 p.val))
    (i : Fin d) (q : Fin (B.bondDim p.succ)) :
    physicalPrefixMatrix B p.succ (extendCutPrefix p.val u i) q =
      (physicalPrefixMatrix B p.castSucc * B.tensor p i) u q := by
  classical
  change prefixProduct B p.succ (extendCutPrefix p.val u i) ⟨0, B.bondBound_pos⟩
    (Fin.castLE (B.bondDim_le p.succ) q) = _
  rw [prefixProduct_step]
  simp only [Matrix.mul_apply]
  rw [Fin.sum_castLE_extend_zero _ (B.bondDim_le p.castSucc)]
  apply Finset.sum_congr rfl
  intro γ _
  split_ifs with hγ
  · rw [show B.zeroPad p i = Matrix.zeroPad D (B.tensor p i) from rfl,
      Matrix.zeroPad_apply_of_lt _ hγ q.isLt]
    rfl
  · rw [prefixProduct_outside B p.castSucc u γ (not_lt.mp hγ), zero_mul]

/-- The left endpoint prefix factor is the scalar identity in the
one-dimensional endpoint bond coordinates.
Source: PGVWC07, endpoint convention preceding Theorem thm:OBC-Vidal. -/
theorem physicalPrefixMatrix_zero (u : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 0)) (q :
    Fin (B.bondDim 0)) :
    physicalPrefixMatrix B 0 u q = 1 := by
  have hq : q.val = 0 := by have h := q.isLt; have hd := B.left_dim; omega
  have h0 : prefixProduct B 0 u = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨j, -⟩ := List.mem_ofFn.mp hx
    exact absurd j.isLt (by simp)
  simp only [physicalPrefixMatrix]
  rw [h0, Matrix.one_apply]
  have hidx : (⟨0, B.bondBound_pos⟩ : Fin D) = Fin.castLE (B.bondDim_le 0) q := Fin.ext hq.symm
  simp only [hidx, ↓reduceIte]

/-- The right endpoint prefix factor is the actual represented physical
state, including its complete complex amplitude.
Source: PGVWC07, the OBC contraction in free-OBC, lines 461--486. -/
theorem physicalPrefixMatrix_last (u : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 N))
    (q : Fin (B.bondDim (Fin.last N))) :
    physicalPrefixMatrix B (Fin.last N) u q = B.coeff (finalCutPrefixEquiv d N u) := by
  have hq : q.val = 0 := by have h := q.isLt; have hd := B.right_dim; omega
  have hfull : prefixProduct B (Fin.last N) u =
      MPSChainTensor.eval B.zeroPad (finalCutPrefixEquiv d N u) := by
    rw [MPSChainTensor.eval_eq_prod_ofFn]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext p
    rfl
  rw [coeff_eq_eval_zeroPad]
  change prefixProduct B (Fin.last N) u ⟨0, B.bondBound_pos⟩
    (Fin.castLE (B.bondDim_le (Fin.last N)) q) = _
  have hq' : Fin.castLE (B.bondDim_le (Fin.last N)) q = ⟨0, B.bondBound_pos⟩ := Fin.ext hq
  rw [hq', hfull]

/-- The actual physical suffix matrix of the supplied representation,
with rows indexed by its original virtual bond.
Source: PGVWC07, free-OBC, actual boundary contractions in lines 461--522. -/
def physicalSuffixMatrix (k : Fin (N + 1)) :
    Matrix (Fin (B.bondDim k)) (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k.val)) ℂ :=
  fun a v ↦ (List.ofFn fun q : Fin (N - k.val) ↦
    B.zeroPad ⟨k.val + q.val, by have := q.isLt; omega⟩
      (v ⟨⟨k.val + q.val, by have := q.isLt; omega⟩,
        notMem_interval_zero_iff.mpr (Nat.le_add_right _ _)⟩)).prod
        (Fin.castLE (B.bondDim_le k) a) ⟨0, B.bondBound_pos⟩

/-- Every actual physical cut coefficient matrix factors through the
original virtual bond by the actual prefix and suffix contractions.
Source: PGVWC07, the OBC contraction in free-OBC, lines 461--486. -/
theorem cutMatrix_eq_physicalPrefix_mul_suffix (k : Fin (N + 1)) :
    cutMatrix (interval N 0 k.val) B.coeff = physicalPrefixMatrix B k *
        physicalSuffixMatrix B k := by
  classical
  have hk : k.val ≤ N := Nat.lt_succ_iff.mp k.isLt
  ext u v
  change B.coeff ((ManyBody.cutEquiv _ (interval N 0 k.val)).symm (u, v)) = _
  rw [coeff_eq_eval_zeroPad, eval_cutEquiv_symm _ hk]
  simp only [Matrix.mul_apply]
  rw [Fin.sum_castLE_extend_zero _ (B.bondDim_le k)]
  apply Finset.sum_congr rfl
  intro γ _
  split_ifs with hγ
  · rfl
  · change prefixProduct B k u ⟨0, B.bondBound_pos⟩ γ * _ = 0
    rw [prefixProduct_outside B k u γ (not_lt.mp hγ), zero_mul]

/-- The actual physical cut column space is contained in the range of
the original-representation prefix matrix. This supplies the rectangular
maps to a minimal representation without assuming a gauge or rank equality.
Source: PGVWC07, free-OBC, lines 461--522. -/
theorem cutColumnSpace_le_range_physicalPrefixMatrix (k : Fin (N + 1)) :
    cutColumnSpace B.coeff k.val ≤ LinearMap.range (physicalPrefixMatrix B k).mulVecLin := by
  rw [cutColumnSpace, ← Matrix.range_mulVecLin,
    cutMatrix_eq_physicalPrefix_mul_suffix B k, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

end OBCChainTensor

end

section

open Matrix
open scoped BigOperators

namespace MPSPreparation

/-- Every physical cut-basis prefix factor has a left inverse, derived
from its basis independence. Source: PGVWC07, free-OBC, left inverses
of retained cut factors in lines 494--508. -/
theorem exists_cutPrefixMatrix_leftInverse {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (C : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k)) (k : ℕ) :
    ∃ T : Matrix (Fin (cutRank (interval N 0 k) ψ)) (RegionConfig (fun _ : Fin N ↦ Fin d)
        (interval N 0 k)) ℂ,
      T * cutPrefixMatrix ψ C k = 1 := by
  classical
  have hli : LinearIndependent ℂ (cutPrefixMatrix ψ C k).col :=
    (C k).linearIndependent.map' (cutColumnSpace ψ k).subtype
      (cutColumnSpace ψ k).ker_subtype
  have hinj := Matrix.mulVec_injective_iff.mpr hli
  obtain ⟨T, hT⟩ := (cutPrefixMatrix ψ C k).mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨LinearMap.toMatrix' T, ?_⟩
  simpa only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hT

end MPSPreparation

namespace OBCChainTensor

open MPSPreparation

/-- Any actual OBC representation maps to any physical minimal cut-basis
representation by local rectangular maps, with a one-sided inverse on
every minimal bond and the exact scalar endpoint identifications.
No full-rank or square-gauge hypothesis is supplied.
Source: PGVWC07, Theorem free-OBC and Eq. eq.lem.II.9, lines 461--522. -/
theorem exists_rectangular_maps_to_cutBasis {d D N : ℕ}
    (B : OBCChainTensor d D N) (ψ : (Fin N → Fin d) → ℂ) (hcoeff : B.coeff = ψ)
    (C : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (hC0 : ∀ q, (C 0 q).val = 1) (hCN : ∀ q, (C N q).val = fullCutVector ψ) :
    ∃ Y : (k : Fin (N + 1)) →
      Matrix (Fin (cutRank (interval N 0 k.val) ψ)) (Fin (B.bondDim k)) ℂ,
    ∃ Z : (k : Fin (N + 1)) →
      Matrix (Fin (B.bondDim k)) (Fin (cutRank (interval N 0 k.val) ψ)) ℂ,
      (∀ k, Y k * Z k = 1) ∧
      (∀ q r, Y 0 q r = 1) ∧ (∀ q r, Z (Fin.last N) q r = 1) ∧
      ∀ (p : Fin N) (i : Fin d),
        cutSiteMatrix ψ C p.val i = Y p.castSucc * B.tensor p i * Z p.succ := by
  classical
  have hlift : ∀ k : Fin (N + 1),
      ∃ Z : Matrix (Fin (B.bondDim k)) (Fin (cutRank (interval N 0 k.val) ψ)) ℂ,
        physicalPrefixMatrix B k * Z = cutPrefixMatrix ψ C k.val := by
    intro k
    have hmem : ∀ q, (C k.val q).val ∈ LinearMap.range (physicalPrefixMatrix B k).mulVecLin := by
      intro q
      have h := cutColumnSpace_le_range_physicalPrefixMatrix B k
      rw [hcoeff] at h
      exact h (C k.val q).property
    choose z hz using hmem
    refine ⟨fun a q ↦ z q a, ?_⟩
    ext u q
    exact congrFun (hz q) u
  choose Z₀ hZ₀ using hlift
  let Z : (k : Fin (N + 1)) →
      Matrix (Fin (B.bondDim k)) (Fin (cutRank (interval N 0 k.val) ψ)) ℂ := fun k ↦
    if k = Fin.last N then Matrix.of fun _ _ ↦ 1 else Z₀ k
  have hZ : ∀ k, physicalPrefixMatrix B k * Z k = cutPrefixMatrix ψ C k.val := by
    intro k
    by_cases hk : k = Fin.last N
    · subst k
      let : Unique (Fin (B.bondDim (Fin.last N))) := Equiv.unique (finCongr B.right_dim)
      ext u q
      have hCN' : ∀ q, (C (Fin.last N).val q).val = fullCutVector ψ := hCN
      simp only [Z, ↓reduceIte, cutPrefixMatrix, hCN']
      rw [Matrix.mul_apply, Fintype.sum_unique, physicalPrefixMatrix_last, Matrix.of_apply,
        mul_one]
      exact congrFun hcoeff (finalCutPrefixEquiv d N u)
    · simpa only [Z, hk, ↓reduceIte] using hZ₀ k
  choose T hT using fun k : Fin (N + 1) ↦ exists_cutPrefixMatrix_leftInverse ψ C k.val
  let Y : (k : Fin (N + 1)) →
      Matrix (Fin (cutRank (interval N 0 k.val) ψ)) (Fin (B.bondDim k)) ℂ :=
    fun k ↦ T k * physicalPrefixMatrix B k
  have hYZ : ∀ k, Y k * Z k = 1 := by
    intro k
    change T k * physicalPrefixMatrix B k * Z k = 1
    rw [Matrix.mul_assoc, hZ, hT]
  refine ⟨Y, Z, hYZ, ?_, ?_, ?_⟩
  · intro q r
    have h := congrArg (fun M ↦ M q q) (hT 0)
    have h1 : ∀ j, cutPrefixMatrix ψ C ((0 : Fin (N + 1)) : ℕ) j q = 1 :=
      fun j ↦ cutPrefixMatrix_zero ψ C hC0 j q
    have h2 : ∀ j, physicalPrefixMatrix B 0 j r = 1 := fun j ↦ physicalPrefixMatrix_zero B j r
    simp only [Matrix.mul_apply, h1, mul_one, Matrix.one_apply_eq] at h
    simpa only [Y, Matrix.mul_apply, h2, mul_one] using h
  · intro q r
    simp only [Z, ↓reduceIte, Matrix.of_apply]
  · intro p i
    have hstep : cutPrefixMatrix ψ C p.val * cutSiteMatrix ψ C p.val i =
        physicalPrefixMatrix B p.castSucc * B.tensor p i * Z p.succ := by
      ext u q
      rw [← cutPrefixMatrix_step]
      calc
        _ = (physicalPrefixMatrix B p.succ * Z p.succ) (extendCutPrefix p.val u i) q :=
          congrArg (fun M ↦ M (extendCutPrefix p.val u i) q) (hZ p.succ).symm
        _ = _ := by simp only [Matrix.mul_apply, physicalPrefixMatrix_step]
    let Tp : Matrix (Fin (cutRank (interval N 0 p.val) ψ)) (RegionConfig (fun _ : Fin N ↦ Fin d)
        (interval N 0 p.val)) ℂ :=
      T p.castSucc
    have hTp : Tp * cutPrefixMatrix ψ C p.val = 1 := hT p.castSucc
    calc
      cutSiteMatrix ψ C p.val i =
          (Tp * cutPrefixMatrix ψ C p.val) * cutSiteMatrix ψ C p.val i := by
        rw [hTp, Matrix.one_mul]
      _ = Tp * (cutPrefixMatrix ψ C p.val * cutSiteMatrix ψ C p.val i) :=
        Matrix.mul_assoc _ _ _
      _ = Tp * (show Matrix (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 p.val)) (Fin
          (cutRank (interval N 0 (p.val + 1)) ψ)) ℂ
            from physicalPrefixMatrix B p.castSucc * B.tensor p i * Z p.succ) :=
        congrArg (fun M ↦ Tp * M) hstep
      _ = _ := by simp only [Y, Tp, Matrix.mul_assoc]

end OBCChainTensor

end
