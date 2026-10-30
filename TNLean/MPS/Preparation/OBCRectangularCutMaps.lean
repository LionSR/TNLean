/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OBCPrefixFactors
import TNLean.MPS.Preparation.MinimalCutRepresentationFactorization
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Rectangular maps from every OBC representation to the physical cut bases

The physical cut column space is contained in the range of the original
prefix contraction. Thus every chosen minimal cut basis lifts through
that prefix matrix. A left inverse of the minimal prefix gives the reverse
map, their product is the identity on the minimal bond, and adjacent
physical prefix recursions prove the local rectangular site formula.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem free-OBC and
Eq. eq.lem.II.9, lines 461--522.
-/

open Matrix
open scoped BigOperators

namespace MPSPreparation

/-- Every physical cut-basis prefix factor has a left inverse, derived
from its basis independence. Source: PGVWC07, free-OBC, left inverses
of retained cut factors in lines 494--508. -/
theorem exists_cutPrefixMatrix_leftInverse {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (C : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k)) (k : ℕ) :
    ∃ T : Matrix (Fin (cutCoefficientRank ψ k)) (CutPrefixConfig d N k) ℂ,
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
    (C : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hC0 : ∀ q, (C 0 q).val = 1) (hCN : ∀ q, (C N q).val = fullCutVector ψ) :
    ∃ Y : (k : Fin (N + 1)) →
      Matrix (Fin (cutCoefficientRank ψ k.val)) (Fin (B.bondDim k)) ℂ,
    ∃ Z : (k : Fin (N + 1)) →
      Matrix (Fin (B.bondDim k)) (Fin (cutCoefficientRank ψ k.val)) ℂ,
      (∀ k, Y k * Z k = 1) ∧
      (∀ q r, Y 0 q r = 1) ∧ (∀ q r, Z (Fin.last N) q r = 1) ∧
      ∀ (p : Fin N) (i : Fin d),
        cutSiteMatrix ψ C p.val i = Y p.castSucc * B.tensor p i * Z p.succ := by
  classical
  have hlift : ∀ k : Fin (N + 1),
      ∃ Z : Matrix (Fin (B.bondDim k)) (Fin (cutCoefficientRank ψ k.val)) ℂ,
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
      Matrix (Fin (B.bondDim k)) (Fin (cutCoefficientRank ψ k.val)) ℂ := fun k ↦
    if k = Fin.last N then Matrix.of fun _ _ ↦ 1 else Z₀ k
  have hZ : ∀ k, physicalPrefixMatrix B k * Z k = cutPrefixMatrix ψ C k.val := by
    intro k
    by_cases hk : k = Fin.last N
    · subst k
      let : Unique (Fin (B.bondDim (Fin.last N))) := Equiv.unique (finCongr B.right_dim)
      have hZl : Z (Fin.last N) = Matrix.of fun _ _ ↦ 1 := by simp [Z]
      ext u q
      rw [hZl]
      simp only [Matrix.mul_apply, Matrix.of_apply, physicalPrefixMatrix_last, mul_one,
        Fintype.sum_unique]
      change B.coeff (finalCutPrefixEquiv d N u) = (C N q).val u
      rw [hCN, hcoeff]
      rfl
    · have hZk : Z k = Z₀ k := by simp [Z, hk]
      rw [hZk]
      exact hZ₀ k
  choose T hT using fun k : Fin (N + 1) ↦ exists_cutPrefixMatrix_leftInverse ψ C k.val
  let Y : (k : Fin (N + 1)) →
      Matrix (Fin (cutCoefficientRank ψ k.val)) (Fin (B.bondDim k)) ℂ :=
    fun k ↦ T k * physicalPrefixMatrix B k
  have hYZ : ∀ k, Y k * Z k = 1 := by
    intro k
    change T k * physicalPrefixMatrix B k * Z k = 1
    rw [Matrix.mul_assoc, hZ, hT]
  refine ⟨Y, Z, hYZ, ?_, ?_, ?_⟩
  · intro q r
    have h := congrArg (fun M ↦ M q q) (hT 0)
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [← h]
    simp only [Y, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro u _
    have hp : B.physicalPrefixMatrix 0 u r = 1 := physicalPrefixMatrix_zero B u r
    rw [hp, mul_one]
    have hu : cutPrefixMatrix ψ C (0 : Fin (N + 1)).val u q = 1 := congrFun (hC0 q) u
    rw [hu, mul_one]
  · intro q r
    simp [Z]
  · intro p i
    have hstep : cutPrefixMatrix ψ C p.val * cutSiteMatrix ψ C p.val i =
        physicalPrefixMatrix B p.castSucc * B.tensor p i * Z p.succ := by
      ext u q
      rw [← cutPrefixMatrix_step]
      calc
        _ = (physicalPrefixMatrix B p.succ * Z p.succ) (extendCutPrefix p.val u i) q :=
          congrArg (fun M ↦ M (extendCutPrefix p.val u i) q) (hZ p.succ).symm
        _ = _ := by simp only [Matrix.mul_apply, physicalPrefixMatrix_step]
    have hT' : T p.castSucc * cutPrefixMatrix ψ C p.castSucc.val = 1 := hT p.castSucc
    have hstep' : cutPrefixMatrix ψ C p.castSucc.val * cutSiteMatrix ψ C p.castSucc.val i =
        physicalPrefixMatrix B p.castSucc * B.tensor p i * Z p.succ := hstep
    calc
      cutSiteMatrix ψ C p.val i = cutSiteMatrix ψ C p.castSucc.val i := rfl
      _ = (T p.castSucc * cutPrefixMatrix ψ C p.castSucc.val) *
          cutSiteMatrix ψ C p.castSucc.val i := by
        rw [hT', Matrix.one_mul]
      _ = T p.castSucc *
          (cutPrefixMatrix ψ C p.castSucc.val * cutSiteMatrix ψ C p.castSucc.val i) :=
        Matrix.mul_assoc _ _ _
      _ = T p.castSucc * (physicalPrefixMatrix B p.castSucc * B.tensor p i * Z p.succ) := by
        rw [hstep']
      _ = _ := by simp only [Y, Matrix.mul_assoc]

end OBCChainTensor
