/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.BlockPermutation
import TNLean.Channel.FixedPoint.DirectSumInverseKraus

import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Simple summands of inverse completely positive maps

This file identifies the simple matrix summands carried into one another by a
star-algebra equivalence between two finite products. It then applies this
classification to the star-algebra equivalence associated with mutually
inverse completely positive trace-preserving maps.

This is the sector-relabeling and dimension-matching part of
arXiv:1606.00608, Appendix C.4, line 1997. The cited proof in
Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8, source lines 322--324, first
permutes summands of equal matrix dimension and only then identifies the map
inside each summand. Unitary implementation is not proved here.
-/

open scoped Matrix

noncomputable section

namespace Matrix

variable {ι κ : Type*}
variable [Finite ι] [DecidableEq ι] [Finite κ] [DecidableEq κ]
variable {d : ι → ℕ} {e : κ → ℕ}
variable [∀ i, NeZero (d i)] [∀ j, NeZero (e j)]

noncomputable local instance sourceMatrix_isSimpleRing (i : ι) :
    IsSimpleRing (Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  have : Nonempty (Fin (d i)) := Fin.pos_iff_nonempty.mp (NeZero.pos (d i))
  exact IsSimpleRing.matrix (Fin (d i)) ℂ

noncomputable local instance targetMatrix_isSimpleRing (j : κ) :
    IsSimpleRing (Matrix (Fin (e j)) (Fin (e j)) ℂ) := by
  have : Nonempty (Fin (e j)) := Fin.pos_iff_nonempty.mp (NeZero.pos (e j))
  exact IsSimpleRing.matrix (Fin (e j)) ℂ

/-- The linear map from one source summand to its paired target summand.

This is the linear restriction used to compare summand dimensions in
arXiv:1005.4545, Theorem 8, source lines 322--324. -/
private noncomputable def blockComponentLinearMap
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (σ : ι ≃ κ) (i : ι) :
    Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ]
      Matrix (Fin (e (σ i))) (Fin (e (σ i))) ℂ := by
  classical
  exact
    { toFun := fun M ↦ T (Pi.single i M) (σ i)
      map_add' := fun M N ↦ by
        simp only [Pi.single_add, map_add, Pi.add_apply]
      map_smul' := fun c M ↦ by
        simp only [Pi.single_smul, map_smul, Pi.smul_apply, RingHom.id_apply] }

/-- A star-algebra equivalence between two finite products of nonzero full
matrix algebras matches their simple summands and their matrix dimensions.

This is the first conclusion of the relabeling argument in arXiv:1606.00608,
Appendix C.4, line 1997, following Wolf--Perez-Garcia,
arXiv:1005.4545, Theorem 8, source lines 322--324. -/
theorem exists_blockEquiv_dim_eq_of_starAlgEquiv_pi_matrix
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)) :
    ∃ σ : ι ≃ κ,
      (∀ i, T.toRingEquiv.mapTwoSidedIdeal
        (MPSTensor.blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
          MPSTensor.blockIdeal (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (σ i)) ∧
      ∀ i, d i = e (σ i) := by
  classical
  obtain ⟨σ, hσ⟩ :=
    MPSTensor.exists_blockEquiv_of_ringEquiv_pi_simple T.toRingEquiv
  refine ⟨σ, hσ, ?_⟩
  intro i
  let φ := blockComponentLinearMap T σ i
  have hφBij : Function.Bijective φ := by
    exact MPSTensor.blockComponentMap_bijective T.toRingEquiv σ hσ i
  have hfinrank := (LinearEquiv.ofBijective φ hφBij).finrank_eq
  rw [Module.finrank_matrix, Module.finrank_matrix] at hfinrank
  simp only [Module.finrank_self, Fintype.card_fin, mul_one] at hfinrank
  exact Nat.mul_self_inj.mp hfinrank

/-- Mutually inverse completely positive trace-preserving maps between two
finite products of nonzero full matrix algebras match their simple summands
and the corresponding matrix dimensions.

This is the simple-summand matching conclusion in arXiv:1606.00608,
Appendix C.4, line 1997, following Wolf--Perez-Garcia,
arXiv:1005.4545, Theorem 8, source lines 322--324.

**Scope restriction (simple summands):** This theorem does not construct the
unitary action within each paired summand. That remaining conclusion is
documented in `docs/paper-gaps/cpsv16_vertical_sector_invertibility.tex`. -/
theorem exists_blockEquiv_dim_eq_of_mutual_inverse_kraus_direct_sum_maps
    [Fintype ι] [Fintype κ]
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (hT : IsKrausDirectSumMap T) (hS : IsKrausDirectSumMap S)
    (hTTP : IsTracePreservingBetweenDirectSums T)
    (hSTP : IsTracePreservingBetweenDirectSums S)
    (hST : S.comp T = LinearMap.id) (hTS : T.comp S = LinearMap.id) :
    let E := (directSumTraceAdjointStarAlgEquiv T S hT hS hTTP hSTP hST hTS).symm
    ∃ σ : ι ≃ κ,
      (∀ i, E.toRingEquiv.mapTwoSidedIdeal
        (MPSTensor.blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
          MPSTensor.blockIdeal (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (σ i)) ∧
      ∀ i, d i = e (σ i) := by
  exact exists_blockEquiv_dim_eq_of_starAlgEquiv_pi_matrix
    (directSumTraceAdjointStarAlgEquiv T S hT hS hTTP hSTP hST hTS).symm

end Matrix
