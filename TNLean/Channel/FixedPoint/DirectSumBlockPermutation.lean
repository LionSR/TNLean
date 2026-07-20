/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.BlockPermutation
import TNLean.Algebra.SkolemNoetherUnitary
import TNLean.Algebra.TraceReindex
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
inside each summand. The present file proves the resulting blockwise-unitary
formula first for the trace-adjoint star-algebra equivalence and then for the
original mutually inverse maps. The transported MPDO specialization is stated
separately.
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

/-- A star-algebra equivalence between finite products of nonzero full matrix
algebras acts by unitary conjugation inside the simple summands selected by its
block-ideal matching.

This is the blockwise-unitary portion of arXiv:1606.00608, Appendix C.4,
line 1997, following Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8,
source lines 322--324. The companion formula for the inverse map is not
asserted here. -/
theorem exists_blockEquiv_dim_eq_unitary_of_starAlgEquiv_pi_matrix
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)) :
    ∃ sigma : ι ≃ κ, ∃ hDim : ∀ i, d i = e (sigma i),
      (∀ i, T.toRingEquiv.mapTwoSidedIdeal
        (MPSTensor.blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
          MPSTensor.blockIdeal
            (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (sigma i)) ∧
      ∃ U : ∀ i, Matrix.unitaryGroup (Fin (e (sigma i))) ℂ,
        ∀ (i : ι) (M : Matrix (Fin (d i)) (Fin (d i)) ℂ),
          T (Pi.single i M) (sigma i) =
            (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
                (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ := by
  obtain ⟨sigma, hsigma, hDim⟩ :=
    exists_blockEquiv_dim_eq_of_starAlgEquiv_pi_matrix T
  exact ⟨sigma, hDim, hsigma,
    MPSTensor.exists_unitary_block_implementers_of_starAlgEquiv_pi_matrix
      T sigma hsigma hDim⟩

/-- A star-algebra equivalence whose action on its matched simple summands is
implemented by unitaries preserves the sum of the block traces.

This is the trace-preservation calculation implicit in the unitary formula of
CPSV16, arXiv:1606.00608, Appendix C.4, line 1997. -/
theorem isTracePreservingBetweenDirectSums_of_unitary_block_implementers
    [Fintype ι] [Fintype κ]
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (sigma : ι ≃ κ)
    (hsigma : ∀ i, T.toRingEquiv.mapTwoSidedIdeal
      (MPSTensor.blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
        MPSTensor.blockIdeal
          (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (sigma i))
    (hDim : ∀ i, d i = e (sigma i))
    (U : ∀ i, Matrix.unitaryGroup (Fin (e (sigma i))) ℂ)
    (hU : ∀ (i : ι) (M : Matrix (Fin (d i)) (Fin (d i)) ℂ),
      T (Pi.single i M) (sigma i) =
        (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
            (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ) :
    IsTracePreservingBetweenDirectSums T.toAlgEquiv.toLinearEquiv.toLinearMap := by
  classical
  have hSingle (i : ι) (M : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
      ∑ j, (T (Pi.single i M) j).trace = M.trace := by
    rw [Finset.sum_eq_single (sigma i)]
    · let V : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ := U i
      let R : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ :=
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M
      rw [show T (Pi.single i M) (sigma i) = V * R * Vᴴ from hU i M]
      have hUnitary : Vᴴ * V = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using
          (Matrix.mem_unitaryGroup_iff'.mp (U i).property)
      calc
        (V * R * Vᴴ).trace = R.trace := by
          rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUnitary, Matrix.one_mul]
        _ = M.trace := Matrix.trace_reindex (finCongr (hDim i)) M
    · intro j _ hj
      have hzero : T (Pi.single i M) j = 0 := by
        exact MPSTensor.ringEquiv_maps_single_support_between
          T.toRingEquiv sigma hsigma M j hj
      rw [hzero, Matrix.trace_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  intro X
  calc
    ∑ j, (T X j).trace =
        ∑ j, (T (∑ i, Pi.single i (X i)) j).trace := by
      rw [Finset.univ_sum_single]
    _ = ∑ j, ((∑ i, T (Pi.single i (X i))) j).trace := by
      rw [map_sum]
    _ = ∑ j, ∑ i, (T (Pi.single i (X i)) j).trace := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_apply, Matrix.trace_sum]
    _ = ∑ i, ∑ j, (T (Pi.single i (X i)) j).trace :=
      Finset.sum_comm
    _ = ∑ i, (X i).trace :=
      Finset.sum_congr rfl fun i _ ↦ hSingle i (X i)

/-- Mutually inverse completely positive trace-preserving maps between two
finite products of nonzero full matrix algebras match their simple summands
and the corresponding matrix dimensions.

This is the simple-summand matching conclusion in arXiv:1606.00608,
Appendix C.4, line 1997, following Wolf--Perez-Garcia,
arXiv:1005.4545, Theorem 8, source lines 322--324.

**Scope restriction (simple summands):** This theorem does not construct the
unitary action within each paired summand. The unitary strengthening is stated
separately below. -/
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

/-- The trace-adjoint star-algebra equivalence associated with mutually inverse
completely positive trace-preserving maps acts by unitary conjugation on its
matched simple matrix summands.

This is the algebraic blockwise-unitary step in arXiv:1606.00608,
Appendix C.4, line 1997. It does not specialize the formula to transported
MPDO sectors or assert the later multiplicity and coefficient relations. -/
theorem exists_blockEquiv_dim_eq_unitary_of_mutual_inverse_kraus_direct_sum_maps
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
    ∃ sigma : ι ≃ κ, ∃ hDim : ∀ i, d i = e (sigma i),
      (∀ i, E.toRingEquiv.mapTwoSidedIdeal
        (MPSTensor.blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
          MPSTensor.blockIdeal
            (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (sigma i)) ∧
      ∃ U : ∀ i, Matrix.unitaryGroup (Fin (e (sigma i))) ℂ,
        ∀ (i : ι) (M : Matrix (Fin (d i)) (Fin (d i)) ℂ),
          E (Pi.single i M) (sigma i) =
            (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
                (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ := by
  exact exists_blockEquiv_dim_eq_unitary_of_starAlgEquiv_pi_matrix
    (directSumTraceAdjointStarAlgEquiv T S hT hS hTTP hSTP hST hTS).symm

/-- Mutually inverse completely positive trace-preserving maps act on paired
simple matrix summands by conjugation with the same unitaries.

Unlike the trace-adjoint formulation above, this statement gives the formulas
for both original maps. This is the form used for the transported maps in
arXiv:1606.00608, Appendix C.4, line 1997. -/
theorem exists_blockEquiv_dim_eq_unitary_forward_of_mutual_inverse_kraus_direct_sum_maps
    [Fintype ι] [Fintype κ]
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (hT : IsKrausDirectSumMap T) (hS : IsKrausDirectSumMap S)
    (hTTP : IsTracePreservingBetweenDirectSums T)
    (hSTP : IsTracePreservingBetweenDirectSums S)
    (hST : S.comp T = LinearMap.id) (hTS : T.comp S = LinearMap.id) :
    ∃ sigma : ι ≃ κ, ∃ hDim : ∀ i, d i = e (sigma i),
      ∃ U : ∀ i, Matrix.unitaryGroup (Fin (e (sigma i))) ℂ,
        (∀ (i : ι) (M : Matrix (Fin (d i)) (Fin (d i)) ℂ),
            T (Pi.single i M) = Pi.single (sigma i)
              ((U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
                Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
                  (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ)) ∧
          ∀ (i : ι) (N : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ),
            S (Pi.single (sigma i) N) = Pi.single i
              ((Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))).symm
                ((U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ * N *
                  (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ))) := by
  let E := (directSumTraceAdjointStarAlgEquiv
    T S hT hS hTTP hSTP hST hTS).symm
  obtain ⟨sigma, hDim, hsigma, U, hU⟩ :=
    exists_blockEquiv_dim_eq_unitary_of_mutual_inverse_kraus_direct_sum_maps
      T S hT hS hTTP hSTP hST hTS
  have hETP : IsTracePreservingBetweenDirectSums
      E.toAlgEquiv.toLinearEquiv.toLinearMap :=
    isTracePreservingBetweenDirectSums_of_unitary_block_implementers
      E sigma hsigma hDim U hU
  have hElinear : E.toAlgEquiv.toLinearEquiv.toLinearMap =
      directSumTraceAdjointMapBetween S := by
    apply LinearMap.ext
    intro A
    exact directSumTraceAdjointStarAlgEquiv_symm_apply
      T S hT hS hTTP hSTP hST hTS A
  have hEsymm : E.symm.toAlgEquiv.toLinearEquiv.toLinearMap = S := by
    rw [← directSumTraceAdjointMapBetween_starAlgEquiv_eq_symm E hETP,
      hElinear, directSumTraceAdjointMapBetween_involutive]
  have hSinjective : Function.Injective S := by
    have hLeft : Function.LeftInverse T S := fun X ↦
      LinearMap.congr_fun hTS X
    exact hLeft.injective
  have hEeqT (X : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) : E X = T X := by
    apply hSinjective
    calc
      S (E X) = E.symm (E X) :=
        (LinearMap.congr_fun hEsymm (E X)).symm
      _ = X := E.symm_apply_apply X
      _ = S (T X) := (LinearMap.congr_fun hST X).symm
  have hTforward (i : ι) (M : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
      T (Pi.single i M) = Pi.single (sigma i)
        ((U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
            (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ) := by
    rw [← hEeqT]
    funext j
    by_cases hj : j = sigma i
    · subst j
      rw [Pi.single_eq_same, hU]
    · have hzero : E (Pi.single i M) j = 0 := by
        exact MPSTensor.ringEquiv_maps_single_support_between
          E.toRingEquiv sigma hsigma M j hj
      rw [hzero, Pi.single_eq_of_ne hj]
  have hSinverse (i : ι)
      (N : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) :
      S (Pi.single (sigma i) N) = Pi.single i
        ((Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))).symm
          ((U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ * N *
            (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ))) := by
    let V : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ := U i
    let X : Matrix (Fin (d i)) (Fin (d i)) ℂ :=
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))).symm (Vᴴ * N * V)
    have hVright : V * Vᴴ = 1 := by
      simpa only [V, Matrix.star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff.mp (U i).property)
    have hEX : E (Pi.single i X) = Pi.single (sigma i) N := by
      funext j
      by_cases hj : j = sigma i
      · subst j
        rw [Pi.single_eq_same, hU]
        change V * Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) X * Vᴴ = N
        rw [show Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) X = Vᴴ * N * V by
          exact (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))).apply_symm_apply _]
        calc
          V * (Vᴴ * N * V) * Vᴴ = (V * Vᴴ) * N * (V * Vᴴ) := by
            simp only [mul_assoc]
          _ = N := by rw [hVright, one_mul, mul_one]
      · have hzero : E (Pi.single i X) j = 0 := by
          exact MPSTensor.ringEquiv_maps_single_support_between
            E.toRingEquiv sigma hsigma X j hj
        rw [hzero, Pi.single_eq_of_ne hj]
    have hEsm : E.symm (Pi.single (sigma i) N) = Pi.single i X := by
      rw [← hEX, E.symm_apply_apply]
    calc
      S (Pi.single (sigma i) N) = E.symm (Pi.single (sigma i) N) :=
        (LinearMap.congr_fun hEsymm (Pi.single (sigma i) N)).symm
      _ = Pi.single i X := hEsm
      _ = Pi.single i
          ((Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))).symm
            ((U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ * N *
              (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ))) := rfl
  exact ⟨sigma, hDim, U, hTforward, hSinverse⟩

end Matrix
