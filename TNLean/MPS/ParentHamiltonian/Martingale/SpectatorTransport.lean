/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbient
import TNLean.MPS.ParentHamiltonian.Martingale.C3Threshold

/-!
# Spectator transport for the open-chain C3 estimate

This file develops the right-spectator map needed to compare the local-volume
operators in Nachtergaele's condition C3 with the fixed-final-volume filtration.
The comparison is by an explicit configuration-space equivalence, never by
definitional equality between operators on different Hilbert spaces.

## References

* Nachtergaele, arXiv:cond-mat/9410110, condition C3, lines 1083--1094.
* Nachtergaele, arXiv:cond-mat/9410110, proof of Theorem 2.1(i), lines 1178--1259.
-/

open scoped BigOperators

namespace ContinuousLinearMap

variable {I S : Type*} [Fintype I] [Fintype S]

/-- The active-coordinate vector obtained by fixing one right spectator. -/
noncomputable def rightFiber (x : EuclideanSpace ℂ (I × S)) (s : S) :
    EuclideanSpace ℂ I :=
  WithLp.toLp 2 fun i => x (i, s)

/-- Apply the same operator independently at every value of a finite right
spectator coordinate. -/
noncomputable def rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × S) →L[ℂ] EuclideanSpace ℂ (I × S) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun p => G (rightFiber x p.2) p.1
      map_add' := by
        intro x y
        apply PiLp.ext
        rintro ⟨i, s⟩
        change (G (rightFiber (x + y) s)) i = _
        rw [show rightFiber (x + y) s = rightFiber x s + rightFiber y s by
          apply PiLp.ext
          intro j
          rfl, map_add]
        rfl
      map_smul' := by
        intro c x
        apply PiLp.ext
        rintro ⟨i, s⟩
        change (G (rightFiber (c • x) s)) i = _
        rw [show rightFiber (c • x) s = c • rightFiber x s by
          apply PiLp.ext
          intro j
          rfl, map_smul]
        rfl }

@[simp] theorem rightFiberwiseMap_apply_apply
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) (i : I) (s : S) :
    rightFiberwiseMap (S := S) G x (i, s) = G (rightFiber x s) i := rfl

@[simp] theorem rightFiber_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) (s : S) :
    rightFiber (rightFiberwiseMap (S := S) G x) s = G (rightFiber x s) := by
  apply PiLp.ext
  intro i
  rfl

/-- Right-spectator extension preserves composition. -/
theorem rightFiberwiseMap_comp
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    (rightFiberwiseMap (S := S) G).comp (rightFiberwiseMap (S := S) H) =
      rightFiberwiseMap (S := S) (G.comp H) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  apply PiLp.ext
  rintro ⟨i, s⟩
  rfl

/-- Right-spectator extension does not increase the operator norm. The statement
also covers an empty spectator type. -/
theorem norm_rightFiberwiseMap_le
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖rightFiberwiseMap (S := S) G‖ ≤ ‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun x ↦ ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg G) (norm_nonneg x)),
    mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ p : I × S, ‖rightFiberwiseMap (S := S) G x p‖ ^ 2 =
        ∑ s, ∑ i, ‖G (rightFiber x s) i‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    _ = ∑ s, ‖G (rightFiber x s)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ s, (‖G‖ * ‖rightFiber x s‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg G) (norm_nonneg _))).mpr (G.le_opNorm _)
    _ = ‖G‖ ^ 2 * ∑ p : I × S, ‖x p‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [mul_pow, EuclideanSpace.norm_sq_eq]
      simp only [rightFiber, Finset.mul_sum]

/-- A vector supported at one right-spectator coordinate. -/
noncomputable def singleRightFiber (s : S) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × S) :=
  WithLp.toLp 2 fun p => if p.2 = s then x p.1 else 0

/-- A vector supported on one spectator fiber has the norm of that fiber. -/
theorem norm_singleRightFiber (s : S) (x : EuclideanSpace ℂ I) :
    ‖singleRightFiber s x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Finset.sum_comm]
  classical
  simp [singleRightFiber]

/-- On a nonempty spectator space, right-spectator extension preserves the
operator norm exactly. -/
theorem norm_rightFiberwiseMap [Nonempty S]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖rightFiberwiseMap (S := S) G‖ = ‖G‖ := by
  apply le_antisymm (norm_rightFiberwiseMap_le G)
  let s : S := Classical.choice ‹Nonempty S›
  refine ContinuousLinearMap.opNorm_le_bound G (norm_nonneg _) fun x ↦ ?_
  calc
    ‖G x‖ = ‖rightFiberwiseMap (S := S) G (singleRightFiber s x)‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
        EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_prod_type, Finset.sum_comm]
      classical
      simp [singleRightFiber, rightFiber]
    _ ≤ ‖rightFiberwiseMap (S := S) G‖ * ‖singleRightFiber s x‖ :=
      (rightFiberwiseMap (S := S) G).le_opNorm _
    _ = ‖rightFiberwiseMap (S := S) G‖ * ‖x‖ := by
      rw [norm_singleRightFiber]

end ContinuousLinearMap

namespace MPSTensor

variable {d D : ℕ}

/-- Before the first full interaction window fits, the fixed-ambient prefix
Hamiltonian vanishes. -/
theorem openPrefixParentHamiltonianES_eq_zero_of_lt
    (A : MPSTensor d D) {L N n : ℕ} (hnL : n < L) :
    openPrefixParentHamiltonianES A L N n = 0 := by
  rw [openPrefixParentHamiltonianES]
  apply Finset.sum_eq_zero
  intro i _
  exfalso
  exact (not_le_of_gt hnL) i.2

/-- Before the first full interaction window fits, the fixed-ambient ground
projection is the identity. -/
theorem openPrefixGroundProjectionES_eq_one_of_lt
    (A : MPSTensor d D) {L N n : ℕ} (hnL : n < L) :
    openPrefixGroundProjectionES A L N n = 1 := by
  rw [openPrefixGroundProjectionES,
    openPrefixParentHamiltonianES_eq_zero_of_lt A hnL]
  simp

/-- For indices strictly below the C3 endpoint, the fixed-ambient martingale
difference vanishes because both adjacent prefix Hamiltonians are zero. -/
theorem fixedAmbient_martingaleDifference_eq_zero_of_lt
    (A : MPSTensor d D) {l N n : ℕ} (hnl : n < l) :
    (fixedAmbientNestedGroundProjectionsES A (l + 1) N).martingaleDifference n = 0 := by
  rw [FrustrationFree.NestedGroundProjections.martingaleDifference]
  change openPrefixGroundProjectionES A (l + 1) N n -
      openPrefixGroundProjectionES A (l + 1) N (n + 1) = 0
  rw [openPrefixGroundProjectionES_eq_one_of_lt A (by omega),
    openPrefixGroundProjectionES_eq_one_of_lt A (by omega), sub_self]

/-- At the first full-window prefix, the prefix and local-interval Hamiltonians
are the same single local interaction. -/
theorem openPrefixParentHamiltonianES_eq_openSuffixParentHamiltonianES_at_endpoint
    (A : MPSTensor d D) {L N : ℕ} (hL : 0 < L) (hLN : L ≤ N) :
    openPrefixParentHamiltonianES A L N L =
      openSuffixParentHamiltonianES A L L N L := by
  classical
  let i : NonwrappingStart L N := ⟨⟨0, by omega⟩, by omega⟩
  have hprefix : openPrefixParentHamiltonianES A L N L = localTermES A L i.1 := by
    let i' : OpenPrefixStart L N L := ⟨i, by simp [i]⟩
    letI : Subsingleton (OpenPrefixStart L N L) :=
      ⟨fun j k => by
        apply Subtype.ext
        apply Subtype.ext
        apply Fin.ext
        have hj := j.2
        have hk := k.2
        omega⟩
    rw [openPrefixParentHamiltonianES, Fintype.sum_subsingleton _ i']
    rfl
  have hsuffix : openSuffixParentHamiltonianES A L L N L = localTermES A L i.1 := by
    have hfilter :
        Finset.univ.filter (fun j : NonwrappingStart L N =>
          L - L ≤ j.1.val ∧ j.1.val + L ≤ L) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hj
        apply Subtype.ext
        apply Fin.ext
        have hjN := j.1.isLt
        simp only [i, Fin.val_zero]
        omega
      · rintro rfl
        simp [i]
    rw [openSuffixParentHamiltonianES, hfilter, Finset.sum_singleton]
  exact hprefix.trans hsuffix.symm

/-- At the endpoint `n = l`, the local ground projection is the next prefix
ground projection. -/
theorem openIntervalGroundProjectionES_at_endpoint
    (A : MPSTensor d D) {l N : ℕ} (hl : 0 < l) (hlN : l + 1 ≤ N) :
    openIntervalGroundProjectionES A (l + 1) l N l =
      openPrefixGroundProjectionES A (l + 1) N (l + 1) := by
  rw [openIntervalGroundProjectionES, openPrefixGroundProjectionES]
  congr 2
  exact (openPrefixParentHamiltonianES_eq_openSuffixParentHamiltonianES_at_endpoint
    A (by omega) hlN).symm

/-- Nachtergaele's C3 product vanishes at the endpoint `n = l`:
`Q_l E_l = G_[0,l+1) (1 - G_[0,l+1)) = 0`. -/
theorem openIntervalGroundProjectionES_comp_martingaleDifference_at_endpoint
    (A : MPSTensor d D) {l N : ℕ} (hl : 0 < l) (hlN : l + 1 ≤ N) :
    (openIntervalGroundProjectionES A (l + 1) l N l).comp
        ((fixedAmbientNestedGroundProjectionsES A (l + 1) N).martingaleDifference l) = 0 := by
  rw [FrustrationFree.NestedGroundProjections.martingaleDifference]
  change (openIntervalGroundProjectionES A (l + 1) l N l).comp
      (openPrefixGroundProjectionES A (l + 1) N l -
        openPrefixGroundProjectionES A (l + 1) N (l + 1)) = 0
  rw [openPrefixGroundProjectionES_eq_one_of_lt A (by omega),
    openIntervalGroundProjectionES_at_endpoint A hl hlN,
    LinearMap.comp_sub, LinearMap.comp_one]
  exact sub_eq_zero.mpr
    ((fixedAmbientNestedGroundProjectionsES A (l + 1) N).isSymmetricProjection (l + 1)
      |>.isIdempotentElem.eq.symm)

end MPSTensor
