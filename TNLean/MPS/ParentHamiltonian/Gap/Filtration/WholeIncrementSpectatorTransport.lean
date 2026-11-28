/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.SpectatorTransport
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.GroupedOpenGap

/-!
# Spectator transport for whole interval increments

The interval projector error in Nachtergaele's condition C3′ is unchanged
by adding free sites to the right, up to the norm contraction of the finite
fiber extension. Kernel identifications are supplied for the active volumes,
so the argument applies to block-diagonal tensors as well as primitive ones.
See arXiv:cond-mat/9410110, condition C3′, lines 1095--1107.

It also contains the following results.

* `MPSTensor.grouped_martingaleDifference_norm_le_of_projector_defect`: grouped C3 from
  whole-interval projector errors.
* `MPSTensor.norm_suffixGroundProjection_comp_prefixDifference_le_active`: spectator extension of a
  grouped martingale error.
-/

section WholeIncrementSpectatorTransport

private theorem norm_projection_difference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U V W : Submodule ℂ E) (hWV : W ≤ V) :
    ‖V.starProjection.comp (U.starProjection - W.starProjection)‖ =
      ‖W.starProjection - U.starProjection.comp V.starProjection‖ := by
  have hVW : V.starProjection.comp W.starProjection = W.starProjection := by
    ext x
    exact V.starProjection_eq_self_iff.mpr (hWV (Submodule.starProjection_apply_mem W x))
  rw [ContinuousLinearMap.comp_sub, hVW]
  change ‖V.starProjection * U.starProjection - W.starProjection‖ =
    ‖W.starProjection - U.starProjection * V.starProjection‖
  rw [← norm_star (V.starProjection * U.starProjection - W.starProjection),
    star_sub, star_mul, (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq, (isSelfAdjoint_starProjection W).star_eq,
    norm_sub_rev]

namespace MPSTensor

variable {d D : ℕ}

/-- A vector lies in the extended left ground space precisely when every
right-coordinate restriction lies in the active local ground space. -/
theorem mem_range_leftBoundaryMapES_iff_rightFiber
    (A : MPSTensor d D) (n r : ℕ)
    (v : EuclideanSpace ℂ (Cfg d (n + r))) :
    v ∈ (leftBoundaryMapES A n r).range ↔ ∀ s : Cfg d r,
      ContinuousLinearMap.rightFiber
        (rightSpectatorConfigLinearIsometryEquiv d n r v) s ∈ ((groundSpace A n).map
            (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  simp only [leftBoundaryMapES, LinearMap.coe_toContinuousLinearMap,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.mem_map_equiv]
  rw [← SetLike.mem_coe, leftBoundaryMap_range_eq]
  rfl

/-- An identification of the active open-chain kernel with the local ground
space identifies the larger-volume prefix kernel with its right extension. -/
theorem ker_hamiltonian_prefix_parentChainInteraction_eq_range_leftBoundaryMapES
    (A : MPSTensor d D) {R n r : ℕ}
    (hker : LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R n).hamiltonian) =
        ((groundSpace A n).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A R (n + r)).restrict fun i ↦ i.val + R ≤ n).hamiltonian) =
      (leftBoundaryMapES A n r).range := by
  ext v
  have hconj : rightSpectatorConfigLinearIsometryEquiv d n r
      (Matrix.toEuclideanLin
          ((parentChainInteraction A R (n + r)).restrict fun i ↦ i.val + R ≤ n).hamiltonian v) =
      ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.toContinuousLinearMap
            (Matrix.toEuclideanLin
                ((parentChainInteraction A R n).restrict fun i ↦ i.val + R ≤ n).hamiltonian))
        (rightSpectatorConfigLinearIsometryEquiv d n r v) := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply] using
      LinearMap.congr_fun
        (hamiltonian_prefix_parentChainInteraction_conj_rightSpectatorConfigLinearIsometryEquiv
          A (n := n) (r := r) (p := n) le_rfl)
        (rightSpectatorConfigLinearIsometryEquiv d n r v)
  rw [mem_range_leftBoundaryMapES_iff_rightFiber, LinearMap.mem_ker,
    ← (rightSpectatorConfigLinearIsometryEquiv d n r).map_eq_zero_iff, hconj]
  change (rightSpectatorConfigLinearIsometryEquiv d n r v) ∈
    LinearMap.ker (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
      (LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin
              ((parentChainInteraction A R n).restrict fun i ↦ i.val + R ≤
                  n).hamiltonian))).toLinearMap ↔ _
  rw [ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff,
    LinearMap.coe_toContinuousLinearMap,
    hamiltonian_prefix_parentChainInteraction_self_eq_hamiltonian_parentChainInteraction, hker]

/-- Reassociation transports any length-indexed subspace to the same subspace
in the equal ambient length. -/
theorem physicalReassocES_map_submodule
    (S : ∀ n, Submodule ℂ (EuclideanSpace ℂ (Cfg d n))) (K L Q : ℕ) :
    (S (K + (L + Q))).map
      (physicalReassocES (d := d) K L Q).toLinearEquiv.toLinearMap =
      S (K + L + Q) := by
  suffices ∀ (n m : ℕ) (h : n = m),
      (S n).map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.arrowCongr (finCongr h) (Equiv.refl (Fin d)))).toLinearEquiv.toLinearMap =
      S m from this _ _ (Nat.add_assoc K L Q).symm
  rintro n m rfl
  change (S n).map LinearMap.id = S n
  exact Submodule.map_id _

/-- The reassociated right interval is the kernel of the parent interaction
on the full suffix window. -/
theorem range_reassocTailBoundaryMapES_eq_ker_hamiltonian_restrict_parentChainInteraction
    (A : MPSTensor d D) {K L Q : ℕ} (hR : 0 < L + Q) :
    (reassocTailBoundaryMapES A K L Q).range =
      LinearMap.ker
          (Matrix.toEuclideanLin
              ((parentChainInteraction A (L + Q) (K + L + Q)).restrict fun i ↦ K + L + Q - (L + Q) ≤
                  i.val ∧ i.val + (L + Q) ≤ K + L + Q).hamiltonian) := by
  rw [reassocTailBoundaryMapES, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, range_tailBoundaryMapES,
    ← ker_hamiltonian_restrict_parentChainInteraction_eq_openChainTailGroundSpaceES A hR]
  exact physicalReassocES_map_submodule
    (fun n ↦ LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A (L + Q) n).restrict fun i ↦ n - (L + Q) ≤ i.val ∧ i.val +
                (L + Q) ≤ n).hamiltonian)) K L Q

/-- The active grouped martingale error is the three-interval projector
error, provided the two prefix kernels are their boundary-condition spaces.
This is the projector identity underlying Nachtergaele's condition C3-prime,
arXiv:cond-mat/9410110, lines 1095--1107. -/
theorem norm_suffixProjection_comp_prefixDifference_eq_projector_defect
    (A : MPSTensor d D) {K L Q : ℕ} (hR : 0 < L + Q)
    (hleft : LinearMap.ker
        (Matrix.toEuclideanLin (parentChainInteraction A (L + Q) (K + L)).hamiltonian) =
      ((groundSpace A (K + L)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (hfull : LinearMap.ker
        (Matrix.toEuclideanLin (parentChainInteraction A (L + Q) (K + L + Q)).hamiltonian) =
      ((groundSpace A (K + L + Q)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ‖LinearMap.toContinuousLinearMap
      ((LinearMap.ker
          (Matrix.toEuclideanLin
              ((parentChainInteraction A (L + Q) (K + L + Q)).restrict fun i ↦ K + L + Q - (L + Q) ≤
                  i.val ∧ i.val + (L + Q) ≤ K + L + Q).hamiltonian)).starProjection.toLinearMap.comp
        (openPrefixGroundProjectionES A (L + Q) (K + L + Q) (K + L) -
          openPrefixGroundProjectionES A (L + Q) (K + L + Q) (K + L + Q)))‖ =
      ‖((groundSpace A (K + L + Q)).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K + L) Q).range.starProjection.comp
          (reassocTailBoundaryMapES A K L Q).range.starProjection‖ := by
  have hWV : ((groundSpace A (K + L + Q)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) ≤
      (reassocTailBoundaryMapES A K L Q).range := by
    rw [← range_groundSpaceMapES,
      ← reassocTailBoundaryMapES_comp_tailVirtualMapES A K L Q]
    exact LinearMap.range_comp_le_range _ _
  simp only [openPrefixGroundProjectionES,
    ker_hamiltonian_prefix_parentChainInteraction_eq_range_leftBoundaryMapES A hleft,
    hamiltonian_prefix_parentChainInteraction_self_eq_hamiltonian_parentChainInteraction, hfull,
    ← range_reassocTailBoundaryMapES_eq_ker_hamiltonian_restrict_parentChainInteraction A hR]
  exact norm_projection_difference _ _ _ hWV

end MPSTensor

end WholeIncrementSpectatorTransport

section GroupedSpectatorNorm

/-!
## Spectator extension of a grouped martingale error

Extending a chain by sites to its right does not increase the norm of a suffix
kernel projection composed with a difference of two prefix kernel projections.
All three Hamiltonians act trivially on the added sites; their kernel
projections therefore extend fiberwise. No injectivity assumption is needed.

This is the fixed-volume passage for the grouped martingale estimate in
Nachtergaele, arXiv:cond-mat/9410110, condition C3-prime and Theorem 2.1(ii).
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Adding right spectator sites does not increase the norm of the grouped
martingale expression. The active suffix ends at the full active volume, and
both prefix endpoints lie within that volume. This is the fixed-volume
extension of Nachtergaele's condition C3-prime, arXiv:cond-mat/9410110,
lines 1095--1104. -/
theorem norm_suffixGroundProjection_comp_prefixDifference_le_active
    (A : MPSTensor d D) {R l n r p : ℕ} (hp : p ≤ n) :
    ‖LinearMap.toContinuousLinearMap
      (((LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A R (n + r)).restrict fun i ↦ n - l ≤ i.val ∧ i.val + R ≤
                n).hamiltonian)).starProjection.toLinearMap).comp
        (openPrefixGroundProjectionES A R (n + r) p -
          openPrefixGroundProjectionES A R (n + r) n))‖ ≤
      ‖LinearMap.toContinuousLinearMap
        (((LinearMap.ker
            (Matrix.toEuclideanLin
                ((parentChainInteraction A R n).restrict fun i ↦ n - l ≤ i.val ∧ i.val + R ≤
                    n).hamiltonian)).starProjection.toLinearMap).comp
          (openPrefixGroundProjectionES A R n p - openPrefixGroundProjectionES A R n n))‖ := by
  let U := rightSpectatorConfigLinearIsometryEquiv d n r
  have hP (q : ℕ) (hq : q ≤ n) :
      U.toLinearEquiv.conj
          (LinearMap.ker
              (Matrix.toEuclideanLin
                  ((parentChainInteraction A R (n + r)).restrict fun i ↦ i.val + R ≤
                      q).hamiltonian)).starProjection.toLinearMap =
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
          (LinearMap.ker
              (Matrix.toEuclideanLin
                  ((parentChainInteraction A R n).restrict fun i ↦ i.val + R ≤
                      q).hamiltonian)).starProjection).toLinearMap :=
    ker_starProjection_conj_of_rightFiberwiseMap _ _
      (hamiltonian_prefix_parentChainInteraction_conj_rightSpectatorConfigLinearIsometryEquiv
        A (r := r) hq)
  have hQ :
      U.toLinearEquiv.conj (LinearMap.ker
          (Matrix.toEuclideanLin
              ((parentChainInteraction A R (n + r)).restrict fun i ↦ n - l ≤ i.val ∧ i.val + R ≤
                  n).hamiltonian)).starProjection.toLinearMap =
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
          (LinearMap.ker
              (Matrix.toEuclideanLin
                  ((parentChainInteraction A R n).restrict fun i ↦ n - l ≤ i.val ∧ i.val + R ≤
                      n).hamiltonian)).starProjection).toLinearMap :=
    ker_starProjection_conj_of_rightFiberwiseMap _ _
      (hamiltonian_restrict_parentChainInteraction_conj_rightSpectatorConfigLinearIsometryEquiv
        A (l := l) (n := n) (r := r) le_rfl)
  have hprod : U.toLinearEquiv.conj
      (((LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A R (n + r)).restrict fun i ↦ n - l ≤ i.val ∧ i.val + R ≤
                n).hamiltonian)).starProjection.toLinearMap).comp
        (openPrefixGroundProjectionES A R (n + r) p -
          openPrefixGroundProjectionES A R (n + r) n)) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        ((LinearMap.ker
            (Matrix.toEuclideanLin
                ((parentChainInteraction A R n).restrict fun i ↦ n - l ≤ i.val ∧ i.val + R ≤
                    n).hamiltonian)).starProjection.comp
          ((LinearMap.ker
              (Matrix.toEuclideanLin
                  ((parentChainInteraction A R n).restrict fun i ↦ i.val + R ≤
                      p).hamiltonian)).starProjection -
            (LinearMap.ker
              (Matrix.toEuclideanLin
                  ((parentChainInteraction A R n).restrict fun i ↦ i.val + R ≤
                      n).hamiltonian)).starProjection))).toLinearMap := by
    simp only [LinearEquiv.conj_comp, map_sub, openPrefixGroundProjectionES,
      hQ, hP p hp, hP n le_rfl]
    rw [← ContinuousLinearMap.toLinearMap_sub, ← ContinuousLinearMap.toLinearMap_comp,
      ← ContinuousLinearMap.rightFiberwiseMap_sub, ContinuousLinearMap.rightFiberwiseMap_comp]
  exact (ContinuousLinearMap.norm_conj_linearIsometryEquiv U _).symm.trans_le
    ((congrArg (fun f ↦ ‖LinearMap.toContinuousLinearMap f‖) hprod).trans_le
      (ContinuousLinearMap.norm_rightFiberwiseMap_le _))

end MPSTensor

end GroupedSpectatorNorm

section GroupedProjectorEstimate

/-!
## Grouped C3 from whole-interval projector errors

An open-chain kernel identity identifies the prefix ground projections with
matrix-product boundary spaces. A bound on the three-interval projector error
then bounds the grouped martingale product after adjoining right spectators.
The first two grouped indices vanish identically.

This is the passage from Nachtergaele's projector estimate in Section 6 to
condition C3-prime, arXiv:cond-mat/9410110, lines 1095--1107.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A uniform three-interval projector error implies grouped C3 for the
range-\(2p\) parent Hamiltonian. The open-chain kernel identities are required
only from the interaction length onwards. This is Nachtergaele's condition
C3-prime with increment and overlap both equal to \(p\). -/
theorem grouped_martingaleDifference_norm_le_of_projector_defect
    (A : MPSTensor d D) {p M : ℕ} (hp : 0 < p)
    (hKernel : ∀ n, 2 * p ≤ n →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (2 * p) n).hamiltonian) =
          ((groundSpace A n).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hDefect : ∀ K : ℕ,
      ‖((groundSpace A (K + p + p)).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K + p) p).range.starProjection.comp
          (reassocTailBoundaryMapES A K p p).range.starProjection‖ ≤ ε) :
    ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p (p * M) n).comp
          ((groupedNestedGroundProjectionsES A p (p * M)).martingaleDifference n))‖ ≤ ε := by
  apply grouped_martingaleDifference_norm_le_of_two_le A hp hε
  intro n hn2 hnM
  have hK : p * (n - 1) + p = p * n := by
    simpa only [Nat.mul_add, Nat.mul_one] using
      congrArg (p * ·) (Nat.sub_add_cancel (show 1 ≤ n by omega))
  have hactive := (norm_suffixProjection_comp_prefixDifference_eq_projector_defect
    A (K := p * (n - 1)) (L := p) (Q := p) (by omega)
    (by rw [← two_mul]
        exact hKernel (p * (n - 1) + p) (by nlinarith [Nat.mul_le_mul_left p hn2]))
    (by rw [← two_mul]
        exact hKernel (p * (n - 1) + p + p) (by nlinarith [Nat.mul_le_mul_left p hn2]))).trans_le
        (hDefect (p * (n - 1)))
  rw [← two_mul] at hactive
  let F (N a b : ℕ) : ℝ :=
    ‖LinearMap.toContinuousLinearMap
      ((LinearMap.ker
        (Matrix.toEuclideanLin
            ((parentChainInteraction A (2 * p) N).restrict fun i ↦ b - 2 * p ≤ i.val ∧ i.val + 2 *
                p ≤ b).hamiltonian)).starProjection.toLinearMap.comp
        (openPrefixGroundProjectionES A (2 * p) N a - openPrefixGroundProjectionES A (2 * p) N b))‖
  change F (p * (n - 1) + p + p) (p * (n - 1) + p) (p * (n - 1) + p + p) ≤ ε at hactive
  rw [hK] at hactive
  have hspectator :
      F (p * n + p + (p * M - (p * n + p))) (p * n) (p * n + p) ≤
        F (p * n + p) (p * n) (p * n + p) :=
    norm_suffixGroundProjection_comp_prefixDifference_le_active A
      (R := 2 * p) (l := 2 * p) (n := p * n + p)
      (r := p * M - (p * n + p)) (p := p * n) (by omega)
  have hbound : F (p * M) (p * n) (p * n + p) ≤ ε := by
    simpa only [Nat.add_sub_of_le (show p * n + p ≤ p * M by
      simpa only [Nat.mul_succ] using Nat.mul_le_mul_left p hnM)] using
        hspectator.trans hactive
  simpa only [F, groupedIntervalGroundProjectionES,
    FrustrationFree.NestedGroundProjections.martingaleDifference,
    groupedNestedGroundProjectionsES, Nat.mul_succ] using hbound

end MPSTensor

end GroupedProjectorEstimate
