/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.LocalSupportTransport
import TNLean.MPS.ParentHamiltonian.Martingale.AdjacentLocalTerms
import TNLean.MPS.ParentHamiltonian.Martingale.C3Threshold
import TNLean.MPS.ParentHamiltonian.Martingale.Gap

/-!
# Spectral gap after physical blocking

This file combines the whole-increment C3-prime estimate with physical blocking.
The resulting parent Hamiltonian is the range-two parent Hamiltonian of the blocked
tensor. No comparison with an interaction on the original unblocked chain is made.

## Main results

* `MPSTensor.IsPrimitiveMPS.exists_blockTensor_parentHamiltonianES_gap_eighth` chooses a
  physical block length and proves the explicit gap constant `1 / 8` for the blocked tensor.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, eqs. (2.4)--(2.5), Theorem 3.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, Section IV.C.
-/

open scoped ComplexOrder InnerProductSpace Matrix.Norms.Frobenius

namespace MPSTensor

variable {d D : ℕ}

/-- The common physical-coordinate isometry from three blocked sites to three
consecutive original blocks. -/
noncomputable def blockedThreeConfigLinearIsometryEquiv (d p : ℕ) :
    EuclideanSpace ℂ (Cfg (blockPhysDim d p) 3) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg d (p + p + p)) :=
  (blockedConfigLinearIsometryEquiv d 3 p).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.arrowCongr (finCongr (by omega : 3 * p = p + p + p))
        (Equiv.refl (Fin d))))

/-- Reindex a one-block spectator configuration as a length-`p` original-site
spectator configuration, retaining the virtual matrix coordinates. -/
noncomputable def blockSpectatorLinearIsometryEquiv (d D p : ℕ) :
    BoundaryFamilySpace (D := D) (Cfg (blockPhysDim d p) 1) ≃ₗᵢ[ℂ]
      BoundaryFamilySpace (D := D) (Cfg d p) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (((blockedConfigEquiv d 1 p).trans
      (Equiv.arrowCongr (finCongr (by omega : 1 * p = p))
        (Equiv.refl (Fin d)))).prodCongr (Equiv.refl (Fin D × Fin D)))

/-- The blocked tail spectator map intertwines with the original whole-block
tail spectator map in the common three-block coordinates. -/
theorem blockedThreeConfigLinearIsometryEquiv_tailBoundaryMapES
    (A : MPSTensor d D) (p : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg (blockPhysDim d p) 1)) :
    blockedThreeConfigLinearIsometryEquiv d p
        (tailBoundaryMapES (blockTensor A p) 1 2 x) =
      reassocTailBoundaryMapES A p p p
        (blockSpectatorLinearIsometryEquiv d D p x) := by
  ext σ
  simp only [blockedThreeConfigLinearIsometryEquiv, LinearIsometryEquiv.trans_apply,
    tailBoundaryMapES_apply, reassocTailBoundaryMapES, ContinuousLinearMap.comp_apply]
  change Matrix.trace (MPSTensor.evalWord (blockTensor A p) (List.ofFn _) * _) =
    Matrix.trace (MPSTensor.evalWord A (List.ofFn _) * _)
  congr 2
  rw [evalWord_blockTensor, ← ofFn_blockedConfigEquiv d 2 p]
  congr 1
  congr 1
  · omega
  simp [blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry,
    decodeBlockEquiv_apply, Function.comp_def, finProdFinEquiv]
  apply (Fin.heq_fun_iff (by omega)).2
  intro k
  congr 1
  apply Fin.ext
  simp
  rw [Nat.mul_add]
  have hk := Nat.mod_add_div k.val p
  omega

/-- The blocked left spectator map intertwines with the original whole-block
left spectator map in the common three-block coordinates. -/
theorem blockedThreeConfigLinearIsometryEquiv_leftBoundaryMapES
    (A : MPSTensor d D) (p : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg (blockPhysDim d p) 1)) :
    blockedThreeConfigLinearIsometryEquiv d p
        (leftBoundaryMapES (blockTensor A p) 2 1 x) =
      leftBoundaryMapES A (p + p) p
        (blockSpectatorLinearIsometryEquiv d D p x) := by
  ext σ
  simp only [blockedThreeConfigLinearIsometryEquiv, LinearIsometryEquiv.trans_apply,
    leftBoundaryMapES_apply]
  change Matrix.trace (MPSTensor.evalWord (blockTensor A p) (List.ofFn _) * _) =
    Matrix.trace (MPSTensor.evalWord A (List.ofFn _) * _)
  congr 2
  rw [evalWord_blockTensor, ← ofFn_blockedConfigEquiv d 2 p]
  congr 1
  congr 1
  · omega
  simp [blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry,
    decodeBlockEquiv_apply, Function.comp_def, finProdFinEquiv]
  apply (Fin.heq_fun_iff (by omega)).2
  intro k
  congr 1
  apply Fin.ext
  simp
  have hk := Nat.mod_add_div k.val p
  omega
  ext a b
  simp [blockSpectatorLinearIsometryEquiv, boundaryFamilyEquiv_apply_apply,
    blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry, Function.comp_def,
    finProdFinEquiv]
  apply congrArg x.1
  congr 1
  funext k
  congr 1
  unfold Function.curry
  funext j
  apply congrArg σ
  apply Fin.ext
  simp
  omega

/-- The three-block Euclidean boundary map intertwines with the common
reassociated physical-coordinate isometry. -/
theorem blockedThreeConfigLinearIsometryEquiv_groundSpaceMapES
    (A : MPSTensor d D) (p : ℕ)
    (x : EuclideanSpace ℂ (Fin D × Fin D)) :
    blockedThreeConfigLinearIsometryEquiv d p
        (groundSpaceMapES (blockTensor A p) 3 x) =
      groundSpaceMapES A (p + p + p) x := by
  rw [blockedThreeConfigLinearIsometryEquiv]
  change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ _)
    (blockedConfigLinearIsometryEquiv d 3 p
      (groundSpaceMapES (blockTensor A p) 3 x)) = _
  rw [blockedConfigLinearIsometryEquiv_groundSpaceMapES]
  apply PiLp.ext
  intro σ
  have hword :
      List.ofFn ((((finCongr (by omega : 3 * p = p + p + p)).arrowCongr
        (Equiv.refl (Fin d))).symm) σ) = List.ofFn σ := by
    convert (List.ofFn_congr (m := p + p + p) (n := 3 * p)
      (by omega) σ).symm using 1
    ext i
    rfl
  simp only [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    Equiv.coe_fn_mk, groundSpaceMapES]
  let X := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm x
  change Matrix.trace (MPSTensor.evalWord A _ * X) =
    Matrix.trace (MPSTensor.evalWord A _ * X)
  rw [hword]

/-- The full three-block ground space maps exactly to the original-site ground
space in the common coordinates. -/
theorem groundSpaceES_three_blockTensor_map
    (A : MPSTensor d D) (p : ℕ) :
    (groundSpaceES (blockTensor A p) 3).map
        (blockedThreeConfigLinearIsometryEquiv d p).toLinearEquiv.toLinearMap =
      groundSpaceES A (p + p + p) := by
  rw [← range_groundSpaceMapES, ← range_groundSpaceMapES]
  ext v
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (blockedThreeConfigLinearIsometryEquiv_groundSpaceMapES A p x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨groundSpaceMapES (blockTensor A p) 3 x, ⟨x, rfl⟩,
      blockedThreeConfigLinearIsometryEquiv_groundSpaceMapES A p x⟩

/-- The blocked one-site-prefix tail space maps exactly to the original whole-block
tail spectator range. -/
theorem openChainTailGroundSpaceES_blockTensor_map
    (A : MPSTensor d D) (p : ℕ) :
    (openChainTailGroundSpaceES (blockTensor A p) 1 2).map
        (blockedThreeConfigLinearIsometryEquiv d p).toLinearEquiv.toLinearMap =
      (reassocTailBoundaryMapES A p p p).range := by
  rw [← range_tailBoundaryMapES]
  ext v
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨blockSpectatorLinearIsometryEquiv d D p x,
      (blockedThreeConfigLinearIsometryEquiv_tailBoundaryMapES A p x).symm⟩
  · rintro ⟨x, hx⟩
    let y := (blockSpectatorLinearIsometryEquiv d D p).symm x
    refine ⟨tailBoundaryMapES (blockTensor A p) 1 2 y, ⟨y, rfl⟩, ?_⟩
    change blockedThreeConfigLinearIsometryEquiv d p
      (tailBoundaryMapES (blockTensor A p) 1 2 y) = v
    rw [blockedThreeConfigLinearIsometryEquiv_tailBoundaryMapES]
    simpa [y] using hx

/-- The blocked one-site-suffix left space maps exactly to the original
whole-block left spectator range. -/
theorem openChainLeftGroundSpaceES_blockTensor_map
    (A : MPSTensor d D) (p : ℕ) :
    (openChainLeftGroundSpaceES (blockTensor A p) 2).map
        (blockedThreeConfigLinearIsometryEquiv d p).toLinearEquiv.toLinearMap =
      (leftBoundaryMapES A (p + p) p).range := by
  rw [← range_leftBoundaryMapES_one]
  ext v
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨blockSpectatorLinearIsometryEquiv d D p x,
      (blockedThreeConfigLinearIsometryEquiv_leftBoundaryMapES A p x).symm⟩
  · rintro ⟨x, hx⟩
    let y := (blockSpectatorLinearIsometryEquiv d D p).symm x
    refine ⟨leftBoundaryMapES (blockTensor A p) 2 1 y, ⟨y, rfl⟩, ?_⟩
    change blockedThreeConfigLinearIsometryEquiv d p
      (leftBoundaryMapES (blockTensor A p) 2 1 y) = v
    rw [blockedThreeConfigLinearIsometryEquiv_leftBoundaryMapES]
    simpa [y] using hx

/-- The whole-block C3-prime projector defect on three consecutive blocks is the
three-site open-chain projector defect of the blocked tensor.

Both sides act on the explicit blocked Hilbert space. The right side is conjugated
from the `3 * p`-site original Hilbert space by `blockedConfigLinearIsometryEquiv`.
This statement transports only the two whole-block spectator spaces and the full
three-block ground space. -/
theorem blockTensor_threeSite_openChain_defect_norm_eq
    [NeZero d] (A : MPSTensor d D) (p : ℕ) :
    ‖openChainTailGroundProjectionES (blockTensor A p) 1 2 ∘L
          openChainLeftGroundProjectionES (blockTensor A p) 2 -
        (groundSpaceES (blockTensor A p) 3).starProjection‖ =
      ‖(reassocTailBoundaryMapES A p p p).range.starProjection ∘L
            (leftBoundaryMapES A (p + p) p).range.starProjection -
          (groundSpaceES A (p + p + p)).starProjection‖ := by
  letI : NeZero (blockPhysDim d p) := ⟨by
    rw [blockPhysDim_eq_pow]
    exact pow_ne_zero p (NeZero.ne d)⟩
  let U := blockedThreeConfigLinearIsometryEquiv d p
  let T := openChainTailGroundSpaceES (blockTensor A p) 1 2
  let L := openChainLeftGroundSpaceES (blockTensor A p) 2
  let G := groundSpaceES (blockTensor A p) 3
  let X := T.starProjection ∘L L.starProjection - G.starProjection
  have hT : T.map U.toLinearEquiv.toLinearMap =
      (reassocTailBoundaryMapES A p p p).range :=
    openChainTailGroundSpaceES_blockTensor_map A p
  have hL : L.map U.toLinearEquiv.toLinearMap =
      (leftBoundaryMapES A (p + p) p).range :=
    openChainLeftGroundSpaceES_blockTensor_map A p
  have hG : G.map U.toLinearEquiv.toLinearMap = groundSpaceES A (p + p + p) :=
    groundSpaceES_three_blockTensor_map A p
  have hconj :
      U.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (X.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      (reassocTailBoundaryMapES A p p p).range.starProjection ∘L
          (leftBoundaryMapES A (p + p) p).range.starProjection -
        (groundSpaceES A (p + p + p)).starProjection := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, X, sub_apply]
    have hTp := Submodule.starProjection_map_apply U T v
    have hLp := Submodule.starProjection_map_apply U L v
    have hGp := Submodule.starProjection_map_apply U G v
    have hTp' : (reassocTailBoundaryMapES A p p p).range.starProjection v =
        U (T.starProjection (U.symm v)) := by
      simpa only [hT] using hTp
    have hLp' : (leftBoundaryMapES A (p + p) p).range.starProjection v =
        U (L.starProjection (U.symm v)) := by
      simpa only [hL] using hLp
    have hGp' : (groundSpaceES A (p + p + p)).starProjection v =
        U (G.starProjection (U.symm v)) := by
      simpa only [hG] using hGp
    rw [hLp', hGp', map_sub]
    have hTpL := Submodule.starProjection_map_apply U T
      (U (L.starProjection (U.symm v)))
    have hTpL' : (reassocTailBoundaryMapES A p p p).range.starProjection
        (U (L.starProjection (U.symm v))) =
      U (T.starProjection (U.symm (U (L.starProjection (U.symm v))))) := by
      simpa only [hT] using hTpL
    rw [hTpL', U.symm_apply_apply]
    simp
  rw [← hconj]
  change ‖X‖ = ‖U.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (X.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖
  have hpost := U.toLinearIsometry.norm_toContinuousLinearMap_comp
    (g := X.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  rw [show U.toLinearIsometry.toContinuousLinearMap =
    U.toContinuousLinearEquiv.toContinuousLinearMap by rfl] at hpost
  rw [hpost]
  apply le_antisymm
  · have h := ContinuousLinearMap.opNorm_comp_le
      (X.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
      U.toContinuousLinearEquiv.toContinuousLinearMap
    rw [U.norm_toContinuousLinearMap] at h
    simpa [ContinuousLinearMap.comp_assoc] using h
  · have h := ContinuousLinearMap.opNorm_comp_le X
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap
    rw [U.symm.norm_toContinuousLinearMap] at h
    simpa using h

private theorem cyclicBackwardSite_forwardSite_one {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    cyclicBackwardSite (cyclicForwardSite i 1) 1 = i := by
  apply Fin.ext
  simp only [cyclicForwardSite, cyclicBackwardSite, Fin.val_mk]
  rw [Nat.mod_eq_of_lt (by omega : 1 < N)]
  by_cases hi : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt hi]
    have hsum : i.val + 1 + N - 1 = i.val + N := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  · have hi_last : i.val + 1 = N := by omega
    have hi_val : N - 1 = i.val := by omega
    rw [hi_last, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega), hi_val]

/-- A primitive MPS tensor with a positive-definite fixed point admits a physical
blocking whose range-two blocked parent Hamiltonian has gap constant `1 / 8`.

The coefficient `7 / 16` is first obtained for the whole-increment C3-prime
projector defect on three original blocks. Explicit blocked Hilbert-space transport
turns it into the adjacent three-site anticommutator estimate. The forward and
backward cyclic transports then cover every overlapping off-diagonal pair, and the
finite-overlap martingale reduction gives the displayed bound.

The conclusion concerns only `blockTensor A p`; it makes no comparison with an
original-site parent interaction. -/
theorem IsPrimitiveMPS.exists_blockTensor_parentHamiltonianES_gap_eighth
    [NeZero d] [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : Matrix.PosDef ρ) :
    ∃ p : ℕ,
      0 < p ∧ IsNBlkInjective A p ∧
        ∀ (N : ℕ) (_hN : 4 ≤ N)
          (v : EuclideanSpace ℂ (Cfg (blockPhysDim d p) N)),
          v ∈ (parentHamiltonianGroundSpaceES (blockTensor A p) 2 N)ᗮ →
            (1 / 8 : ℝ) * ‖v‖ ≤
              ‖parentHamiltonianES (blockTensor A p) 2 N v‖ := by
  obtain ⟨p, hp, hInj, hDefect⟩ :=
    hP.exists_threeBlock_wholeIncrement_defect_le_seven_sixteenths hρ
  let B := blockTensor A p
  letI : NeZero (blockPhysDim d p) := ⟨by
    rw [blockPhysDim_eq_pow]
    exact pow_ne_zero p (NeZero.ne d)⟩
  have hBInj : IsInjective B :=
    (isNBlkInjective_iff_blockTensor_isInjective A p).mp hInj
  have hBlockedDefect :
      ‖openChainTailGroundProjectionES B 1 2 ∘L
            openChainLeftGroundProjectionES B 2 -
          (groundSpaceES B 3).starProjection‖ ≤ 7 / 16 := by
    rw [blockTensor_threeSite_openChain_defect_norm_eq A p]
    simpa only [B, Nat.add_assoc] using hDefect
  have hThree : ∀ w : EuclideanSpace ℂ (Cfg (blockPhysDim d p) 3),
      -(7 / 16 : ℝ) *
          ((⟪localTermES B 2 (0 : Fin 3) w, w⟫_ℂ).re +
            (⟪localTermES B 2 (1 : Fin 3) w, w⟫_ℂ).re) ≤
        (⟪localTermES B 2 (0 : Fin 3) w,
            localTermES B 2 (1 : Fin 3) w⟫_ℂ).re +
          (⟪localTermES B 2 (1 : Fin 3) w,
            localTermES B 2 (0 : Fin 3) w⟫_ℂ).re := by
    intro w
    have hAnti := re_inner_openChain_anticommutator_ge_neg_of_groundProjection_defect
      (A := B) (K := 1) (L₀ := 1) (isNBlkInjective_one_of_isInjective hBInj)
        (by omega) hBlockedDefect w
    norm_num only at hAnti
    change -(7 / 16 : ℝ) *
        ((⟪(openChainTailGroundSpaceES B 1 2)ᗮ.starProjection.toLinearMap w, w⟫_ℂ).re +
          (⟪(openChainLeftGroundSpaceES B 2)ᗮ.starProjection.toLinearMap w, w⟫_ℂ).re) ≤
      (⟪(openChainTailGroundSpaceES B 1 2)ᗮ.starProjection.toLinearMap w,
          (openChainLeftGroundSpaceES B 2)ᗮ.starProjection.toLinearMap w⟫_ℂ).re +
        (⟪(openChainLeftGroundSpaceES B 2)ᗮ.starProjection.toLinearMap w,
          (openChainTailGroundSpaceES B 1 2)ᗮ.starProjection.toLinearMap w⟫_ℂ).re at hAnti
    rw [openChainTailGroundSpaceES_orthogonal_starProjection_eq_localTermES,
      openChainLeftGroundSpaceES_orthogonal_starProjection_eq_localTermES] at hAnti
    have hsum :
        (⟪localTermES B 2 (1 : Fin 3) w, w⟫_ℂ).re +
            (⟪localTermES B 2 (0 : Fin 3) w, w⟫_ℂ).re =
          (⟪localTermES B 2 (0 : Fin 3) w, w⟫_ℂ).re +
            (⟪localTermES B 2 (1 : Fin 3) w, w⟫_ℂ).re := add_comm _ _
    have hcross :
        (⟪localTermES B 2 (1 : Fin 3) w, localTermES B 2 (0 : Fin 3) w⟫_ℂ).re +
            (⟪localTermES B 2 (0 : Fin 3) w, localTermES B 2 (1 : Fin 3) w⟫_ℂ).re =
          (⟪localTermES B 2 (0 : Fin 3) w, localTermES B 2 (1 : Fin 3) w⟫_ℂ).re +
            (⟪localTermES B 2 (1 : Fin 3) w, localTermES B 2 (0 : Fin 3) w⟫_ℂ).re :=
      add_comm _ _
    rw [hsum, hcross] at hAnti
    exact hAnti
  have hAnti : ∀ (N : ℕ) (_hN : 2 * 2 ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N 2 i j →
        ∀ v : EuclideanSpace ℂ (Cfg (blockPhysDim d p) N),
          - (1 - ((1 : ℝ) / (4 * (2 : ℝ)))) *
              (((2 * (2 - 1) : ℕ) : ℝ)⁻¹) *
              ((⟪localTermES B 2 i v, v⟫_ℂ).re +
                (⟪localTermES B 2 j v, v⟫_ℂ).re) ≤
            (⟪localTermES B 2 i v, localTermES B 2 j v⟫_ℂ).re +
              (⟪localTermES B 2 j v, localTermES B 2 i v⟫_ℂ).re := by
    intro N hN i j hji hOverlap v
    have hne : j ≠ i := (Finset.mem_erase.mp hji).1
    norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, invOf_eq_inv]
    rcases cyclicWindowsOverlap_twoSite_cases hOverlap with rfl | hForward | hBackward
    · exact False.elim (hne rfl)
    · subst j
      exact re_inner_localTermES_adjacent_twoSite_forward_ge_of_threeSite
        hThree (by omega) i v
    · subst i
      have hBack := re_inner_localTermES_adjacent_twoSite_backward_ge_of_threeSite
        hThree (by omega) (cyclicForwardSite j 1) v
      rw [cyclicBackwardSite_forwardSite_one (by omega) j] at hBack
      simpa only [add_comm] using hBack
  obtain ⟨_, hGap⟩ :=
    parentHamiltonianES_gap_bound_of_cyclic_window_overlap_anticommutator
      B 2 (by omega) hAnti
  refine ⟨p, hp, hInj, ?_⟩
  intro N hN v hv
  convert hGap N hN v hv using 1 <;> norm_num

end MPSTensor
