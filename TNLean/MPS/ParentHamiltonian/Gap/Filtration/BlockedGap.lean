/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockedGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.Commuting.LocalSupportTransport
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.AdjacentLocalTerms
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.C3Threshold
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Reduction

/-!
# Spectral gap after physical blocking

This file combines the whole-increment C3-prime estimate with physical blocking.
The resulting parent Hamiltonian is the range-two parent Hamiltonian of the blocked
tensor. No comparison with an interaction on the original unblocked chain is made.

## Main results

In the namespace `Kraus.HasComplementaryFixedPointGap`:

* `exists_blockTensor_hamiltonian_parentRingInteraction_gap_eighth` chooses a physical block
  length and proves the explicit gap constant \(1/8\) for the Hamiltonian of the range-two
  parent interaction on the ring of the blocked tensor.
* `exists_blockTensor_hamiltonian_parentRingInteraction_gapped` proves a uniform positive gap
  for the same blocked range-two parent Hamiltonians.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, eqs. (2.4)--(2.5), Theorem 3.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, Section IV.C.
-/

open scoped ComplexOrder InnerProductSpace Matrix.Norms.Frobenius
open Kraus (blockPhysDim decodeBlockEquiv decodeBlockEquiv_apply blockTensor
  isNBlkInjective_iff_blockTensor_isInjective evalWord_blockTensor)

namespace MPSTensor

variable {d D : ℕ}

/-- The common physical-coordinate isometry from three blocked sites to three
consecutive original blocks. -/
private noncomputable def blockedThreeConfigLinearIsometryEquiv (d p : ℕ) :
    EuclideanSpace ℂ (Cfg (blockPhysDim d p) 3) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg d (p + p + p)) :=
  (blockedConfigLinearIsometryEquiv d 3 p).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.arrowCongr (finCongr (by omega : 3 * p = p + p + p))
        (Equiv.refl (Fin d))))

/-- Reindex a one-block spectator configuration as a length-`p` original-site
spectator configuration, retaining the virtual matrix coordinates. -/
private noncomputable def blockSpectatorLinearIsometryEquiv (d D p : ℕ) :
    BoundaryFamilySpace (D := D) (Cfg (blockPhysDim d p) 1) ≃ₗᵢ[ℂ]
      BoundaryFamilySpace (D := D) (Cfg d p) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (((Kraus.blockedConfigEquiv d 1 p).trans
      (Equiv.arrowCongr (finCongr (by omega : 1 * p = p))
        (Equiv.refl (Fin d)))).prodCongr (Equiv.refl (Fin D × Fin D)))

/-- The blocked tail spectator map intertwines with the original whole-block
tail spectator map in the common three-block coordinates. -/
private theorem blockedThreeConfigLinearIsometryEquiv_tailBoundaryMapES
    (A : MPSTensor d D) (p : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg (blockPhysDim d p) 1)) :
    blockedThreeConfigLinearIsometryEquiv d p
        (tailBoundaryMapES (blockTensor A p) 1 2 x) =
      reassocTailBoundaryMapES A p p p
        (blockSpectatorLinearIsometryEquiv d D p x) := by
  ext σ
  simp only [blockedThreeConfigLinearIsometryEquiv, LinearIsometryEquiv.trans_apply,
    tailBoundaryMapES_apply, reassocTailBoundaryMapES, ContinuousLinearMap.comp_apply]
  change Matrix.trace (Kraus.evalWord (blockTensor A p) (List.ofFn _) * _) =
    Matrix.trace (Kraus.evalWord A (List.ofFn _) * _)
  congr 2
  rw [evalWord_blockTensor, ← Kraus.ofFn_blockedConfigEquiv d 2 p]
  congr 1
  congr 1
  · omega
  have hindex (k : Fin (2 * p)) :
      k.val % p + p * (1 + k.val / p) = p + k.val := by
    rw [Nat.mul_add, Nat.mul_one]
    calc
      k.val % p + (p + p * (k.val / p)) = p + (k.val % p + p * (k.val / p)) := by
        ac_rfl
      _ = p + k.val := congrArg (p + ·) (Nat.mod_add_div k.val p)
  suffices (fun k : Fin (2 * p) => σ ⟨k.val % p + p * (1 + k.val / p), by
      rw [hindex]
      omega⟩) ≍ fun k : Fin (p + p) => σ (k.addNat p) by
    simpa [Kraus.blockedConfigEquiv, Kraus.blockConfigEquiv, Equiv.arrowCongr, Equiv.curry,
      decodeBlockEquiv_apply, Function.comp_def, finProdFinEquiv]
  apply (Fin.heq_fun_iff (by omega)).2
  intro k
  congr 1
  apply Fin.ext
  simp only [Fin.addNat_mk]
  rw [Nat.mul_add]
  have hk := Nat.mod_add_div k.val p
  omega

/-- The blocked left spectator map intertwines with the original whole-block
left spectator map in the common three-block coordinates. -/
private theorem blockedThreeConfigLinearIsometryEquiv_leftBoundaryMapES
    (A : MPSTensor d D) (p : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg (blockPhysDim d p) 1)) :
    blockedThreeConfigLinearIsometryEquiv d p
        (leftBoundaryMapES (blockTensor A p) 2 1 x) =
      leftBoundaryMapES A (p + p) p
        (blockSpectatorLinearIsometryEquiv d D p x) := by
  ext σ
  simp only [blockedThreeConfigLinearIsometryEquiv, LinearIsometryEquiv.trans_apply,
    leftBoundaryMapES_apply]
  change Matrix.trace (Kraus.evalWord (blockTensor A p) (List.ofFn _) * _) =
    Matrix.trace (Kraus.evalWord A (List.ofFn _) * _)
  congr 2
  · rw [evalWord_blockTensor, ← Kraus.ofFn_blockedConfigEquiv d 2 p]
    congr 1
    congr 1
    · omega
    suffices (fun k : Fin (2 * p) => σ ⟨k.val % p + p * (k.val / p), by
        rw [Nat.mod_add_div]
        omega⟩) ≍ fun k : Fin (p + p) => σ (Fin.castAdd p k) by
      simpa [Kraus.blockedConfigEquiv, Kraus.blockConfigEquiv, Equiv.arrowCongr, Equiv.curry,
        decodeBlockEquiv_apply, Function.comp_def, finProdFinEquiv]
    apply (Fin.heq_fun_iff (by omega)).2
    intro k
    congr 1
    apply Fin.ext
    simp
    have hk := Nat.mod_add_div k.val p
    omega
  ext a b
  suffices x.ofLp
        (fun k => (decodeBlockEquiv d p).symm
          (Function.curry (fun ij : Fin 3 × Fin p =>
            σ ((finCongr (by omega : 3 * p = p + p + p)) (finProdFinEquiv ij)))
            (Fin.natAdd 2 k)), b, a) =
      x.ofLp
        (fun k => (decodeBlockEquiv d p).symm
          (Function.curry (fun ij => σ (Fin.natAdd (p + p) ij.2)) k), b, a) by
    simpa [blockSpectatorLinearIsometryEquiv, boundaryFamilyEquiv_apply_apply,
      Kraus.blockedConfigEquiv, Kraus.blockConfigEquiv, Equiv.arrowCongr, Equiv.curry,
      Function.comp_def,
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
private theorem blockedThreeConfigLinearIsometryEquiv_groundSpaceMapES
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
  change Matrix.trace (Kraus.evalWord A _ * X) =
    Matrix.trace (Kraus.evalWord A _ * X)
  rw [hword]

/-- A linear map intertwining \(f\) with \(g\circ V\), for a linear equivalence
\(V\), carries the range of \(f\) onto the range of \(g\). -/
private theorem map_range_eq_range_of_intertwine {M N P Q : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    (U : N →ₗ[ℂ] P) (f : M →ₗ[ℂ] N) (g : Q →ₗ[ℂ] P) (V : M ≃ₗ[ℂ] Q)
    (h : ∀ x, U (f x) = g (V x)) :
    (LinearMap.range f).map U = LinearMap.range g := by
  rw [← LinearMap.range_comp, show U ∘ₗ f = g ∘ₗ V.toLinearMap from LinearMap.ext h,
    LinearMap.range_comp_of_range_eq_top _ V.range]

/-- The full three-block ground space maps exactly to the original-site ground
space in the common coordinates. -/
private theorem map_groundSpace_three_blockTensor_map
    (A : MPSTensor d D) (p : ℕ) :
    ((groundSpace (blockTensor A p) 3).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
        (blockedThreeConfigLinearIsometryEquiv d p).toLinearEquiv.toLinearMap =
      ((groundSpace A (p + p + p)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  rw [← range_groundSpaceMapES, ← range_groundSpaceMapES]
  exact map_range_eq_range_of_intertwine _ _ _ (LinearEquiv.refl ℂ _)
    (blockedThreeConfigLinearIsometryEquiv_groundSpaceMapES A p)

/-- The blocked one-site-prefix tail space maps exactly to the original whole-block
tail spectator range. -/
private theorem openChainTailGroundSpaceES_blockTensor_map
    (A : MPSTensor d D) (p : ℕ) :
    (openChainTailGroundSpaceES (blockTensor A p) 1 2).map
        (blockedThreeConfigLinearIsometryEquiv d p).toLinearEquiv.toLinearMap =
      (reassocTailBoundaryMapES A p p p).range := by
  rw [← range_tailBoundaryMapES]
  exact map_range_eq_range_of_intertwine _ _ _
    (blockSpectatorLinearIsometryEquiv d D p).toLinearEquiv
    (blockedThreeConfigLinearIsometryEquiv_tailBoundaryMapES A p)

/-- The blocked one-site-suffix left space maps exactly to the original
whole-block left spectator range. -/
private theorem openChainLeftGroundSpaceES_blockTensor_map
    (A : MPSTensor d D) (p : ℕ) :
    (openChainLeftGroundSpaceES (blockTensor A p) 2).map
        (blockedThreeConfigLinearIsometryEquiv d p).toLinearEquiv.toLinearMap =
      (leftBoundaryMapES A (p + p) p).range := by
  rw [← range_leftBoundaryMapES_one]
  exact map_range_eq_range_of_intertwine _ _ _
    (blockSpectatorLinearIsometryEquiv d D p).toLinearEquiv
    (blockedThreeConfigLinearIsometryEquiv_leftBoundaryMapES A p)

/-- The whole-block C3-prime projector defect on three consecutive blocks is the
three-site open-chain projector defect of the blocked tensor.

Both sides act on the explicit blocked Hilbert space. The right side is conjugated
from the \(3p\)-site original Hilbert space by `blockedConfigLinearIsometryEquiv`.
This statement transports only the two whole-block spectator spaces and the full
three-block ground space. -/
theorem blockTensor_threeSite_openChain_defect_norm_eq
    [NeZero d] (A : MPSTensor d D) (p : ℕ) :
    ‖openChainTailGroundProjectionES (blockTensor A p) 1 2 ∘L
          openChainLeftGroundProjectionES (blockTensor A p) 2 -
        ((groundSpace (blockTensor A p) 3).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap).starProjection‖ =
      ‖(reassocTailBoundaryMapES A p p p).range.starProjection ∘L
            (leftBoundaryMapES A (p + p) p).range.starProjection -
          ((groundSpace A (p + p + p)).map (WithLp.linearEquiv 2 ℂ
              _).symm.toLinearMap).starProjection‖ := by
  let U := blockedThreeConfigLinearIsometryEquiv d p
  let T := openChainTailGroundSpaceES (blockTensor A p) 1 2
  let L := openChainLeftGroundSpaceES (blockTensor A p) 2
  let G := ((groundSpace (blockTensor A p) 3).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
  let X := T.starProjection ∘L L.starProjection - G.starProjection
  have hT : T.map U.toLinearEquiv.toLinearMap =
      (reassocTailBoundaryMapES A p p p).range :=
    openChainTailGroundSpaceES_blockTensor_map A p
  have hL : L.map U.toLinearEquiv.toLinearMap =
      (leftBoundaryMapES A (p + p) p).range :=
    openChainLeftGroundSpaceES_blockTensor_map A p
  have hG : G.map U.toLinearEquiv.toLinearMap = ((groundSpace A (p + p + p)).map (WithLp.linearEquiv
      2 ℂ _).symm.toLinearMap) :=
    map_groundSpace_three_blockTensor_map A p
  have hconj :
      U.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (X.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      (reassocTailBoundaryMapES A p p p).range.starProjection ∘L
          (leftBoundaryMapES A (p + p) p).range.starProjection -
        ((groundSpace A (p + p + p)).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap).starProjection := by
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
    have hGp' : ((groundSpace A (p + p + p)).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap).starProjection v =
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

private theorem _root_.Kraus.HasComplementaryFixedPointGap.exists_blockTensor_anticommutator
    [NeZero d] [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : Matrix.PosDef ρ) :
    ∃ p : ℕ,
      0 < p ∧ Kraus.IsNBlkInjective A p ∧
        ∀ (N : ℕ) (hN : 2 * 2 ≤ N) (i j : Fin N),
          j ∈ Finset.univ.erase i → cyclicWindowsOverlap N 2 i j →
            ∀ v : EuclideanSpace ℂ (Cfg (blockPhysDim d p) N),
              haveI : NeZero N := ⟨by omega⟩;
              let h (k : Fin N) := Matrix.toEuclideanLin
                ((parentRingInteraction (blockTensor A p) 2 N).term k);
              - (1 - ((1 : ℝ) / (4 * (2 : ℝ)))) * (((2 * (2 - 1) : ℕ) : ℝ)⁻¹) *
                  ((⟪h i v, v⟫_ℂ).re + (⟪h j v, v⟫_ℂ).re) ≤
                (⟪h i v, h j v⟫_ℂ).re + (⟪h j v, h i v⟫_ℂ).re := by
  obtain ⟨p, hp, hInj, hDefect⟩ :=
    hP.exists_threeBlock_wholeIncrement_defect_le_seven_sixteenths hρ
  let B := blockTensor A p
  have hBInj : Kraus.IsInjective B :=
    (isNBlkInjective_iff_blockTensor_isInjective A p).mp hInj
  have hBlockedDefect :
      ‖openChainTailGroundProjectionES B 1 2 ∘L
            openChainLeftGroundProjectionES B 2 -
          ((groundSpace B 3).map (WithLp.linearEquiv 2 ℂ
              _).symm.toLinearMap).starProjection‖ ≤ 7 / 16 := by
    rw [blockTensor_threeSite_openChain_defect_norm_eq A p]
    simpa only [B, Nat.add_assoc] using hDefect
  let T₀ := Matrix.toEuclideanLin ((parentRingInteraction B 2 3).term 0)
  let T₁ := Matrix.toEuclideanLin ((parentRingInteraction B 2 3).term 1)
  have hThree : ∀ w : EuclideanSpace ℂ (Cfg (blockPhysDim d p) 3),
      -(7 / 16 : ℝ) * ((⟪T₀ w, w⟫_ℂ).re + (⟪T₁ w, w⟫_ℂ).re) ≤
        (⟪T₀ w, T₁ w⟫_ℂ).re + (⟪T₁ w, T₀ w⟫_ℂ).re := by
    intro w
    have hAnti := re_inner_openChain_anticommutator_ge_neg_of_groundProjection_defect
      (A := B) (K := 1) (L₀ := 1) (Kraus.isNBlkInjective_one_of_isInjective hBInj)
        (by omega) hBlockedDefect w
    norm_num only at hAnti
    change -(7 / 16 : ℝ) *
        ((⟪(openChainTailGroundSpaceES B 1 2)ᗮ.starProjection.toLinearMap w, w⟫_ℂ).re +
          (⟪(openChainLeftGroundSpaceES B 2)ᗮ.starProjection.toLinearMap w, w⟫_ℂ).re) ≤
      (⟪(openChainTailGroundSpaceES B 1 2)ᗮ.starProjection.toLinearMap w,
          (openChainLeftGroundSpaceES B 2)ᗮ.starProjection.toLinearMap w⟫_ℂ).re +
        (⟪(openChainLeftGroundSpaceES B 2)ᗮ.starProjection.toLinearMap w,
          (openChainTailGroundSpaceES B 1 2)ᗮ.starProjection.toLinearMap w⟫_ℂ).re at hAnti
    rw [openChainTailGroundSpaceES_orthogonal_starProjection_eq_parentRingInteraction_term,
      openChainLeftGroundSpaceES_orthogonal_starProjection_eq_parentRingInteraction_term] at hAnti
    linarith
  refine ⟨p, hp, hInj, ?_⟩
  intro N hN i j hji hOverlap v
  have hne : j ≠ i := (Finset.mem_erase.mp hji).1
  dsimp only
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, invOf_eq_inv]
  rcases cyclicWindowsOverlap_twoSite_cases hOverlap with rfl | hForward | hBackward
  · exact False.elim (hne rfl)
  · subst j
    exact re_inner_parentRingInteraction_term_adjacent_twoSite_forward_ge_of_threeSite
      hThree (by omega) i v
  · subst i
    have h := re_inner_parentRingInteraction_term_adjacent_twoSite_forward_ge_of_threeSite
      hThree (by omega) j v
    linarith

end MPSTensor

namespace Kraus.HasComplementaryFixedPointGap

open MPSTensor

variable {d D : ℕ}

/-- A primitive MPS tensor with a positive-definite fixed point admits physical blocking whose
range-two blocked parent interaction on the ring has gap constant \(1/8\).

The coefficient \(7/16\) is first obtained for the whole-increment C3-prime projector defect on
three original blocks. Explicit blocked Hilbert-space transport turns it into the adjacent
three-site anticommutator estimate for the terms of the parent interaction on the ring. The
forward and backward cyclic transports then cover every overlapping off-diagonal pair, and the
finite-overlap martingale reduction gives the displayed bound.

The conclusion concerns only `blockTensor A p`; it makes no comparison with an original-site
parent interaction. -/
theorem exists_blockTensor_hamiltonian_parentRingInteraction_gap_eighth
    [NeZero d] [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : Matrix.PosDef ρ) :
    ∃ p : ℕ,
      0 < p ∧ Kraus.IsNBlkInjective A p ∧
        ∀ (N : ℕ) (hN : 4 ≤ N) (μ : ℂ),
          haveI : NeZero N := ⟨by omega⟩;
          Module.End.HasEigenvalue (Matrix.toEuclideanLin
            (parentRingInteraction (Kraus.blockTensor A p) 2 N).hamiltonian) μ →
          μ = 0 ∨ ((1 / 8 : ℝ) : ℂ) ≤ μ := by
  obtain ⟨p, hp, hInj, hAnti⟩ := hP.exists_blockTensor_anticommutator hρ
  obtain ⟨_, hGap⟩ :=
    hamiltonian_parentRingInteraction_gap_bound_of_cyclic_window_overlap_anticommutator
      (Kraus.blockTensor A p) 2 (by omega) hAnti
  refine ⟨p, hp, hInj, fun N hN μ hμ ↦ ?_⟩
  have hγ : (1 / 8 : ℝ) = 1 / (4 * ((2 : ℕ) : ℝ)) := by norm_num
  rw [hγ]
  exact hGap N hN μ hμ

/-- A primitive MPS tensor with a positive-definite fixed point admits physical blocking whose
range-two blocked parent interaction on the ring has a uniform positive gap.

The conclusion concerns only `blockTensor A p`; it makes no comparison with an original-site
parent interaction. -/
theorem exists_blockTensor_hamiltonian_parentRingInteraction_gapped
    [NeZero d] [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : Matrix.PosDef ρ) :
    ∃ p : ℕ,
      0 < p ∧ Kraus.IsNBlkInjective A p ∧
        ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) (hN : 4 ≤ N) (μ : ℂ),
          haveI : NeZero N := ⟨by omega⟩;
          Module.End.HasEigenvalue (Matrix.toEuclideanLin
            (parentRingInteraction (Kraus.blockTensor A p) 2 N).hamiltonian) μ →
          μ = 0 ∨ (γ : ℂ) ≤ μ := by
  obtain ⟨p, hp, hInj, hGap⟩ :=
    hP.exists_blockTensor_hamiltonian_parentRingInteraction_gap_eighth hρ
  exact ⟨p, hp, hInj, 1 / 8, by norm_num, hGap⟩

end Kraus.HasComplementaryFixedPointGap
