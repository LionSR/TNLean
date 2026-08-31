/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport

/-!
# The fixed-final-volume open-chain C3 estimate

This file compares Nachtergaele's local open-chain martingale product with the
corresponding operators in one fixed final-volume Hilbert space.  The proof
handles the two boundary ranges separately and uses right-spectator conjugacy
for every remaining active index.

## References

* Nachtergaele, arXiv:cond-mat/9410110, condition C3, lines 1083--1094.
* Nachtergaele, arXiv:cond-mat/9410110, proof of Theorem 2.1(i), lines 1178--1259.
-/

open scoped BigOperators ComplexOrder

namespace MPSTensor

/-- Before the first full interaction window fits, the fixed-ambient prefix
Hamiltonian vanishes. -/
theorem openPrefixParentHamiltonianES_eq_zero_of_lt
    (A : MPSTensor d D) {L N n : ℕ} (hnL : n < L) :
    openPrefixParentHamiltonianES A L N n = 0 := by
  rw [openPrefixParentHamiltonianES]
  apply Finset.sum_eq_zero
  intro i _
  exfalso
  have hi := i.2
  omega

/-- Before the first full interaction window fits, the fixed-ambient ground
projection is the identity. -/
theorem openPrefixGroundProjectionES_eq_one_of_lt
    (A : MPSTensor d D) {L N n : ℕ} (hnL : n < L) :
    openPrefixGroundProjectionES A L N n = 1 := by
  have hzero := openPrefixParentHamiltonianES_eq_zero_of_lt A (N := N) hnL
  simp only [openPrefixGroundProjectionES, hzero, LinearMap.ker_zero,
    Submodule.starProjection_top']
  rfl

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
  have hN : 0 < N := lt_of_lt_of_le hL hLN
  let iFin : Fin N := ⟨0, hN⟩
  let i : NonwrappingStart L N := ⟨iFin, by
    change 0 + L ≤ N
    omega⟩
  have hprefix : openPrefixParentHamiltonianES A L N L = localTermES A L i.1 := by
    let i' : OpenPrefixStart L N L := ⟨i, by
      change 0 + L ≤ L
      omega⟩
    let _ : Subsingleton (OpenPrefixStart L N L) :=
      ⟨fun j k => by
        apply Subtype.ext
        apply Subtype.ext
        apply Fin.ext
        have hj := j.2
        have hk := k.2
        omega⟩
    rw [openPrefixParentHamiltonianES, Fintype.sum_subsingleton _ i']
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
        change j.1.val = 0
        omega
      · intro hji
        subst j
        simp [i, iFin]
    rw [openSuffixParentHamiltonianES, hfilter, Finset.sum_singleton]
  exact hprefix.trans hsuffix.symm

/-- At the endpoint \(n=l\), the local ground projection is the next prefix
ground projection. -/
theorem openIntervalGroundProjectionES_at_endpoint
    (A : MPSTensor d D) {l N : ℕ} (hl : 0 < l) (hlN : l + 1 ≤ N) :
    openIntervalGroundProjectionES A (l + 1) l N l =
      openPrefixGroundProjectionES A (l + 1) N (l + 1) := by
  have hHamiltonian :=
    openPrefixParentHamiltonianES_eq_openSuffixParentHamiltonianES_at_endpoint
      A (L := l + 1) (N := N) (by omega) hlN
  have hker :
      LinearMap.ker (openSuffixParentHamiltonianES A (l + 1) (l + 1) N (l + 1)) =
        LinearMap.ker (openPrefixParentHamiltonianES A (l + 1) N (l + 1)) :=
    congrArg LinearMap.ker hHamiltonian.symm
  simp only [openIntervalGroundProjectionES, openPrefixGroundProjectionES]
  exact congrArg (fun U : Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) =>
    U.starProjection.toLinearMap) hker

/-- Nachtergaele's C3 product vanishes at the endpoint \(n=l\):
\(Q_l E_l = G_{[0,l+1)} (1 - G_{[0,l+1)}) = 0\). -/
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
    LinearMap.comp_sub]
  let P := openPrefixGroundProjectionES A (l + 1) N (l + 1)
  change P * 1 - P * P = 0
  rw [mul_one]
  apply sub_eq_zero.mpr
  simpa only [P, fixedAmbientNestedGroundProjectionsES] using
    ((fixedAmbientNestedGroundProjectionsES A (l + 1) N).isSymmetricProjection (l + 1)
      |>.isIdempotentElem.eq).symm

/-- After splitting off the right spectators, the fixed-ambient martingale
component is the fiberwise extension of the physical open-chain component. -/
theorem fixedAmbient_martingaleDifference_conj_rightSpectatorConfigLinearIsometryEquiv
    {A : MPSTensor d D} [NeZero D] {K l r : ℕ}
    (hInj : Kraus.IsNBlkInjective A l) (hl : 0 < l) (hK : 0 < K) :
    (rightSpectatorConfigLinearIsometryEquiv d (K + l + 1) r).toLinearEquiv.toLinearMap.comp
        (((fixedAmbientNestedGroundProjectionsES A (l + 1)
          ((K + l + 1) + r)).martingaleDifference (K + l)).comp
          (rightSpectatorConfigLinearIsometryEquiv d
            (K + l + 1) r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (openChainMartingaleDifferenceES A K l hInj hl hK)).toLinearMap := by
  have hleft :=
    openPrefixGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv
      (r := r) hInj hl (show l + 1 ≤ K + l by omega)
  have hwhole :=
    openPrefixWholeGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv
      (r := r) hInj hl (show l + 1 ≤ K + l + 1 by omega)
  rw [FrustrationFree.NestedGroundProjections.martingaleDifference]
  change (rightSpectatorConfigLinearIsometryEquiv d (K + l + 1) r).toLinearEquiv.toLinearMap.comp
      ((openPrefixGroundProjectionES A (l + 1) ((K + l + 1) + r) (K + l) -
        openPrefixGroundProjectionES A (l + 1) ((K + l + 1) + r) (K + l + 1)).comp
        (rightSpectatorConfigLinearIsometryEquiv d
          (K + l + 1) r).symm.toLinearEquiv.toLinearMap) = _
  rw [LinearMap.sub_comp, LinearMap.comp_sub]
  rw [hleft, hwhole]
  exact congrArg ContinuousLinearMap.toLinearMap
    (ContinuousLinearMap.rightFiberwiseMap_sub
      (S := Cfg d r) (openChainLeftGroundProjectionES A (K + l))
        (groundSpaceES A (K + l + 1)).starProjection).symm

/-- Conjugating the fixed C3 product gives the fiberwise extension of the
physical open-chain C3 product. -/
theorem openIntervalGroundProjectionES_comp_martingaleDifference_conj_rightSpectator
    {A : MPSTensor d D} [NeZero D] {K l r : ℕ}
    (hInj : Kraus.IsNBlkInjective A l) (hl : 0 < l) (hK : 0 < K) :
    (rightSpectatorConfigLinearIsometryEquiv d (K + (l + 1)) r).toLinearEquiv.toLinearMap.comp
        (((openIntervalGroundProjectionES A (l + 1) l
          ((K + (l + 1)) + r) (K + l)).comp
          ((fixedAmbientNestedGroundProjectionsES A (l + 1)
            ((K + (l + 1)) + r)).martingaleDifference (K + l))).comp
          (rightSpectatorConfigLinearIsometryEquiv d
            (K + (l + 1)) r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (openChainTailGroundProjectionES A K (l + 1) ∘L
          openChainMartingaleDifferenceES A K l hInj hl hK)).toLinearMap := by
  let U := rightSpectatorConfigLinearIsometryEquiv d (K + (l + 1)) r
  let Q := openIntervalGroundProjectionES A (l + 1) l
    ((K + (l + 1)) + r) (K + l)
  let E := (fixedAmbientNestedGroundProjectionsES A (l + 1)
    ((K + (l + 1)) + r)).martingaleDifference (K + l)
  let q := openChainTailGroundProjectionES A K (l + 1)
  let e := openChainMartingaleDifferenceES A K l hInj hl hK
  have hQ :=
    openIntervalGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv
      A (K := K) (l := l) (r := r)
  have hE :=
    fixedAmbient_martingaleDifference_conj_rightSpectatorConfigLinearIsometryEquiv
      (r := r) hInj hl hK
  apply LinearMap.ext
  intro x
  change U (Q (E (U.symm x))) =
    ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r) (q.comp e) x
  have hQx := LinearMap.congr_fun hQ (U (E (U.symm x)))
  change U (Q (U.symm (U (E (U.symm x))))) =
    ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r) q (U (E (U.symm x))) at hQx
  rw [LinearIsometryEquiv.symm_apply_apply] at hQx
  have hEx := LinearMap.congr_fun hE x
  change U (E (U.symm x)) =
    ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r) e x at hEx
  rw [hEx] at hQx
  exact hQx

/-- The fixed-volume C3 product has norm at most that of its physical
open-chain representative.  This inequality also covers an empty spectator
configuration type. -/
theorem norm_openIntervalGroundProjectionES_comp_martingaleDifference_le_openChain
    {A : MPSTensor d D} [NeZero D] {K l r : ℕ}
    (hInj : Kraus.IsNBlkInjective A l) (hl : 0 < l) (hK : 0 < K) :
    ‖LinearMap.toContinuousLinearMap
        ((openIntervalGroundProjectionES A (l + 1) l
          ((K + (l + 1)) + r) (K + l)).comp
          ((fixedAmbientNestedGroundProjectionsES A (l + 1)
            ((K + (l + 1)) + r)).martingaleDifference (K + l)))‖ ≤
      ‖openChainTailGroundProjectionES A K (l + 1) ∘L
        openChainMartingaleDifferenceES A K l hInj hl hK‖ := by
  let U := rightSpectatorConfigLinearIsometryEquiv d (K + (l + 1)) r
  let T := LinearMap.toContinuousLinearMap
    ((openIntervalGroundProjectionES A (l + 1) l
      ((K + (l + 1)) + r) (K + l)).comp
      ((fixedAmbientNestedGroundProjectionsES A (l + 1)
        ((K + (l + 1)) + r)).martingaleDifference (K + l)))
  let t := openChainTailGroundProjectionES A K (l + 1) ∘L
    openChainMartingaleDifferenceES A K l hInj hl hK
  have hconj :=
    openIntervalGroundProjectionES_comp_martingaleDifference_conj_rightSpectator
      (r := r) hInj hl hK
  have hconjCLM :
      U.toLinearIsometry.toContinuousLinearMap.comp
          (T.comp U.symm.toLinearIsometry.toContinuousLinearMap) =
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r) t := by
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun hconj x
  calc
    ‖T‖ = ‖U.toLinearIsometry.toContinuousLinearMap.comp
        (T.comp U.symm.toLinearIsometry.toContinuousLinearMap)‖ :=
      (ContinuousLinearMap.norm_conj_linearIsometryEquiv U T).symm
    _ = ‖ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r) t‖ :=
      congrArg norm hconjCLM
    _ ≤ ‖t‖ := ContinuousLinearMap.norm_rightFiberwiseMap_le t

/-- A primitive MPS satisfies Nachtergaele's C3 bound on every active index of
the fixed final-volume filtration.  The same overlap length and coefficient as
in the physical open-chain estimate are used. -/
theorem IsPrimitiveMPS.exists_fixedAmbient_martingaleDifference_norm_lt_c3_threshold
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ l : ℕ, ∃ ε : ℝ, ∃ _hl : 1 < l, ∃ _hInj : Kraus.IsNBlkInjective A l,
      0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      ∀ (N n : ℕ), n < N →
        ‖LinearMap.toContinuousLinearMap
          ((openIntervalGroundProjectionES A (l + 1) l N n).comp
            ((fixedAmbientNestedGroundProjectionsES A (l + 1) N).martingaleDifference n))‖ ≤
          ε := by
  obtain ⟨l, ε, hl, hInj, hε, hε_lt, hOpen⟩ :=
    hP.exists_openChain_martingaleDifference_norm_lt_c3_threshold hρ
  refine ⟨l, ε, hl, hInj, hε, hε_lt, fun N n hnN ↦ ?_⟩
  rcases lt_trichotomy n l with hnl | rfl | hln
  · rw [fixedAmbient_martingaleDifference_eq_zero_of_lt A hnl,
      LinearMap.comp_zero]
    simpa using hε
  · rw [openIntervalGroundProjectionES_comp_martingaleDifference_at_endpoint
      A hl.le (by omega)]
    simpa using hε
  · obtain ⟨K, rfl⟩ : ∃ K, n = K + l := ⟨n - l, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, N = (K + (l + 1)) + r :=
      ⟨N - (K + (l + 1)), by omega⟩
    exact (norm_openIntervalGroundProjectionES_comp_martingaleDifference_le_openChain
      (r := r) hInj hl.le (by omega)).trans (hOpen K (by omega))

end MPSTensor
