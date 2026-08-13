/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Blocked and original parent interactions

This file records the exact local conjugacy underlying comparison of a blocked
range-two parent Hamiltonian with the range-\(2p\) parent Hamiltonian in
original-site coordinates.

## Main results

* `MPSTensor.parentInteractionES_blockTensor_conj` identifies the parent
  interaction on \(N\) blocked sites with the original interaction on \(Np\)
  sites under the canonical blocked-configuration isometry.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, lines 1985--1992.
* B. Nachtergaele, arXiv:cond-mat/9410110, condition C3-prime and the rescaled
  finite-volume sequence in the proof of Theorem 2.1(ii).
-/

namespace MPSTensor

variable {d D : ℕ}

/-- The blocked local parent interaction is exactly the original parent
interaction on the corresponding whole block, after computational-basis
reindexing. No injectivity hypothesis is needed. -/
theorem parentInteractionES_blockTensor_conj
    (A : MPSTensor d D) (p N : ℕ) :
    parentInteractionES A (N * p) =
      (blockedConfigLinearIsometryEquiv d N p).toLinearEquiv.toLinearMap.comp
        ((parentInteractionES (blockTensor A p) N).comp
          (blockedConfigLinearIsometryEquiv d N p).symm.toLinearEquiv.toLinearMap) := by
  let U := blockedConfigLinearIsometryEquiv d N p
  apply LinearMap.ext
  intro v
  rw [parentInteractionES, parentInteractionES]
  rw [Submodule.starProjection_orthogonal', Submodule.starProjection_orthogonal']
  change v - (groundSpaceES A (N * p)).starProjection v =
    U (U.symm v - (groundSpaceES (blockTensor A p) N).starProjection (U.symm v))
  rw [starProjection_groundSpaceES_blockTensor_map_apply A p N v, map_sub,
    U.apply_symm_apply]

/-- The original-site start corresponding to a blocked site. -/
private def alignedOriginalStart {N p : ℕ} (hp : 0 < p) (i : Fin N) : Fin (N * p) :=
  ⟨i.val * p, by
    have hi := i.isLt
    nlinarith⟩

private theorem extractWindow_blockedConfigEquiv_aligned
    (d p : ℕ) (hp : 0 < p) {N : ℕ} (i : Fin N)
    (σ : Cfg (blockPhysDim d p) N) :
    extractWindow (2 * p) (alignedOriginalStart hp i) (blockedConfigEquiv d N p σ) =
      blockedConfigEquiv d 2 p (extractWindow 2 i σ) := by
  funext r
  let k : Fin (N * p) :=
    ⟨(i.val * p + r.val) % (N * p), Nat.mod_lt _ (Nat.mul_pos (Fin.pos i) hp)⟩
  let q : Fin N :=
    ⟨(i.val + (finProdFinEquiv.symm r).1.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
  change decodeBlock d p (σ (finProdFinEquiv.symm k).1)
      (finProdFinEquiv.symm k).2 =
    decodeBlock d p (σ q) (finProdFinEquiv.symm r).2
  have hfst : (finProdFinEquiv.symm k).1 = q := by
    apply Fin.ext
    simp only [finProdFinEquiv_symm_apply]
    change ((i.val * p + r.val) % (N * p)) / p =
      (i.val + r.val / p) % N
    rw [Nat.mod_mul_left_div_self]
    rw [show i.val * p + r.val = r.val + p * i.val by ac_rfl]
    rw [Nat.add_mul_div_left r.val i.val hp]
    congr 1
    omega
  have hsnd : (finProdFinEquiv.symm k).2 = (finProdFinEquiv.symm r).2 := by
    apply Fin.ext
    simp only [finProdFinEquiv_symm_apply]
    change ((i.val * p + r.val) % (N * p)) % p = r.val % p
    rw [Nat.mod_mul_left_mod, Nat.mul_add_mod_self_right]
  rw [hfst, hsnd]

private theorem replaceWindow_blockedConfigEquiv_aligned
    (d p : ℕ) (hp : 0 < p) {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    (σ : Cfg (blockPhysDim d p) N) (τ : Cfg (blockPhysDim d p) 2) :
    replaceWindow (2 * p) (by nlinarith : 2 * p ≤ N * p) (alignedOriginalStart hp i)
        (blockedConfigEquiv d N p σ) (blockedConfigEquiv d 2 p τ) =
      blockedConfigEquiv d N p (replaceWindow 2 hN i σ τ) := by
  funext k
  change (if h : (k.val + N * p - i.val * p) % (N * p) < 2 * p then
      decodeBlock d p
        (τ (finProdFinEquiv.symm
          (⟨(k.val + N * p - i.val * p) % (N * p), h⟩ : Fin (2 * p))).1)
        (finProdFinEquiv.symm
          (⟨(k.val + N * p - i.val * p) % (N * p), h⟩ : Fin (2 * p))).2
    else decodeBlock d p (σ (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2) =
    decodeBlock d p
      ((if h : (((finProdFinEquiv.symm k).1.val + N - i.val) % N) < 2 then
          τ ⟨((finProdFinEquiv.symm k).1.val + N - i.val) % N, h⟩
        else σ (finProdFinEquiv.symm k).1))
      (finProdFinEquiv.symm k).2
  let q := (finProdFinEquiv.symm k).1
  let r := (finProdFinEquiv.symm k).2
  have hk : k.val = q.val * p + r.val := by
    dsimp [q, r]
    simp only [finProdFinEquiv_symm_apply]
    exact (Nat.mod_add_div k.val p).symm.trans (by ac_rfl)
  have hoff :
      (k.val + N * p - i.val * p) % (N * p) =
        ((q.val + N - i.val) % N) * p + r.val := by
    rw [hk]
    have hi : i.val ≤ q.val + N := by omega
    have heq : q.val * p + r.val + N * p - i.val * p =
        (q.val + N - i.val) * p + r.val := by
      rw [show q.val * p + r.val + N * p = r.val + (q.val + N) * p by ring]
      rw [Nat.add_sub_assoc (Nat.mul_le_mul_right p hi), Nat.sub_mul]
      ac_rfl
    rw [heq]
    have hmod : ((q.val + N - i.val) * p + r.val) % (N * p) =
        (((q.val + N - i.val) % N) * p + r.val) := by
      rw [Nat.add_mod, Nat.mul_mod_mul_right]
      have hr : r.val % (N * p) = r.val := Nat.mod_eq_of_lt (by nlinarith [r.isLt])
      rw [hr]
      have hlt : (q.val + N - i.val) % N * p + r.val < N * p := by
        have hqmod := Nat.mod_lt (q.val + N - i.val) (Fin.pos i)
        calc
          (q.val + N - i.val) % N * p + r.val
              < (q.val + N - i.val) % N * p + p :=
            Nat.add_lt_add_left r.isLt _
          _ ≤ N * p := by
            rw [← Nat.succ_mul]
            exact Nat.mul_le_mul_right p (Nat.succ_le_of_lt hqmod)
      rw [Nat.mod_eq_of_lt hlt]
    exact hmod
  have hwindow :
      (k.val + N * p - i.val * p) % (N * p) < 2 * p ↔
        (q.val + N - i.val) % N < 2 := by
    rw [hoff]
    have hr := r.isLt
    constructor <;> intro h
    · by_contra hnot
      have htwo : 2 ≤ (q.val + N - i.val) % N := by omega
      have hmul := Nat.mul_le_mul_right p htwo
      omega
    · calc
        (q.val + N - i.val) % N * p + r.val
            < (q.val + N - i.val) % N * p + p := Nat.add_lt_add_left r.isLt _
        _ ≤ 2 * p := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right p h
  by_cases hqwin : (q.val + N - i.val) % N < 2
  · rw [dif_pos hqwin, dif_pos (hwindow.mpr hqwin)]
    change decodeBlock d p
        (τ (finProdFinEquiv.symm
          (⟨(k.val + N * p - i.val * p) % (N * p), hwindow.mpr hqwin⟩ :
            Fin (2 * p))).1)
        (finProdFinEquiv.symm
          (⟨(k.val + N * p - i.val * p) % (N * p), hwindow.mpr hqwin⟩ :
            Fin (2 * p))).2 =
      decodeBlock d p (τ ⟨(q.val + N - i.val) % N, hqwin⟩) r
    have hidx :
        finProdFinEquiv.symm
          (⟨(k.val + N * p - i.val * p) % (N * p), hwindow.mpr hqwin⟩ :
            Fin (2 * p)) =
          (⟨(q.val + N - i.val) % N, hqwin⟩, r) := by
      apply Prod.ext
      · apply Fin.ext
        simp only [finProdFinEquiv_symm_apply]
        change ((k.val + N * p - i.val * p) % (N * p)) / p =
          (q.val + N - i.val) % N
        rw [hoff]
        rw [show ((q.val + N - i.val) % N * p + r.val) / p =
            (q.val + N - i.val) % N by
          rw [show (q.val + N - i.val) % N * p + r.val =
            r.val + p * ((q.val + N - i.val) % N) by ac_rfl]
          rw [Nat.add_mul_div_left r.val _ hp, Nat.div_eq_of_lt r.isLt, zero_add]]
      · apply Fin.ext
        simp only [finProdFinEquiv_symm_apply]
        change ((k.val + N * p - i.val * p) % (N * p)) % p = r.val
        rw [hoff, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt r.isLt]
    rw [hidx]
  · rw [dif_neg hqwin, dif_neg (not_congr hwindow |>.mpr hqwin)]

/-- Restricting an original-site state to a whole aligned \(2p\) window and
then regrouping it into two blocks agrees with first regrouping the full chain
and then restricting to the corresponding blocked two-site window. -/
private theorem cyclicRestrictES_blockedConfigLinearIsometryEquiv_aligned
    (d p : ℕ) (hp : 0 < p) {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    (ω : Cfg d (N * p)) (v : EuclideanSpace ℂ (Cfg d (N * p))) :
    cyclicRestrictES (d := blockPhysDim d p) (Fin.pos i) 2 i
        ((blockedConfigEquiv d N p).symm ω)
        ((blockedConfigLinearIsometryEquiv d N p).symm v) =
      (blockedConfigLinearIsometryEquiv d 2 p).symm
        (cyclicRestrictES (d := d) (Nat.mul_pos (Fin.pos i) hp) (2 * p)
          (alignedOriginalStart hp i) ω v) := by
  ext τ
  change ((WithLp.linearEquiv 2 ℂ _).symm
      (cyclicRestrictₗ (Fin.pos i) 2 i ((blockedConfigEquiv d N p).symm ω)
        ((WithLp.linearEquiv 2 ℂ _)
          ((blockedConfigLinearIsometryEquiv d N p).symm v)))) τ = _
  simp only [WithLp.linearEquiv_symm_apply, WithLp.coe_linearEquiv]
  simp only [blockedConfigLinearIsometryEquiv_symm_apply_apply]
  change (WithLp.toLp 2
      (cyclicRestrictₗ (Fin.pos i) 2 i ((blockedConfigEquiv d N p).symm ω)
        ((blockedConfigLinearIsometryEquiv d N p).symm v).ofLp)).ofLp τ = _
  rw [WithLp.ofLp_toLp]
  rw [cyclicRestrictₗ_apply]
  rw [blockedConfigLinearIsometryEquiv_symm_apply_apply]
  rw [cyclicRestrictES]
  simp only [LinearMap.withLpMap, LinearMap.comp_apply]
  change v (blockedConfigEquiv d N p
      (cyclicCfg (Fin.pos i) 2 i τ ((blockedConfigEquiv d N p).symm ω))) =
    v (cyclicCfg (Nat.mul_pos (Fin.pos i) hp) (2 * p) (alignedOriginalStart hp i)
      (blockedConfigEquiv d 2 p τ) ω)
  apply congrArg v
  change blockedConfigEquiv d N p
      (replaceWindow 2 hN i ((blockedConfigEquiv d N p).symm ω) τ) =
    replaceWindow (2 * p) (by nlinarith) (alignedOriginalStart hp i) ω
      (blockedConfigEquiv d 2 p τ)
  symm
  simpa using replaceWindow_blockedConfigEquiv_aligned d p hp hN i
    ((blockedConfigEquiv d N p).symm ω) τ

/-- The blocked range-two local term at site \(i\) is exactly conjugate to the
original range-\(2p\) local term at the aligned start \(pi\). -/
theorem localTermES_blockTensor_conj_aligned
    (A : MPSTensor d D) (p : ℕ) (hp : 0 < p) {N : ℕ} (hN : 2 ≤ N)
    (i : Fin N) :
    localTermES A (2 * p) (alignedOriginalStart hp i) =
      (blockedConfigLinearIsometryEquiv d N p).toLinearEquiv.toLinearMap.comp
        ((localTermES (blockTensor A p) 2 i).comp
          (blockedConfigLinearIsometryEquiv d N p).symm.toLinearEquiv.toLinearMap) := by
  apply LinearMap.ext
  intro v
  ext ω
  rw [localTermES_apply A (2 * p) (alignedOriginalStart hp i)
    (by nlinarith : 2 * p ≤ N * p) v ω]
  change parentInteractionES A (2 * p)
      (cyclicRestrictES (d := d) (Nat.mul_pos (Fin.pos i) hp) (2 * p)
        (alignedOriginalStart hp i) ω v)
      (extractWindow (2 * p) (alignedOriginalStart hp i) ω) = _
  simp only [LinearMap.comp_apply]
  change _ = localTermES (blockTensor A p) 2 i
    ((blockedConfigLinearIsometryEquiv d N p).symm v)
      ((blockedConfigEquiv d N p).symm ω)
  rw [localTermES_apply (blockTensor A p) 2 i hN
    ((blockedConfigLinearIsometryEquiv d N p).symm v)
    ((blockedConfigEquiv d N p).symm ω)]
  have hrestrict := cyclicRestrictES_blockedConfigLinearIsometryEquiv_aligned
    d p hp hN i ω v
  have hinteraction := LinearMap.congr_fun
    (parentInteractionES_blockTensor_conj A p 2)
    (cyclicRestrictES (d := d) (Nat.mul_pos (Fin.pos i) hp) (2 * p)
      (alignedOriginalStart hp i) ω v)
  rw [hrestrict]
  rw [hinteraction]
  simp only [LinearMap.comp_apply]
  let y := parentInteractionES (blockTensor A p) 2
    ((blockedConfigLinearIsometryEquiv d 2 p).symm
      (cyclicRestrictES (d := d) (Nat.mul_pos (Fin.pos i) hp) (2 * p)
        (alignedOriginalStart hp i) ω v))
  change y ((blockedConfigEquiv d 2 p).symm
      (extractWindow (2 * p) (alignedOriginalStart hp i) ω)) =
    y (extractWindow 2 i ((blockedConfigEquiv d N p).symm ω))
  apply congrArg y
  have hextract := extractWindow_blockedConfigEquiv_aligned d p hp i
    ((blockedConfigEquiv d N p).symm ω)
  apply (blockedConfigEquiv d 2 p).injective
  simpa using hextract

/-- The range-\(2p\) original parent Hamiltonian dominates, as a quadratic
form, the conjugated blocked range-two Hamiltonian obtained by retaining only
block-aligned starts. This finite cyclic sparse-sum comparison is a TNLean
reconstruction; Nachtergaele's rescaling argument is stated for compatible open
intervals. -/
theorem blockTensor_parentHamiltonianES_conj_le
    (A : MPSTensor d D) (p : ℕ) (hp : 0 < p) {N : ℕ} (hN : 2 ≤ N) :
    (blockedConfigLinearIsometryEquiv d N p).toLinearEquiv.toLinearMap.comp
        ((parentHamiltonianES (blockTensor A p) 2 N).comp
          (blockedConfigLinearIsometryEquiv d N p).symm.toLinearEquiv.toLinearMap) ≤
      parentHamiltonianES A (2 * p) (N * p) := by
  rw [LinearMap.le_def]
  have hFull : parentHamiltonianES A (2 * p) (N * p) =
      ∑ j : Fin (N * p), localTermES A (2 * p) j :=
    parentHamiltonianES_eq_sum_localTermES A (2 * p) (N * p)
  have hSparse :
      (blockedConfigLinearIsometryEquiv d N p).toLinearEquiv.toLinearMap.comp
          ((parentHamiltonianES (blockTensor A p) 2 N).comp
            (blockedConfigLinearIsometryEquiv d N p).symm.toLinearEquiv.toLinearMap) =
        ∑ i : Fin N, localTermES A (2 * p) (alignedOriginalStart hp i) := by
    rw [parentHamiltonianES_eq_sum_localTermES]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact LinearMap.congr_fun (localTermES_blockTensor_conj_aligned A p hp hN i) v |>.symm
  rw [hFull, hSparse]
  let aligned : Finset (Fin (N * p)) := Finset.univ.map
    ⟨alignedOriginalStart hp, fun i j hij => by
      apply Fin.ext
      have hij' := congrArg Fin.val hij
      simp only [alignedOriginalStart] at hij'
      exact Nat.eq_of_mul_eq_mul_right hp hij'⟩
  have hAlignedSum :
      ∑ i : Fin N, localTermES A (2 * p) (alignedOriginalStart hp i) =
        ∑ j ∈ aligned, localTermES A (2 * p) j := by
    dsimp [aligned]
    rw [Finset.sum_map]
    rfl
  rw [hAlignedSum]
  have hsplit := Finset.sum_sdiff (f := fun j : Fin (N * p) => localTermES A (2 * p) j)
    (Finset.subset_univ aligned)
  rw [← hsplit]
  abel_nf
  exact LinearMap.isPositive_sum _ fun j _ => localTermES_isPositive A (2 * p) j

end MPSTensor
