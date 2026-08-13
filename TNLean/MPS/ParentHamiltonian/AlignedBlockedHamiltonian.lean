/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Block-aligned parent Hamiltonians

Physical blocking by `p` sends the range-two interaction of the blocked tensor to the
range-`2 * p` interaction of the original tensor at starts divisible by `p`.  This file
records that local conjugacy, identifies the transported blocked Hamiltonian with the sparse
sum over those starts, and compares that sum with the full original parent Hamiltonian.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, equation (3.14).
* arXiv:2011.12127, Section IV.C.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- The original-chain site at the beginning of blocked site `i`. -/
def alignedOriginalSite {N p : ℕ} (hp : 0 < p) (i : Fin N) : Fin (N * p) :=
  ⟨i.val * p, by
    have hi := i.isLt
    exact Nat.mul_lt_mul_of_pos_right hi hp⟩

@[simp] theorem alignedOriginalSite_val {N p : ℕ} (hp : 0 < p) (i : Fin N) :
    (alignedOriginalSite hp i).val = i.val * p :=
  rfl

/-- Block-aligned starts are pairwise distinct. -/
theorem alignedOriginalSite_injective {N p : ℕ} (hp : 0 < p) :
    Function.Injective (alignedOriginalSite (N := N) hp) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [alignedOriginalSite_val] at hval
  exact Nat.eq_of_mul_eq_mul_right hp hval

@[simp] private theorem blockedConfigEquiv_apply_finProd (d N p : ℕ)
    (σ : Cfg (blockPhysDim d p) N) (i : Fin N) (j : Fin p) :
    blockedConfigEquiv d N p σ (finProdFinEquiv (i, j)) =
      decodeBlock d p (σ i) j := by
  simp [blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry, decodeBlockEquiv_apply,
    Function.comp]

private theorem block_site_add_mod {N p : ℕ} (hNpos : 0 < N) (_hp : 0 < p)
    (i q : Fin N) (r : Fin p) :
    (i.val * p + (q.val * p + r.val)) % (N * p) =
      ((i.val + q.val) % N) * p + r.val := by
  rw [show i.val * p + (q.val * p + r.val) = (i.val + q.val) * p + r.val by ring]
  rw [Nat.add_mod, Nat.mul_mod_mul_right]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le r.isLt (by
    calc p = 1 * p := by simp
      _ ≤ N * p := Nat.mul_le_mul_right p hNpos))]
  rw [Nat.mod_eq_of_lt]
  calc
    (i.val + q.val) % N * p + r.val <
        (i.val + q.val) % N * p + p := Nat.add_lt_add_left r.isLt _
    _ = ((i.val + q.val) % N + 1) * p := by
      rw [Nat.add_mul, Nat.one_mul]
    _ ≤ N * p := Nat.mul_le_mul_right p (by
      exact Nat.succ_le_iff.mpr (Nat.mod_lt _ hNpos))

private theorem block_site_offset_mod {N p : ℕ} (hp : 0 < p)
    (i q : Fin N) (r : Fin p) :
    (q.val * p + r.val + N * p - i.val * p) % (N * p) =
      ((q.val + N - i.val) % N) * p + r.val := by
  let off : Fin N := ⟨(q.val + N - i.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
  have hoff_lt : off.val * p + r.val < N * p := by
    calc
      off.val * p + r.val < off.val * p + p := Nat.add_lt_add_left r.isLt _
      _ = (off.val + 1) * p := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ N * p := Nat.mul_le_mul_right p (by omega)
  have hadd : (i.val * p + (off.val * p + r.val)) % (N * p) = q.val * p + r.val := by
    rw [block_site_add_mod (Fin.pos i) hp i off r]
    have hiq := add_offset_mod_eq i.isLt q.isLt
    change (i.val + off.val) % N = q.val at hiq
    rw [hiq]
  have hoff := offset_mod_eq
    (show i.val * p < N * p from Nat.mul_lt_mul_of_pos_right i.isLt hp) hoff_lt
  rw [hadd] at hoff
  exact hoff

theorem blockedConfigEquiv_extractWindow_aligned
    {N p : ℕ} (hp : 0 < p) (hN : 2 ≤ N)
    (i : Fin N) (σ : Cfg (blockPhysDim d p) N) :
    extractWindow (2 * p) (alignedOriginalSite hp i) (blockedConfigEquiv d N p σ) =
      blockedConfigEquiv d 2 p (extractWindow 2 i σ) := by
  funext k
  obtain ⟨⟨q, r⟩, rfl⟩ := finProdFinEquiv.surjective k
  let qN : Fin N := ⟨q.val, Nat.lt_of_lt_of_le q.isLt hN⟩
  have hsite :
      (⟨((alignedOriginalSite hp i).val + (finProdFinEquiv (q, r)).val) % (N * p),
          Nat.mod_lt _ (Nat.mul_pos (Fin.pos i) hp)⟩ : Fin (N * p)) =
        finProdFinEquiv
          (⟨(i.val + q.val) % N, Nat.mod_lt _ (Fin.pos i)⟩, r) := by
    apply Fin.ext
    simp only [alignedOriginalSite_val]
    rw [show (finProdFinEquiv (q, r)).val = q.val * p + r.val by
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]]
    rw [show (finProdFinEquiv
        (⟨(i.val + q.val) % N, Nat.mod_lt _ (Fin.pos i)⟩, r)).val =
          ((i.val + q.val) % N) * p + r.val by
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]]
    exact block_site_add_mod (Fin.pos i) hp i qN r
  change (blockedConfigEquiv d N p σ)
      (⟨((alignedOriginalSite hp i).val + (finProdFinEquiv (q, r)).val) % (N * p),
        _⟩ : Fin (N * p)) = _
  rw [hsite]
  simp only [blockedConfigEquiv_apply_finProd]
  congr 2

theorem blockedConfigEquiv_replaceWindow_aligned
    {N p : ℕ} (hp : 0 < p) (hN : 2 ≤ N)
    (i : Fin N) (σ : Cfg (blockPhysDim d p) N)
    (τ : Cfg (blockPhysDim d p) 2) :
    blockedConfigEquiv d N p (replaceWindow 2 hN i σ τ) =
      replaceWindow (2 * p) (Nat.mul_le_mul_right p hN) (alignedOriginalSite hp i)
        (blockedConfigEquiv d N p σ) (blockedConfigEquiv d 2 p τ) := by
  funext k
  obtain ⟨⟨q, r⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [blockedConfigEquiv_apply_finProd, replaceWindow]
  have hoff :
      ((finProdFinEquiv (q, r)).val + N * p - (alignedOriginalSite hp i).val) % (N * p) =
        ((q.val + N - i.val) % N) * p + r.val := by
    simp only [alignedOriginalSite_val]
    rw [show (finProdFinEquiv (q, r)).val = q.val * p + r.val by
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]]
    exact block_site_offset_mod hp i q r
  rw [hoff]
  by_cases hq : (q.val + N - i.val) % N < 2
  · have hoff_lt : ((q.val + N - i.val) % N) * p + r.val < 2 * p := by
      calc
        ((q.val + N - i.val) % N) * p + r.val <
            ((q.val + N - i.val) % N) * p + p := Nat.add_lt_add_left r.isLt _
        _ = ((q.val + N - i.val) % N + 1) * p := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ 2 * p := Nat.mul_le_mul_right p (Nat.succ_le_iff.mpr hq)
    rw [dif_pos hq, dif_pos hoff_lt]
    let off : Fin 2 := ⟨(q.val + N - i.val) % N, hq⟩
    have hidx :
        (⟨((q.val + N - i.val) % N) * p + r.val, hoff_lt⟩ : Fin (2 * p)) =
          finProdFinEquiv (off, r) := by
      apply Fin.ext
      simp [off, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [hidx, blockedConfigEquiv_apply_finProd]
  · have hoff_ge : ¬((q.val + N - i.val) % N) * p + r.val < 2 * p := by
      intro h
      have hmul : 2 * p ≤ ((q.val + N - i.val) % N) * p :=
        Nat.mul_le_mul_right p (by omega)
      omega
    rw [dif_neg hq, dif_neg hoff_ge]

/-- A blocked range-two term is the original range-`2 * p` term at the aligned start. -/
theorem localTermES_blockTensor_two_conj (A : MPSTensor d D) {N p : ℕ}
    (hp : 0 < p) (hN : 2 ≤ N) (i : Fin N) :
    localTermES A (2 * p) (alignedOriginalSite hp i) =
      (blockedConfigLinearIsometryEquiv d N p).toLinearEquiv.toLinearMap.comp
        ((localTermES (blockTensor A p) 2 i).comp
          (blockedConfigLinearIsometryEquiv d N p).symm.toLinearEquiv.toLinearMap) := by
  ext v σ
  simp only [LinearMap.comp_apply]
  rw [localTermES_apply A (2 * p) (alignedOriginalSite hp i)
    (Nat.mul_le_mul_right p hN)]
  change parentInteractionES A (2 * p)
      ((cyclicRestrictES (d := d) (Fin.pos (alignedOriginalSite hp i))
        (2 * p) (alignedOriginalSite hp i) σ) v)
      (extractWindow (2 * p) (alignedOriginalSite hp i) σ) =
    localTermES (blockTensor A p) 2 i
      ((blockedConfigLinearIsometryEquiv d N p).symm v)
      ((blockedConfigEquiv d N p).symm σ)
  rw [localTermES_apply (blockTensor A p) 2 i hN]
  have hinteraction := congrArg (fun f => f)
    (show parentInteractionES A (2 * p) =
      (blockedConfigLinearIsometryEquiv d 2 p).toLinearEquiv.toLinearMap.comp
        ((parentInteractionES (blockTensor A p) 2).comp
          (blockedConfigLinearIsometryEquiv d 2 p).symm.toLinearEquiv.toLinearMap) by
      simp only [parentInteractionES, Submodule.starProjection_orthogonal']
      rw [starProjection_groundSpaceES_blockTensor_conj A p 2]
      ext w
      simp)
  have hextract := blockedConfigEquiv_extractWindow_aligned
    (d := d) hp hN i ((blockedConfigEquiv d N p).symm σ)
  simp only [Equiv.apply_symm_apply] at hextract
  have hreplace (τ : Cfg (blockPhysDim d p) 2) :=
    blockedConfigEquiv_replaceWindow_aligned
      (d := d) hp hN i ((blockedConfigEquiv d N p).symm σ) τ
  simp only [Equiv.apply_symm_apply] at hreplace
  change parentInteractionES A (2 * p)
      ((cyclicRestrictES (d := d) (Fin.pos (alignedOriginalSite hp i))
        (2 * p) (alignedOriginalSite hp i) σ) v)
      (extractWindow (2 * p) (alignedOriginalSite hp i) σ) =
    parentInteractionES (blockTensor A p) 2
      ((cyclicRestrictES (d := blockPhysDim d p) (Fin.pos i) 2 i
        ((blockedConfigEquiv d N p).symm σ))
          ((blockedConfigLinearIsometryEquiv d N p).symm v))
      (extractWindow 2 i ((blockedConfigEquiv d N p).symm σ))
  rw [hinteraction]
  simp only [LinearMap.comp_apply]
  change parentInteractionES (blockTensor A p) 2
      ((blockedConfigLinearIsometryEquiv d 2 p).symm
        ((cyclicRestrictES (d := d) (Fin.pos (alignedOriginalSite hp i))
          (2 * p) (alignedOriginalSite hp i) σ) v))
      ((blockedConfigEquiv d 2 p).symm
        (extractWindow (2 * p) (alignedOriginalSite hp i) σ)) = _
  rw [hextract, Equiv.symm_apply_apply]
  apply congrArg (fun w => parentInteractionES (blockTensor A p) 2 w
    (extractWindow 2 i ((blockedConfigEquiv d N p).symm σ)))
  ext τ
  rw [blockedConfigLinearIsometryEquiv_symm_apply_apply]
  rw [cyclicRestrictES_apply, cyclicRestrictES_apply]
  rw [blockedConfigLinearIsometryEquiv_symm_apply_apply]
  change v (cyclicCfg (Fin.pos (alignedOriginalSite hp i)) (2 * p)
      (alignedOriginalSite hp i) (blockedConfigEquiv d 2 p τ) σ) =
    v (blockedConfigEquiv d N p
      (cyclicCfg (Fin.pos i) 2 i τ ((blockedConfigEquiv d N p).symm σ)))
  change v (replaceWindow (2 * p) (Nat.mul_le_mul_right p hN)
      (alignedOriginalSite hp i) σ (blockedConfigEquiv d 2 p τ)) =
    v (blockedConfigEquiv d N p
      (replaceWindow 2 hN i ((blockedConfigEquiv d N p).symm σ) τ))
  rw [← hreplace τ]



/-- The blocked range-two parent Hamiltonian transported to the original chain. -/
noncomputable def transportedBlockedParentHamiltonianES (A : MPSTensor d D)
    (N p : ℕ) :
    EuclideanSpace ℂ (Cfg d (N * p)) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d (N * p)) :=
  (blockedConfigLinearIsometryEquiv d N p).toLinearEquiv.toLinearMap.comp
    ((parentHamiltonianES (blockTensor A p) 2 N).comp
      (blockedConfigLinearIsometryEquiv d N p).symm.toLinearEquiv.toLinearMap)

/-- The sparse original-site sum over starts divisible by `p`. -/
noncomputable def alignedParentHamiltonianES (A : MPSTensor d D)
    (N p : ℕ) (hp : 0 < p) :
    EuclideanSpace ℂ (Cfg d (N * p)) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d (N * p)) :=
  ∑ i : Fin N, localTermES A (2 * p) (alignedOriginalSite hp i)

/-- Transporting the blocked range-two Hamiltonian gives the sparse aligned sum. -/
theorem transportedBlockedParentHamiltonianES_eq_alignedParentHamiltonianES
    (A : MPSTensor d D) {N p : ℕ} (hp : 0 < p) (hN : 2 ≤ N) :
    transportedBlockedParentHamiltonianES A N p =
      alignedParentHamiltonianES A N p hp := by
  rw [transportedBlockedParentHamiltonianES, parentHamiltonianES_eq_sum_localTermES]
  rw [alignedParentHamiltonianES]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact LinearMap.congr_fun (localTermES_blockTensor_two_conj A hp hN i).symm v

/-- The sparse aligned parent Hamiltonian is positive. -/
theorem alignedParentHamiltonianES_isPositive (A : MPSTensor d D)
    (N p : ℕ) (hp : 0 < p) :
    (alignedParentHamiltonianES A N p hp).IsPositive := by
  rw [alignedParentHamiltonianES]
  exact LinearMap.isPositive_sum _ fun i _ => localTermES_isPositive A (2 * p) _

/-- The transported blocked Hamiltonian is positive. -/
theorem transportedBlockedParentHamiltonianES_isPositive (A : MPSTensor d D)
    {N p : ℕ} (hp : 0 < p) (hN : 2 ≤ N) :
    (transportedBlockedParentHamiltonianES A N p).IsPositive := by
  rw [transportedBlockedParentHamiltonianES_eq_alignedParentHamiltonianES A hp hN]
  exact alignedParentHamiltonianES_isPositive A N p hp

/-- The aligned starts form a subset of all original-chain starts. -/
private def alignedOriginalSites {N p : ℕ} (hp : 0 < p) : Finset (Fin (N * p)) :=
  Finset.univ.image (alignedOriginalSite hp)

/-- The sparse aligned Hamiltonian is bounded above by the full original parent Hamiltonian. -/
theorem alignedParentHamiltonianES_le_parentHamiltonianES (A : MPSTensor d D)
    {N p : ℕ} (hp : 0 < p) :
    alignedParentHamiltonianES A N p hp ≤ parentHamiltonianES A (2 * p) (N * p) := by
  rw [parentHamiltonianES_eq_sum_localTermES]
  have hsum :
      ∑ i : Fin N, localTermES A (2 * p) (alignedOriginalSite hp i) =
        ∑ j ∈ alignedOriginalSites hp, localTermES A (2 * p) j := by
    rw [alignedOriginalSites, Finset.sum_image]
    intro i _ j _ hij
    exact alignedOriginalSite_injective hp hij
  rw [alignedParentHamiltonianES, hsum]
  exact Finset.sum_le_univ_sum_of_nonneg fun j =>
    (show 0 ≤ localTermES A (2 * p) j from
      (LinearMap.nonneg_iff_isPositive (localTermES A (2 * p) j)).mpr
        (localTermES_isPositive A (2 * p) j))

/-- Positivity and the full Loewner comparison for the transported blocked Hamiltonian. -/
theorem transportedBlockedParentHamiltonianES_nonneg_le_parentHamiltonianES
    (A : MPSTensor d D) {N p : ℕ} (hp : 0 < p) (hN : 2 ≤ N) :
    0 ≤ transportedBlockedParentHamiltonianES A N p ∧
      transportedBlockedParentHamiltonianES A N p ≤
        parentHamiltonianES A (2 * p) (N * p) := by
  rw [transportedBlockedParentHamiltonianES_eq_alignedParentHamiltonianES A hp hN]
  exact ⟨(LinearMap.nonneg_iff_isPositive
      (alignedParentHamiltonianES A N p hp)).mpr
        (alignedParentHamiltonianES_isPositive A N p hp),
    alignedParentHamiltonianES_le_parentHamiltonianES A hp⟩

end MPSTensor
