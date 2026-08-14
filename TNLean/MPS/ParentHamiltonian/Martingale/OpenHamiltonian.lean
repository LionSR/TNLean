/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# The nonwrapping open-chain parent Hamiltonian

For a chain of length `N`, this file sums the canonical local parent interactions
only over starts whose length-`L` windows stay inside the linear interval.  Thus
no local term crosses the cut between the last and first sites.

The kernel is the open MPS boundary-condition space `groundSpaceES A N` once the
tensor is block-injective at length \(L - 1\).  This is the finite-volume
ground-space input for Nachtergaele's C1--C3 martingale theorem.

## References

* Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16).
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, Section IV.C.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A start site whose length-`L` window does not cross the right endpoint of an
`N`-site open chain.

This is the index set in Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
abbrev NonwrappingStart (L N : ℕ) :=
  {i : Fin N // i.val + L ≤ N}

/-- The open-chain parent Hamiltonian, obtained by summing the canonical local
terms over all nonwrapping length-`L` windows.

For \(L = l + 1\), its starts are \(0, \ldots, N - l - 1\), as in Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
noncomputable def openParentHamiltonianES (A : MPSTensor d D) (L N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i : NonwrappingStart L N, localTermES A L i.1

/-- The open-chain parent Hamiltonian is positive because every summand is an
orthogonal projection. -/
theorem openParentHamiltonianES_isPositive (A : MPSTensor d D) (L N : ℕ) :
    (openParentHamiltonianES A L N).IsPositive := by
  rw [openParentHamiltonianES]
  exact LinearMap.isPositive_sum _ fun i _ => localTermES_isPositive A L i.1

/-- If the open-chain Hamiltonian annihilates a vector, then every individual
nonwrapping local term annihilates it.

This is the elementary frustration-free extraction used before the C1--C3
estimate in Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem localTermES_eq_zero_of_openParentHamiltonianES_eq_zero
    (A : MPSTensor d D) (L N : ℕ) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : openParentHamiltonianES A L N v = 0) (i : NonwrappingStart L N) :
    localTermES A L i.1 v = 0 := by
  rw [openParentHamiltonianES] at hv
  exact ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
    (fun i : NonwrappingStart L N => localTermES A L i.1)
    (fun i => localTermES_isSymmetricProjection A L i.1) hv i

private theorem contiguousRestrictₗ_groundSpaceMap_mem_groundSpace
    {A : MPSTensor d D} {s L N : ℕ} (hsL : s + L ≤ N)
    (τ : Fin N → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    contiguousRestrictₗ s L hsL τ (groundSpaceMap A N X) ∈ groundSpace A L := by
  rw [groundSpace, LinearMap.mem_range]
  let leftWord : List (Fin d) := List.ofFn fun k : Fin s => τ ⟨k.val, by omega⟩
  let rightWord : List (Fin d) := List.ofFn fun k : Fin (N - (s + L)) =>
    τ ⟨s + L + k.val, by omega⟩
  refine ⟨evalWord A rightWord * X * evalWord A leftWord, ?_⟩
  ext σ
  simp only [contiguousRestrictₗ_apply, groundSpaceMap_apply]
  have hlist :
      List.ofFn (contiguousCfg s L σ τ) = leftWord ++ List.ofFn σ ++ rightWord := by
    apply List.ext_getElem
    · simp [leftWord, rightWord, List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      have hkN : k < N := by
        simpa [List.length_ofFn] using hk₁
      simp only [List.getElem_ofFn]
      by_cases hkLeft : k < s
      · have hkNotWin : ¬(s ≤ k ∧ k < s + L) := by omega
        rw [contiguousCfg, dif_neg hkNotWin]
        rw [List.getElem_append_left]
        · rw [List.getElem_append_left]
          · have hkLeftWord : k < leftWord.length := by
              simpa only [leftWord, List.length_ofFn] using hkLeft
            rw [show leftWord[k]'hkLeftWord = τ ⟨k, by omega⟩ from by
              simp only [leftWord, List.getElem_ofFn]]
          · simpa only [leftWord, List.length_ofFn] using hkLeft
        · simpa only [leftWord, List.length_append, List.length_ofFn] using
            (show k < s + L by omega)
      · by_cases hkWin : k < s + L
        · have hwin : s ≤ k ∧ k < s + L := by omega
          rw [contiguousCfg, dif_pos hwin]
          rw [List.getElem_append_left]
          · rw [List.getElem_append_right]
            · rw [List.getElem_ofFn]
              congr 1
              ext
              simp [leftWord]
            · simpa only [leftWord, List.length_ofFn] using
                (show s ≤ k by omega)
          · simpa only [leftWord, List.length_append, List.length_ofFn] using hkWin
        · have hkRight : s + L ≤ k := by omega
          have hkNotWin : ¬(s ≤ k ∧ k < s + L) := by omega
          rw [contiguousCfg, dif_neg hkNotWin]
          rw [List.getElem_append_right]
          · have hRightIndex :
                k - (leftWord ++ List.ofFn σ).length < rightWord.length := by
              simp only [rightWord, leftWord, List.length_append, List.length_ofFn]
              omega
            rw [show rightWord[k - (leftWord ++ List.ofFn σ).length]'hRightIndex =
                τ ⟨k, by omega⟩ from by
              simp only [rightWord, List.getElem_ofFn]
              congr 1
              ext
              simp only [leftWord, List.length_append, List.length_ofFn]
              omega]
          · simpa only [leftWord, List.length_append, List.length_ofFn] using hkRight
  rw [hlist, evalWord_append, evalWord_append]
  calc
    Matrix.trace (evalWord A (List.ofFn σ) *
        (evalWord A rightWord * X * evalWord A leftWord)) =
        Matrix.trace ((evalWord A (List.ofFn σ) * (evalWord A rightWord * X)) *
          evalWord A leftWord) := by
      rw [← Matrix.mul_assoc]
    _ = Matrix.trace (evalWord A leftWord *
        (evalWord A (List.ofFn σ) * (evalWord A rightWord * X))) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((evalWord A leftWord * evalWord A (List.ofFn σ) *
        evalWord A rightWord) * X) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc]

/-- The open MPS boundary-condition space is contained in the kernel of the
open-chain parent Hamiltonian.

Every nonwrapping restriction of an open-boundary MPS vector is again an
open-boundary MPS vector on the smaller interval.  This is the frustration-free
direction of Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem groundSpaceES_le_ker_openParentHamiltonianES
    (A : MPSTensor d D) (L N : ℕ) :
    groundSpaceES A N ≤ LinearMap.ker (openParentHamiltonianES A L N) := by
  intro v hv
  rw [LinearMap.mem_ker, openParentHamiltonianES, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A
    (by omega : L ≤ N) i.1 v]
  intro τ
  rw [mem_groundSpaceES_iff]
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  let eL := WithLp.linearEquiv 2 ℂ (NSiteSpace d L)
  have hvNS : eN v ∈ groundSpace A N := (mem_groundSpaceES_iff A N v).1 hv
  rw [groundSpace, LinearMap.mem_range] at hvNS
  obtain ⟨X, hX⟩ := hvNS
  have hrestrict :
      contiguousRestrictₗ i.1.val L i.2 τ (eN v) ∈ groundSpace A L := by
    rw [← hX]
    exact contiguousRestrictₗ_groundSpaceMap_mem_groundSpace i.2 τ X
  rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i.1) (by omega) i.2] at hrestrict
  simpa [cyclicRestrictES, eN, eL] using hrestrict

/-- Under block injectivity, the kernel of the open-chain parent Hamiltonian is
contained in the open MPS boundary-condition space.

The zero-energy condition supplies every nonwrapping length-\(L₀ + 1\) local
constraint.  The open-chain intersection theorem then grows these constraints
to the full interval.  This is the ground-space step in the C1--C3 argument of
Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_openParentHamiltonianES_le_groundSpaceES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (openParentHamiltonianES A (L₀ + 1) N) ≤ groundSpaceES A N := by
  intro v hv
  rw [mem_groundSpaceES_iff]
  apply contiguous_mem_groundSpace_of_isNBlkInjective hInj hL₀ hL₀N
  intro s hs τ
  let i : NonwrappingStart (L₀ + 1) N := ⟨⟨s, by omega⟩, hs⟩
  have hopen : openParentHamiltonianES A (L₀ + 1) N v = 0 := by
    rwa [LinearMap.mem_ker] at hv
  have hlocal : localTermES A (L₀ + 1) i.1 v = 0 :=
    localTermES_eq_zero_of_openParentHamiltonianES_eq_zero A (L₀ + 1) N hopen i
  have hrestrictES := cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero
    A hL₀N i.1 hlocal τ
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  let eL := WithLp.linearEquiv 2 ℂ (NSiteSpace d (L₀ + 1))
  have hrestrict :
      cyclicRestrictₗ (Fin.pos i.1) (L₀ + 1) i.1 τ (eN v) ∈
        groundSpace A (L₀ + 1) := by
    simpa [cyclicRestrictES, eN, eL] using
      (mem_groundSpaceES_iff A (L₀ + 1) _).1 hrestrictES
  rwa [cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i.1) hL₀N i.2] at hrestrict

/-- For a block-injective tensor, the kernel of the canonical nonwrapping open
parent Hamiltonian is exactly the open MPS boundary-condition space.

Unlike the periodic ground space, this space generally has boundary-matrix
degeneracy.  This is the finite-volume kernel identification used in
Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (openParentHamiltonianES A (L₀ + 1) N) = groundSpaceES A N :=
  le_antisymm
    (ker_openParentHamiltonianES_le_groundSpaceES_of_isNBlkInjective
      hInj hL₀ hL₀N)
    (groundSpaceES_le_ker_openParentHamiltonianES A (L₀ + 1) N)

end MPSTensor
