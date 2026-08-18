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

When the tensor has virtual dimension \(D \ge 1\) and is block-injective at
length \(L₀\), with \(0 < L₀\) and \(L₀ + 1 \le N\), the kernel of the
length-\(L₀ + 1\) open Hamiltonian is the open MPS boundary-condition space
`groundSpaceES A N`. This is the finite-volume ground-space input for
Nachtergaele's C1--C3 martingale theorem.

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

/-- At volume \(N = L > 0\), the compatible open parent Hamiltonian is the
canonical local projector on the full chain.

This is the fixed-window operator underlying \(γ_{l+1} = 1\) in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(i). -/
theorem openParentHamiltonianES_self_eq_parentInteractionES (A : MPSTensor d D)
    {L : ℕ} (hL : 0 < L) :
    openParentHamiltonianES A L L = parentInteractionES A L := by
  let i : NonwrappingStart L L := ⟨⟨0, hL⟩, by simp⟩
  let : Subsingleton (NonwrappingStart L L) :=
    ⟨fun j k => by
      apply Subtype.ext
      apply Fin.ext
      have hj := j.2
      have hk := k.2
      omega⟩
  rw [openParentHamiltonianES, Fintype.sum_subsingleton _ i]
  ext v σ
  rw [localTermES_apply A L i.1 (le_refl L) v σ]
  have hrestrict : cyclicRestrictES (d := d) hL L i.1 σ v = v := by
    ext ω
    change v (cyclicCfg hL L (⟨0, hL⟩ : Fin L) ω σ) = v ω
    rw [show cyclicCfg hL L (⟨0, hL⟩ : Fin L) ω σ = ω by
      funext k
      simp [cyclicCfg, Nat.mod_eq_of_lt k.isLt]]
  rw [hrestrict]
  rw [show extractWindow L i.1 σ = σ by
    funext k
    simp [i, extractWindow, Nat.mod_eq_of_lt k.isLt]]

/-- The full-window compatible open parent Hamiltonian preserves the norm on
the orthogonal complement of its kernel. -/
theorem openParentHamiltonianES_self_norm_eq_of_mem_orthogonal_ker
    (A : MPSTensor d D) {L : ℕ} (hL : 0 < L)
    (v : EuclideanSpace ℂ (Cfg d L))
    (hv : v ∈ (LinearMap.ker (openParentHamiltonianES A L L))ᗮ) :
    ‖openParentHamiltonianES A L L v‖ = ‖v‖ := by
  rw [openParentHamiltonianES_self_eq_parentInteractionES A hL] at hv ⊢
  change ‖(groundSpaceES A L)ᗮ.starProjection v‖ = ‖v‖
  apply Submodule.norm_starProjection_apply
  have hker : LinearMap.ker (parentInteractionES A L) = groundSpaceES A L := by
    ext w
    rw [LinearMap.mem_ker, parentInteractionES_apply_eq_zero_iff]
  rwa [hker] at hv

/-- The compatible open parent Hamiltonian has unit norm gap at the first
full-window volume.

This is \(γ_{l+1} = 1\) in Nachtergaele, arXiv:cond-mat/9410110,
Theorem 2.1(i), for \(L = l + 1\).

**Scope restriction (single-window volume):** This proves only the volume
\(N=L\). It does not establish the general-volume C1--C3 martingale gap; see
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem openParentHamiltonianES_self_unit_gap (A : MPSTensor d D)
    {L : ℕ} (hL : 0 < L) (v : EuclideanSpace ℂ (Cfg d L))
    (hv : v ∈ (LinearMap.ker (openParentHamiltonianES A L L))ᗮ) :
    (1 : ℝ) * ‖v‖ ≤ ‖openParentHamiltonianES A L L v‖ := by
  simpa only [one_mul] using
    (openParentHamiltonianES_self_norm_eq_of_mem_orthogonal_ker A hL v hv).symm.le

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
