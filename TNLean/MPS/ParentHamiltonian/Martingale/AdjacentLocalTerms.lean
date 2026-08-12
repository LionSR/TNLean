/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenChain
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Adjacent open-chain excitation projections

This file identifies, on the explicit three-site Hilbert space, the two
complementary open-chain ground projections with the range-two local parent
Hamiltonian terms based at sites `0` and `1`.

The coordinate bridges compare the open-chain `restrictLast` and tail
`restrictFirst` slices with the cyclic restrictions used to define `localTermES`.
They yield the individual kernel identities before projection uniqueness is
applied; no injectivity or nonzero bond-dimension assumption is needed.

## Main results

* `MPSTensor.ker_localTermES_two_three_zero` identifies the site-`0` kernel
  with the left open-chain ground space.
* `MPSTensor.ker_localTermES_two_three_one` identifies the site-`1` kernel
  with the tail open-chain ground space.
* `MPSTensor.openChainLeftGroundSpaceES_orthogonal_starProjection_eq_localTermES`
  and `MPSTensor.openChainTailGroundSpaceES_orthogonal_starProjection_eq_localTermES`
  identify the complementary excitation projections with those local terms.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, eqs. (2.4)--(2.5).
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127,
  Section IV.C, lines 2013--2078.
-/

namespace MPSTensor

variable {d D : ℕ}

/-! ### Open-chain and cyclic coordinate bridges -/

/-- At site `0` of an `(L+1)`-site chain, fixing the final site by
`restrictLast` is the same coordinate slice as the cyclic restriction.

This is the site-`0` coordinate identification behind the left open-chain
condition in Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4). -/
theorem restrictLast_eq_cyclicRestrictES_zero {L : ℕ}
    (v : EuclideanSpace ℂ (Cfg d (L + 1))) (τ : Cfg d (L + 1)) :
    restrictLast ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))) v) (τ (Fin.last L)) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
        (cyclicRestrictES (d := d) (Fin.pos (0 : Fin (L + 1))) L (0 : Fin (L + 1))
          τ v) := by
  ext σ
  change v.ofLp (Fin.snoc σ (τ (Fin.last L))) = v.ofLp
    (cyclicCfg (d := d) (Fin.pos (0 : Fin (L + 1))) L (0 : Fin (L + 1)) σ τ)
  apply congrArg v.ofLp
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨r, rfl⟩ | rfl
  · have hmod : r.val % (L + 1) = r.val := Nat.mod_eq_of_lt (by omega)
    simp [cyclicCfg, hmod]
  · simp [cyclicCfg]

/-- Fixing the sole prefix site of a three-site state by `tailRestrictₗ` is
exactly `restrictFirst` at that coordinate.

This is the tail/first-coordinate bridge for the site-`1` open-chain condition
in Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4). -/
theorem tailRestrictₗ_one_eq_restrictFirst (u : Fin 1 → Fin d)
    (ψ : NSiteSpace d (1 + 2)) :
    tailRestrictₗ u ψ = restrictFirst ψ (u 0) := by
  ext σ
  simp only [tailRestrictₗ_apply, restrictFirst_apply]
  apply congrArg ψ
  rw [Fin.append_left_eq_cons]
  funext k
  exact congrArg (Fin.cons (u 0) σ) (Fin.ext (by simp))

/-- At site `1` of an `(L+1)`-site chain, fixing the first site by
`restrictFirst` is the same coordinate slice as the cyclic restriction.

This is the site-`1` coordinate identification behind the tail open-chain
condition in Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4). -/
theorem restrictFirst_eq_cyclicRestrictES_one {L : ℕ} (hL : 0 < L)
    (v : EuclideanSpace ℂ (Cfg d (L + 1))) (τ : Cfg d (L + 1)) :
    restrictFirst ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))) v) (τ 0) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
        (cyclicRestrictES (d := d) (Fin.pos (1 : Fin (L + 1))) L (1 : Fin (L + 1))
          τ v) := by
  ext σ
  change v.ofLp (Fin.cons (τ 0) σ) = v.ofLp
    (cyclicCfg (d := d) (Fin.pos (1 : Fin (L + 1))) L (1 : Fin (L + 1)) σ τ)
  apply congrArg v.ofLp
  funext k
  have hOneNat : 1 % (L + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨r, rfl⟩
  · simp [cyclicCfg, hOneNat]
  · have hmod : (r.val + 1 + L) % (L + 1) = r.val := by
      rw [show r.val + 1 + L = r.val + (L + 1) by omega]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp [cyclicCfg, hOneNat, hmod]

/-! ### Individual three-site kernels -/

/-- On the explicit three-site chain, the kernel of the range-two local term at
site `0` is the left open-chain ground space.

Source terminology: this is the ground condition on `Λ_n` inside `Λ_{n+1}` in
Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4). -/
theorem ker_localTermES_two_three_zero (B : MPSTensor d D) :
    LinearMap.ker (localTermES B 2 (0 : Fin 3)) = openChainLeftGroundSpaceES B 2 := by
  ext v
  rw [LinearMap.mem_ker, mem_openChainLeftGroundSpaceES_iff,
    localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES B (by omega)
      (0 : Fin 3) v]
  constructor
  · intro hv j
    have h := hv (fun _ => j)
    rw [mem_groundSpaceES_iff] at h
    rwa [restrictLast_eq_cyclicRestrictES_zero v (fun _ => j)]
  · intro hv τ
    rw [mem_groundSpaceES_iff]
    rw [← restrictLast_eq_cyclicRestrictES_zero v τ]
    exact hv (τ (Fin.last 2))

/-- On the explicit three-site chain, the kernel of the range-two local term at
site `1` is the one-site-prefix tail open-chain ground space.

Source terminology: this is the tail condition on
`Λ_{n+1} \ Λ_{n-l}` inside `Λ_{n+1}` in Nachtergaele,
arXiv:cond-mat/9410110, eq. (2.4). -/
theorem ker_localTermES_two_three_one (B : MPSTensor d D) :
    LinearMap.ker (localTermES B 2 (1 : Fin 3)) = openChainTailGroundSpaceES B 1 2 := by
  ext v
  rw [LinearMap.mem_ker, mem_openChainTailGroundSpaceES_iff,
    localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES B (by omega)
      (1 : Fin 3) v]
  constructor
  · intro hv u
    rw [tailRestrictₗ_one_eq_restrictFirst]
    have h := hv (fun _ => u 0)
    rw [mem_groundSpaceES_iff] at h
    rwa [restrictFirst_eq_cyclicRestrictES_one (by omega) v (fun _ => u 0)]
  · intro hv τ
    rw [mem_groundSpaceES_iff]
    rw [← restrictFirst_eq_cyclicRestrictES_one (by omega) v τ]
    rw [← tailRestrictₗ_one_eq_restrictFirst (fun _ => τ 0)]
    exact hv (fun _ => τ 0)

/-! ### Complementary excitation projections -/

private theorem range_eq_orthogonal_ker_of_isSymmetricProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {P : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) :
    LinearMap.range P = (LinearMap.ker P)ᗮ := by
  have horth : (LinearMap.range P)ᗮ = LinearMap.ker P := hP.isSymmetric.orthogonal_range
  rw [← horth, Submodule.orthogonal_orthogonal]

/-- On the explicit three-site chain, the complementary left open-chain ground
projection is the range-two local parent-Hamiltonian term at site `0`.

The proof uses uniqueness of a symmetric projection from its range, after the
site-`0` kernel has been identified. -/
theorem openChainLeftGroundSpaceES_orthogonal_starProjection_eq_localTermES
    (B : MPSTensor d D) :
    (openChainLeftGroundSpaceES B 2)ᗮ.starProjection.toLinearMap =
      localTermES B 2 (0 : Fin 3) := by
  apply (Submodule.isSymmetricProjection_starProjection
    ((openChainLeftGroundSpaceES B 2)ᗮ)).ext (localTermES_isSymmetricProjection B 2 _)
  rw [Submodule.range_starProjection]
  rw [range_eq_orthogonal_ker_of_isSymmetricProjection
    (localTermES_isSymmetricProjection B 2 (0 : Fin 3))]
  rw [ker_localTermES_two_three_zero]

/-- On the explicit three-site chain, the complementary tail open-chain ground
projection is the range-two local parent-Hamiltonian term at site `1`.

The proof uses uniqueness of a symmetric projection from its range, after the
site-`1` kernel has been identified. -/
theorem openChainTailGroundSpaceES_orthogonal_starProjection_eq_localTermES
    (B : MPSTensor d D) :
    (openChainTailGroundSpaceES B 1 2)ᗮ.starProjection.toLinearMap =
      localTermES B 2 (1 : Fin 3) := by
  apply (Submodule.isSymmetricProjection_starProjection
    ((openChainTailGroundSpaceES B 1 2)ᗮ)).ext (localTermES_isSymmetricProjection B 2 _)
  rw [Submodule.range_starProjection]
  rw [range_eq_orthogonal_ker_of_isSymmetricProjection
    (localTermES_isSymmetricProjection B 2 (1 : Fin 3))]
  rw [ker_localTermES_two_three_one]

end MPSTensor
