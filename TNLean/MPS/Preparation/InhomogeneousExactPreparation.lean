/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousSequence

/-!
# Exact linear-depth preparation of inhomogeneous matrix product states

A nonzero inhomogeneous state with fixed bond bound `D` can be prepared exactly in depth
`O(N)`. Treat the entire ring as one block, normalize its positive-part state, and regard
that `D²`-dimensional vector as one entangled pair. The isometric extension of the polar
factor prepares the target exactly. No injectivity or spectral assumption is required.

This controls the short-chain branch `N < q` when an accuracy-dependent blocking length
exceeds the whole ring. Generic finite-dimensional synthesis is used only for the fixed
finite set `N < 3D`, not for arbitrarily long chains.

## Main result

* `exists_isPreparedInDepth_normalizedChainState`: exact preparation in depth at most `C N`,
  uniformly over all nonzero chains of fixed bond dimension.

## References

* arXiv:2307.01696, paragraphs "The sequential-RG circuit" (including its footnote on
  non-injective tensors) and "Inhomogeneous short-range correlated MPS".
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- **Exact preparation in linear depth.** For fixed physical dimension `d ≥ 1` and bond
bound `D`, there is `C` such that every nonzero inhomogeneous chain state on a positive ring
of `N` sites has a normalized state prepared in depth at most `C N`. No injectivity is assumed.

The sequential circuit of arXiv:2307.01696 is applied to one block covering the ring, with
its normalized positive-part state as the initial pair. -/
theorem exists_isPreparedInDepth_normalizedChainState (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (N : ℕ) [NeZero N] (A : MPSChainTensor d D N), chainState A ≠ 0 →
      ∃ T : ℕ, T ≤ C * N ∧
        IsPreparedInDepth T (fun s => ((‖chainState A‖ : ℂ)⁻¹ • chainState A) s) := by
  classical
  by_cases hd1 : d ≤ 1
  · exact ⟨0, fun N _ A _ => ⟨0, by simp, isPreparedInDepth_zero_of_le_one hd1 _⟩⟩
  have hd2 : 2 ≤ d := by omega
  have hDD : D * D ≤ d ^ (3 * D) := by
    have h : D ≤ d ^ D := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hd2 D)
    calc D * D ≤ d ^ D * d ^ D := Nat.mul_le_mul h h
      _ = d ^ (2 * D) := by rw [← pow_add]; ring_nf
      _ ≤ d ^ (3 * D) := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_blockMatVector d D hDD
  obtain ⟨K, hK⟩ := exists_isPreparedInDepth_of_norm_eq_one hd (3 * D)
  refine ⟨max C K, fun N _ A hA => ?_⟩
  have hunit : ‖(‖chainState A‖ : ℂ)⁻¹ • chainState A‖ = 1 := by
    simpa only [Complex.ofReal_inv] using (norm_smul_inv_norm (𝕜 := ℂ) hA)
  by_cases hN : 3 * D ≤ N
  · have hsum : ∑ _ : Fin 1, N = N := by simp
    let Y : MPVSpace (D * D) 1 := (‖chainState A‖ : ℂ)⁻¹ • chainPosState A hsum
    have hY : ‖Y‖ = 1 := by
      rw [Y, norm_smul, norm_inv, RCLike.norm_coe_norm,
        ← norm_chainState_eq A hsum, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)]
    let e : Fin D × Fin D ≃ Cfg (D * D) 1 :=
      (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (Equiv.funUnique (Fin 1) _).symm)
    let ω : Fin D × Fin D → ℂ := fun p => Y (e p)
    have hω : ∑ p, star (ω p) * ω p = 1 := by
      change ∑ p, star (Y (e p)) * Y (e p) = 1
      rw [e.sum_comp, sum_star_mul_self_eq_norm_sq, hY]
      norm_num
    have hpair : pairFamilyVector (fun _ : Fin 1 => ω) = Y := by
      ext τ
      rw [pairFamilyVector_apply]
      simp only [pairFamilyState, Fin.prod_univ_one]
      have h1 : finRotate 1 0 = 0 := Subsingleton.elim _ _
      have he : e ((finProdFinEquiv.symm (τ 0)).2,
          (finProdFinEquiv.symm (τ 0)).1) = τ := by
        funext k
        rw [Subsingleton.elim k 0]
        change finProdFinEquiv (finProdFinEquiv.symm (τ 0)) = τ 0
        exact Equiv.apply_symm_apply _ _
      rw [h1]
      exact congrArg Y he
    obtain ⟨W, _, hW, hprep⟩ := hC (fun _ : Fin 1 => N) hsum A (fun _ => ω)
      (fun _ => hω) N (fun _ => hN) (fun _ => le_rfl)
    rw [hpair, Y, blockMatVector_smul, ← chainState_eq_blockMatVector hsum hW] at hprep
    exact ⟨C * N, Nat.mul_le_mul_right N (le_max_left C K), hprep⟩
  · by_cases hN1 : N = 1
    · subst N
      exact ⟨0, Nat.zero_le _, isPreparedInDepth_zero_one_site _⟩
    · refine ⟨K, ?_, hK N (by have := NeZero.ne N; omega) (by omega) _ hunit⟩
      exact (le_max_right C K).trans
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne N)))

end MPSPreparation
