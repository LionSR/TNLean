/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockStatePreparation

/-!
# Exact preparation of the periodic state on short chains

The log-depth preparation of arXiv:2307.01696 blocks `q ∝ log(N/ε)` sites. A ring shorter than
this block length carries no block of length `q`; there the periodic state `|φ_N⟩` is prepared
exactly, in depth linear in `N`.

* On a ring of `N ≥ 3D` sites whose `N`-site blocked tensor is injective, `|φ_N⟩` is the state
  `V (P |𝟙⟩)` of a single block, where `B_N = V P` and `|𝟙⟩ = ∑_α |α, α⟩`. It is therefore the
  state `(⊗ₖ V_k) ⊗ₖ |ω⟩` of one block with the pair `ω ∝ P |𝟙⟩`
  (`MPSPreparation.blockIsometryState_normalizedTracePair`), and the circuit of
  `MPSPreparation.exists_isPreparedInDepth_blockIsometryState` prepares it in depth `C N`
  (`MPSPreparation.exists_isPreparedInDepth_normalizedMPVState`). This is the sequential
  preparation of a matrix product state, one site at a time, as in arXiv:quant-ph/0501096.
* On a ring of at most `n₀` sites, every unit vector is prepared in a depth bounded in terms of
  `d` and `n₀` alone (`MPSPreparation.exists_isPreparedInDepth_of_norm_eq_one`).

The source does not treat chains shorter than the block length: its proof of Theorem 1 takes
`N` "such that we have a large number of blocks".
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace
open QuantumCircuit

namespace MPSPreparation

variable {d D : ℕ}

/-- The squared norm of a vector as the sum of the squared moduli of its coefficients. -/
theorem sum_star_mul_self_eq_norm_sq {N : ℕ} (v : MPVSpace d N) :
    ∑ s, star (v s) * v s = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Complex.conj_mul']
  rfl

/-! ### Bounded chains -/

/-- **Unit vectors on bounded chains.** For `d ≥ 1` and every bound `n₀` there is `K` such that
every unit vector on a ring of `N` sites, `2 ≤ N ≤ n₀`, is prepared in depth at most `K` from a
product state.

The proof writes `ψ` as the first column of a unitary on the `N ≤ n₀` sites and decomposes that
unitary into boundedly many two-site gates by `exists_isPairProduct`. arXiv:2307.01696, caption of
Fig. 1(b), says the analogous thing of the circuit for the isometry `V`: it "can be further
expressed with a low-depth circuit of local gates". -/
theorem exists_isPreparedInDepth_of_norm_eq_one (hd : 0 < d) (n₀ : ℕ) :
    ∃ K : ℕ, ∀ N [NeZero N], 2 ≤ N → N ≤ n₀ → ∀ ψ : MPVSpace d N, ‖ψ‖ = 1 →
      IsPreparedInDepth K fun s => ψ s := by
  classical
  have h : ∀ n : Fin (n₀ + 1), ∃ K : ℕ, 2 ≤ n.val →
      ∀ X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ), IsPairProduct d n K X := fun n => by
    by_cases hn : 2 ≤ n.val
    · obtain ⟨K, hK⟩ := exists_isPairProduct hd hn
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose K hK using h
  refine ⟨∑ n, K n, fun N _ hN hNn₀ ψ hψ => ?_⟩
  let V : Matrix (Cfg d N) Unit ℂ := Matrix.of fun s _ => ψ s
  have hV : V.IsIsometry := by
    ext ⟨⟩ ⟨⟩
    rw [mul_apply, one_apply_eq]
    simp only [conjTranspose_apply, V, of_apply]
    rw [sum_star_mul_self_eq_norm_sq, hψ]
    norm_num
  let emb : Unit ↪ Cfg d N := ⟨fun _ _ => ⟨0, hd⟩, fun _ _ _ => rfl⟩
  obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
  have hpp := hK ⟨N, by omega⟩ hN U hU
  have hc := hpp.isCircuitOn (e := id) Function.injective_id fun i j h => by
    ext
    rw [id, id, Fin.val_add_one_of_lt' (by omega), h]
  rw [embedOp_id] at hc
  refine ⟨U, (hc.mono (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨N, by omega⟩ : Fin (n₀ + 1))))).isBondCircuitOfDepth,
    fun _ => Pi.single ⟨0, hd⟩ 1, funext fun s => ?_⟩
  rw [mulVec_productVector_single_zero hd]
  exact (hUV s ()).symm

/-! ### One block -/

/-- The pair `ω(r, l) = Tr P^{(l, r)} / ‖φ_N‖`, where `P` is the positive factor of the `N`-site
blocked tensor `B_N = V P`: up to normalization, `ω` is `P |𝟙⟩` with `|𝟙⟩ = ∑_α |α, α⟩`. -/
noncomputable def normalizedTracePair (A : MPSTensor d D) (N : ℕ) : Fin D × Fin D → ℂ :=
  fun p => (‖mpvState A N‖ : ℂ)⁻¹ *
    Matrix.trace (polarPosTensor (blockTensor A N) (finProdFinEquiv (p.2, p.1)))

/-- **The periodic state is a one-block state.** On a single block of `N` sites, the state
`V ⊗ |ω⟩` with the pair `ω = normalizedTracePair A N`, whose right leg is joined to its own left
leg around the ring, is the normalized periodic state `|φ_N⟩`: indeed
`φ_N(A)(s) = Tr B_N^s = ∑_{(l, r)} ⟨s|V|l, r⟩ Tr P^{(l, r)}`. -/
theorem blockIsometryState_normalizedTracePair (A : MPSTensor d D) (N : ℕ)
    (hN : ∑ _ : Fin 1, N = N) :
    blockIsometryState A (normalizedTracePair A N) hN = normalizedMPVState A N := by
  ext s
  rw [blockIsometryState_apply, normalizedMPVState, PiLp.smul_apply, mpvState_apply,
    mpv_eq_mpvFamily_blockTensor A hN,
    show (fun _ : Fin 1 => blockTensor A N) = fun k => rotatePhysical
      (polarIsoMatrix (blockTensor A N)) (polarPosTensor (blockTensor A N)) from
        funext fun _ => (rotatePhysical_polarIsoMatrix_polarPosTensor _).symm,
    mpvFamily_rotatePhysical, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hrot : finRotate 1 0 = 0 := Subsingleton.elim _ _
  simp only [pairProductState, normalizedTracePair, Fin.prod_univ_one, hrot, mpvFamily,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Prod.mk.eta,
    Equiv.apply_symm_apply]
  ring

/-- **Exact preparation on one block.** There is `C`, depending only on `d` and `D`, such that
for every tensor `A` and every ring of `N ≥ 3D` sites whose `N`-site blocked tensor is injective
and whose periodic state does not vanish, the normalized periodic state `|φ_N⟩` is prepared
exactly in depth at most `C N`.

This is the circuit of arXiv:2307.01696, paragraph "The sequential-RG circuit", applied to one
block covering the whole ring, with the pair `ω ∝ P |𝟙⟩` in place of the pair of the fixed
point. -/
theorem exists_isPreparedInDepth_normalizedMPVState (d D : ℕ) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (N : ℕ) [NeZero N], 3 * D ≤ N →
      Kraus.IsInjective (blockTensor A N) → mpvState A N ≠ 0 →
        IsPreparedInDepth (C * N) fun s => normalizedMPVState A N s := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_blockIsometryState d D
  refine ⟨C, fun A N _ hN3 hinj h0 => ?_⟩
  have hN : ∑ _ : Fin 1, N = N := by simp
  have hid := blockIsometryState_normalizedTracePair A N hN
  have hω : ∑ p, star (normalizedTracePair A N p) * normalizedTracePair A N p = 1 := by
    have h := sum_star_blockIsometryState A (normalizedTracePair A N) hN fun _ => hinj
    rw [pow_one, hid, sum_star_mul_self_eq_norm_sq, norm_normalizedMPVState h0] at h
    rw [← h]; simp
  rw [← hid]
  exact hC A _ hω (fun _ : Fin 1 => N) hN N (fun _ => hN3) (fun _ => le_rfl) fun _ => hinj

end MPSPreparation
