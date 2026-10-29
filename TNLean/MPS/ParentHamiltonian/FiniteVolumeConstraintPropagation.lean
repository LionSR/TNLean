/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ArbitraryInteractionBlockDegeneracy
import TNLean.MPS.ParentHamiltonian.PGVWC07CutRank

/-!
# A finite-ring constraint determines the local MPS kernel

Complementary word spanning turns a zero-energy equation on one nonempty
ring into annihilation of the entire active boundary space. The same local
interaction therefore annihilates the periodic vector on every other ring
at least as long as the interaction range. No complementary span on the
new ring is required.

Source: SPWC10, arXiv:0909.5347, Theorem 5 proof, lines 869–880 of
`Papers/0909.5347/main.tex`; PGVWC07, Theorem 11, `2blocks.1`, proof
lines 1418–1422 of `Papers/quant-ph_0608197/MPSarchive.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D r N L : ℕ} {dim : Fin r → ℕ}

/-- One positive periodic Hamiltonian equation implies annihilation of every
boundary vector of every block, once its complementary word tuples span.
Source: SPWC10, Theorem 5 proof, lines 869–880; PGVWC07, Theorem 11 proof,
lines 1418–1422. -/
theorem boundary_eq_zero_of_periodicInteractionHamiltonianES_eq_zero
    (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (hc : ∀ j, c j ≠ 0)
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hN : 0 < N) (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L))
    (hzero : periodicInteractionHamiltonianES h N (∑ j, c j • mpvState (A j) N) = 0) :
    ∀ j (X : Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      h ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
        (groundSpaceMap (A j) L X)) = 0 := by
  have hterms := (WeightedPositiveKernel.apply_sum_eq_zero_iff
    (fun i : Fin N => periodicLocalInteractionES_isPositive hh i) _).mp hzero
  have hboundaries := weighted_boundary_eq_zero_of_periodicLocalInteractionES_eq_zero
    A c h hLN hSpan ⟨0, hN⟩ (hterms ⟨0, hN⟩)
  intro j X
  exact (smul_eq_zero.mp (hboundaries j X)).resolve_left (hc j)

/-- The finite-ring hypothesis puts each entire local MPS space in the kernel
of the arbitrary local interaction. Source: SPWC10, Theorem 5 proof,
lines 869–880. -/
theorem groundSpaceES_le_ker_of_periodicInteractionHamiltonianES_eq_zero
    (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (hc : ∀ j, c j ≠ 0)
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hN : 0 < N) (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L))
    (hzero : periodicInteractionHamiltonianES h N (∑ j, c j • mpvState (A j) N) = 0) :
    ∀ j, groundSpaceES (A j) L ≤ LinearMap.ker h := by
  have hboundaries := boundary_eq_zero_of_periodicInteractionHamiltonianES_eq_zero
    A c hc h hh hN hLN hSpan hzero
  intro j ψ hψ
  obtain ⟨X, hX⟩ := (mem_groundSpaceES_iff (A j) L ψ).mp hψ
  have heq : (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
      (groundSpaceMap (A j) L X) = ψ := by
    rw [hX, LinearEquiv.symm_apply_apply]
  change h ψ = 0
  rw [← heq]
  exact hboundaries j X

/-- If a local interaction annihilates the active MPS space, each cyclic
translate annihilates the actual periodic vector at every permitted volume.
Source: SPWC10, Theorem 5 proof, lines 877–880. -/
theorem periodicLocalInteractionES_mpvState_eq_zero_of_groundSpaceES_le_ker
    (A : MPSTensor d D) (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L)
    (hker : groundSpaceES A L ≤ LinearMap.ker h)
    {M : ℕ} (hLM : L ≤ M) (i : Fin M) :
    periodicLocalInteractionES h i (mpvState A M) = 0 := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d L hLM i
  apply U.injective
  rw [map_zero]
  simp only [periodicLocalInteractionES, dif_pos hLM, U, LinearEquiv.conj_apply,
    LinearMap.comp_apply, LinearEquiv.apply_symm_apply]
  change ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (M - L))
    (LinearMap.toContinuousLinearMap h) (U (mpvState A M)) = 0
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  have hfiber : ContinuousLinearMap.rightFiber (U (mpvState A M)) τ =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
        (groundSpaceMap A L (Kraus.evalWord A (List.ofFn τ))) := by
    apply PiLp.ext
    intro σ'
    simpa only [ContinuousLinearMap.rightFiber, PiLp.toLp_apply,
      WithLp.coe_symm_linearEquiv, U] using
      cyclicActiveBlock_mpvState_apply A hLM i σ' τ
  have hmem : ContinuousLinearMap.rightFiber (U (mpvState A M)) τ ∈ groundSpaceES A L := by
    rw [mem_groundSpaceES_iff, hfiber, LinearEquiv.apply_symm_apply]
    exact ⟨Kraus.evalWord A (List.ofFn τ), rfl⟩
  have hzero := hker hmem
  rw [ContinuousLinearMap.rightFiberwiseMap_apply_apply]
  exact congrArg (fun v : MPVSpace d L => v σ) hzero

/-- The local-kernel inclusion implies zero energy on every larger ring.
Source: SPWC10, Theorem 5 proof, lines 877–880. -/
theorem periodicInteractionHamiltonianES_mpvState_eq_zero_of_groundSpaceES_le_ker
    (A : MPSTensor d D) (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L)
    (hker : groundSpaceES A L ≤ LinearMap.ker h)
    {M : ℕ} (hLM : L ≤ M) :
    periodicInteractionHamiltonianES h M (mpvState A M) = 0 := by
  rw [periodicInteractionHamiltonianES, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ =>
    periodicLocalInteractionES_mpvState_eq_zero_of_groundSpaceES_le_ker A h hker hLM i

/-- A single finite-ring equation and complementary block injectivity imply
zero energy for the same actual tensor on every ring of permitted length.
This is the finite-to-all-volumes implication in SPWC10, Theorem 5 proof,
lines 869–880, without an assumed local-kernel inclusion. -/
theorem periodicInteractionHamiltonianES_mpvState_eq_zero_all_volumes
    (A : MPSTensor d D) (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hN : 0 < N) (hLN : L ≤ N) (hInj : Kraus.IsNBlkInjective A (N - L))
    (hzero : periodicInteractionHamiltonianES h N (mpvState A N) = 0) :
    ∀ M, L ≤ M → periodicInteractionHamiltonianES h M (mpvState A M) = 0 := by
  let blocks : Fin 1 → MPSTensor d D := fun _ => A
  have hSpan : WordTupleSpanTop blocks (N - L) :=
    wordTupleSpanTop_of_le_one blocks (by omega) (fun _ => hInj)
  have hsum : (∑ j : Fin 1, (1 : ℂ) • mpvState (blocks j) N) = mpvState A N := by
    simp only [Fin.sum_univ_one, one_smul, blocks]
  have hker := groundSpaceES_le_ker_of_periodicInteractionHamiltonianES_eq_zero
    blocks (fun _ => 1) (fun _ => one_ne_zero) h hh hN hLN hSpan (by rwa [hsum])
  intro M hLM
  exact periodicInteractionHamiltonianES_mpvState_eq_zero_of_groundSpaceES_le_ker
    A h (hker 0) hLM

end MPSTensor
