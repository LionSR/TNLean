/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Interaction.ArbitraryInteractionBlockDegeneracy
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BoundaryMatrix.PGVWC07CutRank

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

/-- One periodic Hamiltonian equation for the translates on the ring of a positive semidefinite
local matrix implies annihilation of every boundary vector of every block, once its
complementary word tuples span. Source: SPWC10, Theorem 5 proof, lines 869–880; PGVWC07,
Theorem 11 proof, lines 1418–1422. -/
theorem boundary_eq_zero_of_toEuclideanLin_hamiltonian_translationInvariant_eq_zero
    (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (hc : ∀ j, c j ≠ 0)
    (h : Matrix (Cfg d L) (Cfg d L) ℂ) (hh : h.PosSemidef)
    (hN : 0 < N) (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L))
    (hzero : haveI : NeZero N := ⟨by omega⟩;
      Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian
      (∑ j, c j • mpvState (A j) N) = 0) :
    ∀ j (X : Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      Matrix.toEuclideanLin h ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
        (groundSpaceMap (A j) L X)) = 0 := by
  have : NeZero N := ⟨by omega⟩
  have hpos (i : Fin N) :
      ((ManyBody.Interaction.translationInvariant N h).term i).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (ManyBody.Interaction.translationInvariant_term_nonneg
      (Matrix.nonneg_iff_posSemidef.mpr hh) i)
  rw [Matrix.toLpLin_apply, WithLp.toLp_eq_zero] at hzero
  have hterm : Matrix.toEuclideanLin
      ((ManyBody.Interaction.translationInvariant N h).term ⟨0, hN⟩)
        (∑ j, c j • mpvState (A j) N) = 0 := by
    rw [Matrix.toLpLin_apply, WithLp.toLp_eq_zero]
    exact (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff hpos).mp hzero ⟨0, hN⟩
  have hboundaries :=
    weighted_boundary_eq_zero_of_toEuclideanLin_translationInvariant_term_eq_zero
      A c h hLN hSpan ⟨0, hN⟩ hterm
  intro j X
  exact (smul_eq_zero.mp (hboundaries j X)).resolve_left (hc j)

/-- The finite-ring hypothesis puts each entire local MPS space in the kernel of the arbitrary
positive semidefinite local matrix. Source: SPWC10, Theorem 5 proof, lines 869–880. -/
theorem map_groundSpace_le_ker_of_toEuclideanLin_hamiltonian_translationInvariant_eq_zero
    (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (hc : ∀ j, c j ≠ 0)
    (h : Matrix (Cfg d L) (Cfg d L) ℂ) (hh : h.PosSemidef)
    (hN : 0 < N) (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L))
    (hzero : haveI : NeZero N := ⟨by omega⟩;
      Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian
      (∑ j, c j • mpvState (A j) N) = 0) :
    ∀ j, ((groundSpace (A j) L).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap) ≤ LinearMap.ker (Matrix.toEuclideanLin h) := by
  have : NeZero N := ⟨by omega⟩
  have hboundaries :=
    boundary_eq_zero_of_toEuclideanLin_hamiltonian_translationInvariant_eq_zero
      A c hc h hh hN hLN hSpan hzero
  intro j ψ hψ
  obtain ⟨X, hX⟩ := (mem_map_groundSpace_iff (A j) L ψ).mp hψ
  have heq : (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
      (groundSpaceMap (A j) L X) = ψ := by
    rw [hX, LinearEquiv.symm_apply_apply]
  rw [LinearMap.mem_ker, ← heq]
  exact hboundaries j X

/-- If a local matrix annihilates the active MPS space, each of its translates on the ring
annihilates the actual periodic vector at every permitted volume. Source: SPWC10, Theorem 5
proof, lines 877–880. -/
theorem toEuclideanLin_translationInvariant_term_mpvState_eq_zero_of_map_groundSpace_le_ker
    (A : MPSTensor d D) (h : Matrix (Cfg d L) (Cfg d L) ℂ)
    (hker : ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) ≤ LinearMap.ker
        (Matrix.toEuclideanLin h))
    {M : ℕ} (hLM : L ≤ M) (i : Fin M) :
    haveI : NeZero M := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant M h).term i)
      (mpvState A M) = 0 := by
  have : NeZero M := NeZero.of_pos i.pos
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d L hLM i
  apply U.injective
  rw [map_zero, cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply]
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
  have hmem : ContinuousLinearMap.rightFiber (U (mpvState A M)) τ ∈ ((groundSpace A L).map
      (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
    rw [mem_map_groundSpace_iff, hfiber, LinearEquiv.apply_symm_apply]
    exact ⟨Kraus.evalWord A (List.ofFn τ), rfl⟩
  have hzero := hker hmem
  rw [ContinuousLinearMap.rightFiberwiseMap_apply_apply]
  exact congrArg (fun v : MPVSpace (Fin d) L => v σ) hzero

/-- The local-kernel inclusion implies zero energy of the Hamiltonian of the translates on every
larger ring. Source: SPWC10, Theorem 5 proof, lines 877–880. -/
theorem toEuclideanLin_hamiltonian_translationInvariant_mpvState_eq_zero_of_map_groundSpace_le_ker
    (A : MPSTensor d D) (h : Matrix (Cfg d L) (Cfg d L) ℂ)
    (hker : ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) ≤ LinearMap.ker
        (Matrix.toEuclideanLin h))
    {M : ℕ} [NeZero M] (hLM : L ≤ M) :
    Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M h).hamiltonian
      (mpvState A M) = 0 := by
  rw [ManyBody.Interaction.hamiltonian, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ =>
    toEuclideanLin_translationInvariant_term_mpvState_eq_zero_of_map_groundSpace_le_ker
      A h hker hLM i

/-- A single finite-ring equation for the translates of a positive semidefinite local matrix and
complementary block injectivity imply zero energy for the same actual tensor on every ring of
permitted length. This is the finite-to-all-volumes implication in SPWC10, Theorem 5 proof,
lines 869–880, without an assumed local-kernel inclusion. -/
theorem toEuclideanLin_hamiltonian_translationInvariant_mpvState_eq_zero_all_volumes
    (A : MPSTensor d D) (h : Matrix (Cfg d L) (Cfg d L) ℂ) (hh : h.PosSemidef)
    (hN : 0 < N) (hLN : L ≤ N) (hInj : Kraus.IsNBlkInjective A (N - L))
    (hzero : haveI : NeZero N := ⟨by omega⟩;
      Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian
      (mpvState A N) = 0) :
    ∀ M [NeZero M], L ≤ M → Matrix.toEuclideanLin
      (ManyBody.Interaction.translationInvariant M h).hamiltonian (mpvState A M) = 0 := by
  have : NeZero N := ⟨by omega⟩
  let blocks : Fin 1 → MPSTensor d D := fun _ => A
  have hSpan : WordTupleSpanTop blocks (N - L) :=
    wordTupleSpanTop_of_le_one blocks (by omega) (fun _ => hInj)
  have hsum : (∑ j : Fin 1, (1 : ℂ) • mpvState (blocks j) N) = mpvState A N := by
    simp only [Fin.sum_univ_one, one_smul, blocks]
  have hker := map_groundSpace_le_ker_of_toEuclideanLin_hamiltonian_translationInvariant_eq_zero
    blocks (fun _ => 1) (fun _ => one_ne_zero) h hh hN hLN hSpan (by rwa [hsum])
  intro M _ hLM
  exact toEuclideanLin_hamiltonian_translationInvariant_mpvState_eq_zero_of_map_groundSpace_le_ker
    A h (hker 0) hLM

end MPSTensor
