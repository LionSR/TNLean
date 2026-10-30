/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.WeightedPositiveKernel
import TNLean.MPS.ParentHamiltonian.CyclicBlockState
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction

/-!
# Block ground states for an arbitrary local interaction

The interaction is an arbitrary linear operator, rather than the canonical
parent projector. A simultaneous span on the complementary sites separates
the actual weighted block vectors after the interaction acts. Positivity
then passes from a periodic Hamiltonian equation to its individual local
terms, giving the blockwise Hamiltonian equations.

This is the linear argument of PGVWC07, arXiv:quant-ph/0608197, Theorem 11
(`2blocks.1`), lines 1407–1422 of
`Papers/quant-ph_0608197/MPSarchive.tex`. The simultaneous span is explicit
in the general statement; the source-length specialization is separate.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d r N L : ℕ} {dim : Fin r → ℕ}

/-- A local interaction killing a weighted sum of periodic blocks kills each
weighted summand, provided complementary words span the block matrix algebra.
No parent-interaction or positivity assumption is used at this local step.
Source: PGVWC07, Theorem 11, `2blocks.1`, proof lines 1418–1422. -/
theorem periodicLocalInteractionES_smul_mpvState_eq_zero_of_wordTupleSpanTop
    (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L)
    (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L)) (i : Fin N)
    (hzero : periodicLocalInteractionES h i (∑ j, c j • mpvState (A j) N) = 0) :
    ∀ j, periodicLocalInteractionES h i (c j • mpvState (A j) N) = 0 := by
  classical
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d L hLN i
  let e := (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
  let T : ((j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) →ₗ[ℂ]
      MPVSpace d L :=
    LinearMap.lsum ℂ (fun j => Matrix (Fin (dim j)) (Fin (dim j)) ℂ) ℂ
      (fun j => c j • h.comp (e.toLinearMap.comp (groundSpaceMap (A j) L)))
  have hT : T = 0 := by
    apply LinearMap.ext_on_range (v := wordTuple A (N - L)) (hv := hSpan)
    intro τ
    have hfiber : ContinuousLinearMap.rightFiber
        (U (∑ j, c j • mpvState (A j) N)) τ =
        ∑ j, c j • e (groundSpaceMap (A j) L (Kraus.evalWord (A j) (List.ofFn τ))) := by
      apply PiLp.ext
      intro σ
      simp only [ContinuousLinearMap.rightFiber, PiLp.toLp_apply,
        map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        cyclicActiveBlock_mpvState_apply, U]
      rfl
    have hUzero := congrArg U hzero
    have hRight : ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - L))
        (LinearMap.toContinuousLinearMap h)
        (U (∑ j, c j • mpvState (A j) N)) = 0 := by
      simpa only [U, cyclicActiveBlock_periodicLocalInteractionES_apply, map_zero]
        using hUzero
    have hτ := congrArg (fun v => ContinuousLinearMap.rightFiber v τ) hRight
    have hzeroFiber : ContinuousLinearMap.rightFiber
        (0 : EuclideanSpace ℂ (Cfg d L × Cfg d (N - L))) τ = 0 := by
      apply PiLp.ext
      intro σ
      rfl
    rw [ContinuousLinearMap.rightFiber_rightFiberwiseMap, hfiber, hzeroFiber] at hτ
    simpa only [T, LinearMap.lsum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      wordTuple, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.zero_apply,
      map_sum, map_smul, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
      using hτ
  have hEach (j : Fin r) (X : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
      c j • h (e (groundSpaceMap (A j) L X)) = 0 := by
    have hsingle := LinearMap.lsum_piSingle ℂ
      (fun j => Matrix (Fin (dim j)) (Fin (dim j)) ℂ) ℂ
      (fun j => c j • h.comp (e.toLinearMap.comp (groundSpaceMap (A j) L))) j X
    have heq := LinearMap.congr_fun hT (Pi.single j X)
    simpa only [T, hsingle, LinearMap.zero_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using heq
  intro j
  apply U.injective
  rw [map_zero]
  rw [show U (periodicLocalInteractionES h i (c j • mpvState (A j) N)) =
    ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - L))
      (LinearMap.toContinuousLinearMap h) (U (c j • mpvState (A j) N)) from
        cyclicActiveBlock_periodicLocalInteractionES_apply h hLN i _]
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  have hfiber : ContinuousLinearMap.rightFiber (U (c j • mpvState (A j) N)) τ =
      c j • e (groundSpaceMap (A j) L (Kraus.evalWord (A j) (List.ofFn τ))) := by
    apply PiLp.ext
    intro σ'
    simp only [ContinuousLinearMap.rightFiber, PiLp.toLp_apply,
      map_smul, PiLp.smul_apply, U, cyclicActiveBlock_mpvState_apply]
    rfl
  rw [ContinuousLinearMap.rightFiberwiseMap_apply_apply, hfiber]
  simpa only [map_smul, PiLp.smul_apply, PiLp.zero_apply,
    LinearMap.coe_toContinuousLinearMap'] using
    congrArg (fun v => v σ) (hEach j (Kraus.evalWord (A j) (List.ofFn τ)))

/-- Every actual block vector is a zero-energy state of an arbitrary positive
periodic interaction whenever their sum with nonzero coefficients has zero
energy and the complementary word tuples span. Positivity supplies the individual local
annihilation equations rather than adding them as hypotheses.
Source: PGVWC07, Theorem 11, `2blocks.1`, lines 1407–1422. -/
theorem periodicInteractionHamiltonianES_mpvState_eq_zero_of_wordTupleSpanTop
    (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (hc : ∀ j, c j ≠ 0)
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L))
    (hzero : periodicInteractionHamiltonianES h N (∑ j, c j • mpvState (A j) N) = 0) :
    ∀ j, periodicInteractionHamiltonianES h N (mpvState (A j) N) = 0 := by
  have hterms : ∀ i : Fin N,
      periodicLocalInteractionES h i (∑ j, c j • mpvState (A j) N) = 0 :=
    (WeightedPositiveKernel.apply_sum_eq_zero_iff
      (fun i => periodicLocalInteractionES_isPositive hh i) _).mp hzero
  intro j
  rw [periodicInteractionHamiltonianES, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hblock := periodicLocalInteractionES_smul_mpvState_eq_zero_of_wordTupleSpanTop
    A c h hLN hSpan i (hterms i) j
  rw [map_smul] at hblock
  exact (smul_eq_zero.mp hblock).resolve_left (hc j)

/-- A simultaneous word span makes the actual periodic block vectors linearly
independent when every virtual block is nonempty. This gives the degeneracy
conclusion in PGVWC07, Theorem 11, `2blocks.1`, lines 1407–1416. -/
theorem linearIndependent_mpvState_of_wordTupleSpanTop
    [∀ j, NeZero (dim j)] (A : (j : Fin r) → MPSTensor d (dim j))
    (hSpan : WordTupleSpanTop A N) :
    LinearIndependent ℂ (fun j => mpvState (A j) N) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hMatrices := block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan
    (fun k => c k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) (by
      intro w
      have hw := congrArg (fun v : MPVSpace d N => v w) hc
      simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        mpvState_apply, mpv_eq, coeff_eq, Matrix.smul_mul, Matrix.one_mul,
        Matrix.trace_smul, smul_eq_mul, PiLp.zero_apply] using hw)
  have hj := congrFun (congrFun (hMatrices j) (0 : Fin (dim j))) (0 : Fin (dim j))
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Matrix.zero_apply] using hj

end MPSTensor
