/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.TFAE
import TNLean.MPS.MPU.SourceUCompleteNetwork
import TNLean.MPS.MPU.SourceVCompleteNetwork

/-!
# The simple-tensor equivalence theorem

This file proves Theorem `ThmFund1` of arXiv:1703.09188 (lines 563--601) under
the source's standing canonical-form-II convention: for an MPU tensor
$\mathcal U$ in canonical form II, with source-cut ranks $r$ and $\ell$ and
source gates $u=Y_2\mathbin{-}Y_1$ and $v=X_1\mathbin{-}X_2$, the following are
equivalent:

1. $\mathcal U$ is simple;
2. $r\ell=d^2$;
3. $u$ is unitary;
4. $v$ is unitary.

The proof follows the source route $1\to2\to3\to4\to1$.  The isometry
$u^\dagger u=\Id$ of Lemma `lemuisometry` holds before any of the four
conditions is assumed.  Simplicity gives $v^\dagger v=\Id$ and hence
$r\ell\le d^2$, which with $d^2\le r\ell$ gives $r\ell=d^2$; then the isometry
$u$ is square and therefore unitary; the two-site factorization
$\operatorname{reindex}(U^{(2)})=v\,\operatorname{swap}_{r,\ell}(u)$ of
equations `SVDforms2`--`uuvv` makes $v$ a product of unitaries; and
$v^\dagger v=\Id$ gives `simple2`, hence simplicity.

The fixed pair is the one the convention records: $\rho>0$ is the diagonal
right fixed point of canonical form II (arXiv:1703.09188, line 495), and the
normalized double-layer diagonal satisfies $E^J=|\rho)(\Phi|$ with
$(\Phi|=\operatorname{vec}(\Id_D)^{\mathsf T}$ (equation `Erightleft`,
lines 274--280).  The source cuts, ranks, and both gates are computed from the
same tensor $\mathcal U$ with the same weight $\rho$.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Theorem `ThmFund1` under the standing canonical-form-II convention: for an
MPU tensor $\mathcal U$ in canonical form II, with the source-cut ranks $r$,
$\ell$ and the source gates $u$, $v$ computed from $\mathcal U$ using the
recorded weight $\rho$, the following are equivalent:

1. $\mathcal U$ is simple;
2. $r\ell=d^2$;
3. $u$ is unitary;
4. $v$ is unitary.

The proof is the source's cycle $1\to2\to3\to4\to1$:
`IsMPUCanonicalFormII.sourceU_isIsometry` and the same-weight
`IsMPUCanonicalFormII.sourceV_isIsometry` give $1\to2$; the standing isometry
$u$ with $\ell r=d^2$ is unitary ($2\to3$);
`mpo_two_reindex_eq_sourceV_mul_sourceU_swap` writes the unitary $U^{(2)}$ as
$v$ times the reindexed $u$, so $v$ is unitary ($3\to4$); and
`IsMPU.isMPUSimple_of_sourceV_isIsometry` gives $4\to1$.

Source: arXiv:1703.09188, Theorem `ThmFund1` and its proof (lines 563--601),
with the diagonal fixed point of line 495. -/
theorem IsMPUCanonicalFormII.isMPUSimple_tfae [NeZero d] {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) :
    List.TFAE [IsMPUSimple U,
      r[U] * ℓ[U] = d * d,
      (sourceU U hU.ρ hU.ρ_posDef).IsUnitaryBetween,
      (sourceV U hU.ρ hU.ρ_posDef).IsUnitaryBetween] := by
  have hu : (sourceU U hU.ρ hU.ρ_posDef).IsIsometry := hU.sourceU_isIsometry
  have hrankLower : d * d ≤ r[U] * ℓ[U] := by
    have h := Matrix.IsIsometry.card_le _ hu
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm ℓ[U]] using h
  tfae_have 1 → 2 := fun hS ↦ by
    have hv : (sourceV U hU.ρ hU.ρ_posDef).IsIsometry := hU.sourceV_isIsometry hS
    have hrankUpper := Matrix.IsIsometry.card_le _ hv
    apply le_antisymm
    · simpa only [Fintype.card_prod, Fintype.card_fin] using hrankUpper
    · exact hrankLower
  tfae_have 2 → 3 := fun h ↦
    hu.isUnitaryBetween_of_card_eq _ (by
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [mul_comm]
      exact h)
  tfae_have 3 → 4 := fun h ↦ by
    have hmpo := (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr
      (hU.isMPU.mpo_mem_unitaryGroup (N := 2) one_lt_two)
    have hre := hmpo.reindex _ (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
    rw [mpo_two_reindex_eq_sourceV_mul_sourceU_swap U hU.ρ hU.ρ_posDef] at hre
    exact Matrix.IsUnitaryBetween.of_mul_right _ _ (h.reindex _ _ _) hre
  tfae_have 4 → 1 := fun h ↦
    hU.isMPU.isMPUSimple_of_sourceV_isIsometry hU.ρ hU.ρ_posDef h.1
  tfae_finish

end MPOTensor
