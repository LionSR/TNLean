/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Kraus.Transfer
import QICLean.Channel.KoashiImoto.MeanErgodicProjection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Equality of transfer and adjoint fixed-space dimensions

The transfer map and its trace adjoint have fixed spaces of equal dimension.
In matrix-unit coordinates the trace adjoint is a transpose, so its rank and
nullity agree with those of the original map. No positivity, unitality or
spectral simplicity is required for this finite-dimensional identity.

This identity is used in the stationary-support argument of arXiv:1010.3732,
Appendix C, lines 2653–2717. It does not derive a transfer spectral bound from
a physical Hamiltonian gap.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

private theorem finrank_ker_traceAdjointMap_eq
    {n : Type*} [Fintype n]
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Module.finrank ℂ (Matrix.traceAdjointMap E).ker = Module.finrank ℂ E.ker := by
  classical
  let b := Matrix.stdBasis ℂ n n
  let bT := b.reindex (Equiv.prodComm n n)
  have hRange : Module.finrank ℂ (Matrix.traceAdjointMap E).range =
      Module.finrank ℂ E.range := by
    calc
      _ = (LinearMap.toMatrix bT bT (Matrix.traceAdjointMap E)).rank := by
        rw [Matrix.rank_eq_finrank_range_toLin _ bT bT, Matrix.toLin_toMatrix]
      _ = (LinearMap.toMatrix b b E).rank := by
        rw [Matrix.traceAdjointMap_toMatrix_transpose E, Matrix.rank_transpose]
      _ = Module.finrank ℂ E.range := by
        rw [Matrix.rank_eq_finrank_range_toLin _ b b, Matrix.toLin_toMatrix]
  have hAdj := LinearMap.finrank_range_add_finrank_ker (Matrix.traceAdjointMap E)
  have hOrig := LinearMap.finrank_range_add_finrank_ker E
  rw [hRange] at hAdj
  exact Nat.add_left_cancel (hAdj.trans hOrig.symm)

namespace MPSTensor

/-- The adjoint stationary space and the transfer fixed space have equal
complex dimension. This finite-dimensional trace-duality identity requires
no positivity, normalization, irreducibility or nonzero dimension assumption.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem finrank_adjointFixedSpace_eq_transferFixedSpace
    {d D : ℕ} (B : MPSTensor d D) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM B)) =
      Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap B) 1) := by
  have hId : Matrix.traceAdjointMap
      (LinearMap.id : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) =
        LinearMap.id := by
    ext X i j
    simp only [Matrix.traceAdjointMap_apply_apply, LinearMap.id_apply,
      Matrix.trace_mul_single, MulOpposite.op_one, one_smul]
  have hEq := finrank_ker_traceAdjointMap_eq (LinearMap.id - Kraus.mapLM B)
  rw [Matrix.traceAdjointMap_sub, hId, Kraus.traceAdjointMap_mapLM] at hEq
  rw [Module.End.eigenspace_def, one_smul, Module.End.one_eq_id]
  change Module.finrank ℂ (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM B)) =
    Module.finrank ℂ (LinearMap.ker (Kraus.mapLM B - LinearMap.id))
  rw [← neg_sub (LinearMap.id) (Kraus.mapLM B), LinearMap.ker_neg]
  exact hEq

end MPSTensor
