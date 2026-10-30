/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TimeReversalTraceGauge
import TNLean.MPS.MPU.TwoSiteStandardForm
import QICLean.Algebra.TraceReindex

/-!
# Extracting the time-reversal trace sign

The normalized four-spin trace extracts the sign from the local
relation of a supplied two-site standard form. The relation is an explicit
input here; its deduction from global symmetry is the separate local
characterization theorem.

Source: arXiv:1703.09188, `UUdaggertrick-2`, `eq:sigma-from-trace`,
lines 1587–1610. The intrinsic tensor expression and its path theorem are
in `TimeReversalSignIntrinsic`.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- The normalized trace in arXiv:1703.09188, equation
`eq:sigma-from-trace`, lines 1595–1603, in zero-index square coordinates. -/
noncomputable def timeReversalSign
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℂ :=
  ((d * d : ℕ) : ℂ)⁻¹ * timeReversalTrace u v

private theorem staircaseMiddle_conjTranspose
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (staircaseMiddle (A := Fin d) (E := Fin d) v)ᴴ = staircaseMiddle vᴴ := by
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  by_cases haa : a = a' <;> by_cases hee : e = e' <;>
    simp [staircaseMiddle, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      haa, hee, eq_comm]

/-- The literal three-gate time-reversal equation determines the normalized
trace sign of the actual supplied standard form. Source:
arXiv:1703.09188, `UUdaggertrick-2`, `eq:sigma-from-trace`, lines 1587–1610. -/
theorem TwoSiteStandardFormData.timeReversalSign_eq_of_local_relation
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) {σ : ℂ}
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hlocal : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
      σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
        (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) * (staircaseMiddle v)ᴴ) :
    timeReversalSign u v = σ := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt S.phys_pos⟩
  have hmid : (staircaseMiddle (A := Fin d) (E := Fin d) v)ᴴ *
      staircaseMiddle v = 1 := by
    rw [staircaseMiddle_conjTranspose, staircaseMiddle_mul, S.v_unitary.1,
      staircaseMiddle_one]
  have hfour : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) *
      staircaseMiddle v =
      σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
        (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) := by
    rw [hlocal, Matrix.mul_assoc, hmid, Matrix.mul_one]
  let e : Fin d × Fin d ≃ Fin (d * d) := finProdFinEquiv
  let p := Equiv.prodCongr e e
  let x' := Matrix.reindex e e (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
  have hx' : x' ∈ Matrix.unitaryGroup (Fin (d * d)) ℂ :=
    Matrix.reindex_mem_unitaryGroup e _ x.property
  have hk : Matrix.reindex p p
      ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
        (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) = x' ⊗ₖ x'ᴴ := by
    dsimp only [p, x']
    rw [Matrix.conjTranspose_reindex]
    exact (Matrix.kroneckerMap_reindex (fun a b : ℂ ↦ a * b) e e e e
      (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ).symm
  have hfour' : Matrix.reindex p p
        (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) * staircaseMiddle v) =
      σ • (x' ⊗ₖ x'ᴴ) := by
    simpa only [map_smul, Matrix.coe_reindexLinearEquiv, hk] using
      congrArg (Matrix.reindexLinearEquiv ℂ ℂ p p) hfour
  have htrace := Matrix.trace_swapMatrix_mul_of_eq_smul_kronecker_conjTranspose σ hx' hfour'
  rw [← Matrix.trace_reindex p.symm] at htrace
  change Matrix.trace ((Matrix.reindexRingEquiv ℂ p.symm)
      (Matrix.swapMatrix (d * d) * Matrix.reindex p p
        (staircaseMiddle v * (u ⊗ₖ u) * staircaseMiddle v))) = _ at htrace
  rw [map_mul] at htrace
  have hvalue : timeReversalTrace u v = σ * ((d * d : ℕ) : ℂ) := by
    simpa only [Matrix.coe_reindexRingEquiv, ← Matrix.reindex_symm,
      Equiv.symm_apply_apply, timeReversalTrace, p, e] using htrace
  have hd : ((d * d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)
  rw [timeReversalSign, hvalue]
  calc
    ((d * d : ℕ) : ℂ)⁻¹ * (σ * ((d * d : ℕ) : ℂ)) =
        σ * (((d * d : ℕ) : ℂ)⁻¹ * ((d * d : ℕ) : ℂ)) := by ring
    _ = σ := by rw [inv_mul_cancel₀ hd, mul_one]

end MPOTensor
