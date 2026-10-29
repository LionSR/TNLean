/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TimeReversalTraceGauge
import TNLean.MPS.MPU.TwoSiteStandardForm
import QICLean.Algebra.TraceReindex
import QICLean.Algebra.MatrixAux
import Mathlib.Topology.Algebra.Field

/-!
# The time-reversal trace sign on supplied standard-form paths

The normalized four-site trace extracts the sign from the literal local
time-reversal equation. It is a continuous polynomial in the two supplied
gates, divided by their fixed nonzero dimension. A continuous path satisfying
the local equation therefore has one constant sign.

**Scope restriction (supplied continuous gates):** The path theorem concerns
the actual supplied two-site standard forms and their continuous gates in
the zero-index coordinates. It assumes the displayed local time-reversal
equation at each path point. It does not construct continuous source factors
or derive that equation from global symmetry of an arbitrary MPU path.
See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

Source: arXiv:1703.09188, `eq:sigma-from-trace` and
`prop:sigma-well-defined`, lines 1595–1631.
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
  simp [staircaseMiddle, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_comm, mul_left_comm, mul_assoc]

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
  letI : NeZero d := ⟨Nat.ne_of_gt S.phys_pos⟩
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
  have hfour' : Matrix.reindex p p
        (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) * staircaseMiddle v) =
      σ • (x' ⊗ₖ x'ᴴ) := by
    simpa only [map_smul, x', Matrix.conjTranspose_reindex, Matrix.kroneckerMap_reindex] using
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

/-- The trace expression is continuous in the actual supplied gates.
Source: arXiv:1703.09188, proof of `prop:sigma-well-defined`, lines 1628–1630. -/
theorem continuous_timeReversalSign :
    Continuous (fun p : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ×
        (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ↦ timeReversalSign p.1 p.2) := by
  have hmid : Continuous (fun v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ ↦
      staircaseMiddle (A := Fin d) (E := Fin d) v) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ ↦
      (1 : Matrix (Fin d) (Fin d) ℂ) i.1.1 j.1.1 *
        v (i.1.2, i.2.1) (j.1.2, j.2.1) *
          (1 : Matrix (Fin d) (Fin d) ℂ) i.2.2 j.2.2)
    exact (continuous_const.mul (continuous_id.matrix_elem _ _)).mul continuous_const
  exact continuous_const.mul
    (continuous_const.matrix_mul
      (((hmid.comp continuous_snd).matrix_mul
        (continuous_fst.matrix_kronecker continuous_fst)).matrix_mul
        (hmid.comp continuous_snd))).matrix_trace

/-- A continuous path of actual supplied standard-form gates with the literal
local time-reversal relation has one constant trace sign. This is the
supplied-path reading of arXiv:1703.09188, `prop:sigma-well-defined`,
lines 1628–1630. Continuous gate suppliers and the local relation are stated
explicitly; they are not inferred from a bare path of globally symmetric MPUs. -/
theorem timeReversalSign_eq_on_supplied_path
    (W : ℝ → MPOTensor (d * d) D)
    (u v : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (S : ∀ t ∈ Set.Icc (0 : ℝ) 1, TwoSiteStandardFormData (W t) (u t) (v t))
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 1))
    (hv : ContinuousOn v (Set.Icc (0 : ℝ) 1))
    (hlocal : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ σ : ℂ,
      ∃ x : Matrix.unitaryGroup (Fin d × Fin d) ℂ,
        (σ = 1 ∨ σ = -1) ∧
        staircaseMiddle (A := Fin d) (E := Fin d) (v t) * (u t ⊗ₖ u t) =
          σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) *
              (staircaseMiddle (v t))ᴴ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, timeReversalSign (u t) (v t) = timeReversalSign (u 0) (v 0) := by
  have hcont := continuous_timeReversalSign.comp_continuousOn (hu.prodMk hv)
  have hsq : Set.EqOn ((fun t ↦ timeReversalSign (u t) (v t)) ^ 2) 1
      (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    obtain ⟨σ, x, hσ, heq⟩ := hlocal t ht
    have hvalue := (S t ht).timeReversalSign_eq_of_local_relation x heq
    simpa only [Pi.pow_apply, Pi.one_apply, hvalue] using sq_eq_one_iff.mpr hσ
  rcases isPreconnected_Icc.eq_one_or_eq_neg_one_of_sq_eq hcont hsq with h | h
  · intro t ht
    exact (h ht).trans (h (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).symm
  · intro t ht
    exact (h ht).trans (h (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).symm

end MPOTensor
