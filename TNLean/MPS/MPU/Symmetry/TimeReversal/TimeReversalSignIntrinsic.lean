/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardForm.TwoSiteStandardFormCircuit
import QICLean.Algebra.Matrix.MatrixAux
import Mathlib.Topology.Algebra.Field
import TNLean.MPS.MPU.Symmetry.TimeReversal.TimeReversalTraceGauge
import TNLean.MPS.MPU.StandardForm.TwoSiteStandardForm
import QICLean.Algebra.Matrix.MatrixReindex

/-!
# The time-reversal sign as an intrinsic periodic trace

The four-spin trace of the supplied gates equals the trace of the two-block
periodic operator against exchange of the two physical blocks.
Thus its normalized value depends only on that finite-chain operator and
is continuous in the tensor, without continuous choices of source factors.

Pointwise supplied standard forms and their local time-reversal certificates
still determine that the intrinsic value lies in `{1,-1}`. Those witnesses
need not vary continuously. Constructing the pointwise certificates from
global symmetry is the separate local-characterization theorem.

**Scope restriction (pointwise square standard forms):** The path theorem
requires these standard forms and their local certificates at each
point. It does not derive their availability from global symmetry. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

Source: arXiv:1703.09188, `eq:sigma-from-trace` and
`prop:sigma-well-defined`, lines 1595–1631. The intrinsic-trace reformulation
is derived here from the finite-ring circuit.

It also contains the following results.

* `MPOTensor.timeReversalSign`,
  `MPOTensor.TwoSiteStandardFormData.timeReversalSign_eq_of_local_relation`: extracting the
  time-reversal trace sign.
-/

section TimeReversalSign

/-!
## Extracting the time-reversal trace sign

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

end TimeReversalSign

section TimeReversalSignIntrinsic

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Exchange of the two physical blocks in the length-two periodic
operator. This is the intrinsic trace behind `eq:sigma-from-trace`,
arXiv:1703.09188, lines 1595–1610. -/
noncomputable def timeReversalPeriodicTrace (W : MPOTensor d D) : ℂ :=
  Matrix.trace (Matrix.swapMatrix d *
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)) (mpo W 2))

/-- The normalized intrinsic trace of the two-block periodic operator,
with normalization equal to the physical block dimension. Source:
arXiv:1703.09188, `eq:sigma-from-trace`, lines 1595–1603. -/
noncomputable def intrinsicTimeReversalSign (W : MPOTensor d D) : ℂ :=
  (d : ℂ)⁻¹ * timeReversalPeriodicTrace W

private noncomputable def pairExchange (d : ℕ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d))
      ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  Matrix.reindex (finProdFinEquiv.prodCongr finProdFinEquiv).symm
    (finProdFinEquiv.prodCongr finProdFinEquiv).symm (Matrix.swapMatrix (d * d))

private theorem pairExchange_apply (i j : (Fin d × Fin d) × (Fin d × Fin d)) :
    pairExchange d i j = if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0 := by
  change Matrix.swapMatrix (d * d)
      (finProdFinEquiv i.1, finProdFinEquiv i.2)
      (finProdFinEquiv j.1, finProdFinEquiv j.2) = _
  rw [Matrix.swapMatrix_apply]
  simp only [Equiv.apply_eq_iff_eq]

private theorem pairExchange_mul_apply
    (M : Matrix ((Fin d × Fin d) × (Fin d × Fin d))
      ((Fin d × Fin d) × (Fin d × Fin d)) ℂ) (i j) :
    (pairExchange d * M) i j = M (i.2, i.1) j := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_prod_type, pairExchange_apply, ite_and, ite_mul]

private theorem mul_pairExchange_apply
    (M : Matrix ((Fin d × Fin d) × (Fin d × Fin d))
      ((Fin d × Fin d) × (Fin d × Fin d)) ℂ) (i j) :
    (M * pairExchange d) i j = M i (j.2, j.1) := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_prod_type, pairExchange_apply, ite_and, mul_ite]

private theorem pairExchange_sq : pairExchange d * pairExchange d = 1 := by
  change (Matrix.reindexRingEquiv ℂ
      (finProdFinEquiv.prodCongr finProdFinEquiv).symm) (Matrix.swapMatrix (d * d)) *
    (Matrix.reindexRingEquiv ℂ
      (finProdFinEquiv.prodCongr finProdFinEquiv).symm) (Matrix.swapMatrix (d * d)) = 1
  rw [← map_mul, Matrix.swapMatrix_mul_self, map_one]

private theorem twoSiteUnshiftedLayer_two
    (u : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.reindex (finTwoArrowEquiv (Fin d × Fin d))
        (finTwoArrowEquiv (Fin d × Fin d)) (twoSiteUnshiftedLayer (N := 2) u) = u ⊗ₖ u := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.reindex_apply, finTwoArrowEquiv, twoSiteUnshiftedLayer,
    Fin.prod_univ_two, Matrix.kroneckerMap_apply]

private theorem twoSiteShiftedLayer_two
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.reindex (finTwoArrowEquiv (Fin d × Fin d))
        (finTwoArrowEquiv (Fin d × Fin d)) (twoSiteShiftedLayer (N := 2) v) =
      pairExchange d * staircaseMiddle (A := Fin d) (E := Fin d) v *
        pairExchange d * staircaseMiddle v := by
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  calc
    _ = v (b, c) (b', c') * v (e, a) (e', a') := by
      simp [Matrix.reindex_apply, finTwoArrowEquiv, twoSiteShiftedLayer, Fin.prod_univ_two]
    _ = _ := by
      rw [Matrix.mul_apply]
      simp_rw [mul_pairExchange_apply, pairExchange_mul_apply]
      simp [Fintype.sum_prod_type, staircaseMiddle, Matrix.kroneckerMap_apply,
        Matrix.one_apply, mul_ite, ite_mul, mul_comm]

/-- The gate trace is the trace of exchange against the periodic
operator on two physical blocks. No unitarity or symmetry is needed for
the coordinate/circuit identity. Source context: arXiv:1703.09188,
`eq:sigma-from-trace`, lines 1595–1610, and `StandardForm`, lines 603–617. -/
theorem TwoSiteStandardFormData.timeReversalTrace_eq_periodicTrace
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) :
    timeReversalTrace u v = timeReversalPeriodicTrace W := by
  classical
  let e : Fin d × Fin d ≃ Fin (d * d) := finProdFinEquiv
  let p := Equiv.prodCongr e e
  let f := finTwoArrowEquiv (Fin d × Fin d)
  let q := (finTwoArrowEquiv (Fin (d * d))).trans p.symm
  have hq : (twoSitePairConfigEquiv d 2).symm.trans f = q := by
    apply Equiv.ext
    intro z
    rfl
  have h := congrArg (Matrix.reindexRingEquiv ℂ f)
    (TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := 2) W u v S)
  simp only [map_mul, Matrix.coe_reindexRingEquiv] at h
  rw [twoSiteShiftedLayer_two, twoSiteUnshiftedLayer_two] at h
  change Matrix.reindex ((twoSitePairConfigEquiv d 2).symm.trans f)
      ((twoSitePairConfigEquiv d 2).symm.trans f) (mpo W 2) = _ at h
  rw [hq] at h
  have htrace : timeReversalPeriodicTrace W =
      Matrix.trace (pairExchange d * Matrix.reindex q q (mpo W 2)) := by
    rw [timeReversalPeriodicTrace, ← Matrix.trace_reindex p.symm]
    change Matrix.trace ((Matrix.reindexRingEquiv ℂ p.symm)
      (Matrix.swapMatrix (d * d) *
        Matrix.reindex (finTwoArrowEquiv (Fin (d * d)))
          (finTwoArrowEquiv (Fin (d * d))) (mpo W 2))) = _
    rw [map_mul]
    rfl
  rw [htrace, h]
  change Matrix.trace (pairExchange d *
      (staircaseMiddle v * (u ⊗ₖ u) * staircaseMiddle v)) =
    Matrix.trace (pairExchange d * (pairExchange d * staircaseMiddle v *
      pairExchange d * staircaseMiddle v * (u ⊗ₖ u)))
  calc
    _ = Matrix.trace (staircaseMiddle v * (pairExchange d * staircaseMiddle v * (u ⊗ₖ u))) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      simp only [← Matrix.mul_assoc, pairExchange_sq, Matrix.one_mul]

/-- The normalized gate expression equals an intrinsic value of the tensor's
length-two operator. Source: arXiv:1703.09188,
`eq:sigma-from-trace` and `prop:sigma-well-defined`, lines 1595–1631. -/
theorem TwoSiteStandardFormData.timeReversalSign_eq_intrinsic
    {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) :
    timeReversalSign u v = intrinsicTimeReversalSign W := by
  rw [timeReversalSign, intrinsicTimeReversalSign, S.timeReversalTrace_eq_periodicTrace]

/-- Equality of the two-site periodic operators determines the
intrinsic trace, including between different ambient bond dimensions.
No standard-form choice or canonical presentation is required.
Source: arXiv:1703.09188, `prop:sigma-well-defined`, lines 1613--1627. -/
theorem intrinsicTimeReversalSign_eq_of_mpo_two_eq
    {D' : ℕ} {W : MPOTensor d D} {W' : MPOTensor d D'}
    (hEq : mpo W 2 = mpo W' 2) :
    intrinsicTimeReversalSign W = intrinsicTimeReversalSign W' := by
  rw [intrinsicTimeReversalSign, intrinsicTimeReversalSign,
    timeReversalPeriodicTrace, timeReversalPeriodicTrace, hEq]

/-- Equality of the two-block periodic operators gives representative
independence of the trace sign, even at different ambient bond dimensions.
No canonical presentation, source-cut choices or comparison gauges are
needed. This is the intrinsic form of arXiv:1703.09188,
`prop:sigma-well-defined`, lines 1613–1627. -/
theorem TwoSiteStandardFormData.timeReversalSign_eq_of_mpo_two_eq
    {D' : ℕ} {W : MPOTensor (d * d) D} {W' : MPOTensor (d * d) D'}
    {u v u' v' : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (S' : TwoSiteStandardFormData W' u' v')
    (hEq : mpo W 2 = mpo W' 2) : timeReversalSign u v = timeReversalSign u' v' := by
  rw [S.timeReversalSign_eq_intrinsic, S'.timeReversalSign_eq_intrinsic]
  exact intrinsicTimeReversalSign_eq_of_mpo_two_eq hEq

/-- The intrinsic sign expression is continuous in the tensor,
independently of all source-factor choices. Source context:
arXiv:1703.09188, `prop:sigma-well-defined`, lines 1628–1630. -/
theorem continuous_intrinsicTimeReversalSign :
    Continuous (intrinsicTimeReversalSign : MPOTensor d D → ℂ) := by
  have hmpo : Continuous (fun W : MPOTensor d D ↦ mpo W 2) := by
    apply continuous_matrix
    intro σ τ
    exact (continuous_evalWord (List.ofFn σ) (List.ofFn τ)).matrix_trace
  exact continuous_const.mul (continuous_const.matrix_mul
    (hmpo.matrix_reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)))).matrix_trace

/-- A continuous path of tensors has constant intrinsic sign when
each point admits a supplied standard form and the literal local
time-reversal certificate. The choices are pointwise: no continuous gate,
factor or unitary supplier is assumed. Source: arXiv:1703.09188,
`prop:sigma-well-defined`, lines 1628–1630. -/
theorem intrinsicTimeReversalSign_eq_on_path
    (W : ℝ → MPOTensor (d * d) D) (hW : ContinuousOn W (Set.Icc (0 : ℝ) 1))
    (hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      ∃ _S : TwoSiteStandardFormData (W t) u v,
      ∃ σ : ℂ, ∃ x : Matrix.unitaryGroup (Fin d × Fin d) ℂ,
        (σ = 1 ∨ σ = -1) ∧
        staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
          σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) * (staircaseMiddle v)ᴴ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      intrinsicTimeReversalSign (W t) = intrinsicTimeReversalSign (W 0) := by
  have hcont := continuous_intrinsicTimeReversalSign.comp_continuousOn hW
  have hsq : Set.EqOn ((fun t ↦ intrinsicTimeReversalSign (W t)) ^ 2) 1
      (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    obtain ⟨u, v, S, σ, x, hσ, heq⟩ := hpoint t ht
    have hvalue : intrinsicTimeReversalSign (W t) = σ :=
      S.timeReversalSign_eq_intrinsic.symm.trans (S.timeReversalSign_eq_of_local_relation x heq)
    simpa only [Pi.pow_apply, Pi.one_apply, hvalue] using sq_eq_one_iff.mpr hσ
  rcases isPreconnected_Icc.eq_one_or_eq_neg_one_of_sq_eq hcont hsq with h | h
  · intro t ht
    exact (h ht).trans (h (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).symm
  · intro t ht
    exact (h ht).trans (h (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).symm

end MPOTensor

end TimeReversalSignIntrinsic
