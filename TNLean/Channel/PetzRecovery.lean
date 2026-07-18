/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.CfcKronecker
import TNLean.Channel.KrausCPTP
import TNLean.Channel.MarginalSupportAbsorption

/-!
# The support Petz transpose map for a partial trace

This file constructs the raw Petz transpose map associated with a positive
semidefinite reference matrix and the partial trace over a right tensor factor.
The source formula is defined on the support of the partial trace of the
reference.  Accordingly, the map here is proved completely positive and is
proved to recover its reference matrix, but no global trace-preservation claim
is made.

## Main declarations

* `Matrix.PosSemidef.supportInvSqrt`: the inverse square root on the support.
* `Matrix.partialTraceRightPetzMap`: the raw Petz transpose map for the right
  partial trace.
* `Matrix.partialTraceRightPetzMap_isKrausCP`: complete positivity.
* `Matrix.partialTraceRightPetzMap_partialTraceRight`: recovery of the
  reference matrix.

## References

* Hayden, Jozsa, Petz, and Winter, arXiv:quant-ph/0304007v2,
  Theorem 3, equation (8), and the specialization following their
  relative-entropy monotonicity equation.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse square root of a positive-semidefinite matrix on its support:
the zero eigenspace is sent to zero and every positive eigenvalue `x` is sent
to `(sqrt x)⁻¹`.

This is the singular inverse square root in the support formula of
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
equation (8). -/
noncomputable def PosSemidef.supportInvSqrt {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : Matrix n n ℂ :=
  hρ.isHermitian.cfc fun x ↦ if x ≠ 0 then (Real.sqrt x)⁻¹ else 0

/-- The support inverse square root is Hermitian. -/
theorem PosSemidef.supportInvSqrt_isHermitian {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : hρ.supportInvSqrt.IsHermitian := by
  rw [PosSemidef.supportInvSqrt, ← hρ.isHermitian.cfc_eq]
  exact Matrix.isHermitian_iff_isSelfAdjoint.mpr
    (cfc_predicate (fun x : ℝ ↦ if x ≠ 0 then (Real.sqrt x)⁻¹ else 0) ρ)

/-- Sandwiching a positive-semidefinite matrix by its support inverse square
root gives its support projection.  This is the spectral support identity
underlying the singular Petz formula in arXiv:quant-ph/0304007v2,
equation (8). -/
theorem PosSemidef.supportInvSqrt_mul_self_mul_supportInvSqrt
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    hρ.supportInvSqrt * ρ * hρ.supportInvSqrt =
      hρ.isHermitian.supportProj := by
  let f : ℝ → ℝ := fun x ↦ if x ≠ 0 then (Real.sqrt x)⁻¹ else 0
  change hρ.isHermitian.cfc f * ρ * hρ.isHermitian.cfc f =
    hρ.isHermitian.supportProj
  calc
    hρ.isHermitian.cfc f * ρ * hρ.isHermitian.cfc f =
        hρ.isHermitian.cfc f * hρ.isHermitian.cfc id *
          hρ.isHermitian.cfc f := by rw [hρ.isHermitian.cfc_id]
    _ = hρ.isHermitian.cfc (fun x ↦ f x * id x) *
          hρ.isHermitian.cfc f := by
      rw [← hρ.isHermitian.cfc_mul]
    _ = hρ.isHermitian.cfc (fun x ↦ (f x * id x) * f x) := by
      rw [← hρ.isHermitian.cfc_mul]
    _ = hρ.isHermitian.supportProj := by
      have hdiag :
          Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘
              (fun x ↦ (f x * id x) * f x) ∘ hρ.isHermitian.eigenvalues) =
            Matrix.diagonal (fun i ↦
              if hρ.isHermitian.eigenvalues i ≠ 0 then (1 : ℂ) else 0) := by
        congr 1
        funext i
        simp only [Function.comp_apply, id_eq]
        by_cases hi : hρ.isHermitian.eigenvalues i = 0
        · simp [f, hi]
        · have hpos : 0 < hρ.isHermitian.eigenvalues i :=
            lt_of_le_of_ne (hρ.eigenvalues_nonneg i) (Ne.symm hi)
          have hsqrt : Real.sqrt (hρ.isHermitian.eigenvalues i) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.2 hpos)
          have hreal :
              (Real.sqrt (hρ.isHermitian.eigenvalues i))⁻¹ *
                  hρ.isHermitian.eigenvalues i *
                (Real.sqrt (hρ.isHermitian.eigenvalues i))⁻¹ = 1 := by
            nth_rewrite 2 [← Real.mul_self_sqrt hpos.le]
            field_simp
          simpa [f, hi] using congrArg Complex.ofReal hreal
      unfold Matrix.IsHermitian.supportProj
      rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, hdiag]

section PartialTrace

variable {L R : Type*} [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R]

/-- The raw Petz transpose map for the right partial trace with reference
`σ`.  It is the support formula
`X ↦ sqrt(σ) ((tr_R σ)⁻¹/² X (tr_R σ)⁻¹/² ⊗ 1_R) sqrt(σ)` from
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3, equation (8).

The source states this formula on the support of `tr_R σ`; this definition does
not extend it to a trace-preserving map on the complementary subspace. -/
noncomputable def partialTraceRightPetzMap
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    Matrix L L ℂ →ₗ[ℂ] Matrix (L × R) (L × R) ℂ :=
  singleKrausMap (hσ.isHermitian.cfc Real.sqrt) ∘ₗ
    preparationMap (1 : Matrix R R ℂ) ∘ₗ
      singleKrausMap (PosSemidef.supportInvSqrt
        (PosSemidef.partialTraceRight hσ))

/-- The raw partial-trace Petz map has the displayed support formula from
arXiv:quant-ph/0304007v2, equation (8). -/
theorem partialTraceRightPetzMap_apply
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef)
    (X : Matrix L L ℂ) :
    partialTraceRightPetzMap σ hσ X =
      hσ.isHermitian.cfc Real.sqrt *
        leftKroneckerEmbed (n := R)
          ((PosSemidef.partialTraceRight hσ).supportInvSqrt * X *
            (PosSemidef.partialTraceRight hσ).supportInvSqrt) *
        hσ.isHermitian.cfc Real.sqrt := by
  simp [partialTraceRightPetzMap, preparationMap,
    leftKroneckerEmbed_apply,
    hσ.cfc_sqrt_isHermitian.eq,
    (PosSemidef.partialTraceRight hσ).supportInvSqrt_isHermitian.eq,
    Matrix.mul_assoc]

/-- The raw partial-trace Petz map is completely positive in rectangular Kraus
form.  This is the complete-positivity part of the support formula in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3.  No global trace-preservation claim is made. -/
theorem partialTraceRightPetzMap_isKrausCP
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    IsKrausCP (partialTraceRightPetzMap σ hσ) := by
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact singleKrausMap_isKrausCP _
    · exact preparationMap_isKrausCP _ Matrix.PosSemidef.one
  · exact singleKrausMap_isKrausCP _

/-- The raw partial-trace Petz map recovers its positive-semidefinite reference
matrix:
`R_σ (tr_R σ) = σ`.

This is the automatic reference-recovery identity following
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
equation (8).  It uses only the source's support formula and
does not assert trace preservation away from that support. -/
theorem partialTraceRightPetzMap_partialTraceRight
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    partialTraceRightPetzMap σ hσ (partialTraceRight σ) = σ := by
  rw [partialTraceRightPetzMap_apply]
  have hInv := PosSemidef.supportInvSqrt_mul_self_mul_supportInvSqrt
    (PosSemidef.partialTraceRight hσ)
  rw [hInv]
  set S := hσ.isHermitian.cfc Real.sqrt with hS
  set P := leftKroneckerEmbed (n := R)
    (PosSemidef.partialTraceRight hσ).isHermitian.supportProj with hP
  set Q : Matrix (L × R) (L × R) ℂ := 1 - P with hQ
  have hS_sq : S * S = σ := by
    rw [hS]
    exact hσ.cfc_sqrt_mul_self
  have hS_herm : S.IsHermitian := by
    rw [hS]
    exact hσ.cfc_sqrt_isHermitian
  have hPσ : P * σ = σ := by
    rw [hP]
    exact hσ.leftKroneckerEmbed_supportProj_mul_self
  have hPherm : P.IsHermitian := by
    rw [hP]
    change (leftKroneckerEmbed (n := R)
      (PosSemidef.partialTraceRight hσ).isHermitian.supportProj)ᴴ = _
    rw [← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose,
      (PosSemidef.partialTraceRight hσ).isHermitian.supportProj_isHermitian.eq]
  have hPidem : P * P = P := by
    rw [hP, ← map_mul,
      (PosSemidef.partialTraceRight hσ).isHermitian.supportProj_idem]
  have hQherm : Q.IsHermitian := by
    rw [hQ]
    exact Matrix.isHermitian_one.sub hPherm
  have hQidem : Q * Q = Q := by
    rw [hQ]
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPidem]; abel
  have hQσ : Q * σ = 0 := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul, hPσ, sub_self]
  have hQSQ_pos : (S * Q * S).PosSemidef := by
    have hQpos : Q.PosSemidef := by
      rw [hQherm.posSemidef_iff_eigenvalues_nonneg]
      intro i
      rcases hQherm.eigenvalues_idem_eq_zero_or_one hQidem i with hi | hi
      · simp [hi]
      · simp [hi]
    simpa [hS_herm.eq] using hQpos.mul_mul_conjTranspose_same (Sᴴ)
  have hQSQ_trace : (S * Q * S).trace = 0 := by
    calc
      (S * Q * S).trace = (S * (Q * S)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((Q * S) * S).trace := Matrix.trace_mul_comm _ _
      _ = (Q * (S * S)).trace := by rw [Matrix.mul_assoc]
      _ = (Q * σ).trace := by rw [hS_sq]
      _ = 0 := by rw [hQσ, Matrix.trace_zero]
  have hQSQ : S * Q * S = 0 := hQSQ_pos.trace_eq_zero_iff.mp hQSQ_trace
  calc
    S * P * S = S * (1 - Q) * S := by rw [hQ]; congr 2; abel
    _ = S * S - S * Q * S := by noncomm_ring
    _ = σ := by rw [hQSQ, sub_zero, hS_sq]

end PartialTrace

end Matrix
