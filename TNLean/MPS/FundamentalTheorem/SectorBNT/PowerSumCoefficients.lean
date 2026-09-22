/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.ParentHamiltonian.PrimitiveGaugeExistence

/-!
# Normalized representatives and independence for power-sum coefficients

In a matrix product operator algebra closed at the level of the trace, the
structure constants attached to a chain of length `L` need not be independent of
`L`.  Cirac, Perez-Garcia, Schuch and Verstraete ask in arXiv:1606.00608,
Section 4.5, lines 995--1010, whether renormalization fixed points with genuinely
length-dependent structure constants exist, and record that constants which do
not depend on the length are forced to be nonnegative integers.  The project
open-problem note P6
(`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex`)
builds fixed points whose constants are sums of powers of finitely many complex
weights.

The answer, that the coefficients of an expansion over pairwise inequivalent
normal tensors are the power sums of finite multisets of nonzero weights at
every positive length, is proved in
`TNLean/MPS/FundamentalTheorem/SectorBNT/UnblockedPowerSumCoefficients.lean`.
This file collects the normalization and independence steps that argument uses:
an algebraically normal tensor is brought into left-canonical normalized form by
a gauge transformation and a nonzero rescaling, that rescaling does not disturb
gauge-phase equivalence, and a finite family of pairwise inequivalent normalized
normal tensors has eventually linearly independent periodic vectors.

## Main results

* `MPSTensor.exists_leftCanonical_normalTensor_scale_of_isNormal` — an
  algebraically normal tensor is, after a gauge transformation and a nonzero
  rescaling, left-canonical with primitive irreducible transfer map, and the
  scalar records the rescaling in the periodic vectors.
* `MPSTensor.gaugePhaseEquiv_of_smul_smul_cast` — nonzero rescalings on either
  side do not affect gauge-phase equivalence.
* `MPSTensor.exists_eventually_linearIndependent_of_normalTensor_distinct` —
  past a threshold length, the periodic vectors of a finite family of normalized
  normal tensors that are pairwise not gauge-phase equivalent are linearly
  independent.
* `MPSTensor.sum_smul_mpvState_eq_zero` — a vanishing pointwise combination of
  periodic vectors is a vanishing combination of the corresponding states.

## Source anchors

* arXiv:1606.00608, `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 995--1010 —
  the open question on length-dependent structure constants and the
  length-independent case.
* arXiv:quant-ph/0608197, proof of Theorem 4, lines 765--770 — the
  left-canonical normalization taken without loss of generality.
* Project open-problem note P5,
  `Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.7 —
  the compression setting in which these coefficients arise.
* Project open-problem note P6,
  `Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex` —
  the constructions whose coefficients are power sums of channel weights.

## Tags

matrix product states, renormalization fixed point, structure constants, normal
tensors, linear independence, power sums
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- **Left-canonical normalized representative of an algebraically normal tensor.**

An algebraically normal tensor is, after a gauge and a nonzero rescaling,
left-canonical with primitive irreducible transfer map and spectral radius one.
This is the normalization taken without loss of generality at
arXiv:quant-ph/0608197, proof of Theorem 4, lines 765--770.  The scalar `ζ`
records the rescaling in the periodic vectors. -/
theorem exists_leftCanonical_normalTensor_scale_of_isNormal
    {D : ℕ} [NeZero D] {A : MPSTensor d D} (hA : Kraus.IsNormal A) :
    ∃ (B : MPSTensor d D) (ζ : ℂ), ζ ≠ 0 ∧ GaugeEquiv (ζ • A) B ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) ∧
      IsLeftCanonical B ∧ IsNormalTensor B := by
  obtain ⟨B, ζ, ρ, hζ, hGauge, hMpv, hPrim, _hρ, _, _, _⟩ :=
    exists_isPrimitiveMPS_gauge_of_isNormal hA
  have hLC : IsLeftCanonical B := hPrim.norm
  have hNormalB : Kraus.IsNormal B :=
    isNormal_of_gaugeEquiv ((isNormal_smul_iff hζ A).2 hA) hGauge
  exact ⟨B, ζ, hζ, hGauge, hMpv, hLC,
    isNormalTensor_of_isNormal_leftCanonical B hNormalB hLC⟩

/-- Nonzero rescalings on either side do not affect gauge-phase equivalence. -/
theorem gaugePhaseEquiv_of_smul_smul_cast
    {D₁ D₂ : ℕ} (hdim : D₁ = D₂) {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {c e : ℂ} (hc : c ≠ 0) (he : e ≠ 0)
    (h : GaugePhaseEquiv
      (cast (congr_arg (MPSTensor d) hdim) (c • A)) (e • B)) :
    GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) A) B := by
  subst hdim
  simp only [cast_eq] at h ⊢
  obtain ⟨X, ζ, hζ, hrel⟩ := h
  refine ⟨X, e⁻¹ * (ζ * c), by simp [hζ, hc, he], fun i => ?_⟩
  have hi := hrel i
  simp only [Pi.smul_apply] at hi
  have hB : B i = e⁻¹ • (e • B i) := (inv_smul_smul₀ he (B i)).symm
  rw [hB, hi]
  simp [smul_smul]

/-- Eventual linear independence of the matrix product vectors of a finite family of
normalized normal tensors that are pairwise not gauge-phase equivalent.

This is the arbitrary finite index set version of
`exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv`. -/
theorem exists_eventually_linearIndependent_of_normalTensor_distinct
    {ι : Type*} [Finite ι] {dim : ι → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : ι) → MPSTensor d (dim k))
    (hNormal : ∀ k, IsNormalTensor (A k))
    (hDistinct : ∀ j k : ι, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)) :
    ∃ N₀ : ℕ, ∀ N > N₀,
      LinearIndependent ℂ (fun k : ι => mpvState (d := d) (A k) N) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  set e := Fintype.equivFin ι with he
  obtain ⟨N₀, hLI⟩ :=
    exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv
      (d := d) (dim := fun k => dim (e.symm k)) (fun k => A (e.symm k))
      (fun k => hNormal (e.symm k))
      (fun j k hjk h => hDistinct (e.symm j) (e.symm k)
        (fun hEq => hjk (by simpa using congrArg e hEq)) h)
  refine ⟨N₀, fun N hN => ?_⟩
  have hfun : ((fun k : Fin (Fintype.card ι) => mpvState (d := d) (A (e.symm k)) N) ∘ e)
      = fun k : ι => mpvState (d := d) (A k) N := by
    funext k
    exact congrArg (fun y : ι => mpvState (d := d) (A y) N) (e.symm_apply_apply k)
  rw [← hfun]
  exact (hLI N hN).comp e e.injective

/-- A vanishing pointwise combination of matrix product vectors is a vanishing
combination of the corresponding states. -/
theorem sum_smul_mpvState_eq_zero
    {ι : Type*} [Fintype ι] {dim : ι → ℕ} (A : (k : ι) → MPSTensor d (dim k))
    (g : ι → ℂ) {N : ℕ}
    (h : ∀ σ : Fin N → Fin d, ∑ k, g k * mpv (A k) σ = 0) :
    ∑ k, g k • mpvState (d := d) (A k) N = 0 := by
  apply PiLp.ext
  intro σ
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mpvState_apply, WithLp.ofLp_zero, Pi.zero_apply]
  exact h σ

end MPSTensor
