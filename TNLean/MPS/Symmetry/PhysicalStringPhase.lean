/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalStringSelectionRule

/-!
# Scalar phases in physical string order

The physical predicate in arXiv:0802.0447, display `SOP`, excludes only the
identity matrix. A nonidentity scalar unitary therefore satisfies that literal
condition for every normalized unital tensor, with identity endpoint operators.
The physical string-order predicate uses the explicit projective correction
that excludes every scalar twist.

The fixed-twist criterion below retains the peripheral eigenvalue. Removing
that phase, as in lines 257–275 of the source, need not preserve inequality
with the identity. It does preserve the corrected projective nontriviality
condition, giving the global fixed-twist criterion.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447,
  display `SOP`, Lemma 1, and Theorem 1, lines 114–121 and 189–275.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace
open Filter

namespace MPSTensor

variable {d D : ℕ}

/-- A scalar phase in the physical twist multiplies the twisted transfer map by
that scalar. Source: arXiv:0802.0447, display `EU`, lines 166–175. -/
lemma twistedTransferMap_smul_twist (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ) :
    twistedTransferMap A (μ • u) = μ • twistedTransferMap A u := by
  ext X : 1
  simp only [twistedTransferMap_apply, LinearMap.smul_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.smul_sum, smul_smul]

/-- Scalar rephasing of the twist contributes its length power to the physical
correlator. Source: arXiv:0802.0447, displays `SOPMP` and `EU`, lines 166–181. -/
lemma physicalStringOrderParam_smul_twist (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (x y u : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ) (N : ℕ) :
    physicalStringOrderParam A Λ x y (μ • u) N =
      μ ^ N * physicalStringOrderParam A Λ x y u N := by
  simp only [physicalStringOrderParam, twistedTransferIter, twistedTransferMap_smul_twist,
    smul_pow, LinearMap.smul_apply, map_smul, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul]

/-- The positive-limit string-order condition is invariant under scalar
unit-modulus rephasing of a fixed physical twist. Source: arXiv:0802.0447,
display `SOP`, lines 114–121. -/
lemma hasPhysicalStringOrderWith_smul_twist_iff (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (x y u : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ) (hμ : ‖μ‖ = 1) :
    HasPhysicalStringOrderWith A Λ x y (μ • u) ↔
      HasPhysicalStringOrderWith A Λ x y u := by
  simp only [HasPhysicalStringOrderWith, physicalStringOrderParam_smul_twist,
    norm_mul, norm_pow, hμ, one_pow, one_mul]

/-- Identity physical endpoints and a scalar twist give exactly the scalar's
length power for a normalized unital tensor. This evaluates the literal
string-order definition in arXiv:0802.0447, lines 114–121. -/
theorem physicalStringOrderParam_scalar_twist (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : Kraus.transferMap A 1 = 1) (μ : ℂ) (N : ℕ) :
    physicalStringOrderParam A Λ 1 1 (μ • 1) N = μ ^ N := by
  have hIter : twistedTransferIter A 1 N 1 = 1 := by
    induction N with
    | zero => simp [twistedTransferIter]
    | succ N ih =>
      rw [twistedTransferIter, pow_succ', Module.End.mul_apply]
      change twistedTransferMap A 1 (twistedTransferIter A 1 N 1) = 1
      rw [ih, twistedTransferMap_one, hNorm]
  rw [physicalStringOrderParam_smul_twist]
  simp only [physicalStringOrderParam, twistedTransferMap_one, hNorm, hIter,
    hΛtr, mul_one]

/-- The literal source condition holds for every normalized unital tensor:
choose the scalar twist `-1` and identity physical endpoints.

This concerns exactly the inequality `u ≠ 1` printed in arXiv:0802.0447,
lines 114–121, without imposing nontriviality modulo scalar phases. -/
theorem exists_nonidentity_physicalStringOrderWith_of_unital
    [NeZero d] (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : Kraus.transferMap A 1 = 1) :
    ∃ u x y : Matrix (Fin d) (Fin d) ℂ,
      u * uᴴ = 1 ∧ u ≠ 1 ∧ HasPhysicalStringOrderWith A Λ x y u := by
  refine ⟨-1, 1, 1, by simp, ?_, 1, zero_lt_one, ?_⟩
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M 0 0) h
    norm_num at h00
  · have hvalue (N : ℕ) : ‖physicalStringOrderParam A Λ 1 1 (-1) N‖ = 1 := by
      simpa only [neg_one_smul, norm_pow, norm_neg, norm_one, one_pow] using
        congrArg norm (physicalStringOrderParam_scalar_twist A Λ hΛtr hNorm (-1) N)
    simpa only [hvalue] using (tendsto_const_nhds (x := (1 : ℝ)))

/-- A scalar physical twist with a nonzero fixed matrix must be the identity
under the source's simple-peripheral purity condition. Thus the fixed-point
conclusion of arXiv:0802.0447, Theorem 1, excludes the scalar witnesses allowed
by its literal string-order definition. -/
theorem scalar_twist_eq_one_of_nonzero_fixed
    (A : MPSTensor d D)
    (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (μ : ℂ) (hμ : ‖μ‖ = 1)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X ≠ 0)
    (hFix : twistedTransferMap A (μ • 1) X = X) : μ = 1 := by
  have hμne : μ ≠ 0 := by
    intro h
    simp [h] at hμ
  have hEig : Kraus.transferMap A X = μ⁻¹ • X := by
    have h := congrArg (fun Y => μ⁻¹ • Y) hFix
    simpa only [twistedTransferMap_smul_twist, LinearMap.smul_apply,
      twistedTransferMap_one, smul_smul, inv_mul_cancel₀ hμne, one_smul] using h
  have hInv := (hPure μ⁻¹ X hX (by simp [norm_inv, hμ]) hEig).1
  exact inv_eq_one.mp hInv

/-- If the twisted spectral radius is below one, every fixed physical-endpoint
correlator tends to zero. Source: arXiv:0802.0447, lines 241–244. -/
theorem physicalStringOrderParam_tendsto_zero_of_spectralRadius_lt_one
    (A : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (x y u : Matrix (Fin d) (Fin d) ℂ)
    (hRad : spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
        (twistedTransferMap A u)) < 1) :
    Tendsto (physicalStringOrderParam A Λ x y u) atTop (nhds 0) := by
  have hterm (n m : Fin d) : Tendsto
      (fun N => x m n * stringOrderBoundaryParam A u 1 ((A m)ᴴ * Λ * A n)
        (twistedTransferMap A y 1) N) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (stringOrderBoundaryParam_tendsto_zero_of_spectralRadius_lt_one
        A u 1 ((A m)ᴴ * Λ * A n) (twistedTransferMap A y 1) hRad)
  have hsum := tendsto_finsetSum Finset.univ (fun n _ =>
    tendsto_finsetSum Finset.univ (fun m _ => hterm n m))
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr'
  filter_upwards with N
  conv_rhs => rw [physicalStringOrderParam, twistedTransferMap_apply]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [stringOrderBoundaryParam, Matrix.one_mul]
  congr 1
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (A m)ᴴ (Λ * A n * twistedTransferIter A u N
      (twistedTransferMap A y 1))

/-- A phase-retaining physical selection criterion for a fixed twist, under
exactly the canonical simple-peripheral hypotheses in arXiv:0802.0447,
lines 147–160 and Theorem 1. The twist is not rephased, and the peripheral
phase is retained in the eigenmatrix equation. -/
theorem pureCanonical_exists_physicalStringOrderWith_iff_peripheral_letter
    [NeZero D] (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1) :
    (∃ x y, HasPhysicalStringOrderWith A Λ x y u) ↔
      ∃ (V : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ) (n m : Fin d),
        ‖μ‖ = 1 ∧ twistedTransferMap A u V = μ • V ∧
          Matrix.trace (V * Λ * A n * (A m)ᴴ) ≠ 0 := by
  have hSpect := pureCanonical_twistedTransfer_spectral_lemma
    A Λ hΛpos hΛtr hΛfix hNorm hPure u hu
  constructor
  · intro hSO
    obtain ⟨x, y, s, hs, hlim⟩ := hSO
    have hRad : spectralRadius ℂ
        (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
          (twistedTransferMap A u)) = 1 := by
      apply le_antisymm hSpect.1
      by_contra h
      have hzero := (physicalStringOrderParam_tendsto_zero_of_spectralRadius_lt_one
        A Λ x y u (lt_of_not_ge h)).norm
      have heq : s = 0 := by simpa only [norm_zero] using tendsto_nhds_unique hlim hzero
      exact (ne_of_gt hs) heq
    obtain ⟨V, μ, hV, _, hμ, _, hInter⟩ := hSpect.2.1.mp hRad
    obtain ⟨n, m, hnm⟩ :=
      (pureCanonical_physicalString_selection_rule
        A Λ hΛpos hΛtr hΛfix hNorm hPure u hu V μ hV hμ hInter).2.mp
        ⟨x, y, s, hs, hlim⟩
    exact ⟨V, μ, n, m, hμ,
      twistedTransfer_eigen_of_virtualUnitary A u V μ hNorm hV hInter, hnm⟩
  · rintro ⟨Q, ev, n, m, hev, hEig, hnm⟩
    have hQ : Q ≠ 0 := by
      intro hQ0
      simp [hQ0] at hnm
    have hEig' : Module.End.HasEigenvalue (twistedTransferMap A u) ev :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hEig, hQ⟩
    have hRad : spectralRadius ℂ
        (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
          (twistedTransferMap A u)) = 1 := by
      apply le_antisymm hSpect.1
      have hspec : ev ∈ spectrum ℂ
          (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
            (twistedTransferMap A u)) := by
        rw [AlgEquiv.spectrum_eq]
        exact hEig'.mem_spectrum
      have hevnn : ‖ev‖₊ = 1 := by
        apply NNReal.coe_injective
        simpa only [coe_nnnorm, NNReal.coe_one] using hev
      rw [spectralRadius_eq_of_unital]
      simpa only [hevnn, ENNReal.coe_one] using
        (le_iSup₂ (f := fun z (_ : z ∈ spectrum ℂ
          (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
            (twistedTransferMap A u))) => (‖z‖₊ : ENNReal)) ev hspec)
    obtain ⟨V, μ, hV, _, hμ, _, hInter⟩ := hSpect.2.1.mp hRad
    have hVne : V ≠ 0 := by
      intro hV0
      rw [hV0, zero_mul] at hV
      exact zero_ne_one hV
    obtain ⟨_, c, _, hQV⟩ := hSpect.2.2 ev μ Q V hQ hVne hev hμ hEig
      (twistedTransfer_eigen_of_virtualUnitary A u V μ hNorm hV hInter)
    apply (pureCanonical_physicalString_selection_rule
      A Λ hΛpos hΛtr hΛfix hNorm hPure u hu V μ hV hμ hInter).2.mpr
    refine ⟨n, m, ?_⟩
    intro hzero
    apply hnm
    simp [hQV, Matrix.trace_smul, hzero]

/-- The fixed-point selection criterion with explicit projective
nontriviality: both twists are required to be nonscalar.

**Local fix (projective nontriviality):** This is the corrected form of
arXiv:0802.0447, Theorem 1, using the stated projective convention in
`HasPhysicalStringOrder`. It is not the unchanged printed assertion with
only `u ≠ 1` on the string-order side. See
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`. -/
theorem hasPhysicalStringOrder_iff_exists_fixed_letter
    [NeZero D] (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1) :
    HasPhysicalStringOrder A Λ ↔
      ∃ (u : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin D) (Fin D) ℂ)
        (n m : Fin d),
        u * uᴴ = 1 ∧ (∀ c : ℂ, u ≠ c • 1) ∧
          twistedTransferMap A u V = V ∧
          Matrix.trace (V * Λ * A n * (A m)ᴴ) ≠ 0 := by
  constructor
  · rintro ⟨u, x, y, hu, hnonScalar, hSO⟩
    obtain ⟨V, μ, n, m, hμ, hEig, hnm⟩ :=
      (pureCanonical_exists_physicalStringOrderWith_iff_peripheral_letter
        A Λ hΛpos hΛtr hΛfix hNorm hPure u hu).mp ⟨x, y, hSO⟩
    have hμne : μ ≠ 0 := Complex.ne_zero_of_norm_eq_one hμ
    refine ⟨μ⁻¹ • u, V, n, m,
      phaseShiftedPhysicalUnitary_mul_conjTranspose u μ hu hμ, ?_, ?_, hnm⟩
    · intro c hc
      apply hnonScalar (μ * c)
      calc
        u = μ • (μ⁻¹ • u) := by simp [smul_smul, hμne]
        _ = (μ * c) • 1 := by rw [hc, smul_smul]
    · simp only [twistedTransferMap_smul_twist, LinearMap.smul_apply, hEig,
        smul_smul, inv_mul_cancel₀ hμne, one_smul]
  · rintro ⟨u, V, n, m, hu, hnonScalar, hEig, hnm⟩
    obtain ⟨x, y, hSO⟩ :=
      (pureCanonical_exists_physicalStringOrderWith_iff_peripheral_letter
        A Λ hΛpos hΛtr hΛfix hNorm hPure u hu).mpr
          ⟨V, 1, n, m, by simp, by simpa only [one_smul] using hEig, hnm⟩
    exact ⟨u, x, y, hu, hnonScalar, hSO⟩

end MPSTensor
