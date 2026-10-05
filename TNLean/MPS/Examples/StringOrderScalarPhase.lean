/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalStringPhase
import QICLean.Algebra.SpinCover.Basic
import QICLean.Kraus.Wielandt.Primitivity.EasyDirections
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A four-letter tensor with scalar-only unphased physical symmetry

The tensor has bond dimension two and four linearly independent physical
letters. Its canonical stationary density is `I/2`. Its action on the Pauli
matrices has distinct diagonal symmetric part and nonzero skew entries.
These explicit properties determine its unphased physical symmetries.

The example tests the scalar phase removed between arXiv:0802.0447,
display `SOP` (lines 114–121), and Theorem 1 (lines 257–275).

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447,
  canonical normalization and purity, lines 147–160; Theorem 1, lines 257–275.
* Wolf, *Quantum Channels & Operations*, Theorems 6.4 and 6.7.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace MPSTensor

private def phaseExampleWeight : Fin 4 → ℝ := ![1 / 2, 1 / 8, 1 / 12, 1 / 24]

private def phaseExampleRaw : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![1, -Complex.I; -Complex.I, 1], !![1, -1; 1, 1],
    !![1 - Complex.I, 0; 0, 1 + Complex.I]]

/-- A normalized four-letter tensor formed from the identity and three quarter
turns about the Pauli axes, with probabilities `1/2, 1/4, 1/6, 1/12`.
It supplies explicit canonical data for the phase-convention question in
arXiv:0802.0447, Theorem 1. -/
def stringPhaseTensor : MPSTensor 4 2 :=
  fun j => (Real.sqrt (phaseExampleWeight j) : ℂ) • phaseExampleRaw j

private lemma phaseExampleWeight_pos (j : Fin 4) : 0 < phaseExampleWeight j := by
  fin_cases j <;> norm_num [phaseExampleWeight]

private lemma phaseExampleCoeff_ne_zero (j : Fin 4) :
    (Real.sqrt (phaseExampleWeight j) : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (phaseExampleWeight_pos j)))

private lemma phaseExampleCoeff_star_mul (j : Fin 4) :
    star (Real.sqrt (phaseExampleWeight j) : ℂ) *
      (Real.sqrt (phaseExampleWeight j) : ℂ) = phaseExampleWeight j := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (le_of_lt (phaseExampleWeight_pos j))]

private lemma phaseExampleRaw_linearIndependent : LinearIndependent ℂ phaseExampleRaw := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hg
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hg
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hg
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hg
  norm_num [phaseExampleRaw, Fin.sum_univ_four] at h00 h01 h10 h11
  have h1 : g 1 = 0 := by
    have h : (-2 * Complex.I) * g 1 = 0 := by linear_combination h01 + h10
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have h2 : g 2 = 0 := by linear_combination (h10 - h01) / 2
  have h3 : g 3 = 0 := by
    have h : (-2 * Complex.I) * g 3 = 0 := by linear_combination h00 - h11
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have h0 : g 0 = 0 := by simpa [h1, h2, h3] using h00
  intro i
  fin_cases i <;> assumption

/-- The four physical letters are linearly independent, so no physical
subspace is unused in this example. -/
theorem stringPhaseTensor_linearIndependent : LinearIndependent ℂ stringPhaseTensor := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hsum : ∑ k : Fin 4,
      (g k * (Real.sqrt (phaseExampleWeight k) : ℂ)) • phaseExampleRaw k = 0 := by
    simpa only [stringPhaseTensor, smul_smul] using hg
  have hcoeff := (Fintype.linearIndependent_iff.mp phaseExampleRaw_linearIndependent) _ hsum j
  exact (mul_eq_zero.mp hcoeff).resolve_right (phaseExampleCoeff_ne_zero j)

/-- The four physical letters span all two-by-two matrices. -/
theorem stringPhaseTensor_isInjective : Kraus.IsInjective stringPhaseTensor := by
  apply stringPhaseTensor_linearIndependent.span_eq_top_of_card_eq_finrank'
  simp [Module.finrank_matrix]

private lemma stringPhaseTensor_transfer_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Kraus.transferMap stringPhaseTensor X =
      ∑ j : Fin 4, (phaseExampleWeight j : ℂ) •
        (phaseExampleRaw j * X * (phaseExampleRaw j)ᴴ) := by
  simp only [Kraus.transferMap_apply, stringPhaseTensor, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, phaseExampleCoeff_star_mul]

/-- The example transfer map is unital. -/
theorem stringPhaseTensor_unital : Kraus.transferMap stringPhaseTensor 1 = 1 := by
  rw [stringPhaseTensor_transfer_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseExampleWeight, phaseExampleRaw, Fin.sum_univ_four,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num

/-- The example transfer map is trace preserving. -/
theorem stringPhaseTensor_isTP : Kraus.IsTP stringPhaseTensor := by
  change ∑ j : Fin 4, (stringPhaseTensor j)ᴴ * stringPhaseTensor j = 1
  have hterm (j : Fin 4) : (stringPhaseTensor j)ᴴ * stringPhaseTensor j =
      (phaseExampleWeight j : ℂ) • ((phaseExampleRaw j)ᴴ * phaseExampleRaw j) := by
    simp only [stringPhaseTensor, Matrix.conjTranspose_smul, smul_mul_smul_comm]
    rw [phaseExampleCoeff_star_mul]
  simp_rw [hterm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseExampleWeight, phaseExampleRaw, Fin.sum_univ_four,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num

/-- The faithful normalized dual density is the maximally mixed matrix `I/2`. -/
theorem stringPhaseTensor_canonical :
    Matrix.PosDef ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      Matrix.trace ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 ∧
      Kraus.transferMap (fun i => (stringPhaseTensor i)ᴴ) ((1 / 2 : ℂ) • 1) =
        (1 / 2 : ℂ) • 1 := by
  refine ⟨Matrix.PosDef.one.smul (by norm_num), by norm_num, ?_⟩
  rw [map_smul]
  congr 1
  simpa [Kraus.transferMap_apply, Kraus.IsTP] using stringPhaseTensor_isTP

/-- The example has no peripheral eigenvalue other than one, whose eigenmatrices
are scalar. These are the canonical spectral-purity assumptions of
arXiv:0802.0447, lines 147–160. -/
theorem stringPhaseTensor_pure (ev : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X ≠ 0) (hev : ‖ev‖ = 1)
    (hEig : Kraus.transferMap stringPhaseTensor X = ev • X) :
    ev = 1 ∧ ∃ c : ℂ, X = c • 1 := by
  have hIrr := Kraus.injective_implies_irreducibleCP
    stringPhaseTensor stringPhaseTensor_isInjective
  have hPrim : IsPrimitive (Kraus.transferMap stringPhaseTensor) :=
    Kraus.isPrimitive_mapLM_of_isTP_of_vectorSpreadSpan_eq_top
      stringPhaseTensor stringPhaseTensor_isTP
      (Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top stringPhaseTensor
        (Kraus.isNBlkInjective_one_of_isInjective stringPhaseTensor_isInjective))
  have hev1 := hPrim.unique_peripheral ev
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hEig, hX⟩) hev
  refine ⟨hev1, ?_⟩
  apply Kraus.fixed_eq_scalar_of_irreducible_unital stringPhaseTensor
    (by simpa [KadisonSchwarz.IsUnitalKraus] using stringPhaseTensor_unital) hIrr X
  simpa [hev1] using hEig

private def stringPhaseBloch : Matrix (Fin 3) (Fin 3) ℂ :=
  !![3 / 4, -1 / 12, 1 / 6; 1 / 12, 2 / 3, -1 / 4; -1 / 6, 1 / 4, 7 / 12]

private lemma stringPhaseTensor_transfer_pauli (j : Fin 3) :
    Kraus.transferMap stringPhaseTensor (SpinCover.pauli j) =
      ∑ i : Fin 3, stringPhaseBloch i j • SpinCover.pauli i := by
  rw [stringPhaseTensor_transfer_apply]
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [phaseExampleWeight, phaseExampleRaw, stringPhaseBloch, SpinCover.pauli,
      Fin.sum_univ_four, Fin.sum_univ_three, Matrix.mul_apply, Matrix.vecMul,
      Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num <;> ring

private lemma stringPhaseBloch_joint_centralizer
    (R : Matrix (Fin 3) (Fin 3) ℂ)
    (h : R * stringPhaseBloch = stringPhaseBloch * R)
    (hT : R * stringPhaseBlochᵀ = stringPhaseBlochᵀ * R) :
    ∃ c : ℂ, R = c • 1 := by
  have hSym : R * (stringPhaseBloch + stringPhaseBlochᵀ) =
      (stringPhaseBloch + stringPhaseBlochᵀ) * R := by
    simp only [mul_add, add_mul, h, hT]
  have hoff (i j : Fin 3) (hij : i ≠ j) : R i j = 0 := by
    have hij' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hSym
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals norm_num [stringPhaseBloch, Matrix.mul_apply, Fin.sum_univ_three] at hij' ⊢
    · linear_combination -6 * hij'
    · linear_combination -3 * hij'
    · linear_combination 6 * hij'
    · linear_combination -6 * hij'
    · linear_combination 3 * hij'
    · linear_combination 6 * hij'
  have hd01 : R 1 1 = R 0 0 := by
    have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) h
    norm_num [stringPhaseBloch, Matrix.mul_apply, Fin.sum_univ_three, hoff] at h01
    linear_combination -12 * h01
  have hd02 : R 2 2 = R 0 0 := by
    have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 2) h
    norm_num [stringPhaseBloch, Matrix.mul_apply, Fin.sum_univ_three, hoff] at h02
    linear_combination -6 * h02
  refine ⟨R 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hoff, hd01, hd02]

private lemma stringPhaseTensor_rotation_commutes (W : GL (Fin 2) ℂ)
    (hCov : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      Kraus.transferMap stringPhaseTensor
          ((W : Matrix (Fin 2) (Fin 2) ℂ) * X * (↑W⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) =
        (W : Matrix (Fin 2) (Fin 2) ℂ) * Kraus.transferMap stringPhaseTensor X *
          (↑W⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) :
    SpinCover.pauliConjAd W * stringPhaseBloch =
      stringPhaseBloch * SpinCover.pauliConjAd W := by
  have hcoord (c : Fin 3 → ℂ) (i : Fin 3) :
      Matrix.trace (SpinCover.pauli i * (∑ k, c k • SpinCover.pauli k)) / 2 = c i := by
    simp [Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_smul,
      SpinCover.pauli_mul_pauli_trace, mul_ite]
  have hleft (j : Fin 3) : Kraus.transferMap stringPhaseTensor
      ((W : Matrix (Fin 2) (Fin 2) ℂ) * SpinCover.pauli j *
        (↑W⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) =
      ∑ i : Fin 3, (stringPhaseBloch * SpinCover.pauliConjAd W) i j •
        SpinCover.pauli i := by
    rw [SpinCover.pauli_conj_eq]
    simp_rw [map_sum, map_smul, stringPhaseTensor_transfer_pauli,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp [Matrix.mul_apply, Finset.sum_smul, mul_comm]
  have hright (j : Fin 3) :
      (W : Matrix (Fin 2) (Fin 2) ℂ) *
          Kraus.transferMap stringPhaseTensor (SpinCover.pauli j) *
            (↑W⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) =
      ∑ i : Fin 3, (SpinCover.pauliConjAd W * stringPhaseBloch) i j •
        SpinCover.pauli i := by
    rw [stringPhaseTensor_transfer_pauli, Matrix.mul_sum, Matrix.sum_mul]
    simp_rw [Matrix.mul_smul, Matrix.smul_mul, SpinCover.pauli_conj_eq,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp [Matrix.mul_apply, Finset.sum_smul, mul_comm]
  ext i j
  have h := congrArg (fun M => Matrix.trace (SpinCover.pauli i * M) / 2)
    (hCov (SpinCover.pauli j))
  rw [hleft, hright, hcoord, hcoord] at h
  exact h.symm

/-- Every virtual unitary covariance of this tensor acts identically by
conjugation. The proof uses the Pauli action's orthogonality, so commuting
with the Bloch matrix also implies commuting with its transpose. -/
theorem stringPhaseTensor_conjugation_eq_of_condC2
    (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W * Wᴴ = 1)
    (hCov : CondC2 stringPhaseTensor W) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    W * X * Wᴴ = X := by
  let Wg : GL (Fin 2) ℂ := ⟨W, Wᴴ, hW, mul_eq_one_comm.mp hW⟩
  let R := SpinCover.pauliConjAd Wg
  have hRT : R * stringPhaseBloch = stringPhaseBloch * R :=
    stringPhaseTensor_rotation_commutes Wg hCov
  have hRR : Rᵀ * R = 1 := SpinCover.transpose_mul_pauliConjAd Wg
  have hRR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hRR
  have hRT' : R * stringPhaseBlochᵀ = stringPhaseBlochᵀ * R := by
    have h := congrArg Matrix.transpose hRT
    simp only [Matrix.transpose_mul] at h
    calc
      R * stringPhaseBlochᵀ = R * (stringPhaseBlochᵀ * Rᵀ) * R := by
        simp only [Matrix.mul_assoc, hRR, Matrix.mul_one]
      _ = R * (Rᵀ * stringPhaseBlochᵀ) * R := by rw [h]
      _ = stringPhaseBlochᵀ * R := by
        simp only [← Matrix.mul_assoc, hRR', Matrix.one_mul]
  obtain ⟨c, hRc⟩ := stringPhaseBloch_joint_centralizer R hRT hRT'
  have hconj (j : Fin 3) : W * SpinCover.pauli j * Wᴴ = c • SpinCover.pauli j := by
    have h := SpinCover.pauli_conj_eq Wg j
    change W * SpinCover.pauli j * Wᴴ = ∑ i, R i j • SpinCover.pauli i at h
    simpa [hRc, Matrix.one_apply, mul_ite, ite_smul] using h
  have hcSq : c * c = 1 := by
    rw [hRc] at hRR
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) hRR
    simpa [Matrix.transpose_smul, smul_mul_smul_comm] using h
  have hprod : W * (SpinCover.pauli 0 * SpinCover.pauli 1) * Wᴴ =
      (c * c) • (SpinCover.pauli 0 * SpinCover.pauli 1) := by
    calc
      _ = (W * SpinCover.pauli 0 * Wᴴ) * (W * SpinCover.pauli 1 * Wᴴ) := by
        have hcancel (Y : Matrix (Fin 2) (Fin 2) ℂ) : Wᴴ * (W * Y) = Y := by
          rw [← Matrix.mul_assoc, mul_eq_one_comm.mp hW, Matrix.one_mul]
        simp only [Matrix.mul_assoc, hcancel]
      _ = _ := by rw [hconj, hconj, smul_mul_smul_comm]
  have hxy : SpinCover.pauli 0 * SpinCover.pauli 1 = Complex.I • SpinCover.pauli 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [SpinCover.pauli, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hxy, Matrix.mul_smul, Matrix.smul_mul, hconj, hcSq, one_smul] at hprod
  have hc : c = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hprod
    simp only [Matrix.smul_apply, smul_eq_mul, SpinCover.pauli_two,
      Matrix.of_apply, Matrix.cons_val_zero, mul_one] at h
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa only [mul_one] using h
  have hfix (j : Fin 3) : W * SpinCover.pauli j * Wᴴ = SpinCover.pauli j := by
    simpa [hc] using hconj j
  conv_lhs => rw [SpinCover.pauli_expansion X]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hW, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, hfix]
  exact (SpinCover.pauli_expansion X).symm

/-- The only unitary physical twist with a nonzero fixed twisted eigenmatrix
is the identity. The physical letters are independent, so this conclusion
cannot arise from unused physical directions. -/
theorem stringPhaseTensor_twist_eq_one_of_nonzero_fixed
    (u : Matrix (Fin 4) (Fin 4) ℂ) (hu : u * uᴴ = 1)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : Q ≠ 0)
    (hFix : twistedTransferMap stringPhaseTensor u Q = Q) : u = 1 := by
  have hIrr := Kraus.injective_implies_irreducibleCP
    stringPhaseTensor stringPhaseTensor_isInjective
  have hPrim : IsPrimitive (Kraus.transferMap stringPhaseTensor) :=
    Kraus.isPrimitive_mapLM_of_isTP_of_vectorSpreadSpan_eq_top
      stringPhaseTensor stringPhaseTensor_isTP
      (Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top stringPhaseTensor
        (Kraus.isNBlkInjective_one_of_isInjective stringPhaseTensor_isInjective))
  have hGauge := twistedTransfer_modulus_one_implies_gaugePhase_of_irreducible
    stringPhaseTensor hIrr u hu stringPhaseTensor_unital 1 Q hQ
    (by simpa using hFix) (by simp)
  obtain ⟨W, μ, hW, _, hμ, hInter⟩ :=
    virtualUnitary_of_gaugePhaseEquiv_twisted_of_irreducible
      stringPhaseTensor hIrr u hu stringPhaseTensor_unital hGauge
  have hPhase := (twistedTransfer_peripheral_eq_of_primitive
    stringPhaseTensor hIrr hPrim stringPhaseTensor_unital u W μ hW hμ hInter
      1 Q hQ (by simp) (by simpa using hFix)).1
  have hC1 : CondC1 stringPhaseTensor u W := by simpa [← hPhase] using hInter
  have hCov := condC1_imp_condC2 hW hu hC1
  have hrow (i : Fin 4) : ∑ j, (u i j - (1 : Matrix (Fin 4) (Fin 4) ℂ) i j) •
      stringPhaseTensor j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hC1 i, stringPhaseTensor_conjugation_eq_of_condC2 W hW hCov]
    simp [Matrix.one_apply]
  ext i j
  exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp
    stringPhaseTensor_linearIndependent) _ (hrow i) j)

/-- The explicit nondegenerate example satisfies the literal physical
string-order condition with Hermitian identity endpoints, but has no
nonidentity unitary twist satisfying the fixed-point and letter-trace
conditions printed in arXiv:0802.0447, Theorem 1. -/
theorem stringPhaseTensor_literal_criterion_counterexample :
    (∃ u x y : Matrix (Fin 4) (Fin 4) ℂ,
      u * uᴴ = 1 ∧ u ≠ 1 ∧
        HasPhysicalStringOrderWith stringPhaseTensor ((1 / 2 : ℂ) • 1) x y u) ∧
      ¬ ∃ (u : Matrix (Fin 4) (Fin 4) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ)
        (n m : Fin 4),
        u * uᴴ = 1 ∧ u ≠ 1 ∧ twistedTransferMap stringPhaseTensor u V = V ∧
          Matrix.trace (V * ((1 / 2 : ℂ) • 1) * stringPhaseTensor n *
            (stringPhaseTensor m)ᴴ) ≠ 0 := by
  refine ⟨exists_nonidentity_physicalStringOrderWith_of_unital stringPhaseTensor _
    stringPhaseTensor_canonical.2.1 stringPhaseTensor_unital, ?_⟩
  rintro ⟨u, V, n, m, hu, hune, hFix, htrace⟩
  apply hune
  apply stringPhaseTensor_twist_eq_one_of_nonzero_fixed u hu V ?_ hFix
  intro hV
  simp [hV] at htrace

/-- The projective correction rejects the scalar-only example, although its
literal nonidentity-twist condition holds. This is a regression for the
explicit convention in `HasPhysicalStringOrder`. -/
theorem stringPhaseTensor_not_hasPhysicalStringOrder :
    ¬ HasPhysicalStringOrder stringPhaseTensor ((1 / 2 : ℂ) • 1) := by
  intro hSO
  obtain ⟨u, V, n, m, hu, hnonScalar, hFix, htrace⟩ :=
    (hasPhysicalStringOrder_iff_exists_fixed_letter stringPhaseTensor _
      stringPhaseTensor_canonical.1 stringPhaseTensor_canonical.2.1
      stringPhaseTensor_canonical.2.2 stringPhaseTensor_unital stringPhaseTensor_pure).mp hSO
  apply stringPhaseTensor_literal_criterion_counterexample.2
  exact ⟨u, V, n, m, hu, by simpa using hnonScalar 1, hFix, htrace⟩

end MPSTensor
