/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ConstantPowerSums
import TNLean.MPS.MPDO.BNTCoefficients

/-!
# Length-independent BNT-label structure coefficients

After Theorem IV.13, arXiv:1606.00608 singles out the renormalization fixed
points whose BNT-label structure coefficients
$c^{(L)}_{\alpha,\beta,\gamma} = \operatorname{tr}(\chi^L_{\alpha,\beta,\gamma})$
do not depend on the chain length $L$.  For this case the paper observes
(line 1010) that the diagonal entries of the matrices
$\chi_{\alpha,\beta,\gamma}$ lie in $\{0, 1\}$, so every structure coefficient
is a natural number; with the positivity of Theorem IV.13(ii) the entries in
fact all equal one, and each coefficient is the size of the corresponding
diagonal matrix.  Starting from the same-length product law and the idempotent
condition with natural-number coefficients independent of the length,
Bultinck, Marien, Williamson, Sahinoglu, Haegeman, and Verstraete
(arXiv:1511.08090) recover the known non-chiral topologically ordered phases;
the paper asks whether renormalization fixed points with length-dependent
structure coefficients exist (lines 995--997).  The explicit positive answer
is formalized separately in `TNLean.MPS.MPDO.LengthDependentRFPExample`.

This file defines the length-independence predicate on the BNT-label
coefficient systems of `TNLean.MPS.MPDO.BNTCoefficients` and proves the
naturality consequences for a positive chi witness, together with the
converse.  Every statement in this file stays at the abstract BNT-label level;
the tensor-attached construction and the length-dependent RFP example are
provided by later modules.

The paper derives the $\{0, 1\}$ membership from the power-sum uniqueness
lemma of its appendix (lines 1155--1163, formalized in
`TNLean.Algebra.ScalarPowerSumIdentity`); the proofs here use the elementary
constant-power-sum dichotomy from `TNLean.Algebra.ConstantPowerSums`, which
suffices for this specialization.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Section 4.5, lines 995--1010
* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2017]
  arXiv:1511.08090, Ann. Phys. 378 (2017) 183--233
-/

open scoped BigOperators ComplexOrder

namespace MPOTensor

namespace DiagonalChiFamily

variable {I : Type*} {χ : DiagonalChiFamily I}

/-- Diagonal entries of a positive chi family whose trace-power coefficients
do not depend on the positive exponent all equal one.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem entry_eq_one_of_posEntries_of_forall_tracePowerCoeff_eq
    (hχ : χ.PosEntries) (α β γ : I)
    (hsum : ∀ L : ℕ, 0 < L →
      χ.tracePowerCoeff α β γ L = χ.tracePowerCoeff α β γ 1)
    (k : Fin (χ.dim α β γ)) : χ.entry α β γ k = 1 := by
  have hsum' : ∀ L : ℕ, 0 < L →
      ∑ r, χ.entry α β γ r ^ L = ∑ r, χ.entry α β γ r := by
    intro L hL
    simpa [tracePowerCoeff] using hsum L hL
  rcases Complex.eq_zero_or_eq_one_of_forall_sum_pow_eq
      (fun r => (hχ α β γ r).le) hsum' k with h | h
  · exact absurd h (ne_of_gt (hχ α β γ k))
  · exact h

/-- A diagonal chi matrix all of whose diagonal entries equal one is the
identity matrix.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem matrix_eq_one_of_forall_entry_eq_one
    (hone : ∀ α β γ : I, ∀ k : Fin (χ.dim α β γ), χ.entry α β γ k = 1)
    (α β γ : I) :
    χ.matrix α β γ = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [DiagonalChiFamily.matrix, hone]
  · simp [DiagonalChiFamily.matrix, hij]

/-- When every diagonal entry of a chi family equals one, the trace-power
coefficient at any exponent is the size of the diagonal matrix.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem tracePowerCoeff_eq_dim_of_forall_entry_eq_one
    (hone : ∀ α β γ : I, ∀ k : Fin (χ.dim α β γ), χ.entry α β γ k = 1)
    (α β γ : I) (L : ℕ) :
    χ.tracePowerCoeff α β γ L = (χ.dim α β γ : ℂ) := by
  simp [tracePowerCoeff, hone]

end DiagonalChiFamily

namespace BNTLabelCoefficientFamily

variable {Λ : Type*} (c : BNTLabelCoefficientFamily Λ)

/-- Length independence of the BNT-label structure coefficients: at every
positive chain length the coefficients agree with the length-one
coefficients.

This is the special case singled out in the discussion following
Theorem IV.13, where the structure coefficients
$c^{(L)}_{\alpha,\beta,\gamma}$ are natural numbers independent of $L$ and
connect the renormalization fixed points to non-chiral topologically ordered
phases.  Whether every renormalization fixed point has length-independent
coefficients is the open question of the source.

Source: arXiv:1606.00608, lines 995--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def LengthIndependent : Prop :=
  ∀ L : ℕ, 0 < L → ∀ α β γ : Λ, c.coeff L α β γ = c.coeff 1 α β γ

variable {c}

/-- Length-independent coefficients agree at any two positive lengths.

Source: arXiv:1606.00608, lines 995--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem LengthIndependent.coeff_eq (hLI : c.LengthIndependent)
    {L L' : ℕ} (hL : 0 < L) (hL' : 0 < L') (α β γ : Λ) :
    c.coeff L α β γ = c.coeff L' α β γ := by
  rw [hLI L hL α β γ, hLI L' hL' α β γ]

/-- Every diagonal entry of a positive chi witness for a length-independent
coefficient system equals one.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem HasPositiveLengthChiTracePowerForm.entry_eq_one_of_lengthIndependent
    {χ : DiagonalChiFamily Λ}
    (h : c.HasPositiveLengthChiTracePowerForm χ) (hχ : χ.PosEntries)
    (hLI : c.LengthIndependent) (α β γ : Λ) (k : Fin (χ.dim α β γ)) :
    χ.entry α β γ k = 1 := by
  refine DiagonalChiFamily.entry_eq_one_of_posEntries_of_forall_tracePowerCoeff_eq
    hχ α β γ (fun L hL => ?_) k
  rw [← h L hL α β γ, ← h 1 one_pos α β γ]
  exact hLI L hL α β γ

/-- The diagonal entries of a positive chi witness for a length-independent
coefficient system lie in $\{0, 1\}$, as stated in the source; positivity
excludes the value zero.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem HasPositiveLengthChiTracePowerForm.entry_eq_zero_or_eq_one_of_lengthIndependent
    {χ : DiagonalChiFamily Λ}
    (h : c.HasPositiveLengthChiTracePowerForm χ) (hχ : χ.PosEntries)
    (hLI : c.LengthIndependent) (α β γ : Λ) (k : Fin (χ.dim α β γ)) :
    χ.entry α β γ k = 0 ∨ χ.entry α β γ k = 1 :=
  Or.inr (h.entry_eq_one_of_lengthIndependent hχ hLI α β γ k)

/-- Length-independent coefficients with a positive chi witness equal the
sizes of the corresponding diagonal matrices at every positive length.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem HasPositiveLengthChiTracePowerForm.coeff_eq_dim_of_lengthIndependent
    {χ : DiagonalChiFamily Λ}
    (h : c.HasPositiveLengthChiTracePowerForm χ) (hχ : χ.PosEntries)
    (hLI : c.LengthIndependent) (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    c.coeff L α β γ = (χ.dim α β γ : ℂ) := by
  rw [h L hL α β γ]
  exact DiagonalChiFamily.tracePowerCoeff_eq_dim_of_forall_entry_eq_one
    (h.entry_eq_one_of_lengthIndependent hχ hLI) α β γ L

/-- Length-independent coefficients with a positive chi witness are natural
numbers.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem HasPositiveLengthChiTracePowerForm.exists_natCast_coeff_of_lengthIndependent
    {χ : DiagonalChiFamily Λ}
    (h : c.HasPositiveLengthChiTracePowerForm χ) (hχ : χ.PosEntries)
    (hLI : c.LengthIndependent) (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    ∃ n : ℕ, c.coeff L α β γ = (n : ℂ) :=
  ⟨χ.dim α β γ, h.coeff_eq_dim_of_lengthIndependent hχ hLI L hL α β γ⟩

/-- Conversely, a coefficient system with a chi witness whose diagonal entries
all equal one is length independent.

Source: arXiv:1606.00608, lines 995--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem HasPositiveLengthChiTracePowerForm.lengthIndependent_of_forall_entry_eq_one
    {χ : DiagonalChiFamily Λ}
    (h : c.HasPositiveLengthChiTracePowerForm χ)
    (hone : ∀ α β γ : Λ, ∀ k : Fin (χ.dim α β γ), χ.entry α β γ k = 1) :
    c.LengthIndependent := by
  intro L hL α β γ
  rw [h L hL α β γ, h 1 one_pos α β γ,
    DiagonalChiFamily.tracePowerCoeff_eq_dim_of_forall_entry_eq_one hone,
    DiagonalChiFamily.tracePowerCoeff_eq_dim_of_forall_entry_eq_one hone]

end BNTLabelCoefficientFamily

namespace PositiveBNTLabelChiTracePowerForm

variable {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}

/-- Every diagonal entry of a positive BNT-label chi witness equals one when
the coefficient system is length independent.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem entry_eq_one_of_lengthIndependent (h : PositiveBNTLabelChiTracePowerForm c)
    (hLI : c.LengthIndependent) (α β γ : Λ) (k : Fin (h.chi.dim α β γ)) :
    h.chi.entry α β γ k = 1 :=
  h.tracePower.entry_eq_one_of_lengthIndependent h.posEntries hLI α β γ k

/-- Length-independent coefficients with a positive BNT-label chi witness are
the sizes of the diagonal matrices, hence natural numbers.

Source: arXiv:1606.00608, line 1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem coeff_eq_dim_of_lengthIndependent (h : PositiveBNTLabelChiTracePowerForm c)
    (hLI : c.LengthIndependent) (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    c.coeff L α β γ = (h.chi.dim α β γ : ℂ) :=
  h.tracePower.coeff_eq_dim_of_lengthIndependent h.posEntries hLI L hL α β γ

end PositiveBNTLabelChiTracePowerForm

end MPOTensor
