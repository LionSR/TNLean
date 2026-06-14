/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.PureAreaLaw
import TNLean.Spectral.MixedTransfer
import TNLean.MPS.RFP.Defs

/-!
# Renormalization fixed points saturate the area law

For a pure-state renormalization fixed point the transfer map is idempotent, so
its powers collapse (`𝔼^L = 𝔼` for `L ≥ 1`). The operator-Schmidt Gram matrices
of a block are therefore block-size independent, hence the block entropy is
constant: the area law is saturated.

See arXiv:1606.00608, Section 3 (pure-state area law, line 599).
-/

open scoped Matrix BigOperators
open Matrix

/-- **Cyclic invariance of the entropy charpoly-root sum.** The `negMulLog ∘ Re`
sum over the roots of the characteristic polynomial is unchanged under the cyclic
swap `A * B ↦ B * A` of a (possibly rectangular) product. This is the
Hermitian-free core of `vonNeumannEntropy_mul_comm`: the two characteristic
polynomials differ only by a power of `X`, i.e. by extra roots equal to `0`,
which contribute `negMulLog 0 = 0`. It lets the block entropy be pushed onto the
`D²`-dimensional bond environment even though the intermediate product of two
positive semidefinite Gram matrices is not Hermitian. -/
theorem charpoly_roots_negMulLog_re_mul_comm {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    ((A * B).charpoly.roots.map (fun z : ℂ => Real.negMulLog z.re)).sum
      = ((B * A).charpoly.roots.map (fun z : ℂ => Real.negMulLog z.re)).sum := by
  set f : ℂ → ℝ := fun z => Real.negMulLog z.re with hf
  have hroots : (Polynomial.X ^ Fintype.card n * (A * B).charpoly).roots
      = (Polynomial.X ^ Fintype.card m * (B * A).charpoly).roots := by
    rw [Matrix.charpoly_mul_comm']
  rw [Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
      Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
      Polynomial.roots_pow, Polynomial.roots_pow, Polynomial.roots_X] at hroots
  have hf0 : f 0 = 0 := by simp [hf]
  have key := congrArg (fun s => (Multiset.map f s).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, hf0, smul_zero, zero_add] at key
  exact key

namespace MPSTensor

variable {d D : ℕ}

/-- The operator-Schmidt **left factor** of an `L`-spin block: the
`(d^L) × D²` matrix whose row `u` records the bond-indexed entries of the word
product `A^u`. It is the left factor in the wavefunction-matrix factorization
`schmidtMat = schmidtLeft · (right factor)` of `schmidtMat_eq_mul`. -/
noncomputable def schmidtLeft (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin L → Fin d) (Fin D × Fin D) ℂ :=
  Matrix.of (fun u p => (evalWord A (List.ofFn u)) p.1 p.2)

/-- **Left Gram = transfer-map power on a matrix unit.** The `D² × D²` Gram matrix
of the operator-Schmidt left factor collects the same length-`L` word sum as the
`L`-fold transfer map evaluated on the matrix unit `single b₂ a₂ 1`. -/
theorem schmidtLeft_gram_apply (A : MPSTensor d D) (L : ℕ) (a b : Fin D × Fin D) :
    ((schmidtLeft A L)ᴴ * schmidtLeft A L) a b
      = ((transferMap A ^ L) (Matrix.single b.2 a.2 1)) b.1 a.1 := by
  rw [Matrix.mul_apply, transferMap_pow_apply', Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, schmidtLeft, Matrix.of_apply,
    Matrix.single_apply, RCLike.star_def, mul_ite, mul_one, mul_zero, ite_and, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- **The left Gram is block-size independent for a renormalization fixed point.**
Idempotence of `transferMap A` collapses its positive powers, so the
operator-Schmidt left Gram of an `L`-block agrees with the single-site one for
every `L ≥ 1`. This is the algebraic core of area-law saturation. -/
theorem schmidtLeft_gram_eq_of_isRFP (A : MPSTensor d D) (hRFP : IsRFP A)
    {L : ℕ} (hL : 1 ≤ L) :
    (schmidtLeft A L)ᴴ * schmidtLeft A L = (schmidtLeft A 1)ᴴ * schmidtLeft A 1 := by
  have hIdem : IsIdempotentElem (transferMap A) := hRFP
  ext a b
  rw [schmidtLeft_gram_apply, schmidtLeft_gram_apply,
    hIdem.pow_eq (by omega : L ≠ 0), pow_one]

/-- The operator-Schmidt **right factor** of an `M`-spin complement block: the
`D² × (d^M)` matrix recording the bond-indexed entries of `A^w` with the two
bonds swapped, as in the wavefunction factorization `schmidtMat_eq_mul`. -/
noncomputable def schmidtRight (A : MPSTensor d D) (M : ℕ) :
    Matrix (Fin D × Fin D) (Fin M → Fin d) ℂ :=
  Matrix.of (fun p w => (evalWord A (List.ofFn w)) p.2 p.1)

/-- **Right Gram = transfer-map power on a matrix unit** (complement analogue of
`schmidtLeft_gram_apply`). -/
theorem schmidtRight_gram_apply (A : MPSTensor d D) (M : ℕ) (p q : Fin D × Fin D) :
    (schmidtRight A M * (schmidtRight A M)ᴴ) p q
      = ((transferMap A ^ M) (Matrix.single p.1 q.1 1)) p.2 q.2 := by
  rw [Matrix.mul_apply, transferMap_pow_apply', Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, schmidtRight, Matrix.of_apply,
    Matrix.single_apply, RCLike.star_def, mul_ite, mul_one, mul_zero, ite_and, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **The right Gram is block-size independent for a renormalization fixed point.**
The complement analogue of `schmidtLeft_gram_eq_of_isRFP`. -/
theorem schmidtRight_gram_eq_of_isRFP (A : MPSTensor d D) (hRFP : IsRFP A)
    {M : ℕ} (hM : 1 ≤ M) :
    schmidtRight A M * (schmidtRight A M)ᴴ = schmidtRight A 1 * (schmidtRight A 1)ᴴ := by
  have hIdem : IsIdempotentElem (transferMap A) := hRFP
  ext p q
  rw [schmidtRight_gram_apply, schmidtRight_gram_apply,
    hIdem.pow_eq (by omega : M ≠ 0), pow_one]

/-- The wavefunction matrix factors as `schmidtLeft · schmidtRight` through the
`D × D` bond pair: the operator-Schmidt factorization of `schmidtMat_eq_mul`,
phrased with the named left and right factors. -/
theorem schmidtMat_eq_schmidtLeft_mul_schmidtRight (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) :
    schmidtMat A N L hL = schmidtLeft A L * schmidtRight A (N - L) :=
  schmidtMat_eq_mul A N L hL

/-- **The block entropy is the entropy of the bond environment.** The pure block
entropy `S_L` equals the `negMulLog ∘ Re` charpoly-root sum of the `D²×D²`
*environment matrix* `c · (R Rᴴ)(Lᴴ L)`, where `R = schmidtRight A (N-L)`,
`L = schmidtLeft A L`, and `c = (tr σ^{(N)})⁻¹`. Cyclicity of the spectrum
(`charpoly_roots_negMulLog_re_mul_comm`) moves the `d^L`-dimensional reduced state
onto this bond-indexed core. -/
theorem pureBlockEntropy_eq_env_charpoly (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) :
    pureBlockEntropy A N L hL
      = (((Matrix.trace (pureState A N))⁻¹ •
            ((schmidtRight A (N - L) * (schmidtRight A (N - L))ᴴ)
              * ((schmidtLeft A L)ᴴ * schmidtLeft A L))).charpoly.roots.map
          (fun z : ℂ => Real.negMulLog z.re)).sum := by
  have hρ : reducedPureBlockState A N L hL
      = ((Matrix.trace (pureState A N))⁻¹ • schmidtLeft A L)
        * (schmidtRight A (N - L) * (schmidtRight A (N - L))ᴴ * (schmidtLeft A L)ᴴ) := by
    rw [reducedPureBlockState_eq_gram, schmidtMat_eq_schmidtLeft_mul_schmidtRight A N L hL,
      Matrix.conjTranspose_mul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
  have hcyc : (schmidtRight A (N - L) * (schmidtRight A (N - L))ᴴ * (schmidtLeft A L)ᴴ)
        * ((Matrix.trace (pureState A N))⁻¹ • schmidtLeft A L)
      = (Matrix.trace (pureState A N))⁻¹ •
          ((schmidtRight A (N - L) * (schmidtRight A (N - L))ᴴ)
            * ((schmidtLeft A L)ᴴ * schmidtLeft A L)) := by
    rw [Matrix.mul_smul]
    congr 1
    simp only [Matrix.mul_assoc]
  rw [pureBlockEntropy, vonNeumannEntropy_eq_charpoly_roots, hρ,
    charpoly_roots_negMulLog_re_mul_comm, hcyc]

/-- **A renormalization fixed point saturates the area law.** For a pure-state
renormalization fixed point the operator-Schmidt Gram matrices collapse to their
single-site values, so the `D²×D²` bond-environment matrix governing the block
spectrum is block-size independent. The block entropy is therefore constant in
the block size: the area law is saturated.

Source: arXiv:1606.00608, Section 3 (pure-state area law, line 599);
blueprint `thm:rfp-saturates-area-law`. -/
theorem isSAL_of_isRFP (A : MPSTensor d D) (hRFP : IsRFP A) : IsSAL A := by
  intro N L hL1 hLlt
  rw [pureBlockEntropy_eq_env_charpoly, pureBlockEntropy_eq_env_charpoly,
    schmidtRight_gram_eq_of_isRFP A hRFP (show 1 ≤ N - L by omega),
    schmidtLeft_gram_eq_of_isRFP A hRFP hL1,
    schmidtRight_gram_eq_of_isRFP A hRFP (show 1 ≤ N - (L + 1) by omega),
    schmidtLeft_gram_eq_of_isRFP A hRFP (show 1 ≤ L + 1 by omega)]

end MPSTensor
