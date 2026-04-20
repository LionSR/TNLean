/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Determinant.Bound

/-!
# Hilbert--Schmidt helper lemmas for determinant saturation

This file collects the auxiliary results used in the forward direction of Wolf
Theorem 6.1(2) before the Heisenberg-dual multiplicativity argument proper.

The main ingredients are: determinant saturation forces every eigenvalue of a
CPTP map to have modulus $1$; the standard matrix units give explicit
Hilbert--Schmidt norm computations; and an AM--GM argument upgrades
`‖det T‖ = 1` to a lower bound on the Hilbert--Schmidt norm of the channel.

## Main statements

* `ChannelDeterminant.channel_all_eigenvalues_norm_one` — determinant
  saturation forces every eigenvalue of a CPTP map to lie on the unit circle.
* `ChannelDeterminant.stdBasis_conjTranspose_eq_swap` — conjugate transpose
  swaps the indices of a matrix-unit basis element.
* `ChannelDeterminant.sum_stdBasis_mul_conjTranspose` — the standard basis
  satisfies `∑_{ij} E_{ij} E_{ij}^† = d • 1`.
* `ChannelDeterminant.eq_zero_of_nonneg_of_sum_le_zero` — a finite nonnegative
  family with total sum at most `0` vanishes termwise.
* `ChannelDeterminant.channelDet_norm_one_hs_norm_ge` — determinant
  saturation gives the AM--GM lower bound on the Hilbert--Schmidt norm.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.1.1][Wolf2012QChannels]

## Tags

quantum channel, determinant, Hilbert-Schmidt norm, standard basis, AM-GM
-/
open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker Matrix.Norms.Frobenius
open Matrix

variable {d : ℕ}

open TNLean.Channel.Determinant.Internal

section WolfStatements

variable {T : MatrixEnd d}

/-! ### Helper lemmas for the forward direction of Wolf Thm 6.1(2) -/

namespace ChannelDeterminant

/-- Product of norms = 1 with each factor ≤ 1 implies each factor = 1. -/
private lemma norm_eq_one_of_prod_norm_eq_one
    (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ‖ ≤ 1) (hprod : ‖s.prod‖ = 1) :
    ∀ μ ∈ s, ‖μ‖ = 1 := by
  induction s using Multiset.induction with
  | empty => intro μ hμ; simp only [Multiset.notMem_zero] at hμ
  | @cons a s ih =>
    intro μ hμ
    have ha : ‖a‖ ≤ 1 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ ν ∈ s, ‖ν‖ ≤ 1 := fun ν hν => hs ν (Multiset.mem_cons_of_mem hν)
    rw [Multiset.prod_cons, norm_mul] at hprod
    have hprod_s_le : ‖s.prod‖ ≤ 1 := norm_prod_le_one_of_forall_mem' s hs'
    have ha_eq : ‖a‖ = 1 := by nlinarith [norm_nonneg a, norm_nonneg s.prod]
    have hs_eq : ‖s.prod‖ = 1 := by nlinarith [norm_nonneg a]
    rcases Multiset.mem_cons.mp hμ with rfl | hμs
    · exact ha_eq
    · exact ih hs' hs_eq μ hμs

/-- For a CPTP map with `‖det T‖ = 1`, every eigenvalue has modulus exactly 1. -/
theorem channel_all_eigenvalues_norm_one [NeZero d]
    (hT : IsChannel T) (hdet : ‖channelDet T‖ = 1) :
    ∀ μ : ℂ, Module.End.HasEigenvalue T μ → ‖μ‖ = 1 := by
  let A : Matrix (MatrixBasisIndex d) (MatrixBasisIndex d) ℂ := channelMatrix T
  have hspectrum : spectrum ℂ A = spectrum ℂ T :=
    AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv (matrixSpaceBasis d)) T
  have hroot_le : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ 1 := by
    intro μ hμ
    exact IsChannel.eigenvalue_norm_le_one hT μ
      (Module.End.hasEigenvalue_iff_mem_spectrum.2
        (hspectrum ▸ Matrix.mem_spectrum_of_isRoot_charpoly
          ((Polynomial.mem_roots A.charpoly_monic.ne_zero).1 hμ)))
  have hprod_eq : ‖A.charpoly.roots.prod‖ = 1 := by
    have : ‖channelDet T‖ = ‖A.charpoly.roots.prod‖ := by
      change ‖A.det‖ = ‖A.charpoly.roots.prod‖
      rw [Matrix.det_eq_prod_roots_charpoly]
    rw [← this]; exact hdet
  have hroot_eq := norm_eq_one_of_prod_norm_eq_one _ hroot_le hprod_eq
  intro μ hμ_eig
  have hμ_specT : μ ∈ spectrum ℂ T := Module.End.hasEigenvalue_iff_mem_spectrum.1 hμ_eig
  have hμ_specA : μ ∈ spectrum ℂ A := hspectrum ▸ hμ_specT
  exact hroot_eq μ ((Polynomial.mem_roots A.charpoly_monic.ne_zero).2
    ((Matrix.mem_spectrum_iff_isRoot_charpoly).1 hμ_specA))

private theorem stdBasis_conjTranspose_mul_self (i j : Fin d) :
    (Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j))ᴴ *
        Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j) =
      Matrix.single j j (1 : ℂ) := by
  ext a b
  rw [Matrix.stdBasis_eq_single, Matrix.conjTranspose_single]
  by_cases hja : j = a
  · by_cases hjb : j = b
    · subst hja; subst hjb
      simp only [single, star_one, mul_apply, of_apply, true_and, and_true, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, and_self]
    · have hab : a ≠ b := by simpa only [ne_eq, hja] using hjb
      simp only [single, hja, star_one, mul_apply, of_apply, true_and, hab,
        and_false, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  · simp only [single, star_one, mul_apply, of_apply, hja, false_and, ↓reduceIte,
      mul_ite, mul_one, mul_zero, ite_self, Finset.sum_const_zero]

/-- Conjugate transpose swaps the indices of a matrix-unit basis element. -/
theorem stdBasis_conjTranspose_eq_swap (i j : Fin d) :
    (Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j))ᴴ =
      Matrix.stdBasis ℂ (Fin d) (Fin d) (j, i) := by
  rw [Matrix.stdBasis_eq_single, Matrix.stdBasis_eq_single, Matrix.conjTranspose_single]
  simp only [star_one]

private theorem stdBasis_mul_conjTranspose_self (i j : Fin d) :
    Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j) *
        (Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j))ᴴ =
      Matrix.single i i (1 : ℂ) := by
  simpa only [stdBasis_conjTranspose_eq_swap] using
    (stdBasis_conjTranspose_mul_self (d := d) (i := j) (j := i))

private theorem sum_single_diag_one :
    ∑ j : Fin d, Matrix.single j j (1 : ℂ) = (1 : MatrixAlg d) := by
  simpa only using (Matrix.sum_single_one (m := Fin d) (α := ℂ))

/-- Summing `E_{ij} E_{ij}^†` over the standard matrix basis yields `d • 1`. -/
theorem sum_stdBasis_mul_conjTranspose :
    ∑ ij : Fin d × Fin d,
      Matrix.stdBasis ℂ (Fin d) (Fin d) ij * (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ =
        (d : ℂ) • (1 : MatrixAlg d) := by
  calc
    ∑ ij : Fin d × Fin d,
        Matrix.stdBasis ℂ (Fin d) (Fin d) ij * (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ =
          ∑ ij : Fin d × Fin d, Matrix.single ij.1 ij.1 (1 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro ij _
            rcases ij with ⟨i, j⟩
            simpa only using stdBasis_mul_conjTranspose_self (d := d) i j
    _ = ∑ i : Fin d, ∑ j : Fin d, Matrix.single i i (1 : ℂ) := by
          simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_single, nsmul_eq_mul, mul_one, Finset.univ_product_univ] using
            (Finset.sum_product' (s := (Finset.univ : Finset (Fin d)))
              (t := (Finset.univ : Finset (Fin d)))
              (f := fun i j => Matrix.single i i (1 : ℂ)))
    _ = ∑ i : Fin d, (d : ℂ) • Matrix.single i i (1 : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_single,
            nsmul_eq_mul, mul_one, smul_eq_mul]
    _ = (d : ℂ) • ∑ i : Fin d, Matrix.single i i (1 : ℂ) := by rw [Finset.smul_sum]
    _ = (d : ℂ) • (1 : MatrixAlg d) := by rw [sum_single_diag_one]

private theorem stdBasis_orthonormal_of_inner_eq_trace
    [NormedAddCommGroup (MatrixAlg d)] [InnerProductSpace ℂ (MatrixAlg d)]
    (hinner : ∀ X Y : MatrixAlg d, inner ℂ X Y = Matrix.trace (Y * Xᴴ)) :
    Orthonormal ℂ ⇑(Matrix.stdBasis ℂ (Fin d) (Fin d)) := by
  rw [orthonormal_iff_ite]
  intro a b
  rcases a with ⟨i, j⟩
  rcases b with ⟨k, l⟩
  rw [hinner, Matrix.stdBasis_eq_single, Matrix.stdBasis_eq_single, Matrix.conjTranspose_single]
  rw [Matrix.trace_mul_single]
  simp only [star_one, MulOpposite.op_one, single, of_apply, eq_comm, smul_ite,
    one_smul, smul_zero, Prod.mk.injEq]

/-- If a finite family of nonnegative reals has total sum at most `0`, then every term is `0`. -/
lemma eq_zero_of_nonneg_of_sum_le_zero {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i ≤ 0) :
    ∀ i, f i = 0 := by
  intro i
  have h1 : ∑ i, f i ≥ 0 := Finset.sum_nonneg (fun i _ => hf i)
  have h2 : ∑ i, f i = 0 := le_antisymm hsum h1
  have h3 := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf i) |>.mp h2
  exact h3 i (Finset.mem_univ i)

private lemma complex_star_mul_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [show star z = starRingEnd ℂ z from rfl, Complex.conj_mul',
    ← Complex.ofReal_pow]
  exact Complex.ofReal_re _

private lemma trace_conjTranspose_mul_self_re_eq_sum_sq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    (Matrix.trace (Aᴴ * A)).re = ∑ j, ∑ i, ‖A i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro i _
  simpa only [RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add] using complex_star_mul_re (A i j)

private lemma matrix_det_norm_one_trace_conjTranspose_mul_self_ge [NeZero d]
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hdet : ‖A.det‖ = 1) :
    (d : ℝ) ^ 2 ≤ (Matrix.trace (Aᴴ * A)).re := by
  let B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := Aᴴ * A
  have hBherm : B.IsHermitian := by
    simpa only using Matrix.isHermitian_conjTranspose_mul_self A
  have hBpsd : B.PosSemidef := by
    simpa only using Matrix.posSemidef_conjTranspose_mul_self A
  have hdetB : Matrix.det B = 1 := by
    change Matrix.det (Aᴴ * A) = 1
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    have hconj : star A.det * A.det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [show star A.det = starRingEnd ℂ A.det from rfl, ← Complex.ofReal_pow] using
        (Complex.conj_mul' A.det)
    rw [hconj, hdet]
    norm_num
  have hprod_eq : ∏ i, hBherm.eigenvalues i = 1 := by
    have h : Matrix.det B = ∏ i, (hBherm.eigenvalues i : ℂ) := hBherm.det_eq_prod_eigenvalues
    rw [hdetB] at h
    have h' : ((∏ i, hBherm.eigenvalues i : ℝ) : ℂ) = 1 := by
      simpa only [Complex.ofReal_prod] using h.symm
    exact_mod_cast h'
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hamgm : 1 ≤ (∑ i, hBherm.eigenvalues i) / ((d : ℝ) * d) := by
    have := Real.geom_mean_le_arith_mean (s := Finset.univ) (w := fun _ => (1 : ℝ))
      (z := fun i => hBherm.eigenvalues i)
      (by intro i hi; positivity)
      (by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_one, mul_self_pos,
          ne_eq, Nat.cast_eq_zero, NeZero.ne d, not_false_eq_true])
      (by intro i hi; simpa only using hBpsd.eigenvalues_nonneg i)
    simpa only [ge_iff_le, Real.rpow_one, hprod_eq, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_mul, mul_one, _root_.mul_inv_rev, Real.one_rpow, one_mul] using this
  have hmul_pos : 0 < (d : ℝ) * d := mul_pos hd_pos hd_pos
  have hsum_ge : (d : ℝ) * d ≤ ∑ i, hBherm.eigenvalues i :=
    (one_le_div hmul_pos).mp hamgm
  have htrace_eq : (Matrix.trace B).re = ∑ i, hBherm.eigenvalues i := by
    simpa only [Complex.coe_algebraMap, Complex.re_sum, Complex.ofReal_re] using
      congrArg Complex.re hBherm.trace_eq_sum_eigenvalues
  simpa only [pow_two, ge_iff_le] using hsum_ge.trans_eq htrace_eq.symm

/-- **AM-GM lower bound on Hilbert-Schmidt norm via determinant.**

For a linear endomorphism `Φ` of the matrix algebra with `‖det Φ‖ = 1`,
the Hilbert-Schmidt norm satisfies `‖Φ‖²_HS ≥ d²`. This follows from AM-GM
on the singular values: their product is `|det Φ| = 1`, so their squared sum
(= the HS norm) is at least `d²`.

This is the analytic ingredient for Wolf Thm 6.1(2). -/
lemma channelDet_norm_one_hs_norm_ge [NeZero d]
    (Φ : MatrixEnd d) (hdet_Φ : ‖channelDet Φ‖ = 1) :
    (d : ℝ) ^ 2 ≤ ∑ ij : Fin d × Fin d,
      (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
        Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := by
  let b : Module.Basis (Fin d × Fin d) ℂ (MatrixAlg d) :=
    Matrix.stdBasis ℂ (Fin d) (Fin d)
  let A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := LinearMap.toMatrix b b Φ
  have hA_det : ‖A.det‖ = 1 := by
    simpa only [A, b, LinearMap.det_toMatrix, channelDet_eq_linearMap_det] using hdet_Φ
  have hA_hs :
      (Matrix.trace (Aᴴ * A)).re = ∑ ij : Fin d × Fin d,
        (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
          Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := by
    calc
      (Matrix.trace (Aᴴ * A)).re =
          ∑ ij : Fin d × Fin d, ∑ kl : Fin d × Fin d,
            ‖(Φ (b ij)) kl.1 kl.2‖ ^ 2 := by
              simp only [stdBasis, trace_conjTranspose_mul_self_re_eq_sum_sq,
                LinearMap.toMatrix_apply, Module.Basis.map_repr, Module.Basis.map_apply,
                Module.Basis.coe_reindex, Function.comp_apply,
                Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, Pi.basisFun_apply,
                coe_ofLinearEquiv, LinearEquiv.trans_apply, coe_ofLinearEquiv_symm,
                Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply, Pi.basis_repr,
                Pi.basisFun_repr, of_symm_apply, A, b]
      _ = ∑ ij : Fin d × Fin d,
            (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
              Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := by
            refine Finset.sum_congr rfl ?_
            intro ij _
            have hsum_sq :
                ∑ kl : Fin d × Fin d,
                    ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) kl.1 kl.2‖ ^ 2 =
                  ∑ j : Fin d, ∑ i : Fin d,
                    ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) i j‖ ^ 2 := by
              calc
                ∑ kl : Fin d × Fin d,
                    ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) kl.1 kl.2‖ ^ 2
                    = ∑ i : Fin d, ∑ j : Fin d,
                        ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) i j‖ ^ 2 := by
                          simpa only [Finset.univ_product_univ] using
                            (Finset.sum_product'
                              (s := (Finset.univ : Finset (Fin d)))
                              (t := (Finset.univ : Finset (Fin d)))
                              (f := fun i j =>
                                ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) i j‖ ^ 2))
                _ = ∑ j : Fin d, ∑ i : Fin d,
                      ‖Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) i j‖ ^ 2 := by
                        rw [Finset.sum_comm]
            exact hsum_sq.trans
              (trace_conjTranspose_mul_self_re_eq_sum_sq
                (A := Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).symm
  calc
    (d : ℝ) ^ 2 ≤ (Matrix.trace (Aᴴ * A)).re :=
      matrix_det_norm_one_trace_conjTranspose_mul_self_ge (d := d) A hA_det
    _ = ∑ ij : Fin d × Fin d,
          (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
            Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := hA_hs


end ChannelDeterminant

end WolfStatements
