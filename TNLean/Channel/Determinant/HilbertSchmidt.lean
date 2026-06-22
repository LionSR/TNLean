/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Determinant.Bound
import TNLean.Algebra.MatrixAux
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Hilbert--Schmidt auxiliary lemmas for determinant saturation

This file collects the auxiliary results used in the forward direction of Wolf
Theorem 6.1(2) before the Heisenberg-dual multiplicativity argument proper.

The main ingredients are: determinant saturation forces every eigenvalue of a
CPTP map to have modulus $1$; the standard matrix units give explicit
Hilbert--Schmidt norm computations; and an AM--GM argument upgrades
`‖det T‖ = 1` to a lower bound on the Hilbert--Schmidt norm of the channel.

## Main statements

* `ChannelDeterminant.Internal.channel_all_eigenvalues_norm_one` — determinant
  saturation forces every eigenvalue of a CPTP map to lie on the unit circle.
* `ChannelDeterminant.Internal.stdBasis_conjTranspose_eq_swap` — conjugate
  transpose swaps the indices of a matrix-unit basis element.
* `ChannelDeterminant.Internal.sum_stdBasis_mul_conjTranspose` — the standard
  basis satisfies `∑_{ij} E_{ij} E_{ij}^† = d • 1`.
* `ChannelDeterminant.Internal.channelDet_norm_one_hs_norm_ge` — determinant
  saturation gives the AM--GM lower bound on the Hilbert--Schmidt norm.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1.1][Wolf2012QChannels]

## Tags

quantum channel, determinant, Hilbert-Schmidt norm, standard basis, AM-GM
-/
open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker Matrix.Norms.Frobenius
open Matrix
open ChannelDeterminant.Internal

variable {d : ℕ}

section WolfStatements

variable {T : MatrixEnd d}

/-! ### Auxiliary lemmas for the forward direction of Wolf Theorem 6.1(2) -/

namespace ChannelDeterminant
namespace Internal

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

/-- Conjugate transpose swaps the indices of a matrix-unit basis element. -/
theorem stdBasis_conjTranspose_eq_swap (i j : Fin d) :
    (Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j))ᴴ =
      Matrix.stdBasis ℂ (Fin d) (Fin d) (j, i) := by
  rw [Matrix.stdBasis_eq_single, Matrix.stdBasis_eq_single, Matrix.conjTranspose_single]
  simp only [star_one]

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
            simp [Matrix.stdBasis_eq_single]
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
    _ = (d : ℂ) • (1 : MatrixAlg d) := by rw [Matrix.sum_single_one]

private lemma matrix_det_norm_one_trace_conjTranspose_mul_self_ge [NeZero d]
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hdet : ‖A.det‖ = 1) :
    (d : ℝ) ^ 2 ≤ (Matrix.trace (Aᴴ * A)).re := by
  have h := Matrix.card_le_trace_conjTranspose_mul_self_re_of_det_norm_eq_one A hdet
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using h

/-- **AM-GM lower bound on Hilbert-Schmidt norm via determinant.**

For a linear endomorphism `Φ` of the matrix algebra with `‖det Φ‖ = 1`,
the Hilbert-Schmidt norm satisfies `‖Φ‖²_HS ≥ d²`. This follows from AM-GM
on the singular values: their product is `|det Φ| = 1`, so their squared sum
(= the HS norm) is at least `d²`.

This is the analytic ingredient for Wolf Theorem 6.1(2). -/
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
              simp only [stdBasis, Matrix.trace_conjTranspose_mul_self_re_eq_sum_norm_sq,
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
              (Matrix.trace_conjTranspose_mul_self_re_eq_sum_norm_sq
                (A := Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).symm
  calc
    (d : ℝ) ^ 2 ≤ (Matrix.trace (Aᴴ * A)).re :=
      matrix_det_norm_one_trace_conjTranspose_mul_self_ge (d := d) A hA_det
    _ = ∑ ij : Fin d × Fin d,
          (Matrix.trace ((Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ *
            Φ (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))).re := hA_hs


end Internal
end ChannelDeterminant

end WolfStatements
