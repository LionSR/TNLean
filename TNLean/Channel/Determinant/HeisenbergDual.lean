/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Determinant.HilbertSchmidt
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.Schwarz.MultiplicativeDomainFull

/-!
# Heisenberg-dual multiplicativity from determinant saturation

This file presents the Kadison--Schwarz trace-summing argument in the Heisenberg
picture used in the forward direction of Wolf Theorem 6.1(2).

Starting from a Kraus representation of a CPTP map `T` with `‖channelDet T‖ = 1`,
we show that the Heisenberg dual has determinant of modulus `1`, that equality
holds in Kadison--Schwarz on the standard matrix basis, and hence that each Kraus
operator commutes with the Heisenberg dual on all of `M_d(ℂ)`. The conclusion is
that the Heisenberg dual is multiplicative.

## Main statements

* `ChannelDeterminant.heisenberg_dual_multiplicative` — determinant
  saturation forces the Heisenberg dual to be multiplicative on all matrices.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.1.1][Wolf2012QChannels]

## Tags

quantum channel, Heisenberg dual, Kadison-Schwarz, multiplicative domain
-/
open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker Matrix.Norms.Frobenius
open Matrix

variable {d : ℕ}

/-- The ambient matrix algebra `M_d(ℂ)`. -/
private abbrev MatrixAlg (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Endomorphisms of `M_d(ℂ)`. -/
private abbrev MatrixEnd (d : ℕ) := MatrixAlg d →ₗ[ℂ] MatrixAlg d

/-- Index type for the standard basis of `M_d(ℂ)`.

We use `Fin d × Fin d × Unit`, which has cardinality $d^2$. -/
private abbrev MatrixBasisIndex (d : ℕ) := Fin d × Fin d × Unit

/-- The standard basis of `M_d(ℂ)` coming from matrix units. -/
private noncomputable def matrixSpaceBasis (d : ℕ) :
    Module.Basis (MatrixBasisIndex d) ℂ (MatrixAlg d) :=
  Module.Basis.matrix (Fin d) (Fin d) (Module.Basis.singleton Unit ℂ)

section WolfStatements

variable {T : MatrixEnd d}

namespace ChannelDeterminant

private theorem heisenberg_dual_det_eq_one [NeZero d]
    {T : MatrixEnd d} (hdet : ‖channelDet T‖ = 1)
    {r : ℕ} (K : Fin r → MatrixAlg d) (hK : ∀ X, T X = ∑ i, K i * X * (K i)ᴴ)
    (Td : MatrixEnd d) (hTd : ∀ X, Td X = ∑ i : Fin r, (K i)ᴴ * X * K i) :
    ‖channelDet Td‖ = 1 := by
  let b : Module.Basis (Fin d × Fin d) ℂ (MatrixAlg d) :=
    Matrix.stdBasis ℂ (Fin d) (Fin d)
  have hAdj : ∀ ρ X : MatrixAlg d,
      Matrix.trace (ρ * T X) = Matrix.trace (Td ρ * X) := by
    intro ρ X
    simpa only [hK, Matrix.mul_assoc, hTd, Kraus.map, Kraus.adjointMap] using
      (Kraus.trace_mul_map_eq_trace_adjointMap_mul (K := K) ρ X)
  have hT_star : ∀ X : MatrixAlg d, T Xᴴ = (T X)ᴴ := by
    intro X
    simp only [hK, Matrix.mul_assoc, conjTranspose_sum, conjTranspose_mul,
      conjTranspose_conjTranspose]
  have hmat : LinearMap.toMatrix b b Td = (LinearMap.toMatrix b b T)ᴴ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix_apply, b, RCLike.star_def]
    have hcoef : (Td (Matrix.stdBasis ℂ (Fin d) (Fin d) j)) i.1 i.2 =
        star ((T (Matrix.stdBasis ℂ (Fin d) (Fin d) i)) j.1 j.2) := by
      calc
        (Td (Matrix.stdBasis ℂ (Fin d) (Fin d) j)) i.1 i.2
            = Matrix.trace (Td (Matrix.stdBasis ℂ (Fin d) (Fin d) j) *
                (Matrix.stdBasis ℂ (Fin d) (Fin d) i)ᴴ) := by
                  rcases i with ⟨a, b⟩
                  simp only [stdBasis_eq_single, conjTranspose_single, star_one,
                    trace_mul_single, MulOpposite.op_one, one_smul]
        _ = Matrix.trace (Matrix.stdBasis ℂ (Fin d) (Fin d) j *
              T ((Matrix.stdBasis ℂ (Fin d) (Fin d) i)ᴴ)) := by
              simpa only using (hAdj (Matrix.stdBasis ℂ (Fin d) (Fin d) j)
                ((Matrix.stdBasis ℂ (Fin d) (Fin d) i)ᴴ)).symm
        _ = Matrix.trace (Matrix.stdBasis ℂ (Fin d) (Fin d) j *
              (T (Matrix.stdBasis ℂ (Fin d) (Fin d) i))ᴴ) := by rw [hT_star]
        _ = star (Matrix.trace (T (Matrix.stdBasis ℂ (Fin d) (Fin d) i) *
              (Matrix.stdBasis ℂ (Fin d) (Fin d) j)ᴴ)) := by
              rw [← Matrix.trace_conjTranspose]
              simp only [conjTranspose_mul, conjTranspose_conjTranspose]
        _ = star ((T (Matrix.stdBasis ℂ (Fin d) (Fin d) i)) j.1 j.2) := by
              rcases j with ⟨c, d⟩
              simp only [stdBasis_eq_single, conjTranspose_single, star_one,
                trace_mul_single, MulOpposite.op_one, one_smul, RCLike.star_def]
    simpa only [stdBasis, Module.Basis.map_repr, Module.Basis.map_apply,
      Module.Basis.coe_reindex, Function.comp_apply, Equiv.sigmaEquivProd_symm_apply,
      Pi.basis_apply, Pi.basisFun_apply, coe_ofLinearEquiv, LinearEquiv.trans_apply,
      coe_ofLinearEquiv_symm, Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
      Pi.basis_repr, Pi.basisFun_repr, of_symm_apply, RCLike.star_def] using hcoef
  calc
    ‖channelDet Td‖ = ‖LinearMap.det Td‖ := by rw [channelDet_eq_linearMap_det]
    _ = ‖Matrix.det (LinearMap.toMatrix b b Td)‖ := by
          rw [← LinearMap.det_toMatrix (b := b) (f := Td)]
    _ = ‖Matrix.det ((LinearMap.toMatrix b b T)ᴴ)‖ := by rw [hmat]
    _ = ‖star (Matrix.det (LinearMap.toMatrix b b T))‖ := by
          rw [Matrix.det_conjTranspose]
    _ = ‖Matrix.det (LinearMap.toMatrix b b T)‖ := by
          simp only [LinearMap.det_toMatrix, RCLike.star_def, RCLike.norm_conj]
    _ = ‖LinearMap.det T‖ := by rw [LinearMap.det_toMatrix (b := b) (f := T)]
    _ = ‖channelDet T‖ := by rw [← channelDet_eq_linearMap_det]
    _ = 1 := hdet

private theorem heisenberg_dual_ks_eq_stdBasis [NeZero d]
    {T : MatrixEnd d} (hdet : ‖channelDet T‖ = 1)
    {r : ℕ} (K : Fin r → MatrixAlg d) (hK : ∀ X, T X = ∑ i, K i * X * (K i)ᴴ)
    (hK_tp : ∑ i : Fin r, (K i)ᴴ * K i = 1)
    (Td : MatrixEnd d) (hTd : ∀ X, Td X = ∑ i : Fin r, (K i)ᴴ * X * K i) :
    ∀ ij : Fin d × Fin d,
      Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
        (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) =
      Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
        (Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ := by
  let e : Fin d × Fin d → MatrixAlg d := Matrix.stdBasis ℂ (Fin d) (Fin d)
  set L : Fin r → MatrixAlg d := fun i => (K i)ᴴ with hL_def
  have hTd_kraus : ∀ X, Td X = KadisonSchwarz.krausMap L X := by
    intro X
    simp only [KadisonSchwarz.krausMap, hL_def, hTd, conjTranspose_conjTranspose]
  have hL_unital : KadisonSchwarz.IsUnitalKraus L := by
    change ∑ i, (K i)ᴴ * ((K i)ᴴ)ᴴ = 1
    simp only [conjTranspose_conjTranspose, hK_tp]
  have hdet_Td : ‖channelDet Td‖ = 1 :=
    heisenberg_dual_det_eq_one (d := d) hdet K hK Td hTd
  have hgap_psd : ∀ ij : Fin d × Fin d,
      (Td (e ij * (e ij)ᴴ) - Td (e ij) * (Td (e ij))ᴴ).PosSemidef := by
    intro ij
    have h := KadisonSchwarz.kadison_schwarz L hL_unital (e ij)ᴴ
    simp only [conjTranspose_conjTranspose, KadisonSchwarz.krausMap_conjTranspose] at h
    simpa only [hTd_kraus] using h
  have hgap_trace_nonneg : ∀ ij : Fin d × Fin d,
      0 ≤ (Matrix.trace (Td (e ij * (e ij)ᴴ) - Td (e ij) * (Td (e ij))ᴴ)).re := by
    intro ij
    exact (Complex.le_def.mp (hgap_psd ij).trace_nonneg).1
  have hgap_trace_sum_le : ∑ ij : Fin d × Fin d,
      (Matrix.trace (Td (e ij * (e ij)ᴴ) - Td (e ij) * (Td (e ij))ᴴ)).re ≤ 0 := by
    have hTd_one : Td 1 = 1 := by
      rw [hTd]
      simpa only [mul_one] using hK_tp
    have hfirstC : ∑ ij : Fin d × Fin d, Matrix.trace (Td (e ij * (e ij)ᴴ)) = (d : ℂ) * d := by
      calc
        ∑ ij : Fin d × Fin d, Matrix.trace (Td (e ij * (e ij)ᴴ))
            = Matrix.trace (Td (∑ ij : Fin d × Fin d, e ij * (e ij)ᴴ)) := by
                rw [← Matrix.trace_sum, ← map_sum]
        _ = Matrix.trace (Td ((d : ℂ) • (1 : MatrixAlg d))) := by
              rw [show (∑ ij : Fin d × Fin d, e ij * (e ij)ᴴ) =
                  (d : ℂ) • (1 : MatrixAlg d) by
                simpa only [e] using sum_stdBasis_mul_conjTranspose (d := d)]
        _ = Matrix.trace ((d : ℂ) • Td (1 : MatrixAlg d)) := by
              simp only [map_smul, trace_smul, smul_eq_mul]
        _ = Matrix.trace ((d : ℂ) • (1 : MatrixAlg d)) := by rw [hTd_one]
        _ = (d : ℂ) * d := by
              simp only [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    have hfirst : ∑ ij : Fin d × Fin d, (Matrix.trace (Td (e ij * (e ij)ᴴ))).re = (d : ℝ) ^ 2 := by
      rw [← Complex.re_sum, hfirstC]
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero,
        sub_zero, pow_two]
    have hsecond_eq : ∑ ij : Fin d × Fin d, (Matrix.trace (Td (e ij) * (Td (e ij))ᴴ)).re =
        ∑ ij : Fin d × Fin d, (Matrix.trace ((Td (e ij))ᴴ * Td (e ij))).re := by
      refine Finset.sum_congr rfl ?_
      intro ij _
      have hcyc (X : MatrixAlg d) : Matrix.trace (X * Xᴴ) = Matrix.trace (Xᴴ * X) := by
        simpa only [mul_one] using (Matrix.trace_mul_cycle X (1 : MatrixAlg d) Xᴴ)
      rw [hcyc]
    have hsecond_ge : (d : ℝ) ^ 2 ≤ ∑ ij : Fin d × Fin d,
        (Matrix.trace (Td (e ij) * (Td (e ij))ᴴ)).re := by
      rw [hsecond_eq]
      simpa only using channelDet_norm_one_hs_norm_ge (d := d) Td hdet_Td
    have hsum_eq : ∑ ij : Fin d × Fin d,
        (Matrix.trace (Td (e ij * (e ij)ᴴ) - Td (e ij) * (Td (e ij))ᴴ)).re =
          (∑ ij : Fin d × Fin d, (Matrix.trace (Td (e ij * (e ij)ᴴ))).re) -
          (∑ ij : Fin d × Fin d, (Matrix.trace (Td (e ij) * (Td (e ij))ᴴ)).re) := by
      simp only [Matrix.trace_sub, Complex.sub_re, Finset.sum_sub_distrib]
    rw [hsum_eq]
    nlinarith [hfirst, hsecond_ge]
  have hgap_trace_zero : ∀ ij : Fin d × Fin d,
      (Matrix.trace (Td (e ij * (e ij)ᴴ) - Td (e ij) * (Td (e ij))ᴴ)).re = 0 :=
    eq_zero_of_nonneg_of_sum_le_zero _ hgap_trace_nonneg hgap_trace_sum_le
  intro ij
  have hpsd := hgap_psd ij
  have htr_re := hgap_trace_zero ij
  have htr_im := (Complex.le_def.mp hpsd.trace_nonneg).2.symm
  have htr : Matrix.trace (Td (e ij * (e ij)ᴴ) - Td (e ij) * (Td (e ij))ᴴ) = 0 :=
    Complex.ext htr_re htr_im
  exact sub_eq_zero.mp (hpsd.trace_eq_zero_iff.mp htr)

private theorem heisenberg_dual_basis_commute [NeZero d]
    {r : ℕ} (K : Fin r → MatrixAlg d) (hK_tp : ∑ i : Fin r, (K i)ᴴ * K i = 1)
    (Td : MatrixEnd d) (hTd : ∀ X, Td X = ∑ i : Fin r, (K i)ᴴ * X * K i)
    (hks_stdBasis : ∀ ij : Fin d × Fin d,
      Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij *
        (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)ᴴ) =
      Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) *
        (Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij))ᴴ) :
    ∀ (ij : Fin d × Fin d) (a : Fin r),
      Matrix.stdBasis ℂ (Fin d) (Fin d) ij * K a =
        K a * Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij) := by
  -- TODO(refactor/513): thread the shared `L`/`hTd_kraus`/`hL_unital` setup
  -- through these helpers instead of rebuilding it here and in
  -- `heisenberg_dual_ks_eq_stdBasis`.
  set L : Fin r → MatrixAlg d := fun i => (K i)ᴴ with hL_def
  have hTd_kraus : ∀ X, Td X = KadisonSchwarz.krausMap L X := by
    intro X
    simp only [KadisonSchwarz.krausMap, hL_def, hTd, conjTranspose_conjTranspose]
  have hL_unital : KadisonSchwarz.IsUnitalKraus L := by
    change ∑ i, (K i)ᴴ * ((K i)ᴴ)ᴴ = 1
    simp only [conjTranspose_conjTranspose, hK_tp]
  intro ij
  let e : MatrixAlg d := Matrix.stdBasis ℂ (Fin d) (Fin d) ij
  let es : MatrixAlg d := Matrix.stdBasis ℂ (Fin d) (Fin d) (ij.2, ij.1)
  have hes : es = eᴴ := by
    exact (stdBasis_conjTranspose_eq_swap (d := d) ij.1 ij.2).symm
  have hTd_es : Td es = (Td e)ᴴ := by
    calc
      Td es = KadisonSchwarz.krausMap L es := hTd_kraus es
      _ = (KadisonSchwarz.krausMap L e)ᴴ := by rw [hes, KadisonSchwarz.krausMap_conjTranspose]
      _ = (Td e)ᴴ := by rw [hTd_kraus]
  have hks_basis : Td (eᴴ * e) = (Td e)ᴴ * Td e := by
    calc
      Td (eᴴ * e) = Td (es * esᴴ) := by
        rw [hes]
        simp only [conjTranspose_conjTranspose]
      _ = Td es * (Td es)ᴴ := hks_stdBasis (ij.2, ij.1)
      _ = (Td e)ᴴ * Td e := by
        rw [hTd_es]
        simp only [conjTranspose_conjTranspose]
  have hkseq_kraus : KadisonSchwarz.krausMap L (eᴴ * e) =
      (KadisonSchwarz.krausMap L e)ᴴ * KadisonSchwarz.krausMap L e := by
    simpa only [hTd_kraus] using hks_basis
  have h := KadisonSchwarz.kraus_commute_of_ks_equality
    (K := L) hL_unital (X := e) hkseq_kraus
  intro a
  have ha := h a
  simp only [hL_def, conjTranspose_conjTranspose] at ha
  simpa only [hTd_kraus] using ha

private theorem heisenberg_dual_commute
    {r : ℕ} (K : Fin r → MatrixAlg d) (Td : MatrixEnd d)
    (hbasis_commute : ∀ (ij : Fin d × Fin d) (a : Fin r),
      Matrix.stdBasis ℂ (Fin d) (Fin d) ij * K a =
        K a * Td (Matrix.stdBasis ℂ (Fin d) (Fin d) ij)) :
    ∀ (X : MatrixAlg d) (a : Fin r), X * K a = K a * Td X := by
  intro X a
  set F : MatrixEnd d :=
    LinearMap.mulRight ℂ (K a) - (LinearMap.mulLeft ℂ (K a)).comp Td
  have hF_apply : ∀ Y, F Y = Y * K a - K a * Td Y := fun Y => by
    simp only [LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulLeft_apply, F]
  have hF_zero : F = 0 := by
    apply Module.Basis.ext (matrixSpaceBasis d)
    intro ⟨i, j, u⟩
    simp only [LinearMap.zero_apply]
    rw [hF_apply]
    obtain rfl : u = () := Subsingleton.elim u ()
    have hbasis_eq : matrixSpaceBasis d (i, j, ()) =
        Matrix.stdBasis ℂ (Fin d) (Fin d) (i, j) := by
      simp only [matrixSpaceBasis, Module.Basis.matrix_apply,
        Module.Basis.singleton_apply, Matrix.stdBasis_eq_single]
    rw [hbasis_eq]
    exact sub_eq_zero.mpr (hbasis_commute (i, j) a)
  have hFX : X * K a - K a * Td X = 0 := by
    simpa only [hF_apply X, LinearMap.zero_apply] using
      congrArg (fun G : MatrixEnd d => G X) hF_zero
  exact sub_eq_zero.mp hFX

/-- If a CPTP map saturates the determinant bound, then its Heisenberg dual
is multiplicative on all of `M_d(ℂ)`. This is the analytic core of
Wolf Theorem 6.1(2). -/
theorem heisenberg_dual_multiplicative [NeZero d]
    {T : MatrixEnd d} (_hT : IsChannel T) (hdet : ‖channelDet T‖ = 1)
    (_hall : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → ‖μ‖ = 1)
    {r : ℕ} (K : Fin r → MatrixAlg d) (hK : ∀ X, T X = ∑ i, K i * X * (K i)ᴴ)
    (hK_tp : ∑ i : Fin r, (K i)ᴴ * K i = 1)
    (Td : MatrixEnd d) (hTd : ∀ X, Td X = ∑ i : Fin r, (K i)ᴴ * X * K i) :
    ∀ M N : MatrixAlg d, Td (M * N) = Td M * Td N := by
  have hks_stdBasis := heisenberg_dual_ks_eq_stdBasis (d := d) hdet K hK hK_tp Td hTd
  have hbasis_commute := heisenberg_dual_basis_commute (d := d) K hK_tp Td hTd hks_stdBasis
  have hcommute := heisenberg_dual_commute (d := d) K Td hbasis_commute
  intro M N
  simp only [hTd]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro a _
  have hNKa := hcommute N a
  calc (K a)ᴴ * (M * N) * K a
      = (K a)ᴴ * M * (N * K a) := by simp only [Matrix.mul_assoc]
    _ = (K a)ᴴ * M * (K a * Td N) := by rw [hNKa]
    _ = (K a)ᴴ * M * K a * Td N := by simp only [Matrix.mul_assoc]
    _ = (K a)ᴴ * M * K a * ∑ b : Fin r, (K b)ᴴ * N * K b := by
        rw [show Td N = ∑ b : Fin r, (K b)ᴴ * N * K b from hTd N]

end ChannelDeterminant

end WolfStatements
