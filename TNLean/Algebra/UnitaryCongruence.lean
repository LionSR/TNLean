/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange

/-!
# Congruence factorizations of symmetric and skew-symmetric unitary matrices

The two branches of the finite spectral-projector construction in CPSV17, Lemma
`lemma:conjclass-normalform-continuous`, give congruence factorizations of symmetric and
skew-symmetric unitary matrices (arXiv:1703.09188, lines 1054--1083).

For the skew branch, the spectral projectors of a normal matrix are defined by the continuous
functional calculus applied to point indicators. Transposition pairs the projector at `λ` with
the one at `-λ`, which supplies the paired projectors consumed by
`Matrix.exists_skew_unitary_congruence_of_paired_projectors`. The two branches combine into
`Matrix.exists_unitary_congruence_normalForm`.
-/

open scoped Polynomial

noncomputable section

namespace Matrix

variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]

/-- Transpose commutes with evaluating a polynomial at a square matrix over a commutative
semiring. -/
theorem transpose_aeval (p : R[X]) (A : Matrix n n R) :
    ((Polynomial.aeval A) p).transpose = (Polynomial.aeval A.transpose) p := by
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Matrix.transpose_sum,
    Matrix.transpose_mul, Matrix.transpose_pow]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show ((algebraMap R (Matrix n n R)) (p.coeff i)).transpose =
      (algebraMap R (Matrix n n R)) (p.coeff i) by
    ext j k
    simp only [Matrix.transpose_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : j = k
    · subst k
      rfl
    · have hk : k ≠ j := Ne.symm h
      simp [h, hk]]
  exact (Algebra.commutes (p.coeff i) (A.transpose ^ i)).symm

variable {n : ℕ}

/-- A complex symmetric unitary matrix has a symmetric unitary square root.

This is the symmetric branch of CPSV17, Lemma `lemma:conjclass-normalform-continuous`
(arXiv:1703.09188, lines 1054--1064). -/
theorem exists_symmetric_unitary_squareRoot
    (x : Matrix (Fin n) (Fin n) ℂ)
    (hx : x ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hsym : x.transpose = x) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ,
      S.transpose = S ∧
      S ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      x = S.transpose * S := by
  let _ : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let _ : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let e := CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)
  let a := e x
  have ha_unitary : a ∈ unitary (CStarMatrix (Fin n) (Fin n) ℂ) := by
    change star a * a = 1 ∧ a * star a = 1
    constructor
    · change star (e x) * e x = 1
      rw [← StarHomClass.map_star e, ← map_mul e, ← map_one e]
      exact congrArg e (Matrix.mem_unitaryGroup_iff'.mp hx)
    · change e x * star (e x) = 1
      rw [← StarHomClass.map_star e, ← map_mul e, ← map_one e]
      exact congrArg e (Matrix.mem_unitaryGroup_iff.mp hx)
  have ha_normal : IsStarNormal a := isStarNormal_of_mem_unitary ha_unitary
  have hspec : (spectrum ℂ a).Finite := Matrix.finite_spectrum a
  have hsqrt_cont : ContinuousOn Complex.sqrt (spectrum ℂ a) := hspec.continuousOn _
  have hsqrt_sq (z : ℂ) : Complex.sqrt z * Complex.sqrt z = z := by
    change (z ^ (2 : ℂ)⁻¹) * (z ^ (2 : ℂ)⁻¹) = z
    simpa [pow_two] using Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)
  have hroot_sq :
      cfc (p := IsStarNormal) Complex.sqrt a * cfc (p := IsStarNormal) Complex.sqrt a = a := by
    rw [← cfc_mul (p := IsStarNormal) Complex.sqrt Complex.sqrt a hsqrt_cont hsqrt_cont]
    rw [cfc_congr (p := IsStarNormal) (g := fun z ↦ z) (fun z _ ↦ hsqrt_sq z),
      cfc_id' ℂ a ha_normal]
  have hroot_unitary :
      cfc (p := IsStarNormal) Complex.sqrt a ∈ unitary (CStarMatrix (Fin n) (Fin n) ℂ) := by
    rw [cfc_unitary_iff (p := IsStarNormal) Complex.sqrt a ha_normal hsqrt_cont]
    intro z hz
    have hz_unitary : z ∈ unitary ℂ := spectrum_subset_unitary_of_mem_unitary ha_unitary hz
    have hz_norm_sq : ‖z‖ * ‖z‖ = 1 := by
      have h := congrArg norm (Unitary.mem_iff_star_mul_self.mp hz_unitary)
      simpa [norm_mul] using h
    have hz_norm : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    have hsqrt_norm_sq : ‖Complex.sqrt z‖ * ‖Complex.sqrt z‖ = 1 := by
      have h := congrArg norm (hsqrt_sq z)
      simpa [norm_mul, hz_norm] using h
    have hsqrt_norm : ‖Complex.sqrt z‖ = 1 := by
      nlinarith [norm_nonneg (Complex.sqrt z)]
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hsqrt_norm]
    norm_num
  let q : ℂ[X] := (Lagrange.interpolate hspec.toFinset id) Complex.sqrt
  have hq_eval : Set.EqOn Complex.sqrt (fun z ↦ Polynomial.eval z q) (spectrum ℂ a) := by
    intro z hz
    symm
    exact Lagrange.eval_interpolate_at_node Complex.sqrt (Set.injOn_id _)
      (hspec.mem_toFinset.mpr hz)
  have hroot_poly :
      cfc (p := IsStarNormal) Complex.sqrt a = (Polynomial.aeval a) q := by
    rw [cfc_congr (p := IsStarNormal) hq_eval, cfc_polynomial q a ha_normal]
  let S : Matrix (Fin n) (Fin n) ℂ := (Polynomial.aeval x) q
  have hmapS : e S = cfc (p := IsStarNormal) Complex.sqrt a := by
    rw [hroot_poly]
    change e ((Polynomial.aeval x) q) = (Polynomial.aeval (e x)) q
    simp only [Polynomial.aeval_def]
    change e.toRingHom (Polynomial.eval₂ (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)) x q) = _
    rw [Polynomial.hom_eval₂]
    congr 1
  have hS_sq : S * S = x := by
    apply e.injective
    change e (S * S) = e x
    rw [map_mul e, hmapS]
    simpa [a] using hroot_sq
  have hS_unitary : S ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    apply e.injective
    change e (star S * S) = e 1
    rw [map_mul e, StarHomClass.map_star e, map_one e, hmapS]
    exact hroot_unitary.1
  have hS_symm : S.transpose = S := by
    change ((Polynomial.aeval x) q).transpose = (Polynomial.aeval x) q
    rw [transpose_aeval, hsym]
  exact ⟨S, hS_symm, hS_unitary, by simpa [hS_symm] using hS_sq.symm⟩

end Matrix

namespace Matrix

variable {ι κ m : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype m]

/-- Multiplication of sums weighted by a family of orthogonal idempotents reduces
pointwise to multiplication of their weights. -/
theorem weighted_sum_mul_weighted_sum
    (Q : ι → Matrix m m ℂ)
    (hQmul : ∀ a b, Q a * Q b = if a = b then Q a else 0)
    (u v : ι → ℂ) :
    (∑ a, u a • Q a) * (∑ a, v a • Q a) = ∑ a, (u a * v a) • Q a := by
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [hQmul, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm]

variable [DecidableEq m]

/-- A sum of mutually orthogonal Hermitian idempotents with unit-modulus weights is unitary
when the idempotents sum to the identity. -/
theorem weighted_sum_mem_unitaryGroup
    (Q : ι → Matrix m m ℂ)
    (hQstar : ∀ a, (Q a)ᴴ = Q a)
    (hQmul : ∀ a b, Q a * Q b = if a = b then Q a else 0)
    (hQsum : ∑ a, Q a = 1)
    (u : ι → ℂ)
    (hu : ∀ a, ‖u a‖ = 1) :
    (∑ a, u a • Q a) ∈ Matrix.unitaryGroup m ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (∑ a, u a • Q a)ᴴ * (∑ a, u a • Q a) = 1
  rw [Matrix.conjTranspose_sum]
  simp_rw [Matrix.conjTranspose_smul, hQstar]
  rw [weighted_sum_mul_weighted_sum Q hQmul]
  convert hQsum using 1
  apply Finset.sum_congr rfl
  intro a ha
  have hua : star (u a) * u a = 1 := by
    change (starRingEnd ℂ) (u a) * u a = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu]
    norm_num
  rw [hua, one_smul]

/-- If `H` is a Hermitian involution of trace zero, then `i • H` has determinant one.

The eigenvalues of `H` are `±1` with sum zero, so the eigenvalues of `i • H` are `±i` in equal
numbers. This is the determinant step of the skew branch of CPSV17, Lemma
`lemma:conjclass-normalform-continuous` (arXiv:1703.09188, lines 1081--1083). -/
theorem IsHermitian.det_I_smul_eq_one {H : Matrix m m ℂ} (hH : H.IsHermitian)
    (hHH : H * H = 1) (htr : H.trace = 0) :
    (Complex.I • H).det = 1 := by
  have hev (j : m) : hH.eigenvalues j = 1 ∨ hH.eigenvalues j = -1 := by
    rw [← mul_self_eq_one_iff]
    set v := ⇑(hH.eigenvectorBasis j)
    have hv : v ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 <| hH.eigenvectorBasis.orthonormal.ne_zero j
    have hHv := hH.mulVec_eigenvectorBasis j
    have h1 : (H * H) *ᵥ v = (hH.eigenvalues j * hH.eigenvalues j) • v := by
      rw [← mulVec_mulVec, hHv, mulVec_smul, hHv, smul_smul]
    rw [hHH, one_mulVec] at h1
    exact smul_left_injective ℝ hv (h1.symm.trans (one_smul ℝ v).symm)
  have hexp (j : m) : Complex.I * (hH.eigenvalues j : ℂ) =
      Complex.exp ((Real.pi : ℂ) / 2 * Complex.I * (hH.eigenvalues j : ℂ)) := by
    rcases hev j with h | h
    · rw [h]
      simp
    · rw [h]
      push_cast
      rw [show (Real.pi : ℂ) / 2 * Complex.I * -1 = -Real.pi / 2 * Complex.I by ring,
        Complex.exp_neg_pi_div_two_mul_I]
      ring
  rw [det_smul, hH.det_eq_prod_eigenvalues, Fintype.card, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine (Finset.prod_congr rfl fun j _ ↦ hexp j).trans ?_
  rw [← Complex.exp_sum, ← Finset.mul_sum]
  refine (congrArg (fun z ↦ Complex.exp (_ * z)) hH.trace_eq_sum_eigenvalues.symm).trans ?_
  rw [htr, mul_zero, Complex.exp_zero]

/-- Assemble the skew-symmetric branch of the unitary congruence normal form from the paired
spectral projectors in CPSV17, Lemma `lemma:conjclass-normalform-continuous`
(arXiv:1703.09188, lines 1066--1083).

The two summands of `Sum κ κ` index `P_E` and `P_Eᵀ`. The hypotheses say that these form a
complete orthogonal family of Hermitian projectors. The witnesses are exactly
`S = exp (-iπ/4) ∑_E exp (-iE/2) (P_E + P_Eᵀ)` and
`Λ = i ∑_E (P_E - P_Eᵀ)` from the paper. The determinant of `Λ` is one because its
eigenvalues come in pairs `±i` (lines 1081--1083): `Λ = i H` with `H = ∑_E (P_E - P_Eᵀ)` a
Hermitian involution of trace zero. -/
theorem exists_skew_unitary_congruence_of_paired_projectors
    (P : κ → Matrix m m ℂ)
    (E : κ → ℝ)
    (hPstar : ∀ k, (P k)ᴴ = P k)
    (hPmul : ∀ a b : Sum κ κ,
      Sum.elim P (fun k ↦ (P k).transpose) a *
          Sum.elim P (fun k ↦ (P k).transpose) b =
        if a = b then Sum.elim P (fun k ↦ (P k).transpose) a else 0)
    (hPsum : ∑ a : Sum κ κ, Sum.elim P (fun k ↦ (P k).transpose) a = 1) :
    let x := ∑ k, Complex.exp (-(E k : ℂ) * Complex.I) • (P k - (P k).transpose)
    ∃ S Λ : Matrix m m ℂ,
      S = Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) •
          ∑ k, Complex.exp (-((E k : ℂ) / 2) * Complex.I) •
            (P k + (P k).transpose) ∧
      Λ = Complex.I • ∑ k, (P k - (P k).transpose) ∧
      S.transpose = S ∧
      S ∈ Matrix.unitaryGroup m ℂ ∧
      Λ.map (starRingEnd ℂ) = Λ ∧
      Λ.transpose = -Λ ∧
      Λ ∈ Matrix.unitaryGroup m ℂ ∧
      Λ.det = 1 ∧
      x = S.transpose * Λ * S := by
  let Q : Sum κ κ → Matrix m m ℂ :=
    Sum.elim P (fun k ↦ (P k).transpose)
  let s : Sum κ κ → ℂ := fun a ↦
    Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
      Complex.exp (-((E (Sum.elim id id a) : ℂ) / 2) * Complex.I)
  let l : Sum κ κ → ℂ := Sum.elim (fun _ ↦ Complex.I) (fun _ ↦ -Complex.I)
  let S : Matrix m m ℂ := ∑ a, s a • Q a
  let Λ : Matrix m m ℂ := ∑ a, l a • Q a
  have hPmap (k : κ) : (P k).map (starRingEnd ℂ) = (P k).transpose := by
    calc
      (P k).map (starRingEnd ℂ) = (P k)ᴴ.transpose :=
        (Matrix.conjTranspose_transpose (P k)).symm
      _ = (P k).transpose := congrArg Matrix.transpose (hPstar k)
  have hQstar : ∀ a, (Q a)ᴴ = Q a := by
    intro a
    cases a with
    | inl k => exact hPstar k
    | inr k =>
        ext i j
        have h := congrArg (fun M : Matrix m m ℂ ↦ M j i) (hPstar k)
        simpa [Q, Matrix.conjTranspose_apply, Matrix.transpose_apply] using h
  have hs_formula :
      S = Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) •
          ∑ k, Complex.exp (-((E k : ℂ) / 2) * Complex.I) •
            (P k + (P k).transpose) := by
    dsimp only [S]
    rw [Fintype.sum_sum_type]
    simp only [s, Q, Sum.elim_inl, Sum.elim_inr, id_eq]
    rw [Finset.smul_sum]
    simp_rw [smul_add, smul_smul]
    rw [Finset.sum_add_distrib]
  have hl_formula : Λ = Complex.I • ∑ k, (P k - (P k).transpose) := by
    dsimp only [Λ]
    rw [Fintype.sum_sum_type]
    simp only [l, Q, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.smul_sum]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [neg_smul]
    rw [sub_eq_add_neg]
    congr 1
    exact Finset.sum_neg_distrib (fun x : κ ↦ Complex.I • (P x).transpose)
  have hS_transpose : S.transpose = S := by
    rw [hs_formula]
    simp only [Matrix.transpose_smul, Matrix.transpose_sum, Matrix.transpose_add,
      Matrix.transpose_transpose]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [add_comm]
  have hs_norm (a : Sum κ κ) : ‖s a‖ = 1 := by
    simp only [s, norm_mul]
    rw [Complex.norm_exp, Complex.norm_exp]
    simp
  have hS_unitary : S ∈ Matrix.unitaryGroup m ℂ := by
    exact weighted_sum_mem_unitaryGroup Q hQstar hPmul hPsum s hs_norm
  have hPtransposeMap (k : κ) : (P k).transpose.map (starRingEnd ℂ) = P k := by
    rw [Matrix.transpose_map, hPmap, Matrix.transpose_transpose]
  have hmap_sub (k : κ) :
      (P k - (P k).transpose).map (starRingEnd ℂ) = (P k).transpose - P k := by
    rw [Matrix.map_sub (starRingEnd ℂ) (starRingEnd ℂ).map_sub, hPmap, hPtransposeMap]
  have hmap_sum_finset (t : Finset κ) :
      (∑ k ∈ t, (P k - (P k).transpose)).map (starRingEnd ℂ) =
        ∑ k ∈ t, (P k - (P k).transpose).map (starRingEnd ℂ) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha,
          Matrix.map_add (starRingEnd ℂ) (starRingEnd ℂ).map_add, ih]
  have hmap_sum :
      (∑ k, (P k - (P k).transpose)).map (starRingEnd ℂ) =
        ∑ k, (P k - (P k).transpose).map (starRingEnd ℂ) := by
    simpa using hmap_sum_finset Finset.univ
  have hsum_map :
      (∑ k, (P k - (P k).transpose)).map (starRingEnd ℂ) =
        -(∑ k, (P k - (P k).transpose)) := by
    rw [hmap_sum]
    simp_rw [hmap_sub]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    module
  have hΛ_real : Λ.map (starRingEnd ℂ) = Λ := by
    rw [hl_formula, Matrix.map_smul' (starRingEnd ℂ) Complex.I _
      (starRingEnd ℂ).map_mul, hsum_map, Complex.conj_I]
    module
  have hΛ_transpose : Λ.transpose = -Λ := by
    rw [hl_formula]
    simp only [Matrix.transpose_smul, Matrix.transpose_sum, Matrix.transpose_sub,
      Matrix.transpose_transpose]
    have hneg : (∑ k, ((P k).transpose - P k)) =
        -(∑ k, (P k - (P k).transpose)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      module
    rw [hneg]
    module
  have hl_norm (a : Sum κ κ) : ‖l a‖ = 1 := by
    cases a <;> simp [l]
  have hΛ_unitary : Λ ∈ Matrix.unitaryGroup m ℂ := by
    exact weighted_sum_mem_unitaryGroup Q hQstar hPmul hPsum l hl_norm
  have hΛ_det : Λ.det = 1 := by
    have hΛΛ : Λ * Λ = -1 := by
      dsimp only [Λ]
      rw [weighted_sum_mul_weighted_sum Q hPmul, ← neg_one_smul ℂ (1 : Matrix m m ℂ),
        ← hPsum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      cases a <;> simp [l, Q]
    let H : Matrix m m ℂ := ∑ k, (P k - (P k).transpose)
    have hH : H.IsHermitian := by
      change (∑ k, (P k - (P k).transpose))ᴴ = _
      rw [Matrix.conjTranspose_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Matrix.conjTranspose_sub, hPstar]
      exact congrArg (P k - ·) (hQstar (Sum.inr k))
    have hHH : H * H = 1 := by
      have h := hΛΛ
      rw [hl_formula, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
        neg_one_smul, neg_inj] at h
      exact h
    have htr : H.trace = 0 := by
      simp [H, Matrix.trace_sum, Matrix.trace_sub, Matrix.trace_transpose]
    rw [hl_formula]
    exact hH.det_I_smul_eq_one hHH htr
  have hphase (r : ℝ) :
      Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
          (Complex.exp (-((r : ℂ) / 2) * Complex.I) *
            (Complex.I * (Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
              Complex.exp (-((r : ℂ) / 2) * Complex.I)))) =
        Complex.exp (-(r : ℂ) * Complex.I) := by
    have hquarter :
        Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
            Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) = -Complex.I := by
      rw [← Complex.exp_add]
      convert (Complex.exp_neg ((Real.pi : ℂ) / 2 * Complex.I)).trans
        (congrArg Inv.inv Complex.exp_pi_div_two_mul_I) using 1 <;> ring_nf
      simp
    have hhalf :
        Complex.exp (-((r : ℂ) / 2) * Complex.I) *
            Complex.exp (-((r : ℂ) / 2) * Complex.I) =
          Complex.exp (-(r : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [show Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
        (Complex.exp (-((r : ℂ) / 2) * Complex.I) *
          (Complex.I * (Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
            Complex.exp (-((r : ℂ) / 2) * Complex.I)))) =
        (Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
          Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I)) *
        (Complex.exp (-((r : ℂ) / 2) * Complex.I) *
          Complex.exp (-((r : ℂ) / 2) * Complex.I)) * Complex.I by ring]
    rw [hquarter, hhalf]
    calc
      (-Complex.I * Complex.exp (-(r : ℂ) * Complex.I)) * Complex.I =
          -(Complex.I * Complex.I) * Complex.exp (-(r : ℂ) * Complex.I) := by ring
      _ = Complex.exp (-(r : ℂ) * Complex.I) := by rw [Complex.I_mul_I]; ring
  have hphase_neg (r : ℝ) :
      Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
          (Complex.exp (-((r : ℂ) / 2) * Complex.I) *
            (-Complex.I * (Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
              Complex.exp (-((r : ℂ) / 2) * Complex.I)))) =
        -Complex.exp (-(r : ℂ) * Complex.I) := by
    rw [show Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
        (Complex.exp (-((r : ℂ) / 2) * Complex.I) *
          (-Complex.I * (Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
            Complex.exp (-((r : ℂ) / 2) * Complex.I)))) =
      -(Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
        (Complex.exp (-((r : ℂ) / 2) * Complex.I) *
          (Complex.I * (Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
            Complex.exp (-((r : ℂ) / 2) * Complex.I))))) by ring, hphase]
  have hfactor :
      (∑ k, Complex.exp (-(E k : ℂ) * Complex.I) • (P k - (P k).transpose)) =
        S.transpose * Λ * S := by
    rw [hS_transpose]
    dsimp only [S, Λ]
    rw [weighted_sum_mul_weighted_sum Q hPmul,
      weighted_sum_mul_weighted_sum Q hPmul]
    rw [Fintype.sum_sum_type]
    simp only [s, l, Q, Sum.elim_inl, Sum.elim_inr, id_eq, mul_assoc]
    simp_rw [hphase, hphase_neg, smul_sub]
    rw [Finset.sum_sub_distrib, sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [neg_smul]
  exact ⟨S, Λ, hs_formula, hl_formula, hS_transpose, hS_unitary, hΛ_real,
    hΛ_transpose, hΛ_unitary, hΛ_det, hfactor⟩

end Matrix

section SkewSpectralPairs

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The spectral projector of a square complex matrix at `μ ∈ ℂ`: the continuous functional
calculus applied to the indicator function of the point `μ`. For a normal matrix this is the
orthogonal projector onto the `μ`-eigenspace, and it vanishes when `μ` is not an eigenvalue.
These are the projectors `P_E` of the spectral decompositions in CPSV17, Lemma
`lemma:conjclass-normalform-continuous` (arXiv:1703.09188, lines 1054--1070). -/
def spectralProjector (x : Matrix m m ℂ) (μ : ℂ) : Matrix m m ℂ :=
  cfc (fun z : ℂ ↦ if z = μ then (1 : ℂ) else 0) x

/-- Spectral projectors are Hermitian, since the indicator function of a point is real. -/
theorem conjTranspose_spectralProjector (x : Matrix m m ℂ) (μ : ℂ) :
    (spectralProjector x μ)ᴴ = spectralProjector x μ := by
  change star (cfc _ x) = cfc _ x
  rw [← cfc_star]
  congr 1
  funext z
  split_ifs <;> simp

/-- Spectral projectors of a normal matrix are idempotent, and those at distinct points are
mutually orthogonal. -/
theorem spectralProjector_mul (x : Matrix m m ℂ) [IsStarNormal x] (μ ν : ℂ) :
    spectralProjector x μ * spectralProjector x ν =
      if μ = ν then spectralProjector x μ else 0 := by
  have hspec := Matrix.finite_spectrum x
  unfold spectralProjector
  rw [← cfc_mul _ _ x (hspec.continuousOn _) (hspec.continuousOn _)]
  split_ifs with h
  · subst h
    congr 1
    funext z
    split_ifs <;> simp
  · rw [← cfc_zero ℂ x]
    congr 1
    funext z
    split_ifs <;> simp_all

/-- The spectral projectors of a normal matrix over its finite spectrum sum to the identity. -/
theorem sum_spectralProjector (x : Matrix m m ℂ) [IsStarNormal x] :
    ∑ μ ∈ (Matrix.finite_spectrum x).toFinset, spectralProjector x μ = 1 := by
  have hspec := Matrix.finite_spectrum x
  unfold spectralProjector
  rw [← cfc_sum _ x _ (fun _ _ ↦ hspec.continuousOn _), ← cfc_one ℂ x]
  refine cfc_congr fun z hz ↦ ?_
  simp [Finset.sum_apply, hspec.mem_toFinset.mpr hz]

/-- A normal matrix is the sum of its spectral values weighted by its spectral projectors. -/
theorem sum_smul_spectralProjector (x : Matrix m m ℂ) [IsStarNormal x] :
    ∑ μ ∈ (Matrix.finite_spectrum x).toFinset, μ • spectralProjector x μ = x := by
  have hspec := Matrix.finite_spectrum x
  unfold spectralProjector
  simp_rw [← cfc_smul (R := ℂ) _ _ x (hspec.continuousOn _)]
  rw [← cfc_sum _ x _ (fun _ _ ↦ hspec.continuousOn _)]
  conv_rhs => rw [← cfc_id' ℂ x]
  refine cfc_congr fun z hz ↦ ?_
  simp [Finset.sum_apply, hspec.mem_toFinset.mpr hz]

/-- The spectrum of a complex matrix with `xᵀ = -x` is symmetric under `z ↦ -z`. -/
theorem neg_mem_spectrum_of_transpose_eq_neg {x : Matrix m m ℂ} (hskew : xᵀ = -x) {z : ℂ}
    (hz : z ∈ spectrum ℂ x) : -z ∈ spectrum ℂ x := by
  rw [← spectrum_transpose, hskew, ← spectrum.neg_eq]
  simpa using hz

/-- For a normal matrix with `xᵀ = -x`, transposition sends the spectral projector at `μ` to
the spectral projector at `-μ`.

The projector is a polynomial `q(x)` interpolating the indicator of `μ` on the finite
spectrum, so its transpose is `q(xᵀ) = q(-x)`, which interpolates the indicator of `-μ`. This is
the pairing `P_E ↔ P_Eᵀ` in the skew branch of CPSV17, Lemma
`lemma:conjclass-normalform-continuous` (arXiv:1703.09188, lines 1066--1070). -/
theorem transpose_spectralProjector_of_transpose_eq_neg (x : Matrix m m ℂ) [IsStarNormal x]
    (hskew : xᵀ = -x) (μ : ℂ) :
    (spectralProjector x μ)ᵀ = spectralProjector x (-μ) := by
  have hspec := Matrix.finite_spectrum x
  let f : ℂ → ℂ := fun z ↦ if z = μ then 1 else 0
  let q : ℂ[X] := Lagrange.interpolate hspec.toFinset id f
  have hq : spectralProjector x μ = Polynomial.aeval x q := by
    rw [← cfc_polynomial q x]
    refine cfc_congr fun z hz ↦ ?_
    exact (Lagrange.eval_interpolate_at_node f (Set.injOn_id _)
      (hspec.mem_toFinset.mpr hz)).symm
  rw [hq, transpose_aeval, hskew, ← cfc_polynomial q (-x),
    ← cfc_comp_neg (fun z ↦ q.eval z) x q.continuous.continuousOn]
  refine cfc_congr fun z hz ↦ ?_
  have h := Lagrange.eval_interpolate_at_node f (Set.injOn_id _)
    (hspec.mem_toFinset.mpr (neg_mem_spectrum_of_transpose_eq_neg hskew hz))
  simp only [id] at h
  rw [h]
  simp only [f, neg_eq_iff_eq_neg]

end Matrix

/-- A nonzero complex number has argument in `(-π, 0]` exactly when its negative does not.

This selects one member of each pair `{λ, -λ}` of spectral values in the skew branch of
CPSV17, Lemma `lemma:conjclass-normalform-continuous` (arXiv:1703.09188, lines 1066--1070). -/
theorem Complex.arg_nonpos_iff_not_arg_neg_nonpos {z : ℂ} (hz : z ≠ 0) :
    Complex.arg z ≤ 0 ↔ ¬ Complex.arg (-z) ≤ 0 := by
  have key (w : ℂ) : Complex.arg w ≤ 0 ↔ w.im < 0 ∨ (0 ≤ w.re ∧ w.im = 0) := by
    rw [le_iff_lt_or_eq, Complex.arg_neg_iff, Complex.arg_eq_zero_iff]
  rw [key, key, Complex.neg_re, Complex.neg_im]
  have hz' : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (Complex.ext h.1 h.2)
  rcases lt_trichotomy z.im 0 with h | h | h
  · constructor
    · rintro - (h' | h') <;> [linarith; linarith [h'.2]]
    · intro; exact Or.inl h
  · rcases hz' with hre | hre
    · rcases lt_or_gt_of_ne hre with hre | hre
      · constructor
        · rintro (h' | h') <;> [linarith; linarith [h'.1]]
        · intro h'; exact absurd (Or.inr ⟨by linarith, by linarith⟩) h'
      · constructor
        · rintro - (h' | h') <;> [linarith; linarith [h'.1]]
        · intro; exact Or.inr ⟨hre.le, h⟩
    · exact absurd h hre
  · constructor
    · rintro (h' | h') <;> [linarith; linarith [h'.2]]
    · intro h'; exact absurd (Or.inl (by linarith)) h'

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The paired spectral data of a complex skew-symmetric unitary matrix.

If `x` is unitary and `xᵀ = -x`, there are a finite index set `κ`, Hermitian projectors `P k`,
and angles `E k ∈ [0, π)` such that the family `{P k, (P k)ᵀ}` is a complete orthogonal family
of projectors and `x = ∑ k, exp (-i E k) • (P k - (P k)ᵀ)`. The unit half-phases of the source
are `exp (-i E k / 2)`. This is the spectral decomposition in the skew branch of CPSV17, Lemma
`lemma:conjclass-normalform-continuous` (arXiv:1703.09188, lines 1066--1074), and the
conclusions are exactly the hypotheses of `exists_skew_unitary_congruence_of_paired_projectors`.

The projector `P k` is the spectral projector of `x` at a spectral value `λ_k` with
`arg λ_k ∈ (-π, 0]`, and `E k = -arg λ_k`. Transposition sends the spectral projector at `λ`
to the one at `-λ`, and `λ ↦ -λ` has no fixed point on the spectrum because `x` is unitary,
so exactly one member of each pair `{λ, -λ}` is chosen. -/
lemma exists_paired_spectralProjectors_of_transpose_eq_neg
    (x : Matrix m m ℂ) (hx : x ∈ Matrix.unitaryGroup m ℂ) (hskew : xᵀ = -x) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (P : κ → Matrix m m ℂ) (E : κ → ℝ),
      (∀ k, E k ∈ Set.Ico 0 Real.pi) ∧
      (∀ k, (P k)ᴴ = P k) ∧
      (∀ a b : Sum κ κ,
        Sum.elim P (fun k ↦ (P k)ᵀ) a * Sum.elim P (fun k ↦ (P k)ᵀ) b =
          if a = b then Sum.elim P (fun k ↦ (P k)ᵀ) a else 0) ∧
      (∑ a : Sum κ κ, Sum.elim P (fun k ↦ (P k)ᵀ) a = 1) ∧
      x = ∑ k, Complex.exp (-(E k : ℂ) * Complex.I) • (P k - (P k)ᵀ) := by
  have hnormal : IsStarNormal x := isStarNormal_of_mem_unitary hx
  have hspec := Matrix.finite_spectrum x
  let σ := hspec.toFinset
  have hnorm {z : ℂ} (hz : z ∈ σ) : ‖z‖ = 1 :=
    spectrum.norm_eq_one_of_unitary hx (hspec.mem_toFinset.mp hz)
  have hne {z : ℂ} (hz : z ∈ σ) : z ≠ 0 := by
    intro h
    simpa [h] using hnorm hz
  have hneg {z : ℂ} (hz : z ∈ σ) : -z ∈ σ :=
    hspec.mem_toFinset.mpr
      (neg_mem_spectrum_of_transpose_eq_neg hskew (hspec.mem_toFinset.mp hz))
  let T : Finset ℂ := σ.filter fun z ↦ Complex.arg z ≤ 0
  have hT {z : ℂ} (hz : z ∈ T) : z ∈ σ ∧ Complex.arg z ≤ 0 := Finset.mem_filter.mp hz
  have hsplit (g : ℂ → Matrix m m ℂ) :
      ∑ z ∈ σ, g z = ∑ z ∈ T, g z + ∑ z ∈ T, g (-z) := by
    rw [← Finset.sum_filter_add_sum_filter_not σ (fun z ↦ Complex.arg z ≤ 0)]
    congr 1
    refine Finset.sum_nbij' (fun z ↦ -z) (fun z ↦ -z) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨hneg hz'.1, ?_⟩
      have := (Complex.arg_nonpos_iff_not_arg_neg_nonpos (hne (hneg hz'.1))).mpr
      simp only [neg_neg] at this
      exact this hz'.2
    · intro z hz
      have hz' := hT hz
      refine Finset.mem_filter.mpr ⟨hneg hz'.1, ?_⟩
      exact (Complex.arg_nonpos_iff_not_arg_neg_nonpos (hne hz'.1)).mp hz'.2
    · intro z _; simp
    · intro z _; simp
    · intro z _; simp
  let κ := {z : ℂ // z ∈ T}
  let P : κ → Matrix m m ℂ := fun k ↦ spectralProjector x k.1
  let E : κ → ℝ := fun k ↦ -Complex.arg k.1
  let pt : Sum κ κ → ℂ := Sum.elim (fun k ↦ k.1) (fun k ↦ -k.1)
  have hQ (a : Sum κ κ) : Sum.elim P (fun k ↦ (P k)ᵀ) a = spectralProjector x (pt a) := by
    cases a with
    | inl k => rfl
    | inr k => exact transpose_spectralProjector_of_transpose_eq_neg x hskew k.1
  have hpt : Function.Injective pt := by
    have hcross (k l : κ) : k.1 ≠ -l.1 := by
      intro h
      have hk := hT k.2
      have hl := hT l.2
      have := (Complex.arg_nonpos_iff_not_arg_neg_nonpos (hne hl.1)).mp hl.2
      rw [← h] at this
      exact this hk.2
    rintro (k | k) (l | l) h <;> simp only [pt, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact absurd h (hcross k l)
    · exact absurd h.symm (hcross l k)
    · exact congrArg Sum.inr (Subtype.ext (neg_inj.mp h))
  refine ⟨κ, inferInstance, inferInstance, P, E, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨by simpa [E] using (hT k.2).2, ?_⟩
    have := Complex.neg_pi_lt_arg k.1
    simp only [E]
    linarith
  · intro k
    exact conjTranspose_spectralProjector x k.1
  · intro a b
    simp only [hQ]
    rw [spectralProjector_mul]
    exact if_congr hpt.eq_iff rfl rfl
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← sum_spectralProjector x, hsplit (spectralProjector x)]
    congr 1
    · exact Finset.sum_coe_sort T (spectralProjector x)
    · simp_rw [P, transpose_spectralProjector_of_transpose_eq_neg x hskew]
      exact Finset.sum_coe_sort T (fun z ↦ spectralProjector x (-z))
  · have hphase (k : κ) : Complex.exp (-(E k : ℂ) * Complex.I) = k.1 := by
      have h := Complex.norm_mul_exp_arg_mul_I k.1
      rw [hnorm (hT k.2).1] at h
      simpa [E] using h
    simp_rw [hphase, P, transpose_spectralProjector_of_transpose_eq_neg x hskew]
    conv_lhs => rw [← sum_smul_spectralProjector x, hsplit]
    rw [Finset.sum_coe_sort T (fun z ↦ z • (spectralProjector x z - spectralProjector x (-z))),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [smul_sub, neg_smul, sub_eq_add_neg]

/-- Every complex skew-symmetric unitary matrix is congruent, by a symmetric unitary, to a
real skew-symmetric unitary of determinant one: `x = Sᵀ Λ S`.

This is the skew branch of CPSV17, Lemma `lemma:conjclass-normalform-continuous`
(arXiv:1703.09188, lines 1066--1083): the spectral data of
`exists_paired_spectralProjectors_of_transpose_eq_neg` are assembled by
`exists_skew_unitary_congruence_of_paired_projectors`. -/
lemma exists_skew_unitary_congruence
    (x : Matrix m m ℂ) (hx : x ∈ Matrix.unitaryGroup m ℂ) (hskew : xᵀ = -x) :
    ∃ S Λ : Matrix m m ℂ,
      Sᵀ = S ∧
      S ∈ Matrix.unitaryGroup m ℂ ∧
      Λ.map (starRingEnd ℂ) = Λ ∧
      Λᵀ = -Λ ∧
      Λ ∈ Matrix.unitaryGroup m ℂ ∧
      Λ.det = 1 ∧
      x = Sᵀ * Λ * S := by
  obtain ⟨κ, _, _, P, E, -, hPstar, hPmul, hPsum, hxP⟩ :=
    exists_paired_spectralProjectors_of_transpose_eq_neg x hx hskew
  obtain ⟨S, Λ, -, -, hS, hSu, hΛr, hΛt, hΛu, hΛd, hfac⟩ :=
    exists_skew_unitary_congruence_of_paired_projectors P E hPstar hPmul hPsum
  exact ⟨S, Λ, hS, hSu, hΛr, hΛt, hΛu, hΛd, hxP.trans hfac⟩

variable {n : ℕ}

/-- A complex unitary matrix with `xᵀ = x` or `xᵀ = -x` has the form `x = Sᵀ Λ S`, where `S`
is symmetric and unitary and `Λ` is real with determinant one; `Λ` is symmetric when `x` is
symmetric and skew-symmetric when `x` is skew-symmetric.

This is CPSV17, Lemma `lemma:conjclass-normalform-continuous` (arXiv:1703.09188,
lines 1045--1083). In the symmetric branch `Λ = 1`; the skew branch is
`exists_skew_unitary_congruence`. -/
lemma exists_unitary_congruence_normalForm
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hsymm : xᵀ = x ∨ xᵀ = -x) :
    ∃ S Λ : Matrix (Fin n) (Fin n) ℂ,
      Sᵀ = S ∧
      S ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      Λ.map (starRingEnd ℂ) = Λ ∧
      (xᵀ = x → Λᵀ = Λ) ∧
      (xᵀ = -x → Λᵀ = -Λ) ∧
      Λ.det = 1 ∧
      x = Sᵀ * Λ * S := by
  have hdeg (hs : xᵀ = x) (ha : xᵀ = -x) : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := by
    have hx0 : x = 0 := by
      ext i j
      have h := congrFun (congrFun (hs.symm.trans ha) i) j
      simp only [Matrix.neg_apply] at h
      simp only [Matrix.zero_apply]
      linear_combination h / 2
    have h1 := Matrix.mem_unitaryGroup_iff.mp hx
    rw [hx0, zero_mul] at h1
    exact subsingleton_of_zero_eq_one h1
  rcases hsymm with hs | ha
  · obtain ⟨S, hS, hSu, hxS⟩ := exists_symmetric_unitary_squareRoot x hx hs
    refine ⟨S, 1, hS, hSu, by simp, fun _ ↦ Matrix.transpose_one, fun ha ↦ ?_, Matrix.det_one,
      by rw [Matrix.mul_one]; exact hxS⟩
    have := hdeg hs ha
    exact Subsingleton.elim _ _
  · obtain ⟨S, Λ, hS, hSu, hΛr, hΛt, hΛu, hΛd, hfac⟩ := exists_skew_unitary_congruence x hx ha
    refine ⟨S, Λ, hS, hSu, hΛr, fun hs ↦ ?_, fun _ ↦ hΛt, hΛd, hfac⟩
    have := hdeg hs ha
    exact Subsingleton.elim _ _

end Matrix

end SkewSpectralPairs
