/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange

/-!
# Congruence factorization of symmetric unitary matrices

The two branches of the finite spectral-projector construction in CPSV17, Lemma
`lemma:conjclass-normalform-continuous`, give congruence factorizations of symmetric and
skew-symmetric unitary matrices (arXiv:1703.09188, lines 1054--1082).
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

/-- Multiplication of sums weighted by a complete orthogonal family of idempotents reduces
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

/-- Assemble the skew-symmetric branch of the unitary congruence normal form from the paired
spectral projectors in CPSV17, Lemma `lemma:conjclass-normalform-continuous`
(arXiv:1703.09188, lines 1066--1082).

The two summands of `Sum κ κ` index `P_E` and `P_Eᵀ`. The hypotheses say that these form a
complete orthogonal family of Hermitian projectors. The witnesses are exactly
`S = exp (-iπ/4) ∑_E exp (-iE/2) (P_E + P_Eᵀ)` and
`Λ = i ∑_E (P_E - P_Eᵀ)` from the paper. -/
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
      x = S.transpose * Λ * S := by
  let Q : Sum κ κ → Matrix m m ℂ :=
    Sum.elim P (fun k ↦ (P k).transpose)
  let s : Sum κ κ → ℂ := fun a ↦
    Complex.exp (-((Real.pi : ℂ) / 4) * Complex.I) *
      Complex.exp (-((E (Sum.elim id id a) : ℂ) / 2) * Complex.I)
  let l : Sum κ κ → ℂ := Sum.elim (fun _ ↦ Complex.I) (fun _ ↦ -Complex.I)
  let S : Matrix m m ℂ := ∑ a, s a • Q a
  let Λ : Matrix m m ℂ := ∑ a, l a • Q a
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
  have hPmap (k : κ) : (P k).map (starRingEnd ℂ) = (P k).transpose := by
    ext i j
    have h := congrArg (fun M : Matrix m m ℂ ↦ M j i) (hPstar k)
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using h
  have hPtransposeMap (k : κ) : (P k).transpose.map (starRingEnd ℂ) = P k := by
    ext i j
    have h := congrArg (fun M : Matrix m m ℂ ↦ M i j) (hPstar k)
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using h
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
    hΛ_transpose, hΛ_unitary, hfactor⟩

end Matrix
