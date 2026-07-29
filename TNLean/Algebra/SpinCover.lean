/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SpinCover.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The spin-`½` double cover `SU(2) → SO(3)` — Euler-angle surjectivity

This module proves that the spin-`½` real-rotation cover defined in
`TNLean.Algebra.SpinCover.Basic` is surjective onto `SO(3)` via an explicit
Euler-angle (`ZXZ`) factorization.

## Main results

* `SpinCover.so3_euler_decomp` : every `SO(3)` matrix factors as a `ZXZ` product
  of coordinate rotations
* `SpinCover.spinHalfCover_surjective_onto_SO3` : every `SO(3)` rotation is a
  Pauli conjugation by some `SU(2)` element

The algebraic core (Pauli matrices, `spinHalfCover`, orthogonality,
`spinHalfCoverSO3`) lives in `TNLean.Algebra.SpinCover.Basic` and does not
import the trigonometric stack.

## References

* RMP review (arXiv:2011.12127) around line 1159 (`A^i = σ^i`, on-site `SO(3)`)
-/

open scoped Matrix BigOperators
open Matrix Finset Complex

noncomputable section

namespace SpinCover

/-! ### Generators of `SU(2)` and `SO(3)`

The surjectivity of the spin-`½` cover is proved through an explicit
Euler-angle factorization.  Every rotation of three-space is a product of a
rotation about the `z`-axis, a rotation about the `x`-axis, and a further
rotation about the `z`-axis, and each of these one-parameter families is the
image under the cover of a one-parameter family in `SU(2)`. -/

/-- The diagonal `SU(2)` matrix `diag(e^{-iθ/2}, e^{iθ/2})` covering a rotation by
`θ` about the `z`-axis. -/
def su2Diag (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(θ / 2) * Complex.I), 0; 0, Complex.exp (θ / 2 * Complex.I)]

/-- The `SU(2)` matrix covering a rotation by `β` about the `x`-axis. -/
def su2Xrot (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Real.cos (β / 2), -Complex.I * Real.sin (β / 2);
    -Complex.I * Real.sin (β / 2), Real.cos (β / 2)]

/-- The rotation by `θ` about the `z`-axis. -/
def rotZ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- The rotation by `β` about the `x`-axis. -/
def rotX (β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos β, -Real.sin β; 0, Real.sin β, Real.cos β]

-- Star of the diagonal generator, precomputed to avoid repeated expansion in the
-- membership proof.
private lemma star_su2Diag (θ : ℝ) : star (su2Diag θ) =
    !![Complex.exp (θ / 2 * Complex.I), 0; 0, Complex.exp (-(θ / 2) * Complex.I)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [su2Diag, Matrix.star_apply, Complex.star_def, Complex.exp_conj, map_div₀, map_neg]

lemma su2Diag_mem_specialUnitaryGroup (θ : ℝ) :
    su2Diag θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_su2Diag]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [su2Diag, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add] <;> ring
  · simp [su2Diag, Matrix.det_fin_two_of, mul_comm, ← Complex.exp_add]; ring

lemma su2Xrot_mem_specialUnitaryGroup (β : ℝ) :
    su2Xrot β ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hp : ((Real.cos (β / 2) : ℂ)) ^ 2 + ((Real.sin (β / 2) : ℂ)) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [su2Xrot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.star_def,
        Complex.conj_I, Complex.conj_ofReal, map_mul, map_neg] <;>
      first
        | linear_combination hp - (Real.sin (β / 2) : ℂ) ^ 2 * Complex.I_sq
        | ring
  · rw [su2Xrot, Matrix.det_fin_two_of]
    linear_combination hp - (Real.sin (β / 2) : ℂ) ^ 2 * Complex.I_sq

/-! ### The cover sends the chosen generators to the coordinate rotations -/

/-- Conjugating the Pauli vector by the diagonal cover `su2Diag θ` realizes the
rotation by `θ` about the `z`-axis.  Each of the nine entries is verified by
computing `½ tr(σᵢ · su2Diag θ · σⱼ · (su2Diag θ)⁻¹)` with trigonometric
simplification; the `simp only` list is minimal because explicit `!![…]` matrix
literals make entry extraction definitional. -/
lemma R_su2Diag_eq_rotZ (θ : ℝ) :
    pauliConjAd (su2ToGL (su2Diag θ) (su2Diag_mem_specialUnitaryGroup θ))
      = (rotZ θ).map Complex.ofReal := by
  have hexpP : Complex.exp ((θ : ℂ) / 2 * Complex.I)
      = (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [show (θ : ℂ) / 2 = ((θ / 2 : ℝ) : ℂ) by push_cast; ring, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  have hexpN : Complex.exp (-((θ : ℂ) / 2 * Complex.I))
      = (Real.cos (θ / 2) : ℂ) - (Real.sin (θ / 2) : ℂ) * Complex.I := by
    have harg : -((θ : ℂ) / 2 * Complex.I) = ((-(θ / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_neg,
      Complex.cos_neg, Complex.sin_neg]
    ring
  have hcos : (Real.cos θ : ℂ)
      = (Real.cos (θ / 2) : ℂ) ^ 2 - (Real.sin (θ / 2) : ℂ) ^ 2 := by
    have h : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
      rw [← Real.cos_two_mul' (θ / 2), show 2 * (θ / 2) = θ by ring]
    rw [h]; push_cast; ring
  have hsin : (Real.sin θ : ℂ) = 2 * (Real.sin (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ) := by
    have h : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      rw [← Real.sin_two_mul, show 2 * (θ / 2) = θ by ring]
    rw [h]; push_cast; ring
  have hpyth : (↑(Real.cos (θ * (1 / 2))) : ℂ) ^ 2
      + (↑(Real.sin (θ * (1 / 2))) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliConjAd, su2ToGL_coe, su2ToGL_inv_coe, pauli, su2Diag, rotZ,
      Matrix.adjugate_fin_two_of, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.map_apply, Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
      hexpP, hexpN, hcos, hsin] <;>
    ring

/-- Conjugating the Pauli vector by the cover `su2Xrot β` realizes the rotation by
`β` about the `x`-axis.  Same strategy as `R_su2Diag_eq_rotZ`: minimal `simp only`
list plus `ring` closure. -/
lemma R_su2Xrot_eq_rotX (β : ℝ) :
    pauliConjAd (su2ToGL (su2Xrot β) (su2Xrot_mem_specialUnitaryGroup β))
      = (rotX β).map Complex.ofReal := by
  have hcos : (Real.cos β : ℂ)
      = (Real.cos (β / 2) : ℂ) ^ 2 - (Real.sin (β / 2) : ℂ) ^ 2 := by
    have h : Real.cos β = Real.cos (β / 2) ^ 2 - Real.sin (β / 2) ^ 2 := by
      rw [← Real.cos_two_mul' (β / 2), show 2 * (β / 2) = β by ring]
    rw [h]; push_cast; ring
  have hsin : (Real.sin β : ℂ) = 2 * (Real.sin (β / 2) : ℂ) * (Real.cos (β / 2) : ℂ) := by
    have h : Real.sin β = 2 * Real.sin (β / 2) * Real.cos (β / 2) := by
      rw [← Real.sin_two_mul, show 2 * (β / 2) = β by ring]
    rw [h]; push_cast; ring
  have hpyth : (↑(Real.cos (β * (1 / 2))) : ℂ) ^ 2
      + (↑(Real.sin (β * (1 / 2))) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliConjAd, su2ToGL_coe, su2ToGL_inv_coe, pauli, su2Xrot, rotX,
      Matrix.adjugate_fin_two_of, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.map_apply, Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
      hcos, hsin] <;>
    ring

/-! ### Surjectivity of the cover via the Euler-angle factorization -/

/-- A point on the unit circle is the cosine-sine pair of an angle.  Existence of
the angle comes from the argument of the corresponding unit complex number. -/
lemma exists_cos_sin {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  have hn : ‖(⟨c, s⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk,
      show c * c + s * s = 1 by nlinarith only [h]]
    simp
  have hz : (⟨c, s⟩ : ℂ) ≠ 0 := Complex.ne_zero_of_norm_eq_one hn
  exact ⟨Complex.arg (⟨c, s⟩ : ℂ), by rw [Complex.cos_arg hz, hn]; simp,
    by rw [Complex.sin_arg, hn]; simp⟩

-- The Euler decomposition verifies all nine entries of a three-by-three rotation
-- against the product of three coordinate rotations, each closed by a polynomial
-- certificate over the orthonormality and cofactor relations.  Arithmetic calls
-- are restricted with `only` to avoid passing the full matrix context to each
-- normalization.
lemma so3_euler_decomp (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ : ℝ, M = rotZ α * rotX β * rotZ γ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hM
  obtain ⟨ho, hdet⟩ := hM
  have hoM : M * Mᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp ho
  have hoT : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp ho
  have hadj : Mᵀ = M.adjugate := by
    rw [show Mᵀ = M⁻¹ from (Matrix.inv_eq_right_inv hoM).symm, Matrix.inv_def, hdet]; simp
  -- concrete row/column dot products and cofactors
  have row : ∀ p q : Fin 3, M p 0 * M q 0 + M p 1 * M q 1 + M p 2 * M q 2 =
      if p = q then 1 else 0 := by
    intro p q
    have := congrFun (congrFun hoM p) q
    simpa only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.one_apply] using this
  have col : ∀ p q : Fin 3, M 0 p * M 0 q + M 1 p * M 1 q + M 2 p * M 2 q =
      if p = q then 1 else 0 := by
    intro p q
    have := congrFun (congrFun hoT p) q
    simpa only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.one_apply] using this
  have cof : ∀ p q : Fin 3, M q p = (M.adjugate) p q := by
    intro p q
    have := congrFun (congrFun hadj p) q; rwa [Matrix.transpose_apply] at this
  -- the nine cofactor identities
  have cof00 : M 0 0 = M 1 1 * M 2 2 - M 1 2 * M 2 1 := by
    have := cof 0 0; simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.empty_val'] at this
    linarith only [this]
  have cof01 : M 1 0 = -(M 0 1 * M 2 2) + M 0 2 * M 2 1 := by
    have := cof 0 1; simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at this
    linarith only [this]
  have cof10 : M 0 1 = -(M 1 0 * M 2 2) + M 1 2 * M 2 0 := by
    have := cof 1 0; simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at this
    linarith only [this]
  have cof11 : M 1 1 = M 0 0 * M 2 2 - M 0 2 * M 2 0 := by
    have := cof 1 1; simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at this
    linarith only [this]
  -- norms of relevant rows/cols
  have hr22 : M 2 0 * M 2 0 + M 2 1 * M 2 1 + M 2 2 * M 2 2 = 1 := by
    have := row 2 2; rwa [if_pos rfl] at this
  have hc22 : M 0 2 * M 0 2 + M 1 2 * M 1 2 + M 2 2 * M 2 2 = 1 := by
    have := col 2 2; rwa [if_pos rfl] at this
  have hbound : M 2 2 ^ 2 ≤ 1 := by
    nlinarith only [hr22, sq_nonneg (M 2 0), sq_nonneg (M 2 1)]
  set sβ := Real.sqrt (1 - M 2 2 ^ 2) with hsβdef
  have hsβsq : sβ ^ 2 = 1 - M 2 2 ^ 2 := by
    rw [hsβdef, Real.sq_sqrt (by nlinarith only [hbound])]
  obtain ⟨β, hcosβ, hsinβ⟩ :=
    exists_cos_sin (c := M 2 2) (s := sβ) (by nlinarith only [hsβsq])
  by_cases hs : sβ = 0
  · -- gimbal lock: sin β = 0, so M 2 2 = ±1 and the off-axis entries vanish
    have h22sq : M 2 2 ^ 2 = 1 := by
      have : sβ ^ 2 = 0 := by rw [hs]; ring
      rw [this] at hsβsq
      linarith only [hsβsq]
    have hz20 : M 2 0 = 0 := by
      nlinarith only [hr22, h22sq, sq_nonneg (M 2 0), sq_nonneg (M 2 1)]
    have hz21 : M 2 1 = 0 := by
      nlinarith only [hr22, h22sq, sq_nonneg (M 2 0), sq_nonneg (M 2 1)]
    have hz02 : M 0 2 = 0 := by
      nlinarith only [hc22, h22sq, sq_nonneg (M 0 2), sq_nonneg (M 1 2)]
    have hz12 : M 1 2 = 0 := by
      nlinarith only [hc22, h22sq, sq_nonneg (M 0 2), sq_nonneg (M 1 2)]
    have hcol0 : M 0 0 ^ 2 + M 1 0 ^ 2 = 1 := by
      have := col 0 0
      rw [if_pos rfl] at this
      nlinarith only [this, hz20]
    obtain ⟨α, hcosα, hsinα⟩ :=
      exists_cos_sin (c := M 0 0) (s := M 1 0) (by nlinarith only [hcol0])
    refine ⟨α, β, 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rotZ, rotX, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_fin_const,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
        hcosα, hsinα, hcosβ, hsinβ, Real.cos_zero, Real.sin_zero, hs,
        hz02, hz12, hz20, hz21] <;>
      first
        | linear_combination cof10 + M 1 2 * hz20
        | linear_combination cof11 - M 0 2 * hz20
        | ring
  · have hsβne : sβ ≠ 0 := hs
    obtain ⟨α, hcosα, hsinα⟩ := exists_cos_sin (c := -M 1 2 / sβ) (s := M 0 2 / sβ) (by
      rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hsβne)]
      nlinarith only [hc22, hsβsq])
    obtain ⟨γ, hcosγ, hsinγ⟩ := exists_cos_sin (c := M 2 1 / sβ) (s := M 2 0 / sβ) (by
      rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hsβne)]
      nlinarith only [hr22, hsβsq])
    refine ⟨α, β, γ, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rotZ, rotX, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_fin_const,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
        hcosα, hsinα, hcosβ, hsinβ, hcosγ, hsinγ] <;>
      field_simp <;>
      first
        | linear_combination M 0 0 * hsβsq + cof00 + M 2 2 * cof11
        | linear_combination M 0 1 * hsβsq + cof10 - M 2 2 * cof01
        | linear_combination M 1 0 * hsβsq + cof01 - M 2 2 * cof10
        | linear_combination M 1 1 * hsβsq + cof11 + M 2 2 * cof00
        | nlinarith only [hsβsq, hr22, hc22]

/-! ### The spin-½ cover is onto `SO(3)` -/

/-- The spin-`½` cover is surjective onto `SO(3)`: every rotation of three-space
is the adjoint action of some `SU(2)` matrix on the Pauli vector.  The witness is
read off the Euler-angle factorization of the rotation. -/
theorem spinHalfCover_surjective_onto_SO3 (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ, ∃ hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      pauliConjAd (su2ToGL U hU) = M.map Complex.ofReal := by
  obtain ⟨α, β, γ, hαβγ⟩ := so3_euler_decomp M hM
  have hd : ∀ θ, su2Diag θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    su2Diag_mem_specialUnitaryGroup
  have hx : ∀ b, su2Xrot b ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    su2Xrot_mem_specialUnitaryGroup
  have hU1 : su2Diag α * su2Xrot β ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (hd α) (hx β)
  have hU : su2Diag α * su2Xrot β * su2Diag γ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ hU1 (hd γ)
  refine ⟨su2Diag α * su2Xrot β * su2Diag γ, hU, ?_⟩
  rw [pauliConjAd_su2ToGL_mul _ _ hU1 (hd γ), pauliConjAd_su2ToGL_mul _ _ (hd α) (hx β),
    R_su2Diag_eq_rotZ, R_su2Xrot_eq_rotX, R_su2Diag_eq_rotZ, hαβγ,
    show (Complex.ofReal : ℝ → ℂ) = ⇑Complex.ofRealHom from rfl, ← Matrix.map_mul,
    ← Matrix.map_mul]

end SpinCover
