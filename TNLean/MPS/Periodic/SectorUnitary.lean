/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.GaugePhase
import TNLean.MPS.Irreducible.Adjoint
import TNLean.QPF.Uniqueness

/-!
# Unitarity of the per-sector gauge in the periodic Fundamental Theorem

This module upgrades the per-sector gauge-phase equivalence used in the periodic
overlap argument from a general invertible gauge to a *unitary* gauge.  It is the
per-sector core of `eq:Cvprop` / the corner unitaries `U_v` of arXiv:1708.00029,
Appendix A.

The paper builds `U_v` via `thm:cf` (the single-block canonical-form / Fundamental
Theorem rigidity, cited as Theorem 2.10 of Cirac--Pérez-García).  In the
canonical-form orientation, two left-canonical tensors that are gauge-phase
equivalent are related by a *unitary* gauge: the modulus of the scalar is one and
the invertible intertwiner can be normalized to a unitary.

The main result here, `exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible`,
makes this precise:

> if `A B : MPSTensor d D` are both left-canonical and irreducible and are
> gauge-phase equivalent, then there is a unitary `U` and a unit-modulus scalar
> `ζ` with `B i = ζ • (U * A i * Uᴴ)`.

## Mathematical content

Write `B i = ζ • (X * A i * X⁻¹)` with `X` invertible.  The Perron--Frobenius
normalization step (`gaugePhase_scalar_norm_eq_one_of_leftCanonical_irreducible`)
forces `‖ζ‖ = 1`.  Substituting the gauge relation into `∑ᵢ Bᵢᴴ Bᵢ = 1`
(left-canonicity of `B`) shows that `W := Xᴴ X` is a positive-semidefinite fixed
point of the *adjoint* transfer map `Y ↦ ∑ᵢ Aᵢᴴ Y Aᵢ`.  Left-canonicity of `A`
makes `1` another such fixed point, and irreducibility of `A` (transported to the
conjugate-transposed Kraus family) gives uniqueness of the positive-semidefinite
fixed point up to scalar: `W = c • 1` with `c > 0` real.  Then `U := c^{-1/2} • X`
is unitary and `X⁻¹ = c⁻¹ • Xᴴ`, so `X * A i * X⁻¹ = U * A i * Uᴴ`.

This is the spatial-realization input behind the global corner unitary in
arXiv:1708.00029, Appendix A, lines 1110--1117 (`eq:result`).
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **Per-sector unitarity of the canonical-form gauge** (arXiv:1708.00029,
Appendix A, `thm:cf` / `eq:Cvprop`).

If `A` and `B` are both left-canonical and irreducible MPS tensors related by a
gauge-phase equivalence, then the gauge can be taken *unitary* and the scalar has
unit modulus: there exist a unitary `U` and `ζ` with `‖ζ‖ = 1` and
`B i = ζ • (U * A i * Uᴴ)` for every `i`.

This is the per-sector core of the corner unitaries `U_v`. -/
theorem exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible
    [NeZero D] {A B : MPSTensor d D}
    (h : GaugePhaseEquiv A B)
    (hA_left : IsLeftCanonical A) (hB_left : IsLeftCanonical B)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ i, B i = ζ • ((U : Matrix (Fin D) (Fin D) ℂ) * A i *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
  obtain ⟨X, ζ, hζ_ne, hB⟩ := h
  -- Step 0: the scalar has unit modulus (Perron--Frobenius normalization).
  have hζ1 : ‖ζ‖ = 1 :=
    gaugePhase_scalar_norm_eq_one_of_leftCanonical_irreducible
      hA_left hB_left hB_irr hζ_ne hB
  have hnz1 : ζ * star ζ = 1 := by
    have hmc : ζ * star ζ = ↑(Complex.normSq ζ) := Complex.mul_conj ζ
    rw [Complex.normSq_eq_norm_sq, hζ1] at hmc
    rw [hmc]; norm_num
  -- Inverse relations for the gauge matrix.
  have hXvXi : (↑X : Matrix (Fin D) (Fin D) ℂ) * (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) = 1 :=
    Units.mul_inv X
  have hXiXv : (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) * (↑X : Matrix (Fin D) (Fin D) ℂ) = 1 :=
    Units.inv_mul X
  -- The candidate positive-semidefinite fixed point `W = Xᴴ X`.
  set W : Matrix (Fin D) (Fin D) ℂ :=
    (↑X : Matrix (Fin D) (Fin D) ℂ)ᴴ * (↑X : Matrix (Fin D) (Fin D) ℂ) with hW_def
  -- Per-term expansion of the left-canonical sum of `B`.
  have hbb_term : ∀ i, (B i)ᴴ * B i
      = (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ * ((A i)ᴴ * W * A i) *
          (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) := by
    intro i
    rw [hB i, Matrix.conjTranspose_smul]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hnz1, one_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hW_def]
    simp only [Matrix.mul_assoc]
  -- `W` is a fixed point of the adjoint transfer map: `∑ᵢ Aᵢᴴ W Aᵢ = W`.
  have hSfix : (∑ i, (A i)ᴴ * W * A i) = W := by
    -- First: conjugating `∑ᵢ Aᵢᴴ W Aᵢ` by `X⁻¹` recovers the identity.
    have e1 : (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ * (∑ i, (A i)ᴴ * W * A i) *
        (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) = 1 := by
      calc
        (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ * (∑ i, (A i)ᴴ * W * A i) *
              (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)
            = ∑ i, (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ * ((A i)ᴴ * W * A i) *
                (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) := by
              rw [Finset.mul_sum, Finset.sum_mul]
          _ = ∑ i, (B i)ᴴ * B i :=
              Finset.sum_congr rfl (fun i _ => (hbb_term i).symm)
          _ = 1 := hB_left
    -- `Xᴴ Xⁱᴴ = 1`.
    have hVXi : (↑X : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hXiXv, Matrix.conjTranspose_one]
    -- Conjugate `e1` by `X` to extract the fixed-point identity.
    have key : (↑X : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          ((↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ * (∑ i, (A i)ᴴ * W * A i) *
            (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)) * (↑X : Matrix (Fin D) (Fin D) ℂ)
        = (↑X : Matrix (Fin D) (Fin D) ℂ)ᴴ * 1 * (↑X : Matrix (Fin D) (Fin D) ℂ) := by
      rw [e1]
    rw [show (↑X : Matrix (Fin D) (Fin D) ℂ)ᴴ *
            ((↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ * (∑ i, (A i)ᴴ * W * A i) *
              (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)) * (↑X : Matrix (Fin D) (Fin D) ℂ)
          = ((↑X : Matrix (Fin D) (Fin D) ℂ)ᴴ *
              (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ) * (∑ i, (A i)ᴴ * W * A i) *
              ((↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) * (↑X : Matrix (Fin D) (Fin D) ℂ))
          from by simp only [Matrix.mul_assoc]] at key
    rw [hVXi, hXiXv, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one] at key
    -- `key : ∑ᵢ Aᵢᴴ W Aᵢ = Xᴴ X = W`.
    rw [key, hW_def]
  -- Transfer-map phrasing of the fixed-point identity.
  have hWfix : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) W = W := by
    rw [transferMap_apply]
    simp only [Matrix.conjTranspose_conjTranspose]
    exact hSfix
  -- `1` is a fixed point too (left-canonicity of `A`).
  have h1_fix : transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
      (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    rw [transferMap_apply]
    simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_one]
    exact hA_left
  -- Irreducibility of the conjugate-transposed transfer map.
  have hIrrAdj : IsIrreducibleMap (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor A hA_irr
  -- Positive-semidefiniteness facts.
  have hW_psd : W.PosSemidef := by
    rw [hW_def]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have h1_psd : (1 : Matrix (Fin D) (Fin D) ℂ).PosSemidef := Matrix.PosDef.one.posSemidef
  have h1_ne : (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := one_ne_zero
  -- Uniqueness of the PSD fixed point: `W = c • 1`.
  obtain ⟨c, hc⟩ :=
    posSemidef_fixedPoint_unique_of_irreducible (d := d) (D := D)
      (fun i => (A i)ᴴ) hIrrAdj 1 W h1_psd h1_ne hW_psd h1_fix hWfix
  -- `X` is nonzero, hence so is `W`, hence `c ≠ 0`.
  have hXval_ne : (↑X : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
    intro h0
    exact one_ne_zero (by rw [← hXvXi, h0, Matrix.zero_mul])
  have hW_ne : W ≠ 0 := by
    rw [hW_def]
    intro h0
    exact hXval_ne
      (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [h0, Matrix.trace_zero]))
  have hc_ne : c ≠ 0 := by
    intro hc0; exact hW_ne (by rw [hc, hc0, zero_smul])
  -- `c` is a positive real.
  have hc_nonneg : (0 : ℂ) ≤ c := by
    have hd := hW_psd.diag_nonneg (i := (⟨0, NeZero.pos D⟩ : Fin D))
    have hWii : W (⟨0, NeZero.pos D⟩ : Fin D) (⟨0, NeZero.pos D⟩ : Fin D) = c := by
      rw [hc]; simp [Matrix.smul_apply, Matrix.one_apply_eq]
    rwa [hWii] at hd
  obtain ⟨_, hc_im⟩ := Complex.nonneg_iff.mp hc_nonneg
  have hc_pos : (0 : ℂ) < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_ne)
  obtain ⟨hc_re_pos, _⟩ := Complex.pos_iff.mp hc_pos
  have hc_eq : (c.re : ℂ) = c :=
    Complex.ext (Complex.ofReal_re c.re) (by rw [Complex.ofReal_im]; exact hc_im)
  -- The unitary normalization scalar `s = √(c.re)`.
  set s : ℝ := Real.sqrt c.re with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hc_re_pos
  have hs_ne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs_pos
  have hs_sq : s * s = c.re := Real.mul_self_sqrt (le_of_lt hc_re_pos)
  have hsc : (s : ℂ) * (s : ℂ) = c := by rw [← Complex.ofReal_mul, hs_sq, hc_eq]
  have hscalar : ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) * c = 1 := by
    rw [← hsc]; field_simp
  have hconjs : star ((s : ℂ)⁻¹) = (s : ℂ)⁻¹ := by
    rw [star_inv₀]
    congr 1
    exact Complex.conj_ofReal s
  -- The unitary gauge matrix.
  set U : Matrix (Fin D) (Fin D) ℂ :=
    (s : ℂ)⁻¹ • (↑X : Matrix (Fin D) (Fin D) ℂ) with hU_def
  have hU_unit : Uᴴ * U = 1 := by
    rw [hU_def, Matrix.conjTranspose_smul, hconjs]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [show (↑X : Matrix (Fin D) (Fin D) ℂ)ᴴ * (↑X : Matrix (Fin D) (Fin D) ℂ) = W
        from hW_def.symm, hc, smul_smul, hscalar, one_smul]
  have hU_mem : U ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr (by rw [Matrix.star_eq_conjTranspose]; exact hU_unit)
  -- `Xᴴ = c • X⁻¹`, the key for rewriting the conjugation.
  have hXadj : (↑X : Matrix (Fin D) (Fin D) ℂ)ᴴ
      = c • (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) := by
    have hmul := congrArg (· * (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)) hc
    simp only [hW_def] at hmul
    rwa [Matrix.mul_assoc, hXvXi, Matrix.mul_one, smul_mul_assoc, Matrix.one_mul] at hmul
  -- The unitary conjugation reproduces the gauge conjugation.
  have hconj_i : ∀ i, U * A i * Uᴴ
      = (↑X : Matrix (Fin D) (Fin D) ℂ) * A i * (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ) := by
    intro i
    rw [hU_def, Matrix.conjTranspose_smul, hconjs]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hXadj]
    simp only [mul_smul_comm, smul_smul]
    rw [hscalar, one_smul]
  -- Assemble the result.
  refine ⟨⟨U, hU_mem⟩, ζ, hζ1, fun i => ?_⟩
  rw [hB i]
  congr 1
  exact (hconj_i i).symm

end MPSTensor
