/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.MPS.Core.CanonicalNormalization
import TNLean.MPS.Core.CPPrimitive
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Irreducible.Adjoint
import TNLean.QPF.Assembly
import TNLean.QPF.Uniqueness

/-!
# Unitary gauges for left-canonical irreducible tensors

Gauge-phase equivalences between left-canonical irreducible tensors can be
upgraded from general invertible gauges to unitary gauges.

The paper builds \(U_v\) via the single-block canonical form (the Fundamental
Theorem rigidity, cited as Theorem 2.10 of Cirac--Pérez-García).  In the
canonical-form orientation, two left-canonical tensors that are gauge-phase
equivalent are related by a *unitary* gauge: the modulus of the scalar is one and
the invertible intertwiner can be normalized to a unitary.

More precisely, let \(A=(A^i)_i\) and \(B=(B^i)_i\) be left-canonical
irreducible tensors of the same bond dimension.  If they are related by a gauge
and a nonzero scalar, then there are a unitary matrix \(U\) and a scalar
\(\zeta\), with \(|\zeta|=1\), such that
\[
    B^i=\zeta U A^i U^\dagger
\]
for every physical index \(i\).

## Mathematical content

Write
\[
    B^i=\zeta X A^i X^{-1}
\]
with \(X\) invertible.  Perron--Frobenius normalization forces
\(|\zeta|=1\).  Substituting the gauge relation into
\(\sum_i (B^i)^\dagger B^i=I\) shows that \(W=X^\dagger X\) is a positive
semidefinite fixed point of the adjoint transfer map
\[
    Y\longmapsto\sum_i (A^i)^\dagger Y A^i.
\]
Left-canonicity makes \(I\) another such fixed point, and irreducibility gives
uniqueness of the positive semidefinite fixed point up to scale.  Hence
\(W=cI\) for some real \(c>0\).  It follows that
\(U=c^{-1/2}X\) is unitary and
\[
    X A^i X^{-1}=U A^i U^\dagger.
\]

This is the unitary-gauge input used both in the Fundamental Theorem refinement
of arXiv:1606.00608, Corollary A.6, and in the periodic corner-unitary argument
of arXiv:1708.00029, Appendix A, lines 1110--1117.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Cancellation for conjugation by an invertible matrix:
$X^{-1}(X Y X^\dagger)(X^{-1})^\dagger = Y$. -/
theorem gaugePhase_conj_cancel (X : GL (Fin D) ℂ)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    X⁻¹.val * (X.val * Y * X.valᴴ) * X⁻¹.valᴴ = Y := by
  have h1 : X⁻¹.val * X.val = 1 := Units.inv_mul X
  have h2 : X.valᴴ * X⁻¹.valᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.inv_mul]
    simp
  calc
    X⁻¹.val * (X.val * Y * X.valᴴ) * X⁻¹.valᴴ =
        X⁻¹.val * X.val * Y * (X.valᴴ * X⁻¹.valᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = 1 * Y * 1 := by rw [h1, h2]
    _ = Y := by simp

/-- In a gauge-phase equivalence between normalized irreducible tensor blocks,
the scalar has modulus one.

Applying the gauge relation to a positive fixed point of the first transfer map
gives a positive eigenvector of the second transfer map with eigenvalue
$\zeta\overline\zeta$. Irreducibility and trace preservation force this
eigenvalue to be one. -/
theorem gaugePhase_scalar_norm_eq_one_of_leftCanonical_irreducible
    [NeZero D] {A B : MPSTensor d D}
    (hA_left : IsLeftCanonical A) (hB_left : IsLeftCanonical B)
    (hB_irr : IsIrreducibleTensor B)
    {X : GL (Fin D) ℂ} {ζ : ℂ} (hζ_ne : ζ ≠ 0)
    (hB :
      ∀ i : Fin d,
        B i =
          ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ‖ζ‖ = 1 := by
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    exists_posSemidef_fixedPoint A hA_left (NeZero.pos D)
  obtain ⟨τ, hτ_psd, hτ_ne, hτ_fix⟩ :=
    exists_posSemidef_fixedPoint B hB_left (NeZero.pos D)
  have hB_irrMap : IsIrreducibleMap (transferMap (d := d) (D := D) B) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor B hB_irr
  have hB_cp : IsCPMap (transferMap (d := d) (D := D) B) := transferMap_isCPMap B
  have hEB_eq : ∀ Y, transferMap (d := d) (D := D) B Y =
      (ζ * starRingEnd ℂ ζ) •
        (X.val * transferMap (d := d) (D := D) A
          (X⁻¹.val * Y * X⁻¹.valᴴ) * X.valᴴ) := by
    intro Y
    simp only [transferMap_apply]
    simp_rw [hB]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul, ← Finset.smul_sum, Matrix.conjTranspose_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    congr 1
    exact mul_comm _ _
  let σ : Matrix (Fin D) (Fin D) ℂ := X.val * ρ * X.valᴴ
  have hσ_psd : σ.PosSemidef :=
    hρ_psd.mul_mul_conjTranspose_same X.val
  have hσ_ne : σ ≠ 0 := by
    intro hσ_zero
    apply hρ_ne
    have hcancel :=
      congr_arg (fun Y : Matrix (Fin D) (Fin D) ℂ => X⁻¹.val * Y * X⁻¹.valᴴ)
        hσ_zero
    simp only [σ, Matrix.mul_zero, Matrix.zero_mul] at hcancel
    rwa [gaugePhase_conj_cancel] at hcancel
  have hEB_σ :
      transferMap (d := d) (D := D) B σ =
        (ζ * starRingEnd ℂ ζ) • σ := by
    simp only [σ, hEB_eq, gaugePhase_conj_cancel, hρ_fix]
  have hζζ_real : ζ * starRingEnd ℂ ζ = (↑(‖ζ‖ ^ 2) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hζζ_pos : (0 : ℝ) < ‖ζ‖ ^ 2 := by
    have hnorm_ne : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hζ_ne
    exact sq_pos_of_ne_zero hnorm_ne
  have h_eig_eq : ‖ζ‖ ^ 2 = 1 :=
    (eigenvalue_unique_of_irreducible_cp
      (transferMap (d := d) (D := D) B) hB_cp hB_irrMap
      τ σ 1 (‖ζ‖ ^ 2) hτ_psd hτ_ne one_pos hσ_psd hσ_ne hζζ_pos
      (by simp [hτ_fix]) (by rw [hEB_σ, hζζ_real])).symm
  nlinarith [norm_nonneg ζ]

/-- **Unitarity of a specified canonical-form gauge and phase.**

Let \(A=(A^i)_i\) and \(B=(B^i)_i\) be left-canonical irreducible MPS tensors
related by
\[
    B^i=\zeta X A^iX^{-1},
\]
where \(X\) is invertible and \(\zeta\ne0\). Then \(X\) can be replaced by a
unitary matrix \(U\) without changing \(\zeta\), and \(|\zeta|=1\):
\[
    B^i=\zeta U A^iU^\dagger.
\]

Retaining the phase is needed in the equal-MPV case because the same phase
occurs in the matched copy-weight identity. Source: arXiv:1606.00608,
Corollary A.6, lines 1197--1199. -/
theorem exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
    [NeZero D] {A B : MPSTensor d D}
    (X : GL (Fin D) ℂ) (ζ : ℂ) (hζ_ne : ζ ≠ 0)
    (hB : ∀ i, B i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)))
    (hA_left : IsLeftCanonical A) (hB_left : IsLeftCanonical B)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ, ‖ζ‖ = 1 ∧
      ∀ i, B i = ζ • ((U : Matrix (Fin D) (Fin D) ℂ) * A i *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
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
  refine ⟨⟨U, hU_mem⟩, hζ1, fun i => ?_⟩
  rw [hB i]
  congr 1
  exact (hconj_i i).symm

/-- **Per-sector unitarity of the canonical-form gauge.**

Source: arXiv:1606.00608, Corollary A.6; arXiv:1708.00029, Appendix A.

If \(A=(A^i)_i\) and \(B=(B^i)_i\) are left-canonical irreducible MPS tensors
related by a gauge-phase equivalence, then the gauge can be taken unitary: there
exist a unitary matrix \(U\) and a scalar \(\zeta\), with \(|\zeta|=1\), such
that
\[
    B^i=\zeta U A^i U^\dagger
\]
for every physical index \(i\).

This is the common per-sector input for the Canonical Form II unitary
refinement and the periodic corner unitaries \(U_v\). -/
theorem exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible
    [NeZero D] {A B : MPSTensor d D}
    (h : GaugePhaseEquiv A B)
    (hA_left : IsLeftCanonical A) (hB_left : IsLeftCanonical B)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ i, B i = ζ • ((U : Matrix (Fin D) (Fin D) ℂ) * A i *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  obtain ⟨X, ζ, hζ_ne, hB⟩ := h
  obtain ⟨U, hζ, hConj⟩ :=
    exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
      X ζ hζ_ne hB hA_left hB_left hA_irr hB_irr
  exact ⟨U, ζ, hζ, hConj⟩

end MPSTensor
