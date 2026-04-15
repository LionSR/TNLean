/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.StructuralForm
import TNLean.Spectral.GaugeConstruction
import TNLean.Channel.KrausRepresentation
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Full structural form for RFP tensors (Lemma B.1)

This file proves the full Appendix B structural decomposition for
renormalization fixed-point tensors (arXiv:1606.00608, Lemma B.1). The main
result is `rfp_nt_structural_full`, which shows that a normal tensor in
canonical form II and at a renormalization fixed point admits a decomposition
`A i = X * diagonal Λ * U i * X⁻¹`, where `Λ` has positive diagonal entries
and the family `U` is isometric in the physical index.

The proof is self-contained and packages the full appendix argument in the main
`MPS/RFP` development.

## Proof strategy

The proof assembles the following ingredients:
* `rfp_nt_structural_of_leftCanonical` — left-canonical normal RFP ⟹ injective
* `rfp_nt_cfii_diagonal_fixedPoint` — after unitary conjugation, a diagonal
  positive-definite fixed point for the transfer map exists
* `transferMap_eq_fixedPointProj_of_isRFP_injective` — for an injective
  left-canonical RFP tensor, the transfer map equals `fixedPointProj ρ`, i.e.
  `X ↦ (tr X / tr ρ) • ρ`
* an explicit normalized matrix-unit Kraus family for `fixedPointProj ρ`,
  followed by `kraus_rectangular_freedom'` to extract the physical-index
  isometry family
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private lemma ofReal_re_eq_self_of_pos {z : ℂ} (hz : 0 < z) :
    ((z.re : ℝ) : ℂ) = z := by
  have h := (Complex.lt_def).1 hz
  have hz_im : z.im = 0 := by
    simpa using h.2.symm
  refine Complex.ext ?_ ?_
  · simp
  · simp [hz_im]

private lemma sum_single_diag_const (c : ℂ) :
    ∑ i : Fin D, Matrix.single i i c = c • (1 : Mat) := by
  rw [Matrix.sum_single_eq_diagonal, Matrix.smul_one_eq_diagonal]

private lemma matrixUnits_map (X : Mat) :
    ∑ p : Fin D × Fin D,
      Matrix.single p.1 p.2 (1 : ℂ) * X * (Matrix.single p.1 p.2 (1 : ℂ))ᴴ =
      Matrix.trace X • (1 : Mat) := by
  calc
    ∑ p : Fin D × Fin D,
        Matrix.single p.1 p.2 (1 : ℂ) * X * (Matrix.single p.1 p.2 (1 : ℂ))ᴴ
      = ∑ p : Fin D × Fin D, Matrix.single p.1 p.1 (X p.2 p.2) := by
          refine Finset.sum_congr rfl ?_
          rintro ⟨j, i⟩ _
          rw [Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single]
          simp
    _ = ∑ j : Fin D, ∑ i : Fin D, Matrix.single j j (X i i) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ j : Fin D, Matrix.single j j (∑ i : Fin D, X i i) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact
            (map_sum (Matrix.singleAddMonoidHom (α := ℂ) j j)
              (fun i => X i i) Finset.univ).symm
    _ = ∑ j : Fin D, Matrix.single j j (Matrix.trace X) := by
          simp [Matrix.trace, Matrix.diag]
    _ = Matrix.trace X • (1 : Mat) := by
          simpa using sum_single_diag_const (D := D) (c := Matrix.trace X)

/-- **Lemma B.1** (arXiv:1606.00608, Appendix B): a normal tensor in canonical
form II that is an RFP admits the decomposition `A i = X * Λ * U i * X⁻¹`
with diagonal positive `Λ` and a physical-index isometry `U`.

The proof combines the diagonal fixed-point reduction
`rfp_nt_cfii_diagonal_fixedPoint`, the rank-one classification
`transferMap_eq_fixedPointProj_of_isRFP_injective`, and an explicit Kraus
realization of `fixedPointProj ρ`. Applying `kraus_rectangular_freedom'`
identifies the physical-index family with an isometry and yields the witnesses
`X * diag(Λ) * U i * X⁻¹`. -/
theorem rfp_nt_structural_full (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ (X : Matrix (Fin D) (Fin D) ℂ) (Λ : Fin D → ℝ)
      (U : MPSTensor d D),
      X.det ≠ 0 ∧
      (∀ k, 0 < Λ k) ∧
      (∑ i : Fin d, (U i)ᴴ * U i = 1) ∧
      (∀ i, A i = X * Matrix.diagonal (fun k => (Λ k : ℂ)) * U i * X⁻¹) := by
  classical
  have hInjA : IsInjective A :=
    rfp_nt_structural_of_leftCanonical A hNT hRFP hLeft
  obtain ⟨U₀, ρ, hρ_pd, hρ_diag, hB_left, hB_fix⟩ :=
    rfp_nt_cfii_diagonal_fixedPoint A hNT hRFP hLeft
  let X : Mat := ↑U₀
  let B : MPSTensor d D := fun i => Xᴴ * A i * X
  have hX_det : X.det ≠ 0 := (Matrix.UnitaryGroup.det_isUnit U₀).ne_zero
  have hXhX : Xᴴ * X = 1 := by
    simpa [X, Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U₀
  have hXXh : X * Xᴴ = 1 := by
    simpa [X, Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem U₀.prop
  have hX_inv : X⁻¹ = Xᴴ := by
    exact Matrix.right_inv_eq_left_inv
      (Matrix.mul_nonsing_inv X (Ne.isUnit hX_det)) hXhX
  have hB_eq_gauge : B = gaugeTensor X A := by
    ext i
    simp [B, gaugeTensor, hX_inv]
  have hB_inj : IsInjective B := by
    rw [hB_eq_gauge]
    exact isInjective_conjugate (d := d) A hInjA X hX_det
  obtain ⟨V₀, hV₀_iso, hV₀_prod⟩ := (isRFP_iff_kraus_isometry A).1 hRFP
  have hB_prod : ∀ i₁ i₂ : Fin d,
      B i₁ * B i₂ = ∑ j : Fin d, V₀ (i₁, i₂) j • B j := by
    intro i₁ i₂
    calc
      B i₁ * B i₂ = Xᴴ * A i₁ * X * (Xᴴ * A i₂ * X) := by
        rfl
      _ = Xᴴ * A i₁ * (X * Xᴴ) * A i₂ * X := by
        simp [Matrix.mul_assoc]
      _ = Xᴴ * (A i₁ * A i₂) * X := by
        simp [Matrix.mul_assoc, hXXh]
      _ = Xᴴ * (∑ j : Fin d, V₀ (i₁, i₂) j • A j) * X := by
        rw [hV₀_prod i₁ i₂]
      _ = ∑ j : Fin d, V₀ (i₁, i₂) j • B j := by
        simp [B, Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
  have hB_rfp : IsRFP B :=
    (isRFP_iff_kraus_isometry B).2 ⟨V₀, hV₀_iso, hB_prod⟩
  have htr : Matrix.trace ρ ≠ 0 := ne_of_gt hρ_pd.trace_pos
  have hB_proj : transferMap B = fixedPointProj ρ htr := by
    simpa [htr] using
      transferMap_eq_fixedPointProj_of_isRFP_injective
        B hB_inj hB_rfp hB_left ρ hρ_pd hB_fix
  have hρ_eq_diag : ρ = Matrix.diagonal (fun k => ρ k k) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simpa [hij] using hρ_diag hij
  have hρdiag_pos : ∀ k : Fin D, 0 < ρ k k := by
    have hdiag_pd : (Matrix.diagonal (fun k => ρ k k) : Mat).PosDef := by
      rwa [← hρ_eq_diag]
    rw [Matrix.posDef_diagonal_iff] at hdiag_pd
    exact hdiag_pd
  have htr_re_eq : (((Matrix.trace ρ).re : ℝ) : ℂ) = Matrix.trace ρ :=
    ofReal_re_eq_self_of_pos hρ_pd.trace_pos
  have hρii_re_eq : ∀ k : Fin D, (((ρ k k).re : ℝ) : ℂ) = ρ k k :=
    fun k => ofReal_re_eq_self_of_pos (hρdiag_pos k)
  have hDpos_nat : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast hDpos_nat
  have hD_neC : (D : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne D)
  let Λ : Fin D → ℝ := fun k =>
    Real.sqrt (((D : ℝ) * (ρ k k).re) / (Matrix.trace ρ).re)
  let L : Mat := Matrix.diagonal (fun k => (Λ k : ℂ))
  let c : ℂ := ((1 / Real.sqrt (D : ℝ) : ℝ) : ℂ)
  let E : Fin D × Fin D → Mat := fun p => c • Matrix.single p.1 p.2 (1 : ℂ)
  let K : Fin D × Fin D → Mat := fun p => L * E p
  have hc_norm : c * star c = (1 : ℂ) / (D : ℂ) := by
    have hsqrt_ne : Real.sqrt (D : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hDpos
    have hreal :
        (1 / Real.sqrt (D : ℝ)) * (1 / Real.sqrt (D : ℝ)) = 1 / (D : ℝ) := by
      field_simp [hsqrt_ne]
      have hsq : Real.sqrt (D : ℝ) * Real.sqrt (D : ℝ) = (D : ℝ) := by
        have hnn : 0 ≤ (D : ℝ) := by positivity
        nlinarith [Real.sq_sqrt hnn]
      nlinarith
    have hrealC := congrArg (fun r : ℝ => (r : ℂ)) hreal
    simpa [c, Complex.ofReal_mul, Complex.ofReal_div, hD_neC] using hrealC
  have hE_map : ∀ Y : Mat,
      ∑ p : Fin D × Fin D, E p * Y * (E p)ᴴ =
        (Matrix.trace Y / (D : ℂ)) • (1 : Mat) := by
    intro Y
    calc
      ∑ p : Fin D × Fin D, E p * Y * (E p)ᴴ
        = ∑ p : Fin D × Fin D,
            (c * star c) •
              (Matrix.single p.1 p.2 (1 : ℂ) * Y *
                (Matrix.single p.1 p.2 (1 : ℂ))ᴴ) := by
            refine Finset.sum_congr rfl ?_
            intro p _
            let F : Mat := Matrix.single p.1 p.2 (1 : ℂ)
            have hsingle : Matrix.single p.1 p.2 c = c • F := by
              simp [F, Matrix.smul_single]
            calc
              E p * Y * (E p)ᴴ = Matrix.single p.1 p.2 c * Y * (Matrix.single p.1 p.2 c)ᴴ := by
                rw [hsingle]
              _ = (c • F) * Y * ((c • F)ᴴ) := by rw [hsingle]
              _ = (c * star c) • (F * Y * Fᴴ) := by
                simp [mul_comm, Matrix.conjTranspose_smul, Matrix.mul_assoc, smul_smul]
              _ = (c * star c) •
                    (Matrix.single p.1 p.2 (1 : ℂ) * Y *
                      (Matrix.single p.1 p.2 (1 : ℂ))ᴴ) := by
                simp [F]
      _ = (c * star c) •
            (∑ p : Fin D × Fin D,
              Matrix.single p.1 p.2 (1 : ℂ) * Y *
                (Matrix.single p.1 p.2 (1 : ℂ))ᴴ) := by
            simp_rw [Finset.smul_sum]
      _ = (c * star c) • (Matrix.trace Y • (1 : Mat)) := by
            rw [matrixUnits_map (D := D) Y]
      _ = (Matrix.trace Y / (D : ℂ)) • (1 : Mat) := by
            rw [hc_norm]
            simp [smul_smul, div_eq_mul_inv, mul_comm]
  let T : Mat →ₗ[ℂ] Mat :=
    fixedPointProj (1 : Mat) (by simpa [Matrix.trace_one] using hD_neC)
  have hT_tp : IsTracePreservingMap T := by
    intro Y
    simp [T, fixedPointProj, Matrix.trace_one]
  let e : Fin D × Fin D ≃ Fin (Fintype.card (Fin D × Fin D)) :=
    Fintype.equivFin (Fin D × Fin D)
  let Efin : Fin (Fintype.card (Fin D × Fin D)) → Mat := E ∘ e.symm
  have hEfin_map : ∀ Y : Mat, T Y = ∑ i, Efin i * Y * (Efin i)ᴴ := by
    intro Y
    calc
      T Y = (Matrix.trace Y / (D : ℂ)) • (1 : Mat) := by
        simp [T, fixedPointProj, Matrix.trace_one]
      _ = ∑ p : Fin D × Fin D, E p * Y * (E p)ᴴ := by
        symm
        exact hE_map Y
      _ = ∑ i, Efin i * Y * (Efin i)ᴴ := by
        symm
        change ∑ i, E (e.symm i) * Y * (E (e.symm i))ᴴ = _
        rw [e.symm.sum_comp (fun p : Fin D × Fin D => E p * Y * (E p)ᴴ)]
  have hE_left_fin : ∑ i, (Efin i)ᴴ * Efin i = 1 := by
    exact kraus_sum_conjTranspose_mul_of_tp Efin T hEfin_map hT_tp
  have hE_left : ∑ p : Fin D × Fin D, (E p)ᴴ * E p = 1 := by
    have hsum : ∑ i, (Efin i)ᴴ * Efin i = ∑ p : Fin D × Fin D, (E p)ᴴ * E p := by
      change ∑ i, (E (e.symm i))ᴴ * E (e.symm i) = _
      rw [e.symm.sum_comp (fun p : Fin D × Fin D => (E p)ᴴ * E p)]
    rwa [hsum] at hE_left_fin
  have hL_herm : Lᴴ = L := by
    simp [L, Matrix.diagonal_conjTranspose]
  have hL_sq : L * L = ((D : ℂ) / Matrix.trace ρ) • ρ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hρii_re_pos : 0 < (ρ i i).re := by
        exact (Complex.lt_def).1 (hρdiag_pos i) |>.1
      have htr_re_pos : 0 < (Matrix.trace ρ).re := by
        exact (Complex.lt_def).1 hρ_pd.trace_pos |>.1
      have harg_nonneg : 0 ≤ ((D : ℝ) * (ρ i i).re) / (Matrix.trace ρ).re := by
        exact div_nonneg (by positivity) (le_of_lt htr_re_pos)
      have htr_re_ne : (Matrix.trace ρ).re ≠ 0 := by
        linarith
      have hDdiv : ((((D : ℝ) / (Matrix.trace ρ).re : ℝ)) : ℂ) = (D : ℂ) / Matrix.trace ρ := by
        calc
          ((((D : ℝ) / (Matrix.trace ρ).re : ℝ)) : ℂ)
              = (D : ℂ) / ((((Matrix.trace ρ).re : ℝ)) : ℂ) := by
                  simp [Complex.ofReal_div]
          _ = (D : ℂ) / Matrix.trace ρ := by rw [htr_re_eq]
      have hentry : ((Λ i : ℂ) * (Λ i : ℂ)) = ((D : ℂ) / Matrix.trace ρ) * ρ i i := by
        calc
          ((Λ i : ℂ) * (Λ i : ℂ))
              = ((((D : ℝ) * (ρ i i).re / (Matrix.trace ρ).re : ℝ)) : ℂ) := by
                  have hsqrt := congrArg (fun r : ℝ => (r : ℂ)) (Real.sq_sqrt harg_nonneg)
                  simpa [Λ, sq] using hsqrt
          _ = ((((D : ℝ) / (Matrix.trace ρ).re : ℝ)) : ℂ) * (((ρ i i).re : ℝ) : ℂ) := by
                have hreal :
                    (D : ℝ) * (ρ i i).re / (Matrix.trace ρ).re =
                      ((D : ℝ) / (Matrix.trace ρ).re) * (ρ i i).re := by
                  ring
                simpa [Complex.ofReal_mul, Complex.ofReal_div] using
                  congrArg (fun r : ℝ => (r : ℂ)) hreal
          _ = ((D : ℂ) / Matrix.trace ρ) * ρ i i := by
                rw [hDdiv, hρii_re_eq i]
      simpa [L, Matrix.diagonal_mul_diagonal] using hentry
    · have hρij : ρ i j = 0 := hρ_diag hij
      simp [L, hij, hρij]
  have hK_map : ∀ Y : Mat,
      ∑ p : Fin D × Fin D, K p * Y * (K p)ᴴ = fixedPointProj ρ htr Y := by
    intro Y
    calc
      ∑ p : Fin D × Fin D, K p * Y * (K p)ᴴ
        = ∑ p : Fin D × Fin D, L * (E p * Y * (E p)ᴴ) * L := by
            refine Finset.sum_congr rfl ?_
            intro p _
            simp [K, Matrix.mul_assoc, hL_herm]
      _ = L * (∑ p : Fin D × Fin D, E p * Y * (E p)ᴴ) * L := by
            simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
      _ = L * (((Matrix.trace Y) / (D : ℂ)) • (1 : Mat)) * L := by
            rw [hE_map Y]
      _ = (Matrix.trace Y / (D : ℂ)) • (L * L) := by
            simp
      _ = (Matrix.trace Y / (D : ℂ)) • ((((D : ℂ) / Matrix.trace ρ)) • ρ) := by
            rw [hL_sq]
      _ = (Matrix.trace Y / Matrix.trace ρ) • ρ := by
            have hs :
                (Matrix.trace Y / (D : ℂ)) * ((D : ℂ) / Matrix.trace ρ) =
                  Matrix.trace Y / Matrix.trace ρ := by
              field_simp [hD_neC, htr]
            rw [smul_smul, hs]
      _ = fixedPointProj ρ htr Y := by
            rfl
  have hRangeCard : D * D ≤ (Set.range B).toFinset.card := by
    have hspan_finrank : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range B)) = D * D := by
      rw [hB_inj, finrank_top, Module.finrank_matrix]
      simp
    have hspan_le :
        Module.finrank ℂ ↥(Submodule.span ℂ (Set.range B)) ≤
          (Set.range B).toFinset.card :=
      finrank_span_le_card (R := ℂ) (M := Mat) (s := Set.range B)
    exact hspan_finrank.symm.le.trans hspan_le
  have hrange_card_le : (Set.range B).toFinset.card ≤ d := by
    have hs : Finset.univ.image B = (Set.range B).toFinset := by
      ext M
      simp
    rw [← hs]
    simpa using (Finset.card_image_le (s := Finset.univ) (f := B))
  have hCard : Fintype.card (Fin D × Fin D) ≤ Fintype.card (Fin d) := by
    have hDD_le_d : D * D ≤ d := hRangeCard.trans hrange_card_le
    simpa [Fintype.card_prod, Fintype.card_fin] using hDD_le_d
  have hmapBK : ∀ Y : Mat,
      ∑ i : Fin d, B i * Y * (B i)ᴴ = ∑ p : Fin D × Fin D, K p * Y * (K p)ᴴ := by
    intro Y
    calc
      ∑ i : Fin d, B i * Y * (B i)ᴴ = transferMap B Y := by
        simp [MPSTensor.transferMap_apply]
      _ = fixedPointProj ρ htr Y := by
        rw [hB_proj]
      _ = ∑ p : Fin D × Fin D, K p * Y * (K p)ᴴ := by
        symm
        exact hK_map Y
  obtain ⟨V, hV_iso, hB_decomp⟩ :=
    kraus_rectangular_freedom' B K hmapBK hCard
  let U : MPSTensor d D := fun i => ∑ p : Fin D × Fin D, V i p • E p
  have hV_entry : ∀ p q : Fin D × Fin D,
      ∑ i : Fin d, star (V i p) * V i q = if p = q then 1 else 0 := by
    intro p q
    have h := congrFun (congrFun hV_iso p) q
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  have hU_left : ∑ i : Fin d, (U i)ᴴ * U i = 1 := by
    calc
      ∑ i : Fin d, (U i)ᴴ * U i
          = ∑ i : Fin d,
              (∑ p : Fin D × Fin D, V i p • E p)ᴴ *
                (∑ q : Fin D × Fin D, V i q • E q) := by
              simp [U]
      _ = ∑ i : Fin d, ∑ p : Fin D × Fin D, ∑ q : Fin D × Fin D,
            (star (V i p) * V i q) • ((E p)ᴴ * E q) := by
              simp_rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
                Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = ∑ p : Fin D × Fin D, ∑ q : Fin D × Fin D,
            (∑ i : Fin d, star (V i p) * V i q) • ((E p)ᴴ * E q) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro p _
              rw [Finset.sum_comm]
              simp_rw [← Finset.sum_smul]
      _ = ∑ p : Fin D × Fin D, ∑ q : Fin D × Fin D,
            (if p = q then 1 else 0) • ((E p)ᴴ * E q) := by
              refine Finset.sum_congr rfl ?_
              intro p _
              refine Finset.sum_congr rfl ?_
              intro q _
              rw [hV_entry]
              simp
      _ = ∑ p : Fin D × Fin D, (E p)ᴴ * E p := by
              simp
      _ = 1 := hE_left
  have hB_fact : ∀ i : Fin d, B i = L * U i := by
    intro i
    calc
      B i = ∑ p : Fin D × Fin D, V i p • K p := hB_decomp i
      _ = ∑ p : Fin D × Fin D, V i p • (L * E p) := by
            simp [K]
      _ = L * (∑ p : Fin D × Fin D, V i p • E p) := by
            simp [Finset.mul_sum]
      _ = L * U i := by
            simp [U]
  refine ⟨X, Λ, U, hX_det, ?_, hU_left, ?_⟩
  · intro k
    apply Real.sqrt_pos.2
    have hk_pos : 0 < (ρ k k).re := by
      exact (Complex.lt_def).1 (hρdiag_pos k) |>.1
    have htr_pos : 0 < (Matrix.trace ρ).re := by
      exact (Complex.lt_def).1 hρ_pd.trace_pos |>.1
    positivity
  · intro i
    calc
      A i = X * B i * X⁻¹ := by
        rw [hX_inv]
        calc
          A i = (X * Xᴴ) * A i * (X * Xᴴ) := by simp [hXXh]
          _ = X * (Xᴴ * A i * X) * Xᴴ := by simp [Matrix.mul_assoc]
          _ = X * B i * Xᴴ := by simp [B]
      _ = X * (L * U i) * X⁻¹ := by
        rw [hB_fact i]
      _ = X * Matrix.diagonal (fun k => (Λ k : ℂ)) * U i * X⁻¹ := by
        simp [L, Matrix.mul_assoc]
end MPSTensor
