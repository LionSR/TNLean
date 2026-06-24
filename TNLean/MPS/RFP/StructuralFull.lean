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
and the family `U` is left-canonical with a scaled pair-index orthonormality.

The proof is self-contained and contains the full appendix argument in the main
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
          simp only [one_mul, mul_one]
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
          rw [Matrix.sum_single_eq_diagonal, Matrix.smul_one_eq_diagonal]

/-- Full Appendix B extraction with the diagonal-weight square-sum identity.

This is the structural decomposition `A i = X * Λ * U i * X⁻¹` of Lemma B.1 with
one extra recorded fact: the diagonal weights satisfy `∑ k, (Λ k) ^ 2 = D` in
the matrix-unit normalization used here. That identity comes from
`(Λ k) ^ 2 = D · ρ_{k,k} / tr ρ` together with the trace identity
`∑ k ρ_{k,k} = tr ρ` for the diagonal fixed point `ρ`. It is the seed for the
source trace-normalization `tr(Λ) = 1` after rescaling to the unit pair-index
convention (arXiv:1606.00608, Lemma charact-NT-pure-RFP, lines 1271--1301).

The plain structural form `rfp_nt_structural_full` is the wrapper that drops the
square-sum conjunct; the trace-normalized form
`isIsometryCanonicalForm_of_rfp_nt` is the wrapper that consumes it. -/
theorem rfp_nt_structural_full_sqSum (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ (X : Matrix (Fin D) (Fin D) ℂ) (Λ : Fin D → ℝ)
      (U : MPSTensor d D),
      X.det ≠ 0 ∧
      (∀ k, 0 < Λ k) ∧
      (∑ i : Fin d, (U i)ᴴ * U i = 1) ∧
      (∀ p q : Fin D × Fin D,
        ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2 =
          if p = q then (D : ℂ)⁻¹ else 0) ∧
      (∑ k : Fin D, (Λ k) ^ 2 = (D : ℝ)) ∧
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
      rw [Matrix.diagonal_apply, if_pos rfl]
    · simpa [hij] using hρ_diag hij
  have hρdiag_pos : ∀ k : Fin D, 0 < ρ k k := by
    have hdiag_pd : (Matrix.diagonal (fun k => ρ k k) : Mat).PosDef := by
      rwa [← hρ_eq_diag]
    rw [Matrix.posDef_diagonal_iff] at hdiag_pd
    exact hdiag_pd
  have htr_re_eq : (((Matrix.trace ρ).re : ℝ) : ℂ) = Matrix.trace ρ :=
    (RCLike.ofReal_eq_re_of_isSelfAdjoint
      (IsSelfAdjoint.of_nonneg (le_of_lt hρ_pd.trace_pos))).mp rfl
  have hρii_re_eq : ∀ k : Fin D, (((ρ k k).re : ℝ) : ℂ) = ρ k k :=
    fun k =>
      (RCLike.ofReal_eq_re_of_isSelfAdjoint
        (IsSelfAdjoint.of_nonneg (le_of_lt (hρdiag_pos k)))).mp rfl
  have hDpos_nat : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast hDpos_nat
  have hD_neC : (D : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne D
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
        exact (RCLike.pos_iff.mp (hρdiag_pos i)).1
      have htr_re_pos : 0 < (Matrix.trace ρ).re := by
        exact (RCLike.pos_iff.mp hρ_pd.trace_pos).1
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
            rw [Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc]
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
      simp [Fintype.card_fin]
    have hspan_le :
        Module.finrank ℂ ↥(Submodule.span ℂ (Set.range B)) ≤
          (Set.range B).toFinset.card :=
      finrank_span_le_card (R := ℂ) (M := Mat) (s := Set.range B)
    exact hspan_finrank.symm.le.trans hspan_le
  have hrange_card_le : (Set.range B).toFinset.card ≤ d := by
    have hs : Finset.univ.image B = (Set.range B).toFinset := by
      exact (Set.toFinset_range (f := B)).symm
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
  have hU_entry : ∀ (i : Fin d) (p : Fin D × Fin D), U i p.1 p.2 = c * V i p := by
    intro i p
    simp only [U, E, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [Matrix.sum_apply]
    rw [Finset.sum_eq_single p]
    · simp [mul_comm]
    · intro q _ hq
      have hcoord : q.1 ≠ p.1 ∨ q.2 ≠ p.2 := by
        by_cases h1 : q.1 = p.1
        · right
          intro h2
          apply hq
          exact Prod.ext h1 h2
        · exact Or.inl h1
      rcases hcoord with h1 | h2
      · simp [h1]
      · simp [h2]
    · simp
  have hc_norm' : star c * c = (D : ℂ)⁻¹ := by
    rw [mul_comm, hc_norm]
    simp [div_eq_mul_inv]
  have hU_pair : ∀ p q : Fin D × Fin D,
      ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2 =
        if p = q then (D : ℂ)⁻¹ else 0 := by
    intro p q
    calc
      ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2
          = ∑ i : Fin d, (star c * c) * (star (V i p) * V i q) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [hU_entry i p, hU_entry i q]
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ = (star c * c) * ∑ i : Fin d, star (V i p) * V i q := by
              rw [Finset.mul_sum]
      _ = (star c * c) * (if p = q then 1 else 0) := by
              rw [hV_entry p q]
      _ = if p = q then (D : ℂ)⁻¹ else 0 := by
              by_cases hpq : p = q
              · simpa [hpq] using hc_norm'
              · simp [hpq]
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
              by_cases hpq : p = q <;> simp [hpq]
      _ = ∑ p : Fin D × Fin D, (E p)ᴴ * E p := by
              simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
                Finset.mem_univ, ↓reduceIte]
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
  have htr_re_pos : 0 < (Matrix.trace ρ).re := by
    exact (RCLike.pos_iff.mp hρ_pd.trace_pos).1
  have htr_re_ne : (Matrix.trace ρ).re ≠ 0 := ne_of_gt htr_re_pos
  -- `∑ k (Λ k)^2 = D`: each square is `D · ρ_{k,k} / tr ρ`, and `∑ ρ_{k,k} = tr ρ`.
  have hΛsq : ∀ k : Fin D, (Λ k) ^ 2 = (D : ℝ) * (ρ k k).re / (Matrix.trace ρ).re := by
    intro k
    have hk_nonneg : 0 ≤ (ρ k k).re := le_of_lt (RCLike.pos_iff.mp (hρdiag_pos k)).1
    have harg_nonneg : 0 ≤ ((D : ℝ) * (ρ k k).re) / (Matrix.trace ρ).re :=
      div_nonneg (by positivity) (le_of_lt htr_re_pos)
    simpa [Λ, sq] using Real.sq_sqrt harg_nonneg
  have htrace_re_sum : (Matrix.trace ρ).re = ∑ k : Fin D, (ρ k k).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  have hΛ_sq_sum : ∑ k : Fin D, (Λ k) ^ 2 = (D : ℝ) := by
    calc
      ∑ k : Fin D, (Λ k) ^ 2
          = ∑ k : Fin D, (D : ℝ) * (ρ k k).re / (Matrix.trace ρ).re := by
            exact Finset.sum_congr rfl (fun k _ => hΛsq k)
      _ = (D : ℝ) * (∑ k : Fin D, (ρ k k).re) / (Matrix.trace ρ).re := by
            rw [← Finset.sum_div, ← Finset.mul_sum]
      _ = (D : ℝ) * (Matrix.trace ρ).re / (Matrix.trace ρ).re := by
            rw [htrace_re_sum]
      _ = (D : ℝ) := by
            field_simp [htr_re_ne]
  refine ⟨X, Λ, U, hX_det, ?_, hU_left, hU_pair, hΛ_sq_sum, ?_⟩
  · intro k
    apply Real.sqrt_pos.2
    have hk_pos : 0 < (ρ k k).re := by
      exact (RCLike.pos_iff.mp (hρdiag_pos k)).1
    have htr_pos : 0 < (Matrix.trace ρ).re := by
      exact (RCLike.pos_iff.mp hρ_pd.trace_pos).1
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

/-- **Lemma B.1** (arXiv:1606.00608, Appendix B): a normal tensor in canonical
form II that is an RFP admits the decomposition `A i = X * Λ * U i * X⁻¹`
with diagonal positive `Λ` and a residual tensor `U` satisfying the
left-canonical equation and the scaled pair-index orthonormality
\[
  \sum_i \overline{(U^i)_{\alpha,\beta}}\,(U^i)_{\alpha',\beta'}
  =
  D^{-1}\delta_{(\alpha,\beta),(\alpha',\beta')}.
\]

The proof combines the diagonal fixed-point reduction
`rfp_nt_cfii_diagonal_fixedPoint`, the rank-one classification
`transferMap_eq_fixedPointProj_of_isRFP_injective`, and an explicit Kraus
realization of `fixedPointProj ρ`. Applying `kraus_rectangular_freedom'`
identifies the physical-index coefficients with an isometry. The matrix units
are normalized by $D^{-1/2}$, so the resulting matrix entries carry the
displayed factor $D^{-1}$. -/
theorem rfp_nt_structural_full (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ (X : Matrix (Fin D) (Fin D) ℂ) (Λ : Fin D → ℝ)
      (U : MPSTensor d D),
      X.det ≠ 0 ∧
      (∀ k, 0 < Λ k) ∧
      (∑ i : Fin d, (U i)ᴴ * U i = 1) ∧
      (∀ p q : Fin D × Fin D,
        ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2 =
          if p = q then (D : ℂ)⁻¹ else 0) ∧
      (∀ i, A i = X * Matrix.diagonal (fun k => (Λ k : ℂ)) * U i * X⁻¹) := by
  obtain ⟨X, Λ, U, hX_det, hΛ_pos, hU_left, hU_pair, _, hA_eq⟩ :=
    rfp_nt_structural_full_sqSum A hNT hRFP hLeft
  exact ⟨X, Λ, U, hX_det, hΛ_pos, hU_left, hU_pair, hA_eq⟩

/-- `(√D : ℂ)` times its conjugate is `D`. Used to rescale the `D⁻¹` pair-index
orthonormality to the unit convention. -/
private theorem sqrtCard_star_mul [NeZero D] :
    star ((Real.sqrt (D : ℝ) : ℂ)) * (Real.sqrt (D : ℝ) : ℂ) = (D : ℂ) := by
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hs_sq : Real.sqrt (D : ℝ) * Real.sqrt (D : ℝ) = (D : ℝ) := by
    rw [← pow_two]; exact Real.sq_sqrt (le_of_lt hDpos)
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, hs_sq,
    Complex.ofReal_natCast]

/-- Rescaling a residual tensor `U₀` with `D⁻¹` pair-index orthonormality by the
scalar `√D` upgrades it to the unit pair-index convention
\[
  \sum_i \overline{(U^i)_{\alpha,\beta}}\,(U^i)_{\alpha',\beta'}
  = \delta_{\alpha,\alpha'}\delta_{\beta,\beta'},
  \qquad U^i = \sqrt D\,U_0^i.
\]
Shared between `rfp_nt_structural_full_unit_pair` and
`isIsometryCanonicalForm_of_rfp_nt`. -/
private theorem unit_pair_of_scaled_sqrtCard [NeZero D] (U₀ : MPSTensor d D)
    (hU₀_pair : ∀ p q : Fin D × Fin D,
      ∑ i : Fin d, star (U₀ i p.1 p.2) * U₀ i q.1 q.2 =
        if p = q then (D : ℂ)⁻¹ else 0)
    (p q : Fin D × Fin D) :
    ∑ i : Fin d,
        star (((Real.sqrt (D : ℝ) : ℂ) • U₀ i) p.1 p.2) *
          ((Real.sqrt (D : ℝ) : ℂ) • U₀ i) q.1 q.2 =
      if p = q then 1 else 0 := by
  have hD_ne : (D : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne D)
  set s : ℂ := (Real.sqrt (D : ℝ) : ℂ) with hs
  calc
    ∑ i : Fin d, star ((s • U₀ i) p.1 p.2) * (s • U₀ i) q.1 q.2
        = ∑ i : Fin d, (star s * s) * (star (U₀ i p.1 p.2) * U₀ i q.1 q.2) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (star s * s) * ∑ i : Fin d, star (U₀ i p.1 p.2) * U₀ i q.1 q.2 := by
          rw [Finset.mul_sum]
    _ = (D : ℂ) * (if p = q then (D : ℂ)⁻¹ else 0) := by
          rw [hs, sqrtCard_star_mul, hU₀_pair p q]
    _ = if p = q then 1 else 0 := by
          by_cases hpq : p = q
          · simp [hpq, hD_ne]
          · simp [hpq]

/-- **Unit pair-index form of Lemma B.1.**  This is the same structural
decomposition as the isometry theorem above
(Theorem~\ref{thm:rfp_nt_structural_full}), rewritten in the source convention
for the pair-index isometry equation
\[
  \sum_i \overline{(U^i)_{\alpha,\beta}}\,(U^i)_{\alpha',\beta'}
  =
  \delta_{\alpha,\alpha'}\delta_{\beta,\beta'}.
\]

The theorem is only a normalization comparison: the diagonal factor is rescaled by
\(D^{-1/2}\), and the residual tensor by \(D^{1/2}\).

**Scope restriction (source isometry):** Corollary III.cor3 and the joint
isometry equation in arXiv:1606.00608, lines 550--554, also include the source
trace condition \(\operatorname{tr}\Lambda=1\) and cross-block
\(\delta_{j,j'}\) orthogonality.  Those conclusions are not proved here; this
theorem only compares the scalar normalization for a single block.  This
restriction is recorded in `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`.
Elimination: prove a whole-family isometry form with trace-normalized diagonal
weights and orthogonality between distinct blocks. -/
theorem rfp_nt_structural_full_unit_pair (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ (X : Matrix (Fin D) (Fin D) ℂ) (Λ : Fin D → ℝ)
      (U : MPSTensor d D),
      X.det ≠ 0 ∧
      (∀ k, 0 < Λ k) ∧
      (∀ p q : Fin D × Fin D,
        ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2 =
          if p = q then 1 else 0) ∧
      (∀ i, A i = X * Matrix.diagonal (fun k => (Λ k : ℂ)) * U i * X⁻¹) := by
  classical
  obtain ⟨X, Λ₀, U₀, hX_det, hΛ₀_pos, _, hU₀_pair, hA_eq⟩ :=
    rfp_nt_structural_full A hNT hRFP hLeft
  let sR : ℝ := Real.sqrt (D : ℝ)
  let s : ℂ := (sR : ℂ)
  let Λ : Fin D → ℝ := fun k => Λ₀ k / sR
  let U : MPSTensor d D := fun i => s • U₀ i
  have hDpos_nat : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast hDpos_nat
  have hsR_ne : sR ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 hDpos
  have hsR_pos : 0 < sR := by
    exact Real.sqrt_pos.2 hDpos
  have hs_ne : s ≠ 0 := by
    simpa [s] using Complex.ofReal_ne_zero.mpr hsR_ne
  have hdiag :
      Matrix.diagonal (fun k => (Λ k : ℂ)) =
        s⁻¹ • Matrix.diagonal (fun k => (Λ₀ k : ℂ)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      calc
        Matrix.diagonal (fun k => (Λ k : ℂ)) a a = ((Λ₀ a / sR : ℝ) : ℂ) := by
            simp [Λ, Matrix.diagonal]
        _ = s⁻¹ * (Λ₀ a : ℂ) := by
            rw [Complex.ofReal_div]
            simp [s, div_eq_mul_inv, mul_comm]
        _ = (s⁻¹ • Matrix.diagonal (fun k => (Λ₀ k : ℂ))) a a := by
            simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hab]
  refine ⟨X, Λ, U, hX_det, ?_, ?_, ?_⟩
  · intro k
    exact div_pos (hΛ₀_pos k) hsR_pos
  · intro p q
    exact unit_pair_of_scaled_sqrtCard U₀ hU₀_pair p q
  · intro i
    rw [hA_eq i]
    let L : Matrix (Fin D) (Fin D) ℂ := Matrix.diagonal (fun k => (Λ k : ℂ))
    have hdiag' : Matrix.diagonal (fun k => (Λ₀ k : ℂ)) = s • L := by
      calc
        Matrix.diagonal (fun k => (Λ₀ k : ℂ)) =
            (s * s⁻¹) • Matrix.diagonal (fun k => (Λ₀ k : ℂ)) := by
            simp [hs_ne]
        _ = s • (s⁻¹ • Matrix.diagonal (fun k => (Λ₀ k : ℂ))) := by
            simp [smul_smul]
        _ = s • L := by
            rw [← hdiag]
    have hmove : (s • L) * U₀ i = L * (s • U₀ i) := by
      rw [Matrix.smul_mul, Matrix.mul_smul]
    calc
      X * Matrix.diagonal (fun k => (Λ₀ k : ℂ)) * U₀ i * X⁻¹
          = X * (s • L) * U₀ i * X⁻¹ := by
              rw [hdiag']
      _ = X * L * (s • U₀ i) * X⁻¹ := by
          rw [Matrix.mul_assoc X (s • L) (U₀ i), hmove,
            ← Matrix.mul_assoc X L (s • U₀ i)]
      _ = X * Matrix.diagonal (fun k => (Λ k : ℂ)) * U i * X⁻¹ := by
          simp [L, U]

/-- **Isometry canonical form for a single normal-tensor block**
(arXiv:1606.00608, Lemma charact-NT-pure-RFP, lines 1271--1301, and the
single-block case j = j' of the structural characterization Theorem
charact-MPS, eqs. III_CFI_RFP and III_isometry).

A normal tensor `A` is in *isometry canonical form* when there are an invertible
`X`, a positive diagonal weight `Λ` with `∑ k Λ k = 1` (the source
trace-normalization tr Λ = 1), and a residual tensor `U` satisfying the unit
pair-index isometry
\[
  \sum_i \overline{(U^i)_{\alpha,\beta}}\,(U^i)_{\alpha',\beta'}
  = \delta_{\alpha,\alpha'}\delta_{\beta,\beta'},
\]
such that
\[
  A^i = X \, \sqrt{\Lambda} \, U^i \, X^{-1}.
\]
The square root appears because the source reference tensor is
\(\widehat A^{(\alpha',\beta')}_{\alpha,\beta}
  = \delta_{\alpha,\alpha'}\delta_{\beta,\beta'}\sqrt{\Lambda_\alpha}\)
(arXiv:1606.00608, line 1300): the diagonal that dresses the unit isometry is
`√Λ`, while the trace normalization tr Λ = 1 is imposed on `Λ` itself,
equivalently on the diagonal fixed point `ρ = diag Λ` of the transfer map.

**Local fix (square-root diagonal):** The source's displayed equation
III_NT_RFP (arXiv:1606.00608, line 1278) writes \(A^i = X\Lambda U^iX^{-1}\) with
the diagonal \(\Lambda\) itself (no square root) alongside the unit isometry
condition on \(U\) (lines 1281--1283). That literal pairing is inconsistent:
against the reference tensor \(\widehat A = \sqrt\Lambda\cdot(\text{matrix
unit})\) (line 1300) the residual \(\Lambda^{-1}\widehat A\) has pair-index sum
\(\delta/\Lambda_\alpha\), not \(\delta\), so a unit `U` forces the square-root
dressing `√Λ` in the decomposition. This \(\Lambda\to\sqrt\Lambda\) change is a
local correction of the source display, mathematically correct as stated; it is
documented in `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`.

This records the diagonal j = j' case of the source isometry condition. The
cross-block \(\delta_{j,j'}\) orthogonality between distinct normal-tensor blocks
is a separate condition, recorded in
`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. -/
def IsIsometryCanonicalForm (A : MPSTensor d D) : Prop :=
  ∃ (X : Matrix (Fin D) (Fin D) ℂ) (Λ : Fin D → ℝ) (U : MPSTensor d D),
    X.det ≠ 0 ∧
    (∀ k, 0 < Λ k) ∧
    (∑ k : Fin D, Λ k = 1) ∧
    (∀ p q : Fin D × Fin D,
      ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2 =
        if p = q then 1 else 0) ∧
    (∀ i, A i = X * Matrix.diagonal (fun k => (Real.sqrt (Λ k) : ℂ)) * U i * X⁻¹)

/-- **Trace-normalized isometry canonical form of Lemma B.1**
(arXiv:1606.00608, Lemma charact-NT-pure-RFP, lines 1271--1301).

A normal tensor in canonical form II that is a renormalization fixed point is in
isometry canonical form: it admits a decomposition
`A^i = X √Λ U^i X⁻¹` with `Λ` diagonal, positive, trace-normalized
(`∑ k Λ k = 1`, the source condition `tr(Λ) = 1`), and `U` a unit pair-index
isometry.

The diagonal weight is `Λ k = ρ_{k,k} / tr ρ`, the normalized diagonal fixed
point of the transfer map; trace-normalization is then the trace identity
`∑ k ρ_{k,k} = tr ρ`. The square-root dressing `√Λ` matches the source reference
tensor `Â = √Λ · (matrix unit)` (arXiv:1606.00608, line 1300) and keeps `U` a
genuine unit isometry.

**Local fix (square-root diagonal):** the source display III_NT_RFP
(line 1278) writes `A^i = X Λ U^i X⁻¹` without the square root; the `Λ → √Λ`
correction is documented in the predicate `IsIsometryCanonicalForm` and in
`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. -/
theorem isIsometryCanonicalForm_of_rfp_nt (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    IsIsometryCanonicalForm A := by
  classical
  obtain ⟨X, Λ₀, U₀, hX_det, hΛ₀_pos, _, hU₀_pair, hΛ₀_sq, hA_eq⟩ :=
    rfp_nt_structural_full_sqSum A hNT hRFP hLeft
  let sR : ℝ := Real.sqrt (D : ℝ)
  let s : ℂ := (sR : ℂ)
  -- Rescale to the unit pair-index convention: `U = √D · U₀`, `Λtil = Λ₀ / √D`.
  let Λtil : Fin D → ℝ := fun k => Λ₀ k / sR
  -- The trace-normalized diagonal is `Λ = Λtil² = Λ₀² / D`.
  let Λ : Fin D → ℝ := fun k => (Λtil k) ^ 2
  let U : MPSTensor d D := fun i => s • U₀ i
  have hDpos_nat : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hDpos_nat
  have hsR_ne : sR ≠ 0 := Real.sqrt_ne_zero'.2 hDpos
  have hsR_pos : 0 < sR := Real.sqrt_pos.2 hDpos
  have hs_ne : s ≠ 0 := by simpa [s] using Complex.ofReal_ne_zero.mpr hsR_ne
  have hΛtil_pos : ∀ k, 0 < Λtil k := fun k => div_pos (hΛ₀_pos k) hsR_pos
  -- `√Λ k = Λtil k`, so the decomposition matches the source `√Λ` dressing.
  have hsqrtΛ : ∀ k, Real.sqrt (Λ k) = Λtil k := by
    intro k
    exact Real.sqrt_sq (le_of_lt (hΛtil_pos k))
  refine ⟨X, Λ, U, hX_det, ?_, ?_, ?_, ?_⟩
  · -- `Λ k = Λtil k ^ 2 > 0`.
    intro k
    exact pow_pos (hΛtil_pos k) 2
  · -- `∑ k Λ k = (∑ Λ₀²) / D = D / D = 1`.
    have hsR_sq : sR ^ 2 = (D : ℝ) := Real.sq_sqrt (le_of_lt hDpos)
    have hstep : ∀ k, Λ k = (Λ₀ k) ^ 2 / (D : ℝ) := by
      intro k
      simp only [Λ, Λtil, div_pow]
      rw [hsR_sq]
    calc
      ∑ k : Fin D, Λ k = ∑ k : Fin D, (Λ₀ k) ^ 2 / (D : ℝ) :=
            Finset.sum_congr rfl (fun k _ => hstep k)
      _ = (∑ k : Fin D, (Λ₀ k) ^ 2) / (D : ℝ) := by rw [Finset.sum_div]
      _ = (D : ℝ) / (D : ℝ) := by rw [hΛ₀_sq]
      _ = 1 := by field_simp [hDpos.ne']
  · -- Unit pair-index isometry: `√D · U₀` upgrades the `D⁻¹` form to unit.
    intro p q
    exact unit_pair_of_scaled_sqrtCard U₀ hU₀_pair p q
  · -- Decomposition: `A^i = X √Λ U^i X⁻¹` reduces to the `Λ₀, U₀` form.
    intro i
    rw [hA_eq i]
    let L : Matrix (Fin D) (Fin D) ℂ :=
      Matrix.diagonal (fun k => (Real.sqrt (Λ k) : ℂ))
    have hL_eq : L = Matrix.diagonal (fun k => (Λtil k : ℂ)) := by
      simp only [L, hsqrtΛ]
    have hdiagΛ₀ :
        Matrix.diagonal (fun k => (Λ₀ k : ℂ)) = s • L := by
      rw [hL_eq]
      have hsRC_ne : (sR : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsR_ne
      ext a b
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
        rw [show (Λtil a : ℂ) = (Λ₀ a / sR : ℝ) from by simp [Λtil],
          Complex.ofReal_div]
        rw [show s = (sR : ℂ) from rfl]
        field_simp [hsRC_ne]
      · simp [Matrix.diagonal, hab]
    have hmove : (s • L) * U₀ i = L * (s • U₀ i) := by
      rw [Matrix.smul_mul, Matrix.mul_smul]
    calc
      X * Matrix.diagonal (fun k => (Λ₀ k : ℂ)) * U₀ i * X⁻¹
          = X * (s • L) * U₀ i * X⁻¹ := by rw [hdiagΛ₀]
      _ = X * L * (s • U₀ i) * X⁻¹ := by
            rw [Matrix.mul_assoc X (s • L) (U₀ i), hmove,
              ← Matrix.mul_assoc X L (s • U₀ i)]
      _ = X * Matrix.diagonal (fun k => (Real.sqrt (Λ k) : ℂ)) * U i * X⁻¹ := by
            simp [L, U]

/-- **Per-block trace-normalized isometry canonical form.** Each block of a
multi-block tensor that is a normal, left-canonical renormalization fixed point
is in isometry canonical form: it admits a decomposition
\(A_k^i = X\sqrt{\Lambda_k}\,U^iX^{-1}\) with \(\Lambda_k\) diagonal positive,
trace-normalized (\(\sum_j (\Lambda_k)_j = 1\)), and \(U\) a unit pair-index
isometry.

This is the single-block trace-normalized form (`isIsometryCanonicalForm_of_rfp_nt`,
the diagonal j = j' case of arXiv:1606.00608, Corollary III.cor3, lines
583--589) applied to each block.

**Scope restriction (source isometry):** Corollary III.cor3 also invokes the
cross-block \(\delta_{j,j'}\) orthogonality between distinct normal-tensor blocks
(eq. III_isometry, lines 550--554). This per-block statement omits those
cross-block equations; the gap is recorded in
`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. Deriving the per-block
normal/RFP/left-canonical hypotheses from a whole-tensor canonical-form
fixed-point condition is a separate step. -/
theorem isIsometryCanonicalForm_of_rfp_nt_blocks {r : ℕ} {dim : Fin r → ℕ}
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hNT : ∀ k, IsNormal (A k)) (hRFP : ∀ k, IsRFP (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1) :
    ∀ k, IsIsometryCanonicalForm (A k) :=
  fun k => isIsometryCanonicalForm_of_rfp_nt (A k) (hNT k) (hRFP k) (hLeft k)

/-- **Per-block isometry canonical form.** When each block of a multi-block tensor
is a normal, left-canonical renormalization fixed point, that block admits an
isometry decomposition A_k^i = X diag(Λ) U^i X⁻¹ with X invertible, Λ positive,
and U a physical-index isometry.

This is the isometry canonical form applied separately to each normal-tensor
block; it is a per-block form related to arXiv:1606.00608, Corollary III.cor3,
lines 583--589. The source additionally imposes the normalization tr(Λ_k) = 1;
the statement here gives positive Λ_k without it. The normalization is genuine,
not a conjugation gauge: rescaling Λ_k ↦ Λ_k / tr(Λ_k) factors out as an overall
scalar on A_k, since conjugation by X preserves the scale.

**Scope restriction (source isometry):** Corollary III.cor3 also invokes the
joint isometry condition from eq:III_isometry, lines 550--554. This theorem now
records the diagonal pair-index equation for each block in the normalization used
by `rfp_nt_structural_full`, where the right-hand side is multiplied by
$(\dim k)^{-1}$. It still omits the source trace-normalization of $\Lambda_k$ and the
δ_{j,j'} orthogonality between distinct blocks. This restriction is recorded in
`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. Elimination: strengthen the
normalization comparison, then prove a joint BNT-family isometry form from
whole-tensor canonical-form RFP data.

Deriving the per-block normal/RFP/left-canonical hypotheses from a whole-tensor
canonical-form fixed-point condition is a separate step. -/
theorem rfp_nt_structural_full_blocks {r : ℕ} {dim : Fin r → ℕ}
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hNT : ∀ k, IsNormal (A k)) (hRFP : ∀ k, IsRFP (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1) :
    ∀ k, ∃ (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (Λ : Fin (dim k) → ℝ)
      (U : MPSTensor d (dim k)),
      X.det ≠ 0 ∧ (∀ j, 0 < Λ j) ∧ (∑ i : Fin d, (U i)ᴴ * U i = 1) ∧
      (∀ p q : Fin (dim k) × Fin (dim k),
        ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2 =
          if p = q then (dim k : ℂ)⁻¹ else 0) ∧
      (∀ i, A k i = X * Matrix.diagonal (fun j => (Λ j : ℂ)) * U i * X⁻¹) :=
  fun k => rfp_nt_structural_full (A k) (hNT k) (hRFP k) (hLeft k)

/-- Per-block unit pair-index form of the isometry canonical form
(Theorem~\ref{thm:rfp_nt_structural_full_blocks}).

This only changes the pair-index normalization convention.  In this convention
the contracted identity is \(D_k I\), not \(I\), so the conclusion records the
unit pair-index equation and the decomposition but not a contracted-isometry
equation.

**Scope restriction (source isometry):** Corollary III.cor3 and the joint
isometry equation in arXiv:1606.00608, lines 550--554, also require
\(\operatorname{tr}\Lambda_k=1\) and cross-block \(\delta_{j,j'}\)
orthogonality.  This theorem is only the per-block normalization comparison;
the full source assertion is recorded as a remaining gap in
`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. -/
theorem rfp_nt_structural_full_blocks_unit_pair {r : ℕ} {dim : Fin r → ℕ}
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hNT : ∀ k, IsNormal (A k)) (hRFP : ∀ k, IsRFP (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1) :
    ∀ k, ∃ (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
      (Λ : Fin (dim k) → ℝ) (U : MPSTensor d (dim k)),
      X.det ≠ 0 ∧ (∀ j, 0 < Λ j) ∧
      (∀ p q : Fin (dim k) × Fin (dim k),
        ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2 =
          if p = q then 1 else 0) ∧
      (∀ i, A k i = X * Matrix.diagonal (fun j => (Λ j : ℂ)) * U i * X⁻¹) :=
  fun k => rfp_nt_structural_full_unit_pair (A k) (hNT k) (hRFP k) (hLeft k)

end MPSTensor
