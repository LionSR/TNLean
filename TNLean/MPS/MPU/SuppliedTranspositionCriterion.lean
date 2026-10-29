/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SuppliedFourSpinSourceComparison
import TNLean.MPS.MPU.TranspositionLocalSufficiency

/-!
# Transposition for arbitrary supplied standard forms

The actual four-spin comparison transports the normalized source
certificate to any supplied gates in the same canonical ambient tensor.
Its two independent comparison unitaries combine into one unitary in the
literal four-spin equation. No normalization of the supplied half factors
or chosen gauge witness is required.

**Scope restriction (canonical ambient presentation):** Ambient canonical
form II remains explicit; minimal cut ranks do not eliminate virtual
padding. The finite-chain hypothesis concerns even standard-form lengths.
This is not the unrestricted source criterion; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex` and
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`.

Source: arXiv:1703.09188, `prop:local-char-transposition`, `eq:block-twosites` and
`UUtransposetrick`, lines 1258–1288.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

private theorem transpose_certificate_of_unitary_gate_transport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix (ι × ι) (ι × ι) ℂ)
    (X Y z : Matrix.unitaryGroup ι ℂ) (c : ℂ)
    (h : ((X : Matrix ι ι ℂ) ⊗ₖ (Y : Matrix ι ι ℂ)) * A =
      c • ((z : Matrix ι ι ℂ) ⊗ₖ (z : Matrix ι ι ℂ)ᵀ) *
        (B * ((Y : Matrix ι ι ℂ)ᴴ ⊗ₖ (X : Matrix ι ι ℂ)ᴴ))ᵀ) :
    ∃ w : Matrix.unitaryGroup ι ℂ,
      A = c • ((w : Matrix ι ι ℂ) ⊗ₖ (w : Matrix ι ι ℂ)ᵀ) * Bᵀ := by
  let Ybar : Matrix.unitaryGroup ι ℂ :=
    ⟨(Y : Matrix ι ι ℂ).map (starRingEnd ℂ),
      (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp
        ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr Y.property).map_star⟩
  let w := star X * z * Ybar
  have hXY := (Matrix.isUnitaryBetween_coe_unitaryGroup X).kronecker _ _
    (Matrix.isUnitaryBetween_coe_unitaryGroup Y)
  have hcancel : ((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
      ((X : Matrix ι ι ℂ) ⊗ₖ (Y : Matrix ι ι ℂ)) = 1 := by
    rw [← Matrix.conjTranspose_kronecker]
    exact hXY.1
  have hbar : (Y : Matrix ι ι ℂ)ᴴᵀ = (Ybar : Matrix ι ι ℂ) := rfl
  have hbarT : (Ybar : Matrix ι ι ℂ)ᵀ = (Y : Matrix ι ι ℂ)ᴴ := rfl
  have hw : ((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
      ((z : Matrix ι ι ℂ) ⊗ₖ (z : Matrix ι ι ℂ)ᵀ) *
      ((Y : Matrix ι ι ℂ)ᴴᵀ ⊗ₖ (X : Matrix ι ι ℂ)ᴴᵀ) =
      (w : Matrix ι ι ℂ) ⊗ₖ (w : Matrix ι ι ℂ)ᵀ := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hbar]
    simp only [w, Submonoid.coe_mul, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.transpose_mul, hbarT, Matrix.mul_assoc]
  refine ⟨w, ?_⟩
  calc
    A = ((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
        (((X : Matrix ι ι ℂ) ⊗ₖ (Y : Matrix ι ι ℂ)) * A) := by
      rw [← Matrix.mul_assoc, hcancel, Matrix.one_mul]
    _ = ((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
        (c • ((z : Matrix ι ι ℂ) ⊗ₖ (z : Matrix ι ι ℂ)ᵀ) *
          (B * ((Y : Matrix ι ι ℂ)ᴴ ⊗ₖ (X : Matrix ι ι ℂ)ᴴ))ᵀ) := by rw [h]
    _ = c • (((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
        ((z : Matrix ι ι ℂ) ⊗ₖ (z : Matrix ι ι ℂ)ᵀ) *
        ((Y : Matrix ι ι ℂ)ᴴᵀ ⊗ₖ (X : Matrix ι ι ℂ)ᴴᵀ)) * Bᵀ := by
      simp only [Matrix.transpose_mul, ← Matrix.kroneckerMap_transpose,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = c • ((w : Matrix ι ι ℂ) ⊗ₖ (w : Matrix ι ι ℂ)ᵀ) * Bᵀ := by rw [hw]

namespace TwoSiteStandardFormData

/-- Even-family transposition symmetry forces square intermediate ranks
for any supplied standard form in an explicit canonical ambient tensor.
Source: CPSV17, `prop:local-char-transposition`, lines 1258–1288. -/
theorem intermediateRanks_eq_phys_of_even_mpo_eq_transpose
    {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᵀ) :
    r = d ∧ ℓ = d := by
  obtain ⟨hr, hl⟩ := hW.sourceRanks_eq_phys_of_even_mpo_eq_transpose (S.isMPUSimple hW) hTR
  constructor
  · apply mul_left_cancel₀ S.phys_pos.ne'
    exact S.sourceRanks_eq.1.symm.trans hr
  · apply mul_right_cancel₀ S.phys_pos.ne'
    exact S.sourceRanks_eq.2.symm.trans hl

/-- Even-family transposition gives the literal four-spin certificate for
any supplied square standard form in an explicitly canonical ambient
tensor. No normalized supplied half factors or comparison gauges are
hypotheses. Source: CPSV17, `prop:local-char-transposition` and
`UUtransposetrick`, lines 1258–1288. -/
theorem exists_transposition_certificate_of_square_ranks
    {d D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᵀ) :
    ∃ (c : ℂ) (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      ‖c‖ = 1 ∧
      staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
        c • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) *
          (staircaseMiddle (A := Fin d) (E := Fin d) v)ᵀ := by
  classical
  let T := sourceFactors W hW.ρ hW.ρ_posDef
  obtain ⟨_, _, c, z, hc, hcert⟩ :=
    hW.exists_source_transposition_phase_certificate (S.isMPUSimple hW) T hTR
  let e : (Fin d × Fin d) ≃ Fin (d * d) := finProdFinEquiv
  let p := Equiv.prodCongr e e
  let A := staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)
  let B := staircaseMiddle (A := Fin d) (E := Fin d) v
  obtain ⟨X', Y', hu', hv'⟩ := S.exists_fourSpin_selected_source_gate_gauges_of_square_ranks hW
  rw [hu', hv'] at hcert
  obtain ⟨w, hw⟩ := transpose_certificate_of_unitary_gate_transport
    (Matrix.reindex p p A) (Matrix.reindex p p B) X' Y' z c hcert
  let x : Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    ⟨Matrix.reindex e.symm e.symm w, Matrix.reindex_mem_unitaryGroup _ _ w.property⟩
  refine ⟨c, x, hc, ?_⟩
  apply (Matrix.reindexLinearEquiv ℂ ℂ p p).injective
  change Matrix.reindexLinearEquiv ℂ ℂ p p A =
    Matrix.reindexLinearEquiv ℂ ℂ p p
      ((c • ((x : Matrix _ _ ℂ) ⊗ₖ (x : Matrix _ _ ℂ)ᵀ)) * Bᵀ)
  rw [Matrix.smul_mul, map_smul]
  conv_rhs => rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ p p p]
  have hx : Matrix.reindexLinearEquiv ℂ ℂ p p
      ((x : Matrix _ _ ℂ) ⊗ₖ (x : Matrix _ _ ℂ)ᵀ) =
      (w : Matrix _ _ ℂ) ⊗ₖ (w : Matrix _ _ ℂ)ᵀ := by
    change Matrix.reindex p p
      ((x : Matrix _ _ ℂ) ⊗ₖ (x : Matrix _ _ ℂ)ᵀ) = _
    rw [← Matrix.kroneckerMap_reindex]
    have hx' : Matrix.reindex e e (x : Matrix _ _ ℂ) = (w : Matrix _ _ ℂ) := by
      ext i j
      change (w : Matrix _ _ ℂ) (e (e.symm i)) (e (e.symm j)) =
        (w : Matrix _ _ ℂ) i j
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [hx', ← Matrix.transpose_reindex, hx']
  rw [hx]
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.transpose_reindex]
  rw [← Matrix.smul_mul]
  exact hw

/-- The intermediate dimensions and the literal four-spin transposition
certificate are derived for any supplied standard form in an explicitly
canonical ambient tensor. The gates are relabelled only along the derived
rank equalities. Source: CPSV17, `prop:local-char-transposition`, `UUtransposetrick` and
`eq:block-twosites`, lines 1258–1288. -/
theorem exists_transposition_certificate
    {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᵀ) :
    ∃ (hr : r = d) (hl : ℓ = d) (c : ℂ)
      (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
        (Equiv.refl _) u
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hr) (finCongr hl)) v
      ‖c‖ = 1 ∧
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        c • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) *
          (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᵀ := by
  obtain ⟨hr, hl⟩ := S.intermediateRanks_eq_phys_of_even_mpo_eq_transpose hW hTR
  have S₀ := S.reindexRanks (finCongr hl) (finCongr hr)
  obtain ⟨c, x, hc, hlocal⟩ :=
    S₀.exists_transposition_certificate_of_square_ranks hW hTR
  exact ⟨hr, hl, c, x, hc, hlocal⟩


/-- A supplied square standard form's literal four-spin phase equation
implies transpose symmetry on every positive even standard-form ring in the
explicit ambient canonical scope. All normalized factors and comparison
gauges are derived internally. Source: CPSV17, `prop:local-char-transposition`,
`UUtransposetrick`, lines 1266–1288. -/
theorem mpo_even_eq_transpose_of_transposition_certificate
    {d D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (c : ℂ) (hc : ‖c‖ = 1)
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hlocal : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
      c • ((x : Matrix _ _ ℂ) ⊗ₖ (x : Matrix _ _ ℂ)ᵀ) *
        (staircaseMiddle (A := Fin d) (E := Fin d) v)ᵀ)
    (N : ℕ) (hN : 1 < N) (heven : Even N) : mpo W N = (mpo W N)ᵀ := by
  classical
  let T := sourceFactors W hW.ρ hW.ρ_posDef
  have hr : r[W] = d * d := S.sourceRanks_eq.1
  have hl : ℓ[W] = d * d := S.sourceRanks_eq.2
  let A := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
    (Equiv.refl _) (SourceFactors.sourceU W T)
  let B := Matrix.reindex (Equiv.refl _)
    (Equiv.prodCongr (finCongr hr) (finCongr hl)) (SourceFactors.sourceV W T)
  let e : (Fin d × Fin d) ≃ Fin (d * d) := finProdFinEquiv
  let p := Equiv.prodCongr e e
  let x' : Matrix.unitaryGroup (Fin (d * d)) ℂ :=
    ⟨Matrix.reindex e e x, Matrix.reindex_mem_unitaryGroup _ _ x.property⟩
  let A₀ := Matrix.reindex p p
    (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u))
  let B₀ := Matrix.reindex p p (staircaseMiddle (A := Fin d) (E := Fin d) v)
  have hraw : A₀ = c • ((x' : Matrix _ _ ℂ) ⊗ₖ (x' : Matrix _ _ ℂ)ᵀ) * B₀ᵀ := by
    exact Matrix.reindex_transposition_certificate e hlocal
  obtain ⟨X, Y, hu, hv⟩ := S.exists_fourSpin_selected_source_gate_gauges_of_square_ranks hW
  have hXY := (Matrix.isUnitaryBetween_coe_unitaryGroup X).kronecker _ _
    (Matrix.isUnitaryBetween_coe_unitaryGroup Y)
  have hYX := (Matrix.isUnitaryBetween_coe_unitaryGroup Y).kronecker _ _
    (Matrix.isUnitaryBetween_coe_unitaryGroup X)
  have hAcancel : ((X : Matrix _ _ ℂ)ᴴ ⊗ₖ (Y : Matrix _ _ ℂ)ᴴ) * A = A₀ := by
    change ((X : Matrix _ _ ℂ)ᴴ ⊗ₖ (Y : Matrix _ _ ℂ)ᴴ) *
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
        (Equiv.refl _) (SourceFactors.sourceU W T) = A₀
    rw [hu, ← Matrix.mul_assoc, ← Matrix.conjTranspose_kronecker, hXY.1, Matrix.one_mul]
  have hBcancel : B * ((Y : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)) = B₀ := by
    change Matrix.reindex (Equiv.refl _)
      (Equiv.prodCongr (finCongr hr) (finCongr hl)) (SourceFactors.sourceV W T) *
        ((Y : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)) = B₀
    rw [hv, Matrix.mul_assoc, ← Matrix.conjTranspose_kronecker, hYX.1, Matrix.mul_one]
  have hraw' : ((X : Matrix _ _ ℂ)ᴴ ⊗ₖ (Y : Matrix _ _ ℂ)ᴴ) * A =
      c • ((x' : Matrix _ _ ℂ) ⊗ₖ (x' : Matrix _ _ ℂ)ᵀ) *
        (B * ((Y : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)))ᵀ := by
    rw [hAcancel, hBcancel]
    exact hraw
  obtain ⟨z, hz⟩ := transpose_certificate_of_unitary_gate_transport A B
    (star X) (star Y) x' c (by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose] using hraw')
  exact hW.mpo_even_eq_transpose_of_source_local_certificate
    (S.isMPUSimple hW) T hr hl c hc z hz N hN heven

/-- The literal local criterion for ANY supplied standard form in an
explicit canonical ambient tensor, at exactly the even standard-form
lengths of the source. Intermediate rank equalities are conclusions in
the forward direction. Source: CPSV17, `prop:local-char-transposition`, lines 1258–1288. -/
theorem even_transposition_iff_exists_certificate
    {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W) :
    (∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᵀ) ↔
      ∃ (hr : r = d) (hl : ℓ = d) (c : ℂ)
        (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
        let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
          (Equiv.refl _) u
        let v₀ := Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr hr) (finCongr hl)) v
        ‖c‖ = 1 ∧
        staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
          c • ((x : Matrix _ _ ℂ) ⊗ₖ (x : Matrix _ _ ℂ)ᵀ) *
            (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᵀ := by
  constructor
  · exact S.exists_transposition_certificate hW
  · rintro ⟨hr, hl, c, x, hc, hlocal⟩ N hN heven
    have S₀ := S.reindexRanks (finCongr hl) (finCongr hr)
    exact S₀.mpo_even_eq_transpose_of_transposition_certificate hW c hc x hlocal N hN heven


/-- The literal exponential-phase certificate of the source for any
supplied standard form in the explicit canonical ambient scope. Its
argument is chosen pointwise from the derived unit phase; no continuous
phase or factor selection is assumed. Source: CPSV17, `UUtransposetrick`
and the following phase-removal paragraph, lines 1270–1288. -/
theorem exists_transposition_exponential_certificate
    {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᵀ) :
    ∃ (hr : r = d) (hl : ℓ = d) (φ : ℝ)
      (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
        (Equiv.refl _) u
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hr) (finCongr hl)) v
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        Complex.exp ((φ : ℂ) * Complex.I) •
          ((x : Matrix _ _ ℂ) ⊗ₖ (x : Matrix _ _ ℂ)ᵀ) *
            (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᵀ := by
  obtain ⟨hr, hl, c, x, hc, hlocal⟩ := S.exists_transposition_certificate hW hTR
  have hphase : Complex.exp ((Complex.arg c : ℂ) * Complex.I) = c :=
    congrArg (fun z : Circle => (z : ℂ))
      (Circle.exp_arg ⟨c, mem_sphere_zero_iff_norm.mpr hc⟩)
  exact ⟨hr, hl, Complex.arg c, x, by simpa only [hphase] using hlocal⟩

end TwoSiteStandardFormData

end MPOTensor
