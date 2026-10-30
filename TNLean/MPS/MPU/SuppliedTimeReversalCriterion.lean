/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SuppliedFourSpinSourceComparison
import TNLean.MPS.MPU.TimeReversalLocalSufficiency

/-!
# Time reversal for arbitrary supplied standard forms

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

Source: arXiv:1703.09188, `PropChiral`, `eq:block-twosites` and
`UUdaggertrick`, lines 1201–1252.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

private theorem adjoint_certificate_of_unitary_gate_transport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix (ι × ι) (ι × ι) ℂ)
    (X Y z : Matrix.unitaryGroup ι ℂ) (σ : ℂ)
    (h : ((X : Matrix ι ι ℂ) ⊗ₖ (Y : Matrix ι ι ℂ)) * A =
      σ • ((z : Matrix ι ι ℂ) ⊗ₖ (z : Matrix ι ι ℂ)ᴴ) *
        (B * ((Y : Matrix ι ι ℂ)ᴴ ⊗ₖ (X : Matrix ι ι ℂ)ᴴ))ᴴ) :
    ∃ w : Matrix.unitaryGroup ι ℂ,
      A = σ • ((w : Matrix ι ι ℂ) ⊗ₖ (w : Matrix ι ι ℂ)ᴴ) * Bᴴ := by
  let w := star X * z * Y
  have hXY := (Matrix.isUnitaryBetween_coe_unitaryGroup X).kronecker _ _
    (Matrix.isUnitaryBetween_coe_unitaryGroup Y)
  have hcancel : ((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
      ((X : Matrix ι ι ℂ) ⊗ₖ (Y : Matrix ι ι ℂ)) = 1 := by
    rw [← Matrix.conjTranspose_kronecker]
    exact hXY.1
  have hw : ((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
      ((z : Matrix ι ι ℂ) ⊗ₖ (z : Matrix ι ι ℂ)ᴴ) *
      ((Y : Matrix ι ι ℂ) ⊗ₖ (X : Matrix ι ι ℂ)) =
      (w : Matrix ι ι ℂ) ⊗ₖ (w : Matrix ι ι ℂ)ᴴ := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [w, Submonoid.coe_mul, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  refine ⟨w, ?_⟩
  calc
    A = ((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
        (((X : Matrix ι ι ℂ) ⊗ₖ (Y : Matrix ι ι ℂ)) * A) := by
      rw [← Matrix.mul_assoc, hcancel, Matrix.one_mul]
    _ = ((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
        (σ • ((z : Matrix ι ι ℂ) ⊗ₖ (z : Matrix ι ι ℂ)ᴴ) *
          (B * ((Y : Matrix ι ι ℂ)ᴴ ⊗ₖ (X : Matrix ι ι ℂ)ᴴ))ᴴ) := by rw [h]
    _ = σ • (((X : Matrix ι ι ℂ)ᴴ ⊗ₖ (Y : Matrix ι ι ℂ)ᴴ) *
        ((z : Matrix ι ι ℂ) ⊗ₖ (z : Matrix ι ι ℂ)ᴴ) *
        ((Y : Matrix ι ι ℂ) ⊗ₖ (X : Matrix ι ι ℂ))) * Bᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = σ • ((w : Matrix ι ι ℂ) ⊗ₖ (w : Matrix ι ι ℂ)ᴴ) * Bᴴ := by rw [hw]

namespace TwoSiteStandardFormData

/-- Even-family time reversal gives the literal four-spin certificate for
any supplied square standard form in an explicitly canonical ambient
tensor. No normalized supplied half factors or comparison gauges are
hypotheses. Source: CPSV17, `PropChiral` and `UUdaggertrick`, lines 1201–1252. -/
theorem exists_timeReversal_certificate_of_square_ranks
    {d D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ) :
    ∃ (σ : ℂ) (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      (σ = 1 ∨ σ = -1) ∧
      staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
        σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) *
          (staircaseMiddle (A := Fin d) (E := Fin d) v)ᴴ := by
  classical
  let T := sourceFactors W hW.ρ hW.ρ_posDef
  have hr : r[W] = d * d := S.sourceRanks_eq.1
  have hl : ℓ[W] = d * d := S.sourceRanks_eq.2
  obtain ⟨σ, z, hσ, hcert⟩ :=
    hW.exists_supplied_source_adjoint_certificate (S.isMPUSimple hW) T hr hl hTR
  let e : (Fin d × Fin d) ≃ Fin (d * d) := finProdFinEquiv
  let p := Equiv.prodCongr e e
  let A := staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)
  let B := staircaseMiddle (A := Fin d) (E := Fin d) v
  obtain ⟨X', Y', hu', hv'⟩ := S.exists_fourSpin_selected_source_gate_gauges_of_square_ranks hW
  rw [hu', hv'] at hcert
  obtain ⟨w, hw⟩ := adjoint_certificate_of_unitary_gate_transport
    (Matrix.reindex p p A) (Matrix.reindex p p B) X' Y' z σ hcert
  let x : Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    ⟨Matrix.reindex e.symm e.symm w,
      Matrix.reindex_mem_unitaryGroup e.symm _ w.property⟩
  refine ⟨σ, x, hσ, ?_⟩
  apply (Matrix.reindexLinearEquiv ℂ ℂ p p).injective
  change Matrix.reindexLinearEquiv ℂ ℂ p p A =
    Matrix.reindexLinearEquiv ℂ ℂ p p
      ((σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ)) * Bᴴ)
  rw [Matrix.smul_mul, map_smul]
  conv_rhs => rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ p p p]
  have hx : Matrix.reindexLinearEquiv ℂ ℂ p p
      ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) =
      (w : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
          (w : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ := by
    change Matrix.reindex p p
      ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) = _
    rw [← Matrix.kroneckerMap_reindex]
    have hx' : Matrix.reindex e e (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) =
        (w : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) := by
      ext i j
      change (w : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) (e (e.symm i)) (e (e.symm j)) =
        (w : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) i j
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [hx', ← Matrix.conjTranspose_reindex, hx']
  rw [hx]
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.conjTranspose_reindex]
  rw [← Matrix.smul_mul]
  exact hw

/-- The intermediate dimensions and the literal four-spin time-reversal
certificate are derived for any supplied standard form in an explicitly
canonical ambient tensor. The gates are relabelled only along the derived
rank equalities. Source: CPSV17, `PropChiral`, `UUdaggertrick` and
`eq:block-twosites`, lines 1201–1252. -/
theorem exists_timeReversal_certificate
    {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ) :
    ∃ (hr : r = d) (hl : ℓ = d) (σ : ℂ)
      (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
        (Equiv.refl _) u
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hr) (finCongr hl)) v
      (σ = 1 ∨ σ = -1) ∧
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) *
          (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᴴ := by
  obtain ⟨hr, hl⟩ := S.intermediateRanks_eq_phys_of_even_mpo_eq_adjoint hW hTR
  have S₀ := S.reindexRanks (finCongr hl) (finCongr hr)
  obtain ⟨σ, x, hσ, hlocal⟩ :=
    S₀.exists_timeReversal_certificate_of_square_ranks hW hTR
  exact ⟨hr, hl, σ, x, hσ, hlocal⟩


/-- A supplied square standard form's literal four-spin sign equation
implies adjoint symmetry on every positive even standard-form ring in the
explicit ambient canonical scope. All normalized factors and comparison
gauges are derived internally. Source: CPSV17, `PropChiral`,
`UUdaggertrick` and `eq:dagger-sym-cond`, lines 1214–1236. -/
theorem mpo_even_eq_adjoint_of_timeReversal_certificate
    {d D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hlocal : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
      σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) *
        (staircaseMiddle (A := Fin d) (E := Fin d) v)ᴴ)
    (N : ℕ) (hN : 1 < N) (heven : Even N) : mpo W N = (mpo W N)ᴴ := by
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
    ⟨Matrix.reindex e e x, Matrix.reindex_mem_unitaryGroup e _ x.property⟩
  let A₀ := Matrix.reindex p p
    (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u))
  let B₀ := Matrix.reindex p p (staircaseMiddle (A := Fin d) (E := Fin d) v)
  have hraw : A₀ = σ •
      ((x' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
          (x' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ) * B₀ᴴ := by
    exact Matrix.reindex_adjoint_certificate e hlocal
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
      σ • ((x' : Matrix _ _ ℂ) ⊗ₖ (x' : Matrix _ _ ℂ)ᴴ) *
        (B * ((Y : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)))ᴴ := by
    rw [hAcancel, hBcancel]
    exact hraw
  obtain ⟨z, hz⟩ := adjoint_certificate_of_unitary_gate_transport A B
    (star X) (star Y) x' σ (by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose] using hraw')
  exact hW.mpo_even_eq_adjoint_of_source_local_certificate
    (S.isMPUSimple hW) T hr hl σ hσ z hz N hN heven

/-- The literal local criterion for ANY supplied standard form in an
explicit canonical ambient tensor, at exactly the even standard-form
lengths of the source. Intermediate rank equalities are conclusions in
the forward direction. Source: CPSV17, `PropChiral`, lines 1201–1252. -/
theorem even_timeReversal_iff_exists_certificate
    {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W) :
    (∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ) ↔
      ∃ (hr : r = d) (hl : ℓ = d) (σ : ℂ)
        (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
        let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
          (Equiv.refl _) u
        let v₀ := Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr hr) (finCongr hl)) v
        (σ = 1 ∨ σ = -1) ∧
        staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
          σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
              (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) *
            (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᴴ := by
  constructor
  · exact S.exists_timeReversal_certificate hW
  · rintro ⟨hr, hl, σ, x, hσ, hlocal⟩ N hN heven
    have S₀ := S.reindexRanks (finCongr hl) (finCongr hr)
    exact S₀.mpo_even_eq_adjoint_of_timeReversal_certificate hW σ hσ x hlocal N hN heven

end TwoSiteStandardFormData

end MPOTensor
