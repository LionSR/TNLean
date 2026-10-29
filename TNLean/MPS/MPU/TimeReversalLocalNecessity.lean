/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardFormSourceCuts
import TNLean.MPS.MPU.ConjugationSourceFactors

/-!
# Deriving the local time-reversal certificate from the actual coarse factors

The coarse source factors and their physical-adjoint counterparts are actual
normalized records. The finite-chain hypothesis is exactly at even lengths
of the standard-form tensor, whose site contains two original spins. The
even-family Fundamental Theorem retains an unblocked sign, which cancels in
the two-letter source gate. Its two unitary equations then force a common
local sign. An explicit coordinate dictionary gives the literal
four-original-spin equation without another physical block.

**Scope restriction (canonical source construction):** The public certificate
theorems concern the actual standard form constructed from the chosen simple
reduced canonical source tensor. Arbitrary supplied standard forms and the
converse are separate obligations; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. The original-leg rank
dictionary is proved explicitly. The even-length convention and the need to
retain the intermediate sign are recorded in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`.

Source: arXiv:1703.09188, `PropChiral`, `eq:block-twosites`, and
`UUdaggertrick`, lines 1201–1252.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

private theorem unitary_exchange_sign
    {q : ℕ} [NeZero q] (X Y : Matrix.unitaryGroup (Fin q) ℂ)
    (hK : ((Y : Matrix (Fin q) (Fin q) ℂ) * (X : Matrix (Fin q) (Fin q) ℂ)) ⊗ₖ
      ((X : Matrix (Fin q) (Fin q) ℂ) * (Y : Matrix (Fin q) (Fin q) ℂ)) = 1) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (Y : Matrix (Fin q) (Fin q) ℂ) = σ • (X : Matrix (Fin q) (Fin q) ℂ)ᴴ := by
  obtain ⟨σ, hσ, hYX, hXY⟩ := Matrix.exists_eq_smul_one_of_kronecker_eq_one hK
  have hX : (X : Matrix (Fin q) (Fin q) ℂ) *
      (X : Matrix (Fin q) (Fin q) ℂ)ᴴ = 1 :=
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr X.property).2
  have hY : (Y : Matrix (Fin q) (Fin q) ℂ) =
      σ • (X : Matrix (Fin q) (Fin q) ℂ)ᴴ := by
    calc
      (Y : Matrix (Fin q) (Fin q) ℂ) =
          ((Y : Matrix (Fin q) (Fin q) ℂ) * (X : Matrix (Fin q) (Fin q) ℂ)) *
            (X : Matrix (Fin q) (Fin q) ℂ)ᴴ := by
              rw [Matrix.mul_assoc, hX, Matrix.mul_one]
      _ = σ • (X : Matrix (Fin q) (Fin q) ℂ)ᴴ := by
        rw [hYX, Matrix.smul_mul, Matrix.one_mul]
  have hXY' : (X : Matrix (Fin q) (Fin q) ℂ) * (Y : Matrix (Fin q) (Fin q) ℂ) = σ • 1 := by
    rw [hY, Matrix.mul_smul, hX]
  have hscalar : σ = σ⁻¹ := by
    let i : Fin q := ⟨0, NeZero.pos q⟩
    have h := congrArg (fun M : Matrix (Fin q) (Fin q) ℂ ↦ M i i)
      (hXY'.symm.trans hXY)
    simpa only [Matrix.smul_apply, Matrix.one_apply, ↓reduceIte,
      smul_eq_mul, mul_one] using h
  have hsq : σ ^ 2 = 1 := by
    calc
      σ ^ 2 = σ * σ := pow_two _
      _ = σ⁻¹ * σ := congrArg (· * σ) hscalar
      _ = 1 := inv_mul_cancel₀ hσ
  exact ⟨σ, sq_eq_one_iff.mp hsq, hY⟩

private theorem local_sign_of_adjoint_gate_gauges
    {q : ℕ} [NeZero q]
    (A B : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ)
    (hA : A.IsCoisometry) (X Y : Matrix.unitaryGroup (Fin q) ℂ)
    (hfirst : Bᴴ = ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (Y : Matrix (Fin q) (Fin q) ℂ)) * A)
    (hsecond : Aᴴ = B * ((Y : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
      (X : Matrix (Fin q) (Fin q) ℂ)ᴴ)) :
    ∃ (σ : ℂ) (x : Matrix.unitaryGroup (Fin q) ℂ),
      (σ = 1 ∨ σ = -1) ∧
      A = σ • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
        (x : Matrix (Fin q) (Fin q) ℂ)ᴴ) * Bᴴ := by
  have hdagger := congrArg Matrix.conjTranspose hsecond
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_kronecker] at hdagger
  have hcancel := hdagger
  rw [hfirst, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul] at hcancel
  have hA' : A * Aᴴ = 1 := hA
  have hK : ((Y : Matrix (Fin q) (Fin q) ℂ) * (X : Matrix (Fin q) (Fin q) ℂ)) ⊗ₖ
      ((X : Matrix (Fin q) (Fin q) ℂ) * (Y : Matrix (Fin q) (Fin q) ℂ)) = 1 := by
    have h := congrArg
      (fun M : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ ↦ M * Aᴴ) hcancel
    simpa only [Matrix.mul_assoc, hA', Matrix.mul_one] using h.symm
  obtain ⟨σ, hσ, hY⟩ := unitary_exchange_sign X Y hK
  refine ⟨σ, star X, hσ, ?_⟩
  rw [hdagger, hY, Matrix.smul_kronecker]
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]

private theorem four_spin_gate_reindex
    {d ℓ r : ℕ} (el : Fin ℓ ≃ Fin d) (er : Fin r ≃ Fin d)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    let u₀ := Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) u
    let v₀ := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) v
    let F := Equiv.prodCongr (Equiv.prodCongr el (Equiv.refl (Fin d)))
      (Equiv.prodCongr (Equiv.refl (Fin d)) er)
    let G := Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (Fin d)) er)
      (Equiv.prodCongr el (Equiv.refl (Fin d)))
    staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        Matrix.reindex F (Equiv.refl _)
          (staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u)) ∧
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ =
        Matrix.reindex (Equiv.refl _) G (staircaseMiddle (A := Fin d) (E := Fin d) v) := by
  classical
  let E := Equiv.prodCongr (Equiv.prodCongr el er) (Equiv.prodCongr el er)
  let F := Equiv.prodCongr (Equiv.prodCongr el (Equiv.refl (Fin d)))
    (Equiv.prodCongr (Equiv.refl (Fin d)) er)
  have hmiddle : staircaseMiddle (A := Fin d) (E := Fin d)
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) v) =
      Matrix.reindex F E (staircaseMiddle (A := Fin ℓ) (E := Fin r) v) := by
    apply Matrix.ext
    rintro ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
    simp [staircaseMiddle, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      Matrix.reindex_apply, F, E, Matrix.one_apply,
      el.symm.injective.eq_iff, er.symm.injective.eq_iff]
  have hkronecker :
      Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) u ⊗ₖ
        Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) u =
      Matrix.reindex E (Equiv.refl _) (u ⊗ₖ u) :=
    Matrix.kroneckerMap_reindex (fun a b : ℂ ↦ a * b)
      (Equiv.prodCongr el er) (Equiv.refl _)
      (Equiv.prodCongr el er) (Equiv.refl _) u u
  constructor
  · rw [hmiddle, hkronecker]
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ F E (Equiv.refl _) _ _
  · apply Matrix.ext
    rintro ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
    rfl

/-- The normalized coarse source gates are exactly the literal four-spin
matrices, after the explicit physical-pair and source-rank identifications.
Source: CPSV17, `eq:block-twosites`, lines 1237–1249. -/
theorem coarse_gates_eq_four_spin_gates
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (hrU : r[U] = d) (hlU : ℓ[U] = d)
    (hr : r[MPOTensor.blockTwo U] = d * d) (hl : ℓ[MPOTensor.blockTwo U] = d * d) :
    let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hlU) (finCongr hrU))
      (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef)
    let v₀ := Matrix.reindex (Equiv.refl _)
      (Equiv.prodCongr (finCongr hrU) (finCongr hlU)) (sourceV U hU.ρ hU.ρ_posDef)
    let p := Equiv.prodCongr (finProdFinEquiv (m := d) (n := d))
      (finProdFinEquiv (m := d) (n := d))
    Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
        (SourceFactors.sourceU (MPOTensor.blockTwo U) (hU.twoSiteSourceFactors hsimple)) =
      Matrix.reindex p p (staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀)) ∧
    Matrix.reindex (Equiv.refl _) (Equiv.prodCongr (finCongr hr) (finCongr hl))
        (SourceFactors.sourceV (MPOTensor.blockTwo U) (hU.twoSiteSourceFactors hsimple)) =
      Matrix.reindex p p (staircaseMiddle (A := Fin d) (E := Fin d) v₀) := by
  let er := finProdFinEquiv.trans (finCongr (hU.twoSite_sourceRanks hsimple).1.symm)
  let el := finProdFinEquiv.trans (finCongr (hU.twoSite_sourceRanks hsimple).2.symm)
  let R := finCongr hr
  let L := finCongr hl
  let er₀ := finCongr hrU
  let el₀ := finCongr hlU
  let p := Equiv.prodCongr (finProdFinEquiv (m := d) (n := d))
      (finProdFinEquiv (m := d) (n := d))
  let F := Equiv.prodCongr (Equiv.prodCongr el₀ (Equiv.refl (Fin d)))
    (Equiv.prodCongr (Equiv.refl (Fin d)) er₀)
  let G := Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (Fin d)) er₀)
    (Equiv.prodCongr el₀ (Equiv.refl (Fin d)))
  have her : er.trans R = (Equiv.prodCongr (Equiv.refl (Fin d)) er₀).trans finProdFinEquiv := by
    apply Equiv.ext
    rintro ⟨a, s⟩
    apply Fin.ext
    change s.val + r[U] * a.val = s.val + d * a.val
    exact congrArg (fun n : ℕ ↦ s.val + n * a.val) hrU
  have hel : el.trans L = (Equiv.prodCongr el₀ (Equiv.refl (Fin d))).trans finProdFinEquiv := by
    apply Equiv.ext
    rintro ⟨t, b⟩
    apply Fin.ext
    rfl
  have hrows : (Equiv.prodCongr el er).trans (Equiv.prodCongr L R) = F.trans p := by
    apply Equiv.ext
    rintro ⟨i, j⟩
    apply Prod.ext
    · exact congrArg (fun e : (Fin ℓ[U] × Fin d) ≃ Fin (d * d) ↦ e i) hel
    · exact congrArg (fun e : (Fin d × Fin r[U]) ≃ Fin (d * d) ↦ e j) her
  have hcols : (Equiv.prodCongr er el).trans (Equiv.prodCongr R L) = G.trans p := by
    apply Equiv.ext
    rintro ⟨i, j⟩
    apply Prod.ext
    · exact congrArg (fun e : (Fin d × Fin r[U]) ≃ Fin (d * d) ↦ e i) her
    · exact congrArg (fun e : (Fin ℓ[U] × Fin d) ≃ Fin (d * d) ↦ e j) hel
  obtain ⟨hu, hv⟩ := four_spin_gate_reindex el₀ er₀
    (sourceU U hU.ρ hU.ρ_posDef) (sourceV U hU.ρ hU.ρ_posDef)
  dsimp only
  constructor
  · rw [hU.twoSiteSourceFactors_sourceU hsimple, hu]
    let M := staircaseMiddle (A := Fin ℓ[U]) (E := Fin r[U])
      (sourceV U hU.ρ hU.ρ_posDef) *
        (sourceU U hU.ρ hU.ρ_posDef ⊗ₖ sourceU U hU.ρ hU.ρ_posDef)
    change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr L R) (Equiv.refl _)
        (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr el er) p M) =
      Matrix.reindexLinearEquiv ℂ ℂ p p
        (Matrix.reindexLinearEquiv ℂ ℂ F (Equiv.refl _) M)
    simp only [Matrix.reindexLinearEquiv_comp_apply, Equiv.trans_refl,
      Equiv.refl_trans, hrows]
  · rw [hU.twoSiteSourceFactors_sourceV hsimple, hv]
    let M := staircaseMiddle (A := Fin d) (E := Fin d) (sourceV U hU.ρ hU.ρ_posDef)
    change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.prodCongr R L)
        (Matrix.reindexLinearEquiv ℂ ℂ p (Equiv.prodCongr er el) M) =
      Matrix.reindexLinearEquiv ℂ ℂ p p
        (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) G M)
    simp only [Matrix.reindexLinearEquiv_comp_apply, Equiv.trans_refl,
      Equiv.refl_trans, hcols]

/-- Global adjoint symmetry at even standard-form lengths yields an actual local
sign certificate for the normalized coarse source gates, in physical-block
coordinates. The rank equalities, adjoint factors and comparison gauges are
all derived. Source: arXiv:1703.09188, proof of `PropChiral`, lines 1237–1252. -/
theorem IsMPUCanonicalFormII.exists_coarse_timeReversal_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᴴ) :
    ∃ (hr : r[MPOTensor.blockTwo U] = d * d)
      (hl : ℓ[MPOTensor.blockTwo U] = d * d)
      (σ : ℂ) (x : Matrix.unitaryGroup (Fin (d * d)) ℂ),
      (σ = 1 ∨ σ = -1) ∧
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          (SourceFactors.sourceU (MPOTensor.blockTwo U) (hU.twoSiteSourceFactors hsimple)) =
        σ • ((x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
          (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ) *
          (Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr) (finCongr hl))
            (SourceFactors.sourceV (MPOTensor.blockTwo U)
              (hU.twoSiteSourceFactors hsimple)))ᴴ := by
  classical
  let W := MPOTensor.blockTwo U
  let hW := hU.blockTwo
  let S : SourceFactors W hW.ρ := hU.twoSiteSourceFactors hsimple
  have hSW := hU.isMPUSimple_blockTwo hsimple
  obtain ⟨hrU, hlU⟩ := hU.sourceRanks_eq_phys_of_standardForm_even_mpo_eq_adjoint hsimple hTR
  obtain ⟨hrB, hlB⟩ := hU.twoSite_sourceRanks hsimple
  have hr : r[W] = d * d := hrB.trans (congrArg (d * ·) hrU)
  have hl : ℓ[W] = d * d := hlB.trans (congrArg (· * d) hlU)
  let T := SourceFactors.physicalAdjoint hW hSW S hr hl
  have hEq : ∀ N : ℕ, 1 < N → Even N →
      mpo W N = mpo (MPOTensor.physicalAdjointTensor W) N := by
    intro N hN heven
    rw [mpo_physicalAdjointTensor_eq_conjTranspose]
    exact hTR N hN heven
  have huS := hW.sourceFactors_sourceU_isUnitaryBetween hSW S
  have huT := hW.physicalAdjointTensor.sourceFactors_sourceU_isUnitaryBetween
    (hW.isMPUSimple_physicalAdjointTensor hSW) T
  obtain ⟨hrFT, hlFT, X, Y, hu, hv⟩ :=
    hW.exists_supplied_source_gate_unitary_gauges_of_mpo_eq_even
      hW.physicalAdjointTensor S T huS huT hEq
  let L := finCongr hl
  let R := finCongr hr
  let LA := finCongr ((leftRank_physicalAdjointTensor W).trans hr)
  let RA := finCongr ((rightRank_physicalAdjointTensor W).trans hl)
  let A := Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _) (SourceFactors.sourceU W S)
  let B := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L) (SourceFactors.sourceV W S)
  let X' : Matrix.unitaryGroup (Fin (d * d)) ℂ :=
    ⟨Matrix.reindex LA LA X, Matrix.reindex_mem_unitaryGroup _ _ X.property⟩
  let Y' : Matrix.unitaryGroup (Fin (d * d)) ℂ :=
    ⟨Matrix.reindex RA RA Y, Matrix.reindex_mem_unitaryGroup _ _ Y.property⟩
  let erA := finCongr (rightRank_physicalAdjointTensor W).symm
  let elA := finCongr (leftRank_physicalAdjointTensor W).symm
  let erFT := finCongr hrFT.symm
  let elFT := finCongr hlFT.symm
  have hUA : Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)
      (Matrix.reindex (Equiv.prodCongr elA erA) (Equiv.refl _)
        (SourceFactors.sourceV W S)ᴴ) = Bᴴ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  have hUFT : Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)
      (Matrix.reindex (Equiv.prodCongr elFT erFT) (Equiv.refl _)
        (SourceFactors.sourceU W S)) = A := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  have hVA : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erA elA)
        (SourceFactors.sourceU W S)ᴴ) = Aᴴ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  have hVFT : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erFT elFT)
        (SourceFactors.sourceV W S)) = B := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  have hfirst : Bᴴ = ((X' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
      (Y' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)) * A := by
    have h := congrArg (Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)) hu
    dsimp only [T] at h
    rw [SourceFactors.sourceU_physicalAdjoint] at h
    rw [Matrix.reindex_kronecker_mul] at h
    rw [hUA, hUFT] at h
    exact h
  have hsecond : Aᴴ = B * ((Y' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ ⊗ₖ
      (X' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ) := by
    have h := congrArg (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)) hv
    dsimp only [T] at h
    rw [SourceFactors.sourceV_physicalAdjoint] at h
    rw [Matrix.reindex_mul_kronecker] at h
    rw [hVA, hVFT] at h
    simpa only [X', Y', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex] using h
  have hA : A.IsCoisometry := (huS.reindex _ (Equiv.prodCongr L R) (Equiv.refl _)).2
  let : NeZero (d * d) := hW.neZero_phys
  obtain ⟨σ, x, hσ, hlocal⟩ := local_sign_of_adjoint_gate_gauges A B hA X' Y' hfirst hsecond
  exact ⟨hr, hl, σ, x, hσ, hlocal⟩

/-- The literal four-original-spin time-reversal certificate for the actual
canonical source standard form. The source ranks are proved to equal d;
the supplied gates are then transported only along these canonical rank
identifications. No local certificate or gauge-existence premise is assumed.
Source: arXiv:1703.09188, `PropChiral`, `eq:block-twosites` and
`UUdaggertrick`, lines 1201–1252. The finite-chain hypothesis is at even
standard-form lengths, and no additional blocking is used. -/
theorem IsMPUCanonicalFormII.exists_local_timeReversal_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᴴ) :
    ∃ (hrU : r[U] = d) (hlU : ℓ[U] = d) (σ : ℂ)
      (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hlU) (finCongr hrU))
        (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef)
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hrU) (finCongr hlU)) (sourceV U hU.ρ hU.ρ_posDef)
      (σ = 1 ∨ σ = -1) ∧
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) * (staircaseMiddle v₀)ᴴ := by
  obtain ⟨hrU, hlU⟩ := hU.sourceRanks_eq_phys_of_standardForm_even_mpo_eq_adjoint hsimple hTR
  obtain ⟨hr, hl, σ, x, hσ, h⟩ := hU.exists_coarse_timeReversal_certificate hsimple hTR
  let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hlU) (finCongr hrU))
    (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef)
  let v₀ := Matrix.reindex (Equiv.refl _)
    (Equiv.prodCongr (finCongr hrU) (finCongr hlU)) (sourceV U hU.ρ hU.ρ_posDef)
  let A := staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀)
  let B := staircaseMiddle (A := Fin d) (E := Fin d) v₀
  let e : (Fin d × Fin d) ≃ Fin (d * d) := finProdFinEquiv
  let p := Equiv.prodCongr e e
  let E := Matrix.reindexLinearEquiv ℂ ℂ p p
  let x₀ : Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    ⟨Matrix.reindex e.symm e.symm (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ),
      Matrix.reindex_mem_unitaryGroup _ _ x.property⟩
  obtain ⟨hA, hB⟩ := coarse_gates_eq_four_spin_gates hU hsimple hrU hlU hr hl
  rw [hA, hB, Matrix.smul_mul] at h
  have h' := congrArg (Matrix.reindexLinearEquiv ℂ ℂ p.symm p.symm) h
  rw [map_smul, ← Matrix.reindexLinearEquiv_mul ℂ ℂ p.symm p.symm p.symm] at h'
  have hA' : Matrix.reindexLinearEquiv ℂ ℂ p.symm p.symm
      (Matrix.reindex p p A) = A := by
    change E.symm (E A) = A
    exact E.symm_apply_apply A
  have hB' : Matrix.reindexLinearEquiv ℂ ℂ p.symm p.symm
      (Matrix.reindex p p B)ᴴ = Bᴴ := by
    rw [Matrix.conjTranspose_reindex]
    change E.symm (E Bᴴ) = Bᴴ
    exact E.symm_apply_apply Bᴴ
  have hk : Matrix.reindexLinearEquiv ℂ ℂ p.symm p.symm
      ((x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
        (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ) =
      (x₀ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
        (x₀ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ := by
    change Matrix.reindex (Equiv.prodCongr e.symm e.symm)
        (Equiv.prodCongr e.symm e.symm)
        ((x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
          (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ) = _
    dsimp only [x₀]
    rw [Matrix.conjTranspose_reindex]
    exact (Matrix.kroneckerMap_reindex (fun a b : ℂ ↦ a * b)
      e.symm e.symm e.symm e.symm
      (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
      (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ).symm
  rw [hA', hk, hB'] at h'
  refine ⟨hrU, hlU, σ, x₀, hσ, ?_⟩
  change A = σ • ((x₀ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
    (x₀ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) * Bᴴ
  rw [Matrix.smul_mul]
  exact h'

/-- The actual constructed standard form can be supplied together with its
literal local time-reversal certificate. This derives the pointwise data
needed by the intrinsic-sign path theorem, without assuming the missing
certificate or continuity of any factor choice. Source: arXiv:1703.09188,
`PropChiral` and `UUdaggertrick`, lines 1201–1252. -/
theorem IsMPUCanonicalFormII.exists_twoSiteStandardFormData_timeReversal_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᴴ) :
    ∃ u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      ∃ _S : TwoSiteStandardFormData (MPOTensor.blockTwo U) u v,
      ∃ (σ : ℂ) (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
        (σ = 1 ∨ σ = -1) ∧
        staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
          σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) * (staircaseMiddle v)ᴴ := by
  obtain ⟨hrU, hlU, σ, x, hσ, hlocal⟩ :=
    hU.exists_local_timeReversal_certificate hsimple hTR
  exact ⟨_, _, (hU.twoSiteStandardFormData hsimple).reindexRanks
    (finCongr hlU) (finCongr hrU), σ, x, hσ, hlocal⟩

end MPOTensor
