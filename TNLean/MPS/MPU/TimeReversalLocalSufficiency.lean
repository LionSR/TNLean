/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceFactorsStandardForm
import TNLean.MPS.MPU.TimeReversalLocalNecessity

/-!
# Even-ring contraction of the local time-reversal equation

The literal local sign equation gives both adjoint gate relations. Actual
standard-form data for the supplied normalized factors and their derived
physical-adjoint factors then close these relations on every even ring.
The local antecedent is unchanged; blocking only identifies the even ring
whose periodic operator is the conclusion.

Source: arXiv:1703.09188, `PropChiral`, `UUdaggertrick`, and
`eq:dagger-sym-cond`, lines 1214–1236. **Scope restriction (canonical source
construction):** The supplied factors use the recorded weight of a reduced
canonical presentation; see `docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix Kronecker

namespace MPOTensor

private theorem adjoint_gate_gauges_of_local_sign
    {q : ℕ} (A B : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (x : Matrix.unitaryGroup (Fin q) ℂ)
    (hlocal : A = σ • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (x : Matrix (Fin q) (Fin q) ℂ)ᴴ) * Bᴴ) :
    ∃ X Y : Matrix.unitaryGroup (Fin q) ℂ,
      Bᴴ = ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
        (Y : Matrix (Fin q) (Fin q) ℂ)) * A ∧
      Aᴴ = B * ((Y : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
        (X : Matrix (Fin q) (Fin q) ℂ)ᴴ) := by
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσstar : star σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hxx : (x : Matrix (Fin q) (Fin q) ℂ)ᴴ *
      (x : Matrix (Fin q) (Fin q) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp x.property
  let X := star x
  let Y : Matrix.unitaryGroup (Fin q) ℂ := ⟨σ • (x : Matrix (Fin q) (Fin q) ℂ), by
    rw [← Matrix.isUnitaryBetween_iff_mem_unitaryGroup]
    constructor
    · change (σ • (x : Matrix (Fin q) (Fin q) ℂ))ᴴ *
        (σ • (x : Matrix (Fin q) (Fin q) ℂ)) = 1
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, hσstar, one_smul, hxx]
    · change (σ • (x : Matrix (Fin q) (Fin q) ℂ)) *
        (σ • (x : Matrix (Fin q) (Fin q) ℂ))ᴴ = 1
      have hσstar' : σ * star σ = 1 := by rw [mul_comm, hσstar]
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, hσstar', one_smul]
      exact ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr x.property).2⟩
  let K := (x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)ᴴ
  have hK : Kᴴ * K = 1 :=
    ((Matrix.isUnitaryBetween_coe_unitaryGroup x).kronecker _ _
      (Matrix.isUnitaryBetween_star_coe_unitaryGroup x)).1
  have hXY : ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (Y : Matrix (Fin q) (Fin q) ℂ)) = σ • Kᴴ := by
    change (x : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
      (σ • (x : Matrix (Fin q) (Fin q) ℂ)) = _
    rw [Matrix.kronecker_smul]
    simp only [K, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose]
  refine ⟨X, Y, ?_, ?_⟩
  · rw [hXY, hlocal]
    change Bᴴ = (σ • Kᴴ) * ((σ • K) * Bᴴ)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hσsq, one_smul]
    rw [← Matrix.mul_assoc, hK, Matrix.one_mul]
  · have h := congrArg Matrix.conjTranspose hlocal
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose] at h
    simpa only [X, Y, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
      Matrix.smul_kronecker] using h

/-- The local sign equation for actual normalized source factors closes on
every positive even ring. No extra local equation or adjoint-factor supplier
is assumed. Source: CPSV17, `PropChiral`, the implication proved by
`eq:dagger-sym-cond`, lines 1214–1236. -/
theorem IsMPUCanonicalFormII.mpo_even_eq_adjoint_of_source_local_certificate
    {q D : ℕ} {U : MPOTensor q D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ)
    (hr : r[U] = q) (hl : ℓ[U] = q)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (x : Matrix.unitaryGroup (Fin q) ℂ)
    (hlocal :
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          (SourceFactors.sourceU U S) =
        σ • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
          (x : Matrix (Fin q) (Fin q) ℂ)ᴴ) *
          (Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr) (finCongr hl))
            (SourceFactors.sourceV U S))ᴴ)
    (N : ℕ) (hN : 1 < N) (heven : Even N) : mpo U N = (mpo U N)ᴴ := by
  classical
  let T := SourceFactors.physicalAdjoint hU hsimple S hr hl
  let L := finCongr hl
  let R := finCongr hr
  let LA := finCongr ((leftRank_physicalAdjointTensor U).trans hr)
  let RA := finCongr ((rightRank_physicalAdjointTensor U).trans hl)
  let A := Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _) (SourceFactors.sourceU U S)
  let B := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L) (SourceFactors.sourceV U S)
  obtain ⟨dataS⟩ := hU.exists_twoSiteStandardFormData_sourceFactors hsimple S
  obtain ⟨dataT⟩ := hU.physicalAdjointTensor.exists_twoSiteStandardFormData_sourceFactors
    (hU.isMPUSimple_physicalAdjointTensor hsimple) T
  have dataA : TwoSiteStandardFormData (MPOTensor.blockTwo U) A B := dataS.reindexRanks L R
  have dataB : TwoSiteStandardFormData
      (MPOTensor.blockTwo (MPOTensor.physicalAdjointTensor U)) Bᴴ Aᴴ := by
    have data := dataT.reindexRanks LA RA
    change TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.physicalAdjointTensor U))
      (Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)
        (SourceFactors.sourceU (ρ := hU.ρ) (MPOTensor.physicalAdjointTensor U) T))
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)
        (SourceFactors.sourceV (ρ := hU.ρ) (MPOTensor.physicalAdjointTensor U) T)) at data
    dsimp only [T] at data
    rw [SourceFactors.sourceU_physicalAdjoint hU hsimple S hr hl,
      SourceFactors.sourceV_physicalAdjoint hU hsimple S hr hl] at data
    have hu : Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)
        (Matrix.reindex
          (Equiv.prodCongr (finCongr (leftRank_physicalAdjointTensor U).symm)
            (finCongr (rightRank_physicalAdjointTensor U).symm))
          (Equiv.refl _) (SourceFactors.sourceV U S)ᴴ) = Bᴴ := by
      ext ⟨i, j⟩ ⟨k, l⟩
      rfl
    have hv : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)
        (Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr (rightRank_physicalAdjointTensor U).symm)
            (finCongr (leftRank_physicalAdjointTensor U).symm))
          (SourceFactors.sourceU U S)ᴴ) = Aᴴ := by
      ext ⟨i, j⟩ ⟨k, l⟩
      rfl
    rw [hu, hv] at data
    exact data
  obtain ⟨X, Y, hfirst, hsecond⟩ := adjoint_gate_gauges_of_local_sign A B σ hσ x hlocal
  rw [hfirst, hsecond] at dataB
  rcases heven with ⟨m, rfl⟩
  let : NeZero m := ⟨by omega⟩
  have h := dataA.mpo_eq_of_gate_gauges (N := m) X Y dataB
  rw [mpo_blockTwo_eq_reindex_blockTensor, mpo_blockTwo_eq_reindex_blockTensor] at h
  have h' := (Matrix.reindex _ _).injective h
  rw [mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex] at h'
  have h'' := (Matrix.reindex _ _).injective h'
  rw [mpo_physicalAdjointTensor_eq_conjTranspose] at h''
  rw [Nat.mul_two] at h''
  exact h''

/-- The original four-spin equation for the chosen source gates implies
adjoint symmetry at every even length of their actual standard-form tensor.
No stronger all-length symmetry is assumed. Source: CPSV17, `PropChiral`,
`UUdaggertrick` and `eq:dagger-sym-cond`, lines 1214–1236. -/
theorem IsMPUCanonicalFormII.mpo_standardForm_even_eq_adjoint_of_local_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (hrU : r[U] = d) (hlU : ℓ[U] = d)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hlocal :
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hlU) (finCongr hrU))
        (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef)
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hrU) (finCongr hlU)) (sourceV U hU.ρ hU.ρ_posDef)
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        σ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) * (staircaseMiddle v₀)ᴴ)
    (N : ℕ) (hN : 1 < N) (heven : Even N) :
    mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᴴ := by
  classical
  obtain ⟨hrB, hlB⟩ := hU.twoSite_sourceRanks hsimple
  have hr : r[MPOTensor.blockTwo U] = d * d := hrB.trans (congrArg (d * ·) hrU)
  have hl : ℓ[MPOTensor.blockTwo U] = d * d := hlB.trans (congrArg (· * d) hlU)
  let e : (Fin d × Fin d) ≃ Fin (d * d) := finProdFinEquiv
  let x' : Matrix.unitaryGroup (Fin (d * d)) ℂ :=
    ⟨Matrix.reindex e e (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      Matrix.reindex_mem_unitaryGroup _ _ x.property⟩
  have hsource :
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          (SourceFactors.sourceU (ρ := hU.ρ) (MPOTensor.blockTwo U)
            (hU.twoSiteSourceFactors hsimple)) =
        σ • ((x' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
          (x' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᴴ) *
          (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr (finCongr hr) (finCongr hl))
            (SourceFactors.sourceV (ρ := hU.ρ) (MPOTensor.blockTwo U)
              (hU.twoSiteSourceFactors hsimple)))ᴴ := by
    obtain ⟨hA, hB⟩ := coarse_gates_eq_four_spin_gates hU hsimple hrU hlU hr hl
    rw [hA, hB]
    exact Matrix.reindex_adjoint_certificate e hlocal
  exact hU.blockTwo.mpo_even_eq_adjoint_of_source_local_certificate
    (hU.isMPUSimple_blockTwo hsimple) (hU.twoSiteSourceFactors hsimple)
    hr hl σ hσ x' hsource N hN heven

/-- The chosen canonical source standard form obeys the literal local
criterion with exactly the source's even-standard-form-length convention.
The rank identifications in the local equation are derived in the forward
implication. Source: CPSV17, `PropChiral`, lines 1201–1252. -/
theorem IsMPUCanonicalFormII.standardForm_even_timeReversal_iff_exists_local_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) :
    (∀ N : ℕ, 1 < N → Even N → mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᴴ) ↔
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
  constructor
  · exact hU.exists_local_timeReversal_certificate hsimple
  · rintro ⟨hrU, hlU, σ, x, hσ, hlocal⟩ N hN heven
    exact hU.mpo_standardForm_even_eq_adjoint_of_local_certificate
      hsimple hrU hlU σ hσ x hlocal N hN heven

end MPOTensor
