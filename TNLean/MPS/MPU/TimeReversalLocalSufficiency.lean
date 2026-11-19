/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceFactorsStandardForm
import TNLean.MPS.MPU.TimeReversalLocalNecessity
import TNLean.MPS.MPU.TimeReversalGateCertificate

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
  let L := finCongr hl
  let R := finCongr hr
  let A := Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _) (SourceFactors.sourceU U S)
  let B := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L) (SourceFactors.sourceV U S)
  obtain ⟨dataS⟩ := hU.exists_twoSiteStandardFormData_sourceFactors hsimple S
  have dataA : TwoSiteStandardFormData (MPOTensor.blockTwo U) A B := dataS.reindexRanks L R
  rcases heven with ⟨m, rfl⟩
  let : NeZero m := ⟨by omega⟩
  exact mpo_even_eq_conjTranspose_of_blockTwo
    (dataA.mpo_blockTwo_eq_conjTranspose_of_local_sign σ hσ x hlocal m)

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
