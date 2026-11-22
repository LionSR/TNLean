/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.Transposition.TranspositionLocalNecessity
import TNLean.MPS.MPU.StandardForm.SourceFactorsStandardForm
import QICLean.Analysis.Isometry.UnitPhaseScalar
import TNLean.MPS.MPU.Symmetry.Transposition.TranspositionGateCertificate

/-!
# Even-ring converse of the local transposition phase equation

For a unit phase c, the local equation for the actual normalized source
factors gives transpose symmetry on every even ring, through the standard form
of the two-site block that these factors supply
(`MPOTensor.TwoSiteStandardFormData.mpo_blockTwo_eq_transpose_of_local_phase`).
No phase sign restriction, transform witness or extra local hypothesis is added.

Source: arXiv:1703.09188, `prop:local-char-transposition` and
`UUtransposetrick`, lines 1258–1288. **Scope restriction (canonical source
construction):** The final equivalence concerns the standard form actually
constructed from a simple reduced canonical tensor; arbitrary supplied
presentations remain covered by `docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix Kronecker

namespace MPOTensor

/-- The actual normalized source phase equation implies transpose symmetry
on every even ring. The actual transpose factors and their standard forms are
derived internally. Source: CPSV17, `prop:local-char-transposition`,
lines 1266–1288. -/
theorem IsMPUCanonicalFormII.mpo_even_eq_transpose_of_source_local_certificate
    {q D : ℕ} {U : MPOTensor q D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ)
    (hr : r[U] = q) (hl : ℓ[U] = q)
    (c : ℂ) (hc : ‖c‖ = 1) (x : Matrix.unitaryGroup (Fin q) ℂ)
    (hlocal :
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          (SourceFactors.sourceU U S) =
        c • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
          (x : Matrix (Fin q) (Fin q) ℂ)ᵀ) *
          (Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr) (finCongr hl)) (SourceFactors.sourceV U S))ᵀ)
    (N : ℕ) (hN : 1 < N) (heven : Even N) : mpo U N = (mpo U N)ᵀ := by
  classical
  let L := finCongr hl
  let R := finCongr hr
  let A := Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _) (SourceFactors.sourceU U S)
  let B := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L) (SourceFactors.sourceV U S)
  obtain ⟨dataS⟩ := hU.exists_twoSiteStandardFormData_sourceFactors hsimple S
  have dataA : TwoSiteStandardFormData (MPOTensor.blockTwo U) A B := dataS.reindexRanks L R
  rcases heven with ⟨m, rfl⟩
  let : NeZero m := ⟨by omega⟩
  exact mpo_even_eq_transpose_of_blockTwo
    (dataA.mpo_blockTwo_eq_transpose_of_local_phase c hc x hlocal m)

/-- The original four-spin equation for the chosen source gates implies
transpose symmetry at every even length of their actual standard-form tensor.
No stronger all-length symmetry is assumed. Source: CPSV17, `prop:local-char-transposition` and
`UUtransposetrick`, lines 1258–1288. -/
theorem IsMPUCanonicalFormII.mpo_standardForm_even_eq_transpose_of_local_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (hrU : r[U] = d) (hlU : ℓ[U] = d)
    (c : ℂ) (hc : ‖c‖ = 1)
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hlocal :
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hlU) (finCongr hrU))
        (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef)
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hrU) (finCongr hlU)) (sourceV U hU.ρ hU.ρ_posDef)
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        c • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) * (staircaseMiddle v₀)ᵀ)
    (N : ℕ) (hN : 1 < N) (heven : Even N) :
    mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᵀ := by
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
        c • ((x' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
          (x' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᵀ) *
          (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr (finCongr hr) (finCongr hl))
            (SourceFactors.sourceV (ρ := hU.ρ) (MPOTensor.blockTwo U)
              (hU.twoSiteSourceFactors hsimple)))ᵀ := by
    obtain ⟨hA, hB⟩ := coarse_gates_eq_four_spin_gates hU hsimple hrU hlU hr hl
    rw [hA, hB]
    exact Matrix.reindex_transposition_certificate e hlocal
  exact hU.blockTwo.mpo_even_eq_transpose_of_source_local_certificate
    (hU.isMPUSimple_blockTwo hsimple) (hU.twoSiteSourceFactors hsimple)
    hr hl c hc x' hsource N hN heven

/-- The chosen canonical source standard form obeys the literal local
criterion with exactly the source's even-standard-form-length convention.
The rank identifications in the local equation are derived in the forward
implication. Source: CPSV17, `prop:local-char-transposition`, lines 1258–1288. -/
theorem IsMPUCanonicalFormII.standardForm_even_transposition_iff_exists_local_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) :
    (∀ N : ℕ, 1 < N → Even N → mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᵀ) ↔
      ∃ (hrU : r[U] = d) (hlU : ℓ[U] = d) (c : ℂ)
        (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
        let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hlU) (finCongr hrU))
          (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef)
        let v₀ := Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr hrU) (finCongr hlU)) (sourceV U hU.ρ hU.ρ_posDef)
        ‖c‖ = 1 ∧
        staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
          c • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) * (staircaseMiddle v₀)ᵀ := by
  constructor
  · exact hU.exists_local_transposition_certificate hsimple
  · rintro ⟨hrU, hlU, c, x, hc, hlocal⟩ N hN heven
    exact hU.mpo_standardForm_even_eq_transpose_of_local_certificate
      hsimple hrU hlU c hc x hlocal N hN heven


end MPOTensor
