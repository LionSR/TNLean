/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TranspositionLocalNecessity
import TNLean.MPS.MPU.SourceFactorsStandardForm

/-!
# Even-ring converse of the local transposition phase equation

For a unit phase c, the local equation gives both source gate relations with
X=x† and Y=conj(c) conj(x). The actual transpose source factors and the actual
standard-form supplier then close these equations on every even ring. No
phase sign restriction, transform witness or extra local hypothesis is added.

Source: arXiv:1703.09188, `prop:local-char-transposition` and
`UUtransposetrick`, lines 1258–1288. **Scope restriction (canonical source
construction):** The final equivalence concerns the standard form actually
constructed from a simple reduced canonical tensor; arbitrary supplied
presentations remain covered by `docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix Kronecker

namespace MPOTensor

private theorem transpose_gate_gauges_of_local_phase
    {q : ℕ} (A B : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (x : Matrix.unitaryGroup (Fin q) ℂ)
    (hlocal : A = c • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (x : Matrix (Fin q) (Fin q) ℂ)ᵀ) * Bᵀ) :
    ∃ X Y : Matrix.unitaryGroup (Fin q) ℂ,
      Bᵀ = ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
        (Y : Matrix (Fin q) (Fin q) ℂ)) * A ∧
      Aᵀ = B * ((Y : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
        (X : Matrix (Fin q) (Fin q) ℂ)ᴴ) := by
  have hcc : c * star c = 1 := by
    have h := Complex.mul_conj c
    rw [Complex.normSq_eq_norm_sq, hc] at h
    simpa only [one_pow, Complex.ofReal_one] using h
  have hcc' : star c * c = 1 := by rw [mul_comm, hcc]
  let Xbar := (x : Matrix (Fin q) (Fin q) ℂ).map (starRingEnd ℂ)
  have hbar : Xbar.IsUnitaryBetween :=
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr x.property).map_star
  have hxt : ((x : Matrix (Fin q) (Fin q) ℂ)ᵀ).IsUnitaryBetween :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr
      (Matrix.transpose_mem_unitaryGroup_iff.mpr x.property)
  have hxtdag : (x : Matrix (Fin q) (Fin q) ℂ)ᵀᴴ = Xbar := rfl
  have hbardag : Xbarᴴ = (x : Matrix (Fin q) (Fin q) ℂ)ᵀ := by
    rw [← hxtdag, Matrix.conjTranspose_conjTranspose]
  let X := star x
  let Y : Matrix.unitaryGroup (Fin q) ℂ := ⟨star c • Xbar, by
    rw [Matrix.mem_unitaryGroup_iff']
    change (star c • Xbar)ᴴ * (star c • Xbar) = 1
    rw [Matrix.conjTranspose_smul, star_star, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcc, one_smul]
    exact hbar.1⟩
  let K := (x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)ᵀ
  have hK : Kᴴ * K = 1 :=
    ((Matrix.isUnitaryBetween_coe_unitaryGroup x).kronecker _ _ hxt).1
  have hXY : ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (Y : Matrix (Fin q) (Fin q) ℂ)) = star c • Kᴴ := by
    change (x : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ (star c • Xbar) = _
    rw [Matrix.kronecker_smul]
    simp only [K, Matrix.conjTranspose_kronecker, hxtdag]
  have hYX : ((Y : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
      (X : Matrix (Fin q) (Fin q) ℂ)ᴴ) =
      c • ((x : Matrix (Fin q) (Fin q) ℂ)ᵀ ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)) := by
    change (star c • Xbar)ᴴ ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)ᴴᴴ = _
    rw [Matrix.conjTranspose_smul, star_star, hbardag,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_kronecker]
  refine ⟨X, Y, ?_, ?_⟩
  · rw [hXY, hlocal]
    change Bᵀ = (star c • Kᴴ) * ((c • K) * Bᵀ)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc', one_smul]
    rw [← Matrix.mul_assoc, hK, Matrix.one_mul]
  · have h := congrArg Matrix.transpose hlocal
    simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose,
      ← Matrix.kroneckerMap_transpose] at h
    simpa only [hYX] using h

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
  let T := SourceFactors.physicalTranspose hU hsimple S hr hl
  let L := finCongr hl
  let R := finCongr hr
  let LA := finCongr ((source_ranks_physicalTransposeTensor U).2.trans hr)
  let RA := finCongr ((source_ranks_physicalTransposeTensor U).1.trans hl)
  let A := Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _) (SourceFactors.sourceU U S)
  let B := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L) (SourceFactors.sourceV U S)
  obtain ⟨dataS⟩ := hU.exists_twoSiteStandardFormData_sourceFactors hsimple S
  obtain ⟨dataT⟩ := hU.physicalTransposeTensor.exists_twoSiteStandardFormData_sourceFactors
    (hU.isMPUSimple_physicalTransposeTensor hsimple) T
  have dataA : TwoSiteStandardFormData (MPOTensor.blockTwo U) A B := dataS.reindexRanks L R
  have dataB : TwoSiteStandardFormData
      (MPOTensor.blockTwo (MPOTensor.physicalTransposeTensor U)) Bᵀ Aᵀ := by
    have data := dataT.reindexRanks LA RA
    dsimp only [T] at data
    rw [SourceFactors.sourceU_physicalTranspose, SourceFactors.sourceV_physicalTranspose] at data
    simpa only [A, B, L, R, LA, RA, Matrix.transpose_reindex] using data
  obtain ⟨X, Y, hfirst, hsecond⟩ := transpose_gate_gauges_of_local_phase A B c hc x hlocal
  rw [hfirst, hsecond] at dataB
  rcases heven with ⟨m, rfl⟩
  letI : NeZero m := ⟨by omega⟩
  have h := dataA.mpo_eq_of_gate_gauges (N := m) X Y dataB
  rw [mpo_blockTwo_eq_reindex_blockTensor, mpo_blockTwo_eq_reindex_blockTensor] at h
  have h' := (Matrix.reindex _ _).injective h
  rw [mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex] at h'
  have h'' := (Matrix.reindex _ _).injective h'
  rw [mpo_physicalTransposeTensor] at h''
  simpa only [mul_two] using h''

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
  let p := Equiv.prodCongr e e
  let E := Matrix.reindexLinearEquiv ℂ ℂ p p
  let x' : Matrix.unitaryGroup (Fin (d * d)) ℂ :=
    ⟨Matrix.reindex e e (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      Matrix.reindex_mem_unitaryGroup _ _ x.property⟩
  apply hU.blockTwo.mpo_even_eq_transpose_of_source_local_certificate
    (hU.isMPUSimple_blockTwo hsimple) (hU.twoSiteSourceFactors hsimple)
    hr hl c hc x' ?_ N hN heven
  obtain ⟨hA, hB⟩ := coarse_gates_eq_four_spin_gates hU hsimple hrU hlU hr hl
  rw [hA, hB]
  have h := congrArg E hlocal
  rw [Matrix.smul_mul, map_smul,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ p p p] at h
  have hK : E ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
      (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) =
      (x' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
        (x' : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᵀ := by
    change Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) _ = _
    dsimp only [x']
    rw [Matrix.transpose_reindex]
    exact (Matrix.kroneckerMap_reindex (fun a b : ℂ ↦ a * b) e e e e
      (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ).symm
  rw [hK] at h
  simp only [Matrix.transpose_reindex] at ⊢
  rw [Matrix.smul_mul]
  exact h

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
