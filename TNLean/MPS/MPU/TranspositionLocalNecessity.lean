/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.PhysicalTransposeSourceFactors
import TNLean.MPS.MPU.TimeReversalLocalNecessity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Local transposition phase from the actual even periodic family

The actual physical-transpose factor record has gates vᵀ,uᵀ. The even-family
Fundamental Theorem supplies its two unitary gauge relations. Transposing the
second and cancelling the coisometric first gate makes the two Kronecker
factors scalar. Their unitarity forces a unit-modulus scalar, with no sign
restriction. This proves a local phase certificate for the actual normalized
supplied factors, without assuming a missing gauge or transform witness.

Source: arXiv:1703.09188, `prop:local-char-transposition`,
`UUtransposetrick`, lines 1258–1288. **Scope restriction (canonical source
factors):** The tensor has a reduced canonical presentation and the supplied
factors use its recorded boundary; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. This module does not
assert the unrestricted supplied-standard-form equivalence or its converse.
-/

open scoped Matrix Kronecker

namespace MPOTensor

/-- Transposing the second gauge relation and cancelling `A` against the first through its
coisometry leaves a Kronecker product equal to a scalar, which yields a unit-modulus phase
`c` and a unitary `x` with `A = c • (x ⊗ₖ xᵀ) * Bᵀ`. Source: CPSV17,
`prop:local-char-transposition`, lines 1266–1288. -/
private theorem transpose_local_phase_of_gate_gauges
    {q : ℕ} [NeZero q]
    (A B : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ) (hA : A.IsCoisometry)
    (X Y : Matrix.unitaryGroup (Fin q) ℂ)
    (hfirst : Bᵀ = ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (Y : Matrix (Fin q) (Fin q) ℂ)) * A)
    (hsecond : Aᵀ = B * ((Y : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
      (X : Matrix (Fin q) (Fin q) ℂ)ᴴ)) :
    ∃ (c : ℂ) (x : Matrix.unitaryGroup (Fin q) ℂ), ‖c‖ = 1 ∧
      A = c • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
        (x : Matrix (Fin q) (Fin q) ℂ)ᵀ) * Bᵀ := by
  let Xbar := (X : Matrix (Fin q) (Fin q) ℂ).map (starRingEnd ℂ)
  let Ybar := (Y : Matrix (Fin q) (Fin q) ℂ).map (starRingEnd ℂ)
  have htranspose (M : Matrix (Fin q) (Fin q) ℂ) : Mᴴᵀ = M.map (starRingEnd ℂ) := rfl
  have hdagger := congrArg Matrix.transpose hsecond
  simp only [Matrix.transpose_transpose, Matrix.transpose_mul,
    ← Matrix.kroneckerMap_transpose, htranspose] at hdagger
  have hD : A = (Ybar ⊗ₖ Xbar) * Bᵀ := hdagger
  have hcancel := hD
  rw [hfirst, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul] at hcancel
  have hAA : A * Aᴴ = 1 := hA
  have hK : (Ybar * (X : Matrix (Fin q) (Fin q) ℂ)) ⊗ₖ
      (Xbar * (Y : Matrix (Fin q) (Fin q) ℂ)) = 1 := by
    apply Matrix.mul_left_injective_of_inv A Aᴴ hAA
    simpa only [Matrix.one_mul] using hcancel.symm
  obtain ⟨c, _, hYX, _⟩ := Matrix.exists_eq_smul_one_of_kronecker_eq_one hK
  have hXX : (X : Matrix (Fin q) (Fin q) ℂ) *
      (X : Matrix (Fin q) (Fin q) ℂ)ᴴ = 1 :=
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr X.property).2
  have hY : Ybar = c • (X : Matrix (Fin q) (Fin q) ℂ)ᴴ := by
    calc
      Ybar = (Ybar * (X : Matrix (Fin q) (Fin q) ℂ)) *
          (X : Matrix (Fin q) (Fin q) ℂ)ᴴ := by
            rw [Matrix.mul_assoc, hXX, Matrix.mul_one]
      _ = c • (X : Matrix (Fin q) (Fin q) ℂ)ᴴ := by
        rw [hYX, Matrix.smul_mul, Matrix.one_mul]
  have hYunit : Ybar.IsUnitaryBetween :=
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr Y.property).map_star
  have hUnit : (Ybar * (X : Matrix (Fin q) (Fin q) ℂ)).IsUnitaryBetween :=
    hYunit.mul _ _ ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr X.property)
  have hGram : (c * star c) • (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
    have h := hUnit.1
    rw [hYX] at h
    simpa only [Matrix.IsIsometry, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul] using h
  let i : Fin q := ⟨0, NeZero.pos q⟩
  have hc : c * star c = 1 := by
    have h := congrArg (fun M : Matrix (Fin q) (Fin q) ℂ ↦ M i i) hGram
    simpa only [Matrix.smul_apply, Matrix.one_apply, ↓reduceIte,
      smul_eq_mul, mul_one] using h
  have hnorm : ‖c‖ = 1 := by
    have h := congrArg norm hc
    simp only [norm_mul, norm_star, norm_one] at h
    nlinarith [norm_nonneg c]
  let x := star X
  refine ⟨c, x, hnorm, ?_⟩
  rw [hD, hY, Matrix.smul_kronecker]
  rfl

/-- Pure supplied-gate algebra after the actual FT comparison. Keeping the
tensor records and source-rank definitions out of this conversion avoids
unfolding either canonical weights or tensor operations in matrix reindexing.
Source: CPSV17, `UUtransposetrick`, lines 1258–1288. -/
private theorem transposition_certificate_of_supplied_gate_gauges
    {d l r lT rT : ℕ}
    (u : Matrix (Fin l × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin l) ℂ)
    (uT : Matrix (Fin lT × Fin rT) (Fin d × Fin d) ℂ)
    (vT : Matrix (Fin d × Fin d) (Fin rT × Fin lT) ℂ)
    (hr : r = d) (hl : l = d) (hrSwap : rT = l) (hlSwap : lT = r)
    (hd : 0 < d)
    (huS : u.IsUnitaryBetween)
    (hTU : uT =
      Matrix.reindex
        (Equiv.prodCongr (finCongr hlSwap.symm)
          (finCongr hrSwap.symm))
        (Equiv.refl _) vᵀ)
    (hTV : vT =
      Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hrSwap.symm)
          (finCongr hlSwap.symm))
        uᵀ)
    (hGauges :
      ∃ (hrFT : rT = r)
        (hlFT : lT = l)
        (x : Matrix.unitaryGroup (Fin lT) ℂ)
        (y : Matrix.unitaryGroup (Fin rT) ℂ),
        uT =
          ((x : Matrix _ _ ℂ) ⊗ₖ (y : Matrix _ _ ℂ)) *
            Matrix.reindex
              (Equiv.prodCongr (finCongr hlFT.symm) (finCongr hrFT.symm))
              (Equiv.refl _) u ∧
        vT =
          Matrix.reindex (Equiv.refl _)
              (Equiv.prodCongr (finCongr hrFT.symm) (finCongr hlFT.symm))
              v *
            (star (y : Matrix _ _ ℂ) ⊗ₖ star (x : Matrix _ _ ℂ))) :
    ∃ (c : ℂ)
      (x : Matrix.unitaryGroup (Fin d) ℂ), ‖c‖ = 1 ∧
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          u =
        c • ((x : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d) (Fin d) ℂ)ᵀ) *
          (Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr) (finCongr hl)) v)ᵀ := by
  classical
  obtain ⟨hrFT, hlFT, X, Y, hu, hv⟩ := hGauges
  let L := finCongr hl
  let R := finCongr hr
  let LA := finCongr (hlSwap.trans hr)
  let RA := finCongr (hrSwap.trans hl)
  let A := Matrix.reindex (Equiv.prodCongr L R) (Equiv.refl _) u
  let B := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr R L) v
  let X' : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨Matrix.reindex LA LA (X : Matrix (Fin lT) (Fin lT) ℂ),
      Matrix.reindex_mem_unitaryGroup LA _ X.property⟩
  let Y' : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨Matrix.reindex RA RA (Y : Matrix (Fin rT) (Fin rT) ℂ),
      Matrix.reindex_mem_unitaryGroup RA _ Y.property⟩
  let erA := finCongr hrSwap.symm
  let elA := finCongr hlSwap.symm
  let erFT := finCongr hrFT.symm
  let elFT := finCongr hlFT.symm
  have hUA : Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)
      (Matrix.reindex (Equiv.prodCongr elA erA) (Equiv.refl _)
        vᵀ) = Bᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  have hUFT : Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)
      (Matrix.reindex (Equiv.prodCongr elFT erFT) (Equiv.refl _)
        u) = A := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  have hVA : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erA elA)
        uᵀ) = Aᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  have hVFT : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erFT elFT)
        v) = B := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  have hfirst : Bᵀ = ((X' : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      (Y' : Matrix (Fin d) (Fin d) ℂ)) * A := by
    calc
      Bᵀ = Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _) uT := by rw [hTU, hUA]
      _ = Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)
          (((X : Matrix (Fin lT) (Fin lT) ℂ) ⊗ₖ (Y : Matrix (Fin rT) (Fin rT) ℂ)) *
            Matrix.reindex (Equiv.prodCongr elFT erFT) (Equiv.refl _) u) :=
        congrArg (Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)) hu
      _ = (Matrix.reindex LA LA (X : Matrix (Fin lT) (Fin lT) ℂ) ⊗ₖ
            Matrix.reindex RA RA (Y : Matrix (Fin rT) (Fin rT) ℂ)) *
          Matrix.reindex (Equiv.prodCongr LA RA) (Equiv.refl _)
            (Matrix.reindex (Equiv.prodCongr elFT erFT) (Equiv.refl _) u) :=
        Matrix.reindex_kronecker_mul LA RA _ _ _
      _ = ((X' : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (Y' : Matrix (Fin d) (Fin d) ℂ)) * A := by
        rw [hUFT]
  have hsecond : Aᵀ = B * ((Y' : Matrix (Fin d) (Fin d) ℂ)ᴴ ⊗ₖ
      (X' : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
    calc
      Aᵀ = Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA) vT := by rw [hTV, hVA]
      _ = Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)
          (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erFT elFT) v *
            (star (Y : Matrix (Fin rT) (Fin rT) ℂ) ⊗ₖ
              star (X : Matrix (Fin lT) (Fin lT) ℂ))) :=
        congrArg (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)) hv
      _ = Matrix.reindex (Equiv.refl _) (Equiv.prodCongr RA LA)
            (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erFT elFT) v) *
          (Matrix.reindex RA RA (star (Y : Matrix (Fin rT) (Fin rT) ℂ)) ⊗ₖ
            Matrix.reindex LA LA (star (X : Matrix (Fin lT) (Fin lT) ℂ))) :=
        Matrix.reindex_mul_kronecker RA LA _ _ _
      _ = B * ((Y' : Matrix (Fin d) (Fin d) ℂ)ᴴ ⊗ₖ (X' : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
        rw [hVFT, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
          ← Matrix.conjTranspose_reindex, ← Matrix.conjTranspose_reindex]
  have hA : A.IsCoisometry := (huS.reindex _ (Equiv.prodCongr L R) (Equiv.refl _)).2
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨c, x, hc, hlocal⟩ := transpose_local_phase_of_gate_gauges A B hA X' Y' hfirst hsecond
  exact ⟨c, x, hc, hlocal⟩

/-- Gate comparison at derived square ranks, kept abstract in the supplied factor
record. Source: CPSV17, `UUtransposetrick`, lines 1258–1288. -/
private theorem source_transposition_certificate_of_gate_transport
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ)
    (hr : r[U] = d) (hl : ℓ[U] = d)
    (T : SourceFactors (MPOTensor.physicalTransposeTensor U) hU.physicalTransposeTensor.ρ)
    (hTU : SourceFactors.sourceU (MPOTensor.physicalTransposeTensor U) T =
      Matrix.reindex
        (Equiv.prodCongr (finCongr (source_ranks_physicalTransposeTensor U).2.symm)
          (finCongr (source_ranks_physicalTransposeTensor U).1.symm))
        (Equiv.refl _) (SourceFactors.sourceV U S)ᵀ)
    (hTV : SourceFactors.sourceV (MPOTensor.physicalTransposeTensor U) T =
      Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr (source_ranks_physicalTransposeTensor U).1.symm)
          (finCongr (source_ranks_physicalTransposeTensor U).2.symm))
        (SourceFactors.sourceU U S)ᵀ)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᵀ) :
    ∃ (c : ℂ)
      (x : Matrix.unitaryGroup (Fin d) ℂ), ‖c‖ = 1 ∧
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          (SourceFactors.sourceU U S) =
        c • ((x : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d) (Fin d) ℂ)ᵀ) *
          (Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr) (finCongr hl)) (SourceFactors.sourceV U S))ᵀ := by
  classical
  have hEq : ∀ N : ℕ, 1 < N → Even N →
      mpo U N = mpo (MPOTensor.physicalTransposeTensor U) N := by
    intro N hN heven
    rw [mpo_physicalTransposeTensor]
    exact hTR N hN heven
  have huS := hU.sourceFactors_sourceU_isUnitaryBetween hsimple S
  have huT := hU.physicalTransposeTensor.sourceFactors_sourceU_isUnitaryBetween
    (hU.isMPUSimple_physicalTransposeTensor hsimple) T
  have hGauges := hU.exists_supplied_source_gate_unitary_gauges_of_mpo_eq_even
    hU.physicalTransposeTensor S T huS huT hEq
  exact transposition_certificate_of_supplied_gate_gauges
    (SourceFactors.sourceU U S) (SourceFactors.sourceV U S)
    (SourceFactors.sourceU (MPOTensor.physicalTransposeTensor U) T)
    (SourceFactors.sourceV (MPOTensor.physicalTransposeTensor U) T)
    hr hl (source_ranks_physicalTransposeTensor U).1 (source_ranks_physicalTransposeTensor U).2
    (Nat.pos_of_ne_zero hU.neZero_phys.out) huS hTU hTV hGauges

/-- Use the actual transpose factors in the abstract comparison. Source:
CPSV17, `UUtransposetrick`, lines 1258–1288. -/
private theorem source_transposition_certificate_of_even_symmetry
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ)
    (hr : r[U] = d) (hl : ℓ[U] = d)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᵀ) :
    ∃ (c : ℂ)
      (x : Matrix.unitaryGroup (Fin d) ℂ), ‖c‖ = 1 ∧
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          (SourceFactors.sourceU U S) =
        c • ((x : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d) (Fin d) ℂ)ᵀ) *
          (Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr) (finCongr hl)) (SourceFactors.sourceV U S))ᵀ := by
  let T : SourceFactors (MPOTensor.physicalTransposeTensor U)
      hU.physicalTransposeTensor.ρ := SourceFactors.physicalTranspose hU hsimple S hr hl
  exact source_transposition_certificate_of_gate_transport hU hsimple S hr hl T
    (SourceFactors.sourceU_physicalTranspose hU hsimple S hr hl)
    (SourceFactors.sourceV_physicalTranspose hU hsimple S hr hl) hTR

/-- Actual even-chain transposition symmetry gives a literal local phase
certificate for the supplied normalized source factors. All gauges and
square-rank identifications are derived. Source: CPSV17,
`prop:local-char-transposition` and `UUtransposetrick`, lines 1258–1288. -/
theorem IsMPUCanonicalFormII.exists_source_transposition_phase_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᵀ) :
    ∃ (hr : r[U] = d) (hl : ℓ[U] = d) (c : ℂ)
      (x : Matrix.unitaryGroup (Fin d) ℂ), ‖c‖ = 1 ∧
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          (SourceFactors.sourceU U S) =
        c • ((x : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d) (Fin d) ℂ)ᵀ) *
          (Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr) (finCongr hl)) (SourceFactors.sourceV U S))ᵀ := by
  obtain ⟨hr, hl⟩ := hU.sourceRanks_eq_phys_of_even_mpo_eq_transpose hsimple hTR
  obtain ⟨c, x, hc, hlocal⟩ :=
    source_transposition_certificate_of_even_symmetry hU hsimple S hr hl hTR
  exact ⟨hr, hl, c, x, hc, hlocal⟩

/-- The actual chosen source standard form has the literal four-original-spin
transpose certificate under symmetry at even standard-form lengths. The
rank identifications and phase are derived from the actual periodic family.
Source: CPSV17, `UUtransposetrick`, lines 1258–1288. -/
theorem IsMPUCanonicalFormII.exists_local_transposition_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᵀ) :
    ∃ (hrU : r[U] = d) (hlU : ℓ[U] = d) (c : ℂ)
      (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hlU) (finCongr hrU))
        (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef)
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hrU) (finCongr hlU)) (sourceV U hU.ρ hU.ρ_posDef)
      ‖c‖ = 1 ∧ staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        c • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) * (staircaseMiddle v₀)ᵀ := by
  obtain ⟨hr, hl, c, x, hc, h⟩ :=
    hU.blockTwo.exists_source_transposition_phase_certificate
      (hU.isMPUSimple_blockTwo hsimple) (hU.twoSiteSourceFactors hsimple) hTR
  change Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
      (SourceFactors.sourceU (ρ := hU.ρ) (MPOTensor.blockTwo U)
        (hU.twoSiteSourceFactors hsimple)) =
    c • ((x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
      (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᵀ) *
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr (finCongr hr) (finCongr hl))
        (SourceFactors.sourceV (ρ := hU.ρ) (MPOTensor.blockTwo U)
          (hU.twoSiteSourceFactors hsimple)))ᵀ at h
  obtain ⟨hrB, hlB⟩ := hU.twoSite_sourceRanks hsimple
  have hrU : r[U] = d := mul_left_cancel₀ hU.neZero_phys.out (hrB.symm.trans hr)
  have hlU : ℓ[U] = d := mul_right_cancel₀ hU.neZero_phys.out (hlB.symm.trans hl)
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
      (Matrix.reindex p p B)ᵀ = Bᵀ := by
    rw [Matrix.transpose_reindex]
    change E.symm (E Bᵀ) = Bᵀ
    exact E.symm_apply_apply Bᵀ
  have hk : Matrix.reindexLinearEquiv ℂ ℂ p.symm p.symm
      ((x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
        (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᵀ) =
      (x₀ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
        (x₀ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ := by
    change Matrix.reindex (Equiv.prodCongr e.symm e.symm)
      (Equiv.prodCongr e.symm e.symm)
      ((x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) ⊗ₖ
        (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᵀ) = _
    dsimp only [x₀]
    rw [Matrix.transpose_reindex]
    exact (Matrix.kroneckerMap_reindex (fun a b : ℂ ↦ a * b)
      e.symm e.symm e.symm e.symm
      (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
      (x : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)ᵀ).symm
  rw [hA', hk, hB'] at h'
  refine ⟨hrU, hlU, c, x₀, hc, ?_⟩
  change A = c • ((x₀ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
    (x₀ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) * Bᵀ
  rw [Matrix.smul_mul]
  exact h'

/-- The local scalar can be written in the literal exponential-phase form of
CPSV17, `UUtransposetrick`, lines 1270–1276. No sign restriction is imposed. -/
theorem IsMPUCanonicalFormII.exists_source_transposition_exponential_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᵀ) :
    ∃ (hr : r[U] = d) (hl : ℓ[U] = d) (φ : ℝ)
      (x : Matrix.unitaryGroup (Fin d) ℂ),
      Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
          (SourceFactors.sourceU U S) =
        Complex.exp ((φ : ℂ) * Complex.I) •
          ((x : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (x : Matrix (Fin d) (Fin d) ℂ)ᵀ) *
          (Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr) (finCongr hl)) (SourceFactors.sourceV U S))ᵀ := by
  obtain ⟨hr, hl, c, x, hc, hlocal⟩ :=
    hU.exists_source_transposition_phase_certificate hsimple S hTR
  have hphase : Complex.exp ((Complex.arg c : ℂ) * Complex.I) = c := by
    simpa only [hc, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I c
  exact ⟨hr, hl, Complex.arg c, x, by simpa only [hphase] using hlocal⟩

/-- Literal exponential-phase form of the four-original-spin certificate for
the actual chosen standard form. Source: CPSV17, `UUtransposetrick`,
lines 1270–1276. The periodic hypothesis is only at even standard-form lengths. -/
theorem IsMPUCanonicalFormII.exists_local_transposition_exponential_certificate
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo U) N = (mpo (MPOTensor.blockTwo U) N)ᵀ) :
    ∃ (hrU : r[U] = d) (hlU : ℓ[U] = d) (φ : ℝ)
      (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hlU) (finCongr hrU))
        (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef)
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hrU) (finCongr hlU)) (sourceV U hU.ρ hU.ρ_posDef)
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        Complex.exp ((φ : ℂ) * Complex.I) •
          ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) * (staircaseMiddle v₀)ᵀ := by
  obtain ⟨hr, hl, c, x, hc, hlocal⟩ := hU.exists_local_transposition_certificate hsimple hTR
  have hphase : Complex.exp ((Complex.arg c : ℂ) * Complex.I) = c := by
    simpa only [hc, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I c
  exact ⟨hr, hl, Complex.arg c, x, by simpa only [hphase] using hlocal⟩

end MPOTensor
