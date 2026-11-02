/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.EvenFamilyVirtualGauge
import TNLean.MPS.MPU.SourceFactorsScalar
import TNLean.MPS.MPU.ConjugationSourceFactors

/-!
# Supplied source gates from equality on even periodic chains

The unblocked virtual sign from even-family equality cancels in the actual
source gate, because that gate contracts two right factors. Thus the existing
normalized supplied-factor comparison gives the two literal source-gate
relations without assuming equality on odd chains or taking another block.

Source: arXiv:1703.09188, `FundamentalMPU`, lines 624–648, and `PropChiral`,
lines 1209–1252. **Scope restriction (reduced canonical presentation):** Both
MPU tensors carry reduced full-support canonical presentations; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. These are relations
between the actual supplied normalized factors, not assumed local witnesses.
-/

open scoped Matrix Kronecker

namespace MPOTensor

private theorem supplied_gate_gauges_of_eq_virtualSandwich
    {d D : ℕ} {U V : MPOTensor d D} (z : Matrix.unitaryGroup (Fin D) ℂ)
    (hV : V = virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ)))
    {ρ ρ' : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (T : SourceFactors V ρ')
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (huT : (SourceFactors.sourceU V T).IsUnitaryBetween) :
    ∃ (hr : r[V] = r[U]) (hl : ℓ[V] = ℓ[U])
      (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      SourceFactors.sourceU V T =
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm))
            (Equiv.refl _) (SourceFactors.sourceU U S) ∧
      SourceFactors.sourceV V T =
        Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr.symm) (finCongr hl.symm))
            (SourceFactors.sourceV U S) *
          (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := by
  subst V
  obtain ⟨W₁, W₂, hX₁, hY₁, hX₂, hY₂⟩ :=
    exists_source_factor_unitary_gauges_of_virtualSandwich U z S T huS huT
  obtain ⟨x, y, hu, hv⟩ := supplied_source_factor_gate_relations S T z _ _ W₁ W₂
    hX₁ hY₁ hX₂ hY₂
  exact ⟨(source_rank_virtual_unitary_sandwich U z).1,
    (source_rank_virtual_unitary_sandwich U z).2, x, y, hu, hv⟩

/-- Equality on even periodic chains expresses the signed target as an actual
unitary virtual sandwich of the original tensor, without blocking. Source:
CPSV17, the comparison in `PropChiral`, lines 1237–1252. -/
theorem IsMPUCanonicalFormII.eq_sign_virtualSandwich_of_mpo_eq_even
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → Even N → mpo U N = mpo V N) :
    ∃ (η : ℂ) (z : Matrix.unitaryGroup (Fin D) ℂ), (η = 1 ∨ η = -1) ∧
      η • V = virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ)) := by
  obtain ⟨_, η, z, hηsign, hz⟩ := hU.exists_unitary_virtual_sign_gauge_of_mpo_eq_even hV hEq
  have hηsq : η ^ 2 = 1 := sq_eq_one_iff.mpr hηsign
  have hz' : ∀ i j, V i j = η • ((z : Matrix (Fin D) (Fin D) ℂ) * U i j *
      (z : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
    simpa only [cast_eq] using hz
  refine ⟨η, z, hηsign, ?_⟩
  funext i j
  change η • V i j = _
  rw [hz' i j, smul_smul, ← pow_two, hηsq, one_smul]
  rfl

/-- Equality on even periodic chains preserves both original source ranks.
The possible scalar sign does not change either matrix rank. Source:
CPSV17, the zero-index observation preceding `PropChiral`, lines 1201–1213. -/
theorem IsMPUCanonicalFormII.source_ranks_eq_of_mpo_eq_even
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → Even N → mpo U N = mpo V N) :
    r[V] = r[U] ∧ ℓ[V] = ℓ[U] := by
  obtain ⟨η, z, hηsign, hP⟩ := hU.eq_sign_virtualSandwich_of_mpo_eq_even hV hEq
  have hη0 : η ≠ 0 := by rcases hηsign with rfl | rfl <;> norm_num
  have hrank := source_rank_virtual_unitary_sandwich U z
  rw [← hP] at hrank
  exact ⟨(source_ranks_smul V hη0).1.symm.trans hrank.1,
    (source_ranks_smul V hη0).2.symm.trans hrank.2⟩

/-- The actual supplied source gates have the usual unitary relations already
from equality on even periodic chains: the possible unblocked sign has square
one and disappears in their two-letter contraction. Source: CPSV17,
`FundamentalMPU`, lines 624–648, as used in `PropChiral`, lines 1237–1252. -/
theorem IsMPUCanonicalFormII.exists_supplied_source_gate_unitary_gauges_of_mpo_eq_even
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    {ρ ρ' : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (T : SourceFactors V ρ')
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (huT : (SourceFactors.sourceU V T).IsUnitaryBetween)
    (hEq : ∀ N : ℕ, 1 < N → Even N → mpo U N = mpo V N) :
    ∃ (hr : r[V] = r[U]) (hl : ℓ[V] = ℓ[U])
      (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      SourceFactors.sourceU V T =
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm))
            (Equiv.refl _) (SourceFactors.sourceU U S) ∧
      SourceFactors.sourceV V T =
        Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr.symm) (finCongr hl.symm))
            (SourceFactors.sourceV U S) *
          (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := by
  classical
  obtain ⟨η, z, hηsign, hP⟩ := hU.eq_sign_virtualSandwich_of_mpo_eq_even hV hEq
  have hηsq : η ^ 2 = 1 := sq_eq_one_iff.mpr hηsign
  have hη0 : η ≠ 0 := by rcases hηsign with rfl | rfl <;> norm_num
  let er := finCongr (source_ranks_smul V hη0).1
  let el := finCongr (source_ranks_smul V hη0).2
  have huScaled : (SourceFactors.sourceU (η • V) (T.smul η hη0)).IsUnitaryBetween := by
    rw [SourceFactors.sourceU_smul, hηsq, one_smul]
    exact huT.reindex _ _ (Equiv.refl _)
  obtain ⟨hrP, hlP, x, y, hu, hv⟩ :=
    supplied_gate_gauges_of_eq_virtualSandwich z hP S (T.smul η hη0) huS huScaled
  let hr : r[V] = r[U] := (source_ranks_smul V hη0).1.symm.trans hrP
  let hl : ℓ[V] = ℓ[U] := (source_ranks_smul V hη0).2.symm.trans hlP
  let x' : Matrix.unitaryGroup (Fin ℓ[V]) ℂ :=
    ⟨Matrix.reindex el el (x : Matrix (Fin ℓ[η • V]) (Fin ℓ[η • V]) ℂ),
      Matrix.reindex_mem_unitaryGroup _ _ x.property⟩
  let y' : Matrix.unitaryGroup (Fin r[V]) ℂ :=
    ⟨Matrix.reindex er er (y : Matrix (Fin r[η • V]) (Fin r[η • V]) ℂ),
      Matrix.reindex_mem_unitaryGroup _ _ y.property⟩
  have hcancelU : Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
      (SourceFactors.sourceU (η • V) (T.smul η hη0)) = SourceFactors.sourceU V T := by
    rw [SourceFactors.sourceU_smul, hηsq, one_smul]
    let E := Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr el er)
      (Equiv.refl (Fin d × Fin d))
    change E (E.symm (SourceFactors.sourceU V T)) = _
    exact E.apply_symm_apply _
  have hcancelV : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
      (SourceFactors.sourceV (η • V) (T.smul η hη0)) = SourceFactors.sourceV V T := by
    rw [SourceFactors.sourceV_smul]
    let E := Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl (Fin d × Fin d))
      (Equiv.prodCongr er el)
    change E (E.symm (SourceFactors.sourceV V T)) = _
    exact E.apply_symm_apply _
  have hrows : Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
      (Matrix.reindex (Equiv.prodCongr (finCongr hlP.symm) (finCongr hrP.symm))
        (Equiv.refl _) (SourceFactors.sourceU U S)) =
      Matrix.reindex (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm))
        (Equiv.refl _) (SourceFactors.sourceU U S) := by
    ext ⟨l, r⟩ ij
    rfl
  have hcols : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
      (Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hrP.symm) (finCongr hlP.symm))
        (SourceFactors.sourceV U S)) =
      Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hr.symm) (finCongr hl.symm))
        (SourceFactors.sourceV U S) := by
    ext ij ⟨r, l⟩
    rfl
  refine ⟨hr, hl, x', y', ?_, ?_⟩
  · have h := congrArg (Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)) hu
    rw [hcancelU, Matrix.reindex_kronecker_mul, hrows] at h
    exact h
  · have h := congrArg (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)) hv
    rw [hcancelV, Matrix.reindex_mul_kronecker, hcols] at h
    simpa only [x', y', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex] using h

end MPOTensor
