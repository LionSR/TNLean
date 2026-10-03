/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AffineIntervalIsometry
import QICLean.Algebra.TraceReindex

/-!
# Physical reindexing of prefix Gram hulls

Regrouping physical coordinates by output and input bijections reindexes
every input density matrix. Positivity and trace are preserved, and the
resulting virtual prefix Gram is unchanged. The physical Gram set and its
real affine hull therefore depend only on the prefix operator, rather than
the chosen physical configuration indexing.

Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace MPUCircuit

variable {o i o' i' m : Type*}
  [Fintype o] [Fintype i] [Fintype o'] [Fintype i']

/-- Bijective changes of physical output and input coordinates preserve
the prefix Gram when the input density is reindexed by the same bijection.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prefixInputGram_physical_reindex
    (F : o → i → Matrix Unit m ℂ) (eo : o ≃ o') (ei : i ≃ i')
    (ρ : Matrix i i ℂ) :
    prefixInputGram (fun a b ↦ F (eo.symm a) (ei.symm b))
      (Matrix.reindex ei ei ρ) = prefixInputGram F ρ := by
  have h := Fintype.sum_equiv (eo.symm.prodCongr (ei.symm.prodCongr ei.symm))
    (fun x : o' × (i' × i') ↦ (Matrix.reindex ei ei ρ) x.2.2 x.2.1 •
      ((F (eo.symm x.1) (ei.symm x.2.1))ᴴ * (1 : Matrix Unit Unit ℂ) *
        F (eo.symm x.1) (ei.symm x.2.2)))
    (fun x : o × (i × i) ↦ ρ x.2.2 x.2.1 •
      ((F x.1 x.2.1)ᴴ * (1 : Matrix Unit Unit ℂ) * F x.1 x.2.2))
    (by intro x; rfl)
  simpa only [Fintype.sum_prod_type, prefixInputGram, intervalGramTransfer] using h

/-- Bijective changes of physical output and input coordinates preserve
the entire set of physical prefix Grams, including arbitrary entangled input
densities on the prefix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem densityPrefixGrams_physical_reindex
    (F : o → i → Matrix Unit m ℂ) (eo : o ≃ o') (ei : i ≃ i') :
    densityPrefixGrams (fun a b ↦ F (eo.symm a) (ei.symm b)) = densityPrefixGrams F := by
  ext P
  constructor
  · rintro ⟨ρ, hρ, ht, hP⟩
    refine ⟨Matrix.reindex ei.symm ei.symm ρ, hρ.submatrix ei, ?_, ?_⟩
    · rw [Matrix.trace_reindex, ht]
    · have h := prefixInputGram_physical_reindex F eo ei
        (Matrix.reindex ei.symm ei.symm ρ)
      have hρeq : Matrix.reindex ei ei (Matrix.reindex ei.symm ei.symm ρ) = ρ := by
        ext a b
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          Equiv.apply_symm_apply]
      rw [hρeq] at h
      exact h.symm.trans hP
  · rintro ⟨ρ, hρ, ht, hP⟩
    refine ⟨Matrix.reindex ei ei ρ, hρ.submatrix ei.symm, ?_, ?_⟩
    · rw [Matrix.trace_reindex, ht]
    · exact (prefixInputGram_physical_reindex F eo ei ρ).trans hP

/-- Bijective changes of physical output and input coordinates preserve
the entire real affine hull of physical prefix Grams.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prefixGramAffineHull_physical_reindex
    (F : o → i → Matrix Unit m ℂ) (eo : o ≃ o') (ei : i ≃ i') :
    prefixGramAffineHull (fun a b ↦ F (eo.symm a) (ei.symm b)) = prefixGramAffineHull F := by
  rw [prefixGramAffineHull, densityPrefixGrams_physical_reindex]
  rfl

end MPUCircuit
