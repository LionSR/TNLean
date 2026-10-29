/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ConjugationSourceFactors
import TNLean.MPS.MPU.TimeReversalSign

/-!
# Independence of the time-reversal sign from supplied source representatives

The supplied-factor Fundamental Theorem derives the two gate gauges from
equality of the actual finite-chain operators. In zero-index coordinates,
the canonical rank identifications carry these gauges to the physical
coordinate space. The existing trace-gauge theorem then gives equality of
the normalized trace signs. No gauge-existence hypothesis is supplied.

**Scope restriction (reduced canonical representatives):** Both actual
tensors have canonical-form-II presentations in the same ambient bond
dimension. Their source ranks equal the physical dimension, so their gates
are written in the zero-index coordinates of the time-reversal trace.
See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

Source: arXiv:1703.09188, `prop:sigma-well-defined`, lines 1613–1631,
using `FundamentalMPU`, lines 624–648.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- The trace sign of the supplied source factors, in the canonical
zero-index coordinates. Source: arXiv:1703.09188,
`eq:sigma-from-trace`, lines 1595–1603. -/
noncomputable def SourceFactors.timeReversalSign
    {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (hr : r[U] = d) (hl : ℓ[U] = d) : ℂ :=
  MPOTensor.timeReversalSign
    (Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr)) (Equiv.refl _)
      (SourceFactors.sourceU U S))
    (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr (finCongr hr) (finCongr hl))
      (SourceFactors.sourceV U S))

/-- Two actual supplied canonical representatives of the same finite-chain
MPU have the same normalized time-reversal trace sign. The Fundamental
Theorem supplies the gauges; their existence is not a premise. Source:
arXiv:1703.09188, `prop:sigma-well-defined`, lines 1613–1627. -/
theorem IsMPUCanonicalFormII.source_timeReversalSign_eq_of_mpo_eq
    {U V : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    {ρ ρ' : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (T : SourceFactors V ρ')
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (huT : (SourceFactors.sourceU V T).IsUnitaryBetween)
    (hrU : r[U] = d) (hlU : ℓ[U] = d) (hrV : r[V] = d) (hlV : ℓ[V] = d)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    S.timeReversalSign hrU hlU = T.timeReversalSign hrV hlV := by
  classical
  obtain ⟨hr, hl, x, y, hu, hv⟩ :=
    hU.exists_supplied_source_gate_unitary_gauges_of_mpo_eq hV S T huS huT hEq
  let elU := finCongr hlU
  let erU := finCongr hrU
  let elV := finCongr hlV
  let erV := finCongr hrV
  let uU := Matrix.reindex (Equiv.prodCongr elU erU) (Equiv.refl _) (SourceFactors.sourceU U S)
  let vU := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erU elU) (SourceFactors.sourceV U S)
  let uV := Matrix.reindex (Equiv.prodCongr elV erV) (Equiv.refl _) (SourceFactors.sourceU V T)
  let vV := Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erV elV) (SourceFactors.sourceV V T)
  let x' : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨Matrix.reindex elV elV x, Matrix.reindex_mem_unitaryGroup _ _ x.property⟩
  let y' : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨Matrix.reindex erV erV y, Matrix.reindex_mem_unitaryGroup _ _ y.property⟩
  have hu' : uV = ((x' : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ y') * uU := by
    have h := congrArg (Matrix.reindex (Equiv.prodCongr elV erV) (Equiv.refl _)) hu
    change uV = Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr elV erV) (Equiv.refl _)
      (((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ y) *
        Matrix.reindex (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm))
          (Equiv.refl _) (SourceFactors.sourceU U S)) at h
    rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.prodCongr elV erV)
      (Equiv.prodCongr elV erV) (Equiv.refl _)] at h
    have hcoords : Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr elV erV)
        (Equiv.refl _)
        (Matrix.reindex (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm))
          (Equiv.refl _) (SourceFactors.sourceU U S)) = uU := by
      ext i j
      change SourceFactors.sourceU U S
          ((finCongr hl.symm).symm (elV.symm i.1),
            (finCongr hr.symm).symm (erV.symm i.2)) j =
        SourceFactors.sourceU U S (elU.symm i.1, erU.symm i.2) j
      congr 1 <;> apply Prod.ext <;> apply Fin.ext <;> rfl
    rw [hcoords] at h
    have hxy : Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr elV erV)
        (Equiv.prodCongr elV erV)
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ y) =
        ((x' : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ y') :=
      (Matrix.kroneckerMap_reindex _ elV elV erV erV x y).symm
    rwa [hxy] at h
  have hv' : vV = vU * ((y' : Matrix (Fin d) (Fin d) ℂ)ᴴ ⊗ₖ
      (x' : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
    have h := congrArg (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr erV elV)) hv
    change vV = Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.prodCongr erV elV)
      (Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr hr.symm) (finCongr hl.symm)) (SourceFactors.sourceV U S) *
        ((y : Matrix (Fin r[V]) (Fin r[V]) ℂ)ᴴ ⊗ₖ
          (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)ᴴ)) at h
    rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _)
      (Equiv.prodCongr erV elV) (Equiv.prodCongr erV elV)] at h
    have hcoords : Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _)
        (Equiv.prodCongr erV elV)
        (Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr hr.symm) (finCongr hl.symm))
          (SourceFactors.sourceV U S)) = vU := by
      ext i j
      change SourceFactors.sourceV U S i
          ((finCongr hr.symm).symm (erV.symm j.1),
            (finCongr hl.symm).symm (elV.symm j.2)) =
        SourceFactors.sourceV U S i (erU.symm j.1, elU.symm j.2)
      congr 1 <;> apply Prod.ext <;> apply Fin.ext <;> rfl
    rw [hcoords] at h
    have hxy : Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr erV elV)
        (Equiv.prodCongr erV elV)
        ((y : Matrix (Fin r[V]) (Fin r[V]) ℂ)ᴴ ⊗ₖ
          (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)ᴴ) =
        ((y' : Matrix (Fin d) (Fin d) ℂ)ᴴ ⊗ₖ (x' : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
      simp only [x', y', Matrix.conjTranspose_reindex]
      exact (Matrix.kroneckerMap_reindex _ erV erV elV elV
        (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)ᴴ
        (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)ᴴ).symm
    rwa [hxy] at h
  change MPOTensor.timeReversalSign uU vU = MPOTensor.timeReversalSign uV vV
  rw [hu', hv', MPOTensor.timeReversalSign, MPOTensor.timeReversalSign]
  exact congrArg (fun z : ℂ ↦ ((d * d : ℕ) : ℂ)⁻¹ * z)
    (timeReversalTrace_gauge uU vU x' y' x'.property y'.property).symm

end MPOTensor
