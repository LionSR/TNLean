/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PolarUnitaryCorrectionKronecker
import QICLean.Algebra.MatrixReindexUnitary
import TNLean.PEPS.AreaLaw.Amplification.SupportedPolarCorrection

/-!
# A supported unitary polar correction

An operator `D` acting on a set `S` of sites has a unitary polar factor that acts on the
same set `S`. For all vectors `x, y`, this unitary satisfies the two-sided correction
estimate `‖U x - y‖ ≤ ‖D x - y‖ + ‖Dᴴ y - x‖`. No auxiliary system is adjoined, and no
invertibility or normalization of `D` is required.

## Main statements

* `QuantumCircuit.exists_supported_unitary_polar_correction`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `02-information.tex`, lines 565–595, equations
  `eq:info-reset-polar-errors` and `eq:info-reset-unitary`: the polar partial isometry of
  `D`, a square operator on the finite space of `S`, extends to a unitary on that same space
  and is tensored with the identity outside `S`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker

namespace QuantumCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- **A unitary polar factor on the same support.** Every operator `D` acting on a set `S` of
sites has a unitary `U`, also acting on `S`, with
`‖U x - y‖ ≤ ‖D x - y‖ + ‖Dᴴ y - x‖` for all vectors `x, y`. The unitary is the polar factor
of the local operator of `D`, tensored with the identity outside `S`; no dilation on an
additional system is used.
Source: `02-information.tex`, lines 580–595, equation `eq:info-reset-unitary`. -/
theorem exists_supported_unitary_polar_correction (S : Finset ι)
    {D : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hD : D ∈ supportedOperators q (S : Set ι)) :
    ∃ U : Matrix (ι → Fin q) (ι → Fin q) ℂ,
      U ∈ unitaryGroup (ι → Fin q) ℂ ∧ U ∈ supportedOperators q (S : Set ι) ∧
      ∀ x y : (ι → Fin q) → ℂ,
        ‖WithLp.toLp 2 (U *ᵥ x) - WithLp.toLp 2 y‖ ≤
          ‖WithLp.toLp 2 (D *ᵥ x) - WithLp.toLp 2 y‖ +
            ‖WithLp.toLp 2 (Dᴴ *ᵥ y) - WithLp.toLp 2 x‖ := by
  set e := FiniteProduct.splitEquiv (fun _ : ι => Fin q) S with he
  obtain ⟨D', hD'⟩ := TNLean.PEPS.EncodedFrame.exists_kronecker_one_of_mem_supportedOperators hD
  have hDe : D.submatrix e.symm e.symm =
      D' ⊗ₖ (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ) := hD'
  obtain ⟨U', hpolar, -, -⟩ := exists_unitary_polar_correction D'
  obtain ⟨hV, -, -, hcorr⟩ :=
    unitary_polar_correction_kronecker_one (m := ↥Sᶜ → Fin q) D' U' hpolar
  set V := (U' : Matrix (S → Fin q) (S → Fin q) ℂ) ⊗ₖ
    (1 : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ) with hVdef
  -- Transport of vectors to the coordinates `S × Sᶜ`.
  have hvec (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) (v : (ι → Fin q) → ℂ) :
      A.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) = (A *ᵥ v) ∘ e.symm := by
    rw [submatrix_mulVec_equiv, Equiv.symm_symm]
    congr 2
    ext x
    simp
  have hdist (f g : (ι → Fin q) → ℂ) :
      ‖WithLp.toLp 2 (f ∘ e.symm) - WithLp.toLp 2 (g ∘ e.symm)‖ =
        ‖WithLp.toLp 2 f - WithLp.toLp 2 g‖ := by
    rw [← WithLp.toLp_sub, ← WithLp.toLp_sub]
    exact EuclideanSpace.norm_toLp_comp_equiv e.symm (f - g)
  have hUe : (V.submatrix e e).submatrix e.symm e.symm = V := by simp
  refine ⟨V.submatrix e e, ?_, ?_, fun x y ↦ ?_⟩
  · simpa only [reindex_apply, Equiv.symm_symm] using
      reindex_mem_unitaryGroup e.symm _ hV
  · exact kronecker_one_submatrix_mem_supportedOperators S _
  · have h := hcorr (WithLp.toLp 2 (x ∘ e.symm)) (WithLp.toLp 2 (y ∘ e.symm))
    rw [toEuclideanCLM_toLp, toEuclideanCLM_toLp, toEuclideanCLM_toLp, ← hDe,
      conjTranspose_submatrix, hvec, hvec, ← hUe, hvec, hdist, hdist, hdist] at h
    exact h

end QuantumCircuit
