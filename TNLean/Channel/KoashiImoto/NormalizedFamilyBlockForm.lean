/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PositiveSemidefiniteNormalization
import TNLean.Algebra.TraceReindex
import TNLean.Channel.KoashiImoto.FamilyFixedPointBlockForm

/-!
# A normalized block form for a preserved family of states

For a finite family of density matrices with positive-definite common average, the common
fixed-point decomposition can be normalized into member-dependent probabilities and density
matrices.  The density matrix on the multiplicity factor remains common to the whole family.

This is the full-support specialization of HJPW, arXiv:quant-ph/0304007v2, Property 1
(lines 785--789).  The proof continues the fixed-point formula at lines 853--856 through
the normalized state decomposition at lines 857--858.  The action of preserving operations
on the common factors, beginning at line 860, is not included.

## Main declaration

* `Kraus.exists_commonInvariant_normalizedStateBlockForm`: a common direct-sum tensor
  decomposition with member-dependent probability weights and density matrices.

**Scope restriction (full support):** The common average is assumed positive definite on the
ambient space, in place of HJPW's reduction to the joint support (lines 761--763).  This is
documented in `docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker
open Matrix

namespace Kraus

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Normalized state-block form of a full-support invariant family.**

There is one direct-sum tensor decomposition in which every family member has the form
\[
  U^*\rho_xU=\bigoplus_j q_{j|x}\,\sigma_j\otimes\tau_{j|x}.
\]
The weights are nonnegative and sum to one, while both `σ j` and `τ x j` are density
matrices.  The factors are ordered oppositely from HJPW Property 1: `σ j` is the common
factor, corresponding to HJPW's `ω_j`.

This is the full-support specialization of HJPW, arXiv:quant-ph/0304007v2, Property 1
(lines 785--789), with its proof formula at lines 857--858.  At zero weight, `τ x j` is
chosen to be maximally mixed; HJPW does not specify this irrelevant choice.

**Scope restriction (full support):** `hρbar` replaces HJPW's joint-support reduction
(lines 761--763).  Documented in
`docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex`. -/
theorem exists_commonInvariant_normalizedStateBlockForm
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρpos : ∀ x, (ρ x).PosSemidef) (hρtrace : ∀ x, (ρ x).trace = 1)
    (hρbar : (commonAverage ρ).PosDef) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin D)
      (U : Mat) (σ : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ)
      (q : Kidx → Fin K → ℝ)
      (τ : Kidx → ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ j, 0 < d j) ∧ (∀ j, 0 < m j) ∧
        (∀ j, (σ j).PosSemidef) ∧ (∀ j, (σ j).trace = 1) ∧
        (∀ x j, 0 ≤ q x j) ∧ (∀ x, ∑ j, q x j = 1) ∧
        (∀ x j, (τ x j).PosSemidef) ∧ (∀ x j, (τ x j).trace = 1) ∧
        ∀ x, star U * ρ x * U =
          Matrix.reindex e e
            (Matrix.blockDiagonal' fun j ↦
              (q x j : ℂ) • (σ j ⊗ₖ τ x j)) := by
  classical
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, hσpos, hσtrace, hfamily⟩ :=
    exists_commonInvariant_fixedPointBlockForm hρbar
  choose X hXform using hfamily
  have hXpos : ∀ x j, (X x j).PosSemidef := by
    intro x j
    have hreindexed :
        (Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X x k)).PosSemidef := by
      rw [← hXform x]
      simpa only [star_eq_conjTranspose] using
        (hρpos x).conjTranspose_mul_mul_same U
    have hblockDiagonal :
        (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X x k).PosSemidef := by
      have hprincipal := hreindexed.submatrix e
      simpa only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
        Equiv.symm_comp_self, Matrix.submatrix_id_id] using hprincipal
    have hblock : (σ j ⊗ₖ X x j).PosSemidef := by
      have hprincipal := hblockDiagonal.submatrix (fun i ↦ ⟨j, i⟩)
      have heq :
          (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X x k).submatrix
              (fun i ↦ ⟨j, i⟩) (fun i ↦ ⟨j, i⟩) =
            σ j ⊗ₖ X x j := by
        ext i k
        exact Matrix.blockDiagonal'_apply_eq
          (fun r : Fin K ↦ σ r ⊗ₖ X x r) j i k
      rw [heq] at hprincipal
      exact hprincipal
    have hpartial := hblock.partialTraceLeft
    simpa only [Matrix.partialTraceLeft_kronecker, hσtrace, one_smul] using hpartial
  let q : Kidx → Fin K → ℝ := fun x j ↦ (X x j).trace.re
  let τ : ∀ x j, Matrix (Fin (d j)) (Fin (d j)) ℂ :=
    fun x j ↦ Matrix.normalizePosSemidef ⟨0, hd j⟩ (X x j)
  have hqnonneg : ∀ x j, 0 ≤ q x j := by
    intro x j
    exact (Complex.nonneg_iff.mp (hXpos x j).trace_nonneg).1
  have hqsum : ∀ x, ∑ j, q x j = 1 := by
    intro x
    have hUright : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have htraceX : ∑ j, (X x j).trace = 1 := by
      have htrace := congrArg Matrix.trace (hXform x)
      rw [Matrix.trace_mul_cycle (star U) (ρ x) U, hUright, Matrix.one_mul,
        hρtrace x, Matrix.trace_reindex, Matrix.trace_blockDiagonal'] at htrace
      simpa only [Matrix.trace_kronecker, hσtrace, one_mul] using htrace.symm
    change ∑ j, (X x j).trace.re = 1
    calc
      ∑ j, (X x j).trace.re =
          Complex.reAddGroupHom (∑ j, (X x j).trace) :=
        (map_sum Complex.reAddGroupHom (fun j ↦ (X x j).trace) Finset.univ).symm
      _ = 1 := by rw [htraceX]; rfl
  have hτpos : ∀ x j, (τ x j).PosSemidef := by
    intro x j
    exact Matrix.normalizePosSemidef_posSemidef ⟨0, hd j⟩ (hXpos x j)
  have hτtrace : ∀ x j, (τ x j).trace = 1 := by
    intro x j
    exact Matrix.normalizePosSemidef_trace ⟨0, hd j⟩ (hXpos x j)
  refine ⟨K, d, m, e, U, σ, q, τ, hU, hd, hm, hσpos, hσtrace,
    hqnonneg, hqsum, hτpos, hτtrace, ?_⟩
  intro x
  rw [hXform x]
  apply congrArg (Matrix.reindex e e)
  congr 1
  funext j
  calc
    σ j ⊗ₖ X x j =
        σ j ⊗ₖ ((q x j : ℂ) • τ x j) := by
      rw [Matrix.trace_re_smul_normalizePosSemidef ⟨0, hd j⟩ (hXpos x j)]
    _ = (q x j : ℂ) • (σ j ⊗ₖ τ x j) := Matrix.kronecker_smul _ _ _

end Kraus
