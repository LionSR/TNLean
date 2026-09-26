/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockDiagonalNormalization
import TNLean.MPS.MPDO.SourceBNTBlocking

/-!
# Normalization preserving simultaneous block injectivity

Independent nonzero rescalings and virtual gauges preserve simultaneous
block injectivity at the same word length. Primitive normalization therefore
retains the length used in the block-injective intersection and closure
arguments of CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129.
-/

open scoped BigOperators ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Independent nonzero rescalings preserve simultaneous injectivity at each
fixed word length. This is the scalar part of the normalization implicit in
CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem wordTupleSpanTop_of_family_smul
    (A : (j : Fin r) → MPSTensor d (dim j)) (ζ : Fin r → ℂ)
    (hζ : ∀ j, ζ j ≠ 0) {S : ℕ} (hSpan : WordTupleSpanTop A S) :
    WordTupleSpanTop (fun j ↦ ζ j • A j) S := by
  classical
  unfold WordTupleSpanTop at hSpan ⊢
  refine top_unique fun M _ ↦ ?_
  have hM : (fun j ↦ ((ζ j) ^ S)⁻¹ • M j) ∈
      Submodule.span ℂ (Set.range (wordTuple A S)) := by
    rw [hSpan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hM
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨c, ?_⟩
  funext j
  have hcj : (∑ w, c w • Kraus.evalWord (A j) (List.ofFn w)) =
      ((ζ j) ^ S)⁻¹ • M j := by
    simpa [wordTuple, Fintype.linearCombination_apply] using congrFun hc j
  have hword (w : Fin S → Fin d) :
      Kraus.evalWord (ζ j • A j) (List.ofFn w) =
        (ζ j) ^ S • Kraus.evalWord (A j) (List.ofFn w) := by
    have h := Kraus.evalWord_smul (ζ j) (A j) (List.ofFn w)
    rw [List.length_ofFn] at h
    exact h
  have hscaled := congrArg (fun X ↦ (ζ j) ^ S • X) hcj
  simpa only [Finset.sum_apply, Pi.smul_apply, wordTuple, hword,
    List.length_ofFn, Finset.smul_sum, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero S (hζ j)), one_smul, mul_comm] using hscaled

/-- Primitive normalization preserves a supplied simultaneous injectivity
length, every block ground space, and the span of the periodic component
vectors. No inequivalence or normalization hypothesis is required on the
original family. Source: CPGSV21, arXiv:2011.12127, Section IV.C,
block-injective canonical form and closure, lines 2114--2129. -/
theorem exists_isPrimitiveMPS_family_of_wordTupleSpanTop
    [∀ j, NeZero (dim j)] (A : (j : Fin r) → MPSTensor d (dim j))
    {S : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) :
    ∃ (B : (j : Fin r) → MPSTensor d (dim j))
      (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      (∀ j, IsPrimitiveMPS (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
      WordTupleSpanTop B S ∧
      (∀ j L, groundSpace (A j) L = groundSpace (B j) L) ∧
      (∀ N, bntMPSVectorSpan A N = bntMPSVectorSpan B N) := by
  classical
  choose B ζ ρ hζ hGauge hmpv hP hρ hGS _hPI _hCGS using
    fun j ↦ exists_isPrimitiveMPS_gauge_of_isNormal
      ⟨S, hS, isNBlkInjective_of_wordTupleSpanTop A hSpan j⟩
  refine ⟨B, ρ, hP, hρ,
    wordTupleSpanTop_of_family_gaugeEquiv
      (wordTupleSpanTop_of_family_smul A ζ hζ hSpan) hGauge, hGS, ?_⟩
  intro N
  rw [← iSup_mpvSubmodule_eq_bntMPSVectorSpan A N,
    ← iSup_mpvSubmodule_eq_bntMPSVectorSpan B N]
  apply iSup_congr
  intro j
  have hvec : (mpv (B j) : NSiteSpace d N) = (ζ j) ^ N • mpv (A j) :=
    funext (hmpv j N)
  simp only [mpvSubmodule, hvec,
    Submodule.span_singleton_smul_eq (pow_ne_zero N (hζ j)).isUnit]

/-- Primitive normalization preserves the supplied simultaneous injectivity
length and both sides of the periodic parent ground-space identity.
Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem exists_isPrimitiveMPS_family_parentHamiltonian_eq_of_wordTupleSpanTop
    [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) :
    ∃ (B : (j : Fin r) → MPSTensor d (dim j))
      (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      (∀ j, IsPrimitiveMPS (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
      WordTupleSpanTop B S ∧
      (∀ L N, parentHamiltonian (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        parentHamiltonian (toTensorFromBlocks (d := d) (μ := μ) B) L N) ∧
      (∀ N, bntMPSVectorSpan A N = bntMPSVectorSpan B N) := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, hBNT⟩ :=
    exists_isPrimitiveMPS_family_of_wordTupleSpanTop A hS hSpan
  refine ⟨B, ρ, hP, hρ, hSpanB, ?_, hBNT⟩
  intro L N
  exact parentHamiltonian_eq_of_groundSpace_eq
    (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq
      μ μ A B hμ hμ (fun j ↦ hGS j L)) N

end MPSTensor
