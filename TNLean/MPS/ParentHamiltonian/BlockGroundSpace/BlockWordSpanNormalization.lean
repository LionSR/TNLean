/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockDiagonalNormalization
import TNLean.MPS.CanonicalForm.BlockSeparation.SimultaneousBlocking
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BoundaryMatrix.BlockIntersectionBoundaryDecomposition
import TNLean.MPS.Tensor.GroundSpace.ChainGroundSpace
import TNLean.MPS.Tensor.BondReindex
import TNLean.MPS.Transfer.Spectrum.GaugePhase

/-!
# Normalization preserving simultaneous block injectivity

Independent nonzero rescalings and virtual gauges preserve simultaneous
block injectivity at the same word length. Primitive normalization therefore
retains the length used in the block-injective intersection and closure
arguments of CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129.

It also contains the following results.

* `MPSTensor.not_gaugePhaseEquiv_of_wordTupleSpanTop`: separation of simultaneously injective
  blocks.
-/

open MPTensor

section BlockWordSpanNormalization

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
theorem exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop
    [∀ j, NeZero (dim j)] (A : (j : Fin r) → MPSTensor d (dim j))
    {S : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) :
    ∃ (B : (j : Fin r) → MPSTensor d (dim j))
      (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      (∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
      WordTupleSpanTop B S ∧
      (∀ j L, groundSpace (A j) L = groundSpace (B j) L) ∧
      (∀ N, bntMPSVectorSpan A N = bntMPSVectorSpan B N) := by
  classical
  choose B ζ ρ hζ hGauge hmpv hP hρ hGS _hPI _hCGS using
    fun j ↦ exists_hasComplementaryFixedPointGap_gauge_of_isNormal
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
theorem exists_hasComplementaryFixedPointGap_family_parentHamiltonian_eq_of_wordTupleSpanTop
    [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) :
    ∃ (B : (j : Fin r) → MPSTensor d (dim j))
      (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      (∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
      WordTupleSpanTop B S ∧
      (∀ L N, parentHamiltonian (toTensorFromBlocks (α := Fin d) (μ := μ) A) L N =
        parentHamiltonian (toTensorFromBlocks (α := Fin d) (μ := μ) B) L N) ∧
      (∀ N, bntMPSVectorSpan A N = bntMPSVectorSpan B N) := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, hBNT⟩ :=
    exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop A hS hSpan
  refine ⟨B, ρ, hP, hρ, hSpanB, ?_, hBNT⟩
  intro L N
  exact parentHamiltonian_eq_of_groundSpace_eq
    (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq
      μ μ A B hμ hμ (fun j ↦ hGS j L)) N

end MPSTensor

end BlockWordSpanNormalization

section BlockWordSpanSeparation

/-!
## Separation of simultaneously injective blocks

Simultaneous spanning of the product matrix algebra excludes gauge-phase
equivalence between distinct blocks. This supplies the separation condition
from the block-injectivity hypothesis of Cirac--Perez-Garcia--Schuch--Verstraete
2021, Section IV.C, arXiv:2011.12127, lines 2114--2129.
-/

namespace MPSTensor

/-- Distinct blocks whose word tuples span the product algebra cannot be
gauge-phase equivalent. Their periodic vectors belong to disjoint local ground
spaces and are nonzero because the boundary maps are injective.

Source: arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem not_gaugePhaseEquiv_of_wordTupleSpanTop
    {d r S : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]
    (A : (j : Fin r) → MPSTensor d (dim j)) (hSpan : WordTupleSpanTop A S)
    (i j : Fin r) (hij : i ≠ j) (h : dim j = dim i) :
    ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) (A j)) (A i) := by
  rintro ⟨X, ζ, hζ, hX⟩
  have hvec : (mpv (A i) : NSiteSpace d S) = ζ ^ S • mpv (A j) := by
    ext σ
    simpa only [Pi.smul_apply, smul_eq_mul, mpv_cast_dim h (A j) S σ] using
      mpv_eq_pow_mul_of_gaugePhase _ _ X ζ hX S σ
  have hzero : (mpv (A i) : NSiteSpace d S) = 0 :=
    (Submodule.disjoint_def.mp
      ((groundSpace_iSupIndep_of_wordTupleSpanTop A hSpan).pairwiseDisjoint hij)) _
      (mpv_mem_groundSpace (A i) S)
      (hvec ▸ (groundSpace (A j) S).smul_mem (ζ ^ S)
        (mpv_mem_groundSpace (A j) S))
  exact one_ne_zero (groundSpaceMap_injective_of_isNBlkInjective
    (isNBlkInjective_of_wordTupleSpanTop A hSpan i)
    (by simpa only [← mpv_eq_groundSpaceMap_one, map_zero] using hzero))

end MPSTensor

end BlockWordSpanSeparation
