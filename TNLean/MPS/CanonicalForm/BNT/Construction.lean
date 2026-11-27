/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BlockFamily
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapInjective
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapNT
import TNLean.MPS.Transfer.Spectrum.GaugePhase
import TNLean.MPS.CanonicalForm.BNT.Separation
import TNLean.MPS.CanonicalForm.BNT.Basic

/-!
# Basis of normal tensors from separated block hypotheses

Separated blockwise hypotheses pass from canonical-form and
normal-canonical-form hypotheses to the basis-of-normal-tensors formulation.
The source BNT expansion in arXiv:1606.00608, Section II keeps repeated copies
inside a sector with coefficients `μ_{j,q}` and multiplicities `M_j`; that
paper-faithful sector structure is represented by `IsBNTCanonicalForm` in the
fundamental-theorem files. The results here are auxiliary tools for already
separated finite block families.

## Main results

1. **`BlocksNotGaugePhaseEquiv`**: the separation condition asserting that distinct
   equal-dimension blocks are not gauge-phase equivalent.

2. **`cross_overlap_tendsto_zero_of_separated_bnt_data`**: separated injective
   left-canonical blocks have decaying cross-overlaps. The proof combines:
   - Dimension-mismatch case: `mpvOverlap_tendsto_zero_of_dim_ne`
   - Same-dimension case: `mpvOverlap_tendsto_zero` (using `blocks_not_equiv` to supply
     `¬GaugePhaseEquiv`)

3. **`exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal`**: asymptotically
   orthonormal overlaps give eventual linear independence of the matrix product vectors.

4. **`IsNormalCanonicalFormBNT`**: normal-canonical separated hypotheses retained for
   the primitive-transfer-map route. That its blocks form a basis of normal tensors of their
   weighted direct sum is `IsNormalCanonicalFormBNT.isCPSVBasisOfNormalTensors` in
   `TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge`.

## Design note on coefficients

In the full paper (arXiv:1606.00608, eq. decBSV), the decomposition into a basis of normal
tensors uses summed coefficients `c_j(N) = Σ_{q in group j} μ_{j,q}^N`.
The results below concern already separated one-representative block families
and do not perform the raw coefficient comparison for the two-layer BNT
decomposition. That comparison is carried out for sector decompositions, where
the sums `Σ_q μ_{j,q}^N` and their multiplicities remain visible.
-/

open MPTensor

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-! ### `IsNormalCanonicalFormBNT` hypotheses -/

/-- Normal canonical form with BNT separation: extends `IsNormalCanonicalForm`
with the requirement that distinct blocks are not gauge-phase equivalent, so the
block family is a basis of normal tensors. The block weight moduli are
non-increasing (inherited from `IsNormalCanonicalForm`); equal-modulus blocks are
allowed. Grouping into a basis of normal tensors is governed by gauge-phase
equivalence of the block tensors, not by distinctness of weight moduli.

**Scope restriction (basis of representatives).** The `blocks_not_equiv` field
keeps one representative per gauge-phase class, so this surface still suppresses
the repeated equal-class copies of the full arXiv:1606.00608 BNT decomposition.
The raw multiplicity data (weights `μ_{j,q}` with multiplicities, contributing the
power sum `c_N^{(j)} = ∑_q μ_{j,q}^N`) is carried instead by `SectorDecomposition`
and the SectorBNT comparison theorems; see
`docs/paper-gaps/cpsv16_ft_one_copy_scope_restriction.tex`.

`IsNormalCanonicalFormBNT` uses the spectral/primitive-transfer-map version of normality
(`IsNormalCanonicalForm`): irreducible, primitive, left-canonical blocks, hence normal
tensors. -/
structure IsNormalCanonicalFormBNT {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop extends
    IsNormalCanonicalForm μ A where
  /-- Distinct blocks are not gauge-phase equivalent (BNT separation). -/
  blocks_not_equiv : ∀ j k : Fin r, j ≠ k →
    ∀ (h : dim j = dim k),
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)

namespace IsNormalCanonicalFormBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Rebuild `IsNormalCanonicalFormBNT` from the separated blockwise hypotheses plus
the BNT separation assumption. -/
theorem ofSeparatedData
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin (dim k)) (A k)))
    (hμ : HasOrderedNonzeroWeights μ)
    (hDim : ∀ k, 0 < dim k)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    IsNormalCanonicalFormBNT μ A where
  toIsNormalCanonicalForm :=
    IsNormalCanonicalForm.ofSeparatedData hIrr hLeft hPrim hμ hDim
  blocks_not_equiv := hBlocks

end IsNormalCanonicalFormBNT

/-- Distinct same-dimension blocks in a separated irreducible trace-preserving
family are not proportional at arbitrarily large chain lengths. -/
theorem exists_ge_not_forall_mpv_eq_mul_of_blocksNotGaugePhaseEquiv_of_irreducible_TP
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hOverlap : ∀ k, Filter.Tendsto (fun N => mpvOverlap (α := Fin d) (A k) (A k) N)
      Filter.atTop (nhds (1 : ℂ)))
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k) (Nmin : ℕ) :
    ∃ N : ℕ, Nmin ≤ N ∧
      ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin d,
        mpv (cast (congr_arg (MPSTensor d) hdim) (A j)) σ = c * mpv (A k) σ := by
  have hA_self_cast :
      Tendsto
        (fun N =>
          mpvOverlap (α := Fin d) (cast (congr_arg (MPSTensor d) hdim) (A j))
            (cast (congr_arg (MPSTensor d) hdim) (A j)) N)
        atTop (nhds (1 : ℂ)) := by
    refine (hOverlap j).congr ?_
    intro N
    unfold mpvOverlap
    apply Finset.sum_congr rfl
    intro σ _
    rw [mpv_cast_dim hdim (A j) N σ]
  exact exists_ge_not_forall_mpv_eq_mul_of_not_gaugePhaseEquiv_of_irreducible_TP
    (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k)
    ((isIrreducibleFamily_cast_dim hdim (A j)).mpr (hIrr j))
    (hIrr k)
    ((leftCanonical_cast_dim hdim (A j)).mpr (hLeft j))
    (hLeft k)
    hA_self_cast (hOverlap k)
    (hBlocks j k hjk hdim) Nmin

/-- **Existential BNT linear independence from asymptotic orthonormal overlaps.**

If the self-overlaps of a finite block family tend to `1` and the cross-overlaps
of distinct blocks tend to `0`, then the MPV states are linearly independent for
every sufficiently large system size.  This is the threshold form of
`eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal`. -/
lemma exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hSelf : ∀ j,
      Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hOff : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (α := Fin d) (A i) (A j) N) atTop (nhds (0 : ℂ))) :
    ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin r => mpvState (d := d) (A j) N) := by
  have hOrtho := eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal A hSelf hOff
  rw [Filter.Eventually] at hOrtho
  obtain ⟨N0, hN0⟩ := Filter.mem_atTop_sets.mp hOrtho
  exact ⟨N0, fun N hN => hN0 N (le_of_lt hN)⟩

/-! ### Cross-overlap decay from separated BNT hypotheses -/

section SeparatedBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Separated-hypotheses version of BNT cross-overlap decay.

Only injectivity, left-canonical normalization, and the BNT non-equivalence assumption are used. -/
theorem cross_overlap_tendsto_zero_of_separated_bnt_data
    [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : ∀ k, Kraus.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      (hdim := hdim) (A := A j) (B := A k)
      (hA_irr := irreducibleTensor_of_injective (A j) (hInj j))
      (hB_irr := irreducibleTensor_of_injective (A k) (hInj k))
      (hA_norm := hLeft j)
      (hB_norm := hLeft k)
      (hNot := hBlocks j k hjk hdim)
  · exact mpvOverlap_tendsto_zero_of_dim_ne (A j) (A k)
      (hInj j)
      (hInj k)
      (hLeft j)
      (hLeft k)
      hdim

end SeparatedBNT

/-! ### Cross-overlap decay from separated normal BNT hypotheses -/

section SeparatedNormalBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Separated-hypotheses version of normal BNT cross-overlap decay.

Only irreducibility, left-canonical normalization, and the BNT non-equivalence
assumption are used. -/
theorem cross_overlap_tendsto_zero_of_separated_normal_bnt_data
    [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (α := Fin d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      (hdim := hdim) (A := A j) (B := A k)
      (hA_irr := hIrr j)
      (hB_irr := hIrr k)
      (hA_norm := hLeft j)
      (hB_norm := hLeft k)
      (hNot := hBlocks j k hjk hdim)
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP (A j) (A k)
      (hIrr j)
      (hIrr k)
      (hLeft j)
      (hLeft k)
      hdim

end SeparatedNormalBNT

end MPSTensor
