import TNLean.PiAlgebra.CanonicalFormSep
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.SpectralGapNT
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.BNT.Separation
import TNLean.MPS.BNT.Basic
import TNLean.MPS.Overlap.CastDecay

/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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

3. **`isBNT_of_separated_bnt_data`**: the separated block hypotheses give
   a valid `IsBNT` structure with the required overlap and independence properties.

4. **`IsNormalCanonicalFormBNT`**: normal-canonical separated hypotheses retained for
   the primitive-transfer-map route. Its forgetful projections feed the explicit
   separated-hypotheses lemmas.

## Design note on coefficients

In the full paper (arXiv:1606.00608, eq. decBSV), the decomposition into a basis of normal
tensors uses summed coefficients `c_j(N) = Σ_{q in group j} μ_{j,q}^N`.
The results below concern already separated one-representative block families
and do not perform the raw coefficient comparison for the two-layer BNT
decomposition. That comparison is carried out for sector decompositions, where
the sums `Σ_q μ_{j,q}^N` and their multiplicities remain visible.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-! ### `IsNormalCanonicalFormBNT` hypotheses -/

/-- Normal canonical form with BNT separation: extends `IsNormalCanonicalForm` with
the requirement that distinct blocks are not gauge-phase equivalent and that the
block weight moduli `‖μ_j‖` are **strictly decreasing**.

These hypotheses keep one representative per strict weight-modulus class. They do
not retain repeated equal-modulus sectors; the full multiplicity structure (weights
`μ_{j,q}` and multiplicities `M_j` as in arXiv:1606.00608) is recorded in
`SectorDecomposition` and the sector-weight comparison theorems.

**Scope restriction (one-copy-per-sector):** This is the already grouped
single-representative surface, not the full CPSV16 BNT multiplicity structure.
The general source decomposition allows repeated equal-modulus copies inside a
sector through the raw coefficients `μ_{j,q}`. The restriction is documented in
`docs/paper-gaps/ft_one_copy_scope_restriction.tex`.

`IsNormalCanonicalFormBNT` uses the spectral/primitive-transfer-map version of normality
(`IsNormalCanonicalForm`), while the later `IsBNT` hypotheses ask for blockwise
`IsNormal` (the equivalent algebraic eventual-block-injectivity notion). The
primitive-to-normal implication must be supplied explicitly when passing to `IsBNT`. -/
structure IsNormalCanonicalFormBNT {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop extends
    IsNormalCanonicalForm μ A where
  /-- Strict ordering of the block weights by modulus (strengthened from `Antitone`). -/
  mu_strict_anti : StrictAnti (fun k : Fin r => ‖μ k‖)
  /-- Distinct blocks are not gauge-phase equivalent (BNT separation). -/
  blocks_not_equiv : ∀ j k : Fin r, j ≠ k →
    ∀ (h : dim j = dim k),
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)
  /-- The dominant block weight has unit modulus.

  Source convention from arXiv:1606.00608 (paragraph after `eq:II_CF1`): one can always
  renormalize the canonical form so that `|μ_k| ≤ 1` and at least one weight equals one.
  This is a definitional choice rather than an extra restriction: an MPS state is invariant
  under overall rescaling of the underlying tensor, so any canonical form can be adjusted
  to satisfy `‖μ 0‖ = 1`. Combined with `mu_strict_anti`, this fixes `‖μ 0‖ = 1` and
  `‖μ k‖ < 1` for `k ≥ 1`. -/
  mu_dom_norm_one : ∀ h : 0 < r, ‖μ ⟨0, h⟩‖ = 1

namespace IsNormalCanonicalFormBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Project normal-CF-BNT hypotheses to blockwise irreducibility. -/
def toHasIrreducibleBlocks (hNCF : IsNormalCanonicalFormBNT μ A) :
    HasIrreducibleBlocks (d := d) A :=
  hNCF.toIsNormalCanonicalForm.toHasIrreducibleBlocks

/-- Project normal-CF-BNT hypotheses to left-canonical block-family normalization. -/
def toIsLeftCanonicalBlockFamily (hNCF : IsNormalCanonicalFormBNT μ A) :
    IsLeftCanonicalBlockFamily (d := d) A :=
  hNCF.toIsNormalCanonicalForm.toIsLeftCanonicalBlockFamily

/-- Project normal-CF-BNT hypotheses to blockwise primitive transfer maps. -/
def toHasPrimitiveBlocks (hNCF : IsNormalCanonicalFormBNT μ A) :
    HasPrimitiveBlocks (d := d) A :=
  hNCF.toIsNormalCanonicalForm.toHasPrimitiveBlocks

/-- Project restricted normal-CF-BNT hypotheses to strict weight inequalities.

This projection is for the already-grouped single-representative special case, not
for the full CPSV multiplicity BNT surface. -/
def toHasStrictOrderedNonzeroWeights (hNCF : IsNormalCanonicalFormBNT μ A) :
    HasStrictOrderedNonzeroWeights μ where
  mu_strict_anti := hNCF.mu_strict_anti
  mu_ne_zero := hNCF.toIsNormalCanonicalForm.mu_ne_zero

/-- Project normal-CF-BNT hypotheses to self-overlap normalization. -/
def toHasNormalizedSelfOverlap [∀ k, NeZero (dim k)]
    (hNCF : IsNormalCanonicalFormBNT μ A) :
    HasNormalizedSelfOverlap (d := d) A :=
  hNCF.toIsNormalCanonicalForm.toHasNormalizedSelfOverlap

/-- Each block weight has modulus at most `1`.

Source: arXiv:1606.00608, paragraph after `eq:II_CF1`. The dominant block
weight has unit modulus (`mu_dom_norm_one`); the remaining blocks have
strictly smaller modulus by `mu_strict_anti`, hence are bounded by `1`. -/
lemma mu_norm_le_one (hNCF : IsNormalCanonicalFormBNT μ A) (k : Fin r) :
    ‖μ k‖ ≤ 1 := by
  by_cases hr : 0 < r
  · have hdom : ‖μ ⟨0, hr⟩‖ = 1 := hNCF.mu_dom_norm_one hr
    have hle : (⟨0, hr⟩ : Fin r) ≤ k := Fin.mk_le_of_le_val (Nat.zero_le _)
    have hanti : ‖μ k‖ ≤ ‖μ ⟨0, hr⟩‖ := hNCF.mu_strict_anti.antitone hle
    rw [hdom] at hanti
    exact hanti
  · exact absurd k.isLt (by omega)

/-- Rebuild `IsNormalCanonicalFormBNT` from the additive split formulation plus
the BNT separation assumption and the source-faithful dominant-block
normalization `‖μ ⟨0, _⟩‖ = 1`.

**Scope restriction (one-copy-per-sector):** The strict weight-ordering input
selects one representative per modulus class. This constructor does not recover
the multiplicity data of the full CPSV16 BNT decomposition; see
`docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
def ofSeparatedData
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hPrim : HasPrimitiveBlocks (d := d) A)
    (hμ : HasStrictOrderedNonzeroWeights μ)
    (hDim : ∀ k, 0 < dim k)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hμDom : ∀ h : 0 < r, ‖μ ⟨0, h⟩‖ = 1) :
    IsNormalCanonicalFormBNT μ A where
  toIsNormalCanonicalForm :=
    IsNormalCanonicalForm.ofStrictSeparatedData hIrr hLeft hPrim hμ hDim
  mu_strict_anti := hμ.mu_strict_anti
  blocks_not_equiv := hBlocks
  mu_dom_norm_one := hμDom

end IsNormalCanonicalFormBNT

/-- Distinct same-dimension blocks in a separated irreducible trace-preserving
family are not proportional at arbitrarily large chain lengths. -/
theorem exists_ge_not_forall_mpv_eq_mul_of_blocksNotGaugePhaseEquiv_of_irreducible_TP
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    {j k : Fin r} (hjk : j ≠ k) (hdim : dim j = dim k) (Nmin : ℕ) :
    ∃ N : ℕ, Nmin ≤ N ∧
      ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin d,
        mpv (cast (congr_arg (MPSTensor d) hdim) (A j)) σ = c * mpv (A k) σ := by
  have hA_self_cast :
      Tendsto
        (fun N =>
          mpvOverlap (d := d) (cast (congr_arg (MPSTensor d) hdim) (A j))
            (cast (congr_arg (MPSTensor d) hdim) (A j)) N)
        atTop (nhds (1 : ℂ)) := by
    refine (hOverlap.overlap_tendsto_one j).congr ?_
    intro N
    unfold mpvOverlap
    apply Finset.sum_congr rfl
    intro σ _
    rw [mpv_cast_dim hdim (A j) N σ]
  exact exists_ge_not_forall_mpv_eq_mul_of_not_gaugePhaseEquiv_of_irreducible_TP
    (cast (congr_arg (MPSTensor d) hdim) (A j)) (A k)
    ((isIrreducibleTensor_cast_dim hdim (A j)).mpr (hIrr.block_irreducible j))
    (hIrr.block_irreducible k)
    ((leftCanonical_cast_dim hdim (A j)).mpr (hLeft.leftCanonical j))
    (hLeft.leftCanonical k)
    hA_self_cast (hOverlap.overlap_tendsto_one k)
    (hBlocks j k hjk hdim) Nmin

/-- The block-diagonal tensor `toTensorFromBlocks μ A` carries the obvious coefficient
expansion over its blocks. -/
private theorem spans_mpv_toTensorFromBlocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) :
    ∀ N : ℕ, ∃ c : Fin r → ℂ, ∀ σ : Fin N → Fin d,
      mpv (toTensorFromBlocks μ A) σ = ∑ k : Fin r, c k * mpv (A k) σ := by
  intro N
  refine ⟨fun k => μ k ^ N, ?_⟩
  intro σ
  simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ A σ

/-- **Existential BNT linear independence from asymptotic orthonormal overlaps.**

If the self-overlaps of a finite block family tend to `1` and the cross-overlaps
of distinct blocks tend to `0`, then the MPV states are linearly independent for
every sufficiently large system size.  This is the threshold form of
`bntFamilies_eventually_linearIndependent`. -/
lemma exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hSelf : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hOff : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds (0 : ℂ))) :
    ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin r => mpvState (d := d) (A j) N) := by
  have hOrtho := bntFamilies_eventually_linearIndependent A hSelf hOff
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
    (hInj : HasInjectiveBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      (hdim := hdim) (A := A j) (B := A k)
      (hA_inj := hInj.block_injective j)
      (hB_inj := hInj.block_injective k)
      (hA_norm := hLeft.leftCanonical j)
      (hB_norm := hLeft.leftCanonical k)
      (hNot := hBlocks j k hjk hdim)
  · exact mpvOverlap_tendsto_zero_of_dim_ne (A j) (A k)
      (hInj.block_injective j)
      (hInj.block_injective k)
      (hLeft.leftCanonical j)
      (hLeft.leftCanonical k)
      hdim

/-- Separated-hypotheses construction of an `IsBNT` witness.

The only role of `μ` is to specify the block-diagonal tensor `toTensorFromBlocks μ A` and its
obvious coefficient decomposition.  Strict weight ordering is not used here. -/
lemma isBNT_of_separated_bnt_data [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : HasInjectiveBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    IsBNT (toTensorFromBlocks μ A) r dim A where
  normal := fun j => (hInj.block_injective j).isNormal
  spans_mpv := spans_mpv_toTensorFromBlocks μ A
  eventually_li :=
    exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal A
      hOverlap.overlap_tendsto_one
      (fun i j hij =>
        cross_overlap_tendsto_zero_of_separated_bnt_data A hInj hLeft hBlocks i j hij)

end SeparatedBNT

/-! ### Cross-overlap decay from separated normal BNT hypotheses -/

section SeparatedNormalBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Separated-hypotheses version of normal BNT cross-overlap decay.

Only irreducibility, left-canonical normalization, and the BNT non-equivalence
assumption are used. -/
theorem cross_overlap_tendsto_zero_of_separated_normal_bnt_data
    [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) := by
  by_cases hdim : dim j = dim k
  · exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      (hdim := hdim) (A := A j) (B := A k)
      (hA_irr := hIrr.block_irreducible j)
      (hB_irr := hIrr.block_irreducible k)
      (hA_norm := hLeft.leftCanonical j)
      (hB_norm := hLeft.leftCanonical k)
      (hNot := hBlocks j k hjk hdim)
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP (A j) (A k)
      (hIrr.block_irreducible j)
      (hIrr.block_irreducible k)
      (hLeft.leftCanonical j)
      (hLeft.leftCanonical k)
      hdim

/-- The NT hypotheses already supply the `spans_mpv` and `eventually_li` hypotheses used by the
proportional-FT / permutation arguments. The only missing ingredient for a full `IsBNT`
construction is blockwise `IsNormal`. -/
theorem spans_mpv_and_eventually_li_of_separated_normal_bnt_data [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hNCF : IsNormalCanonicalForm μ A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    (∀ N : ℕ, ∃ c : Fin r → ℂ, ∀ σ : Fin N → Fin d,
      mpv (toTensorFromBlocks μ A) σ = ∑ j : Fin r, c j * mpv (A j) σ) ∧
    (∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun j : Fin r => mpvState (d := d) (A j) N)) :=
  ⟨spans_mpv_toTensorFromBlocks μ A,
   exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal A
     (fun j => hNCF.overlap_tendsto_one j)
     (fun i j hij =>
       cross_overlap_tendsto_zero_of_separated_normal_bnt_data A
         hNCF.toHasIrreducibleBlocks
         hNCF.toIsLeftCanonicalBlockFamily
         hBlocks i j hij)⟩

/-- Separated-hypotheses version of `IsNormalCanonicalFormBNT.isBNT`.

Here `hNCF` supplies normality via the primitive-transfer-map characterization from
`IsNormalCanonicalForm`, while `hNormal` supplies the equivalent algebraic `IsNormal` hypotheses
(eventual block injectivity) required by `IsBNT`. In applications `hNormal` comes from the
Wielandt / primitive-to-normal implication. -/
theorem isBNT_of_separated_normal_bnt_data [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hNCF : IsNormalCanonicalForm μ A)
    (hNormal : ∀ j, IsNormal (A j))
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A) :
    IsBNT (toTensorFromBlocks μ A) r dim A := by
  obtain ⟨hSpans, hLI⟩ :=
    spans_mpv_and_eventually_li_of_separated_normal_bnt_data μ A hNCF hBlocks
  exact ⟨hNormal, hSpans, hLI⟩

end SeparatedNormalBNT

namespace IsNormalCanonicalFormBNT

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Cross-overlap decay for normal-CF-BNT blocks.

**Scope restriction (one-copy-per-sector):** The hypothesis
`IsNormalCanonicalFormBNT` is the separated, already grouped variant documented
in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
theorem cross_overlap_tendsto_zero
    [∀ k, NeZero (dim k)]
    (hNCF : IsNormalCanonicalFormBNT μ A) (j k : Fin r) (hjk : j ≠ k) :
    Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) :=
  cross_overlap_tendsto_zero_of_separated_normal_bnt_data A
    hNCF.toHasIrreducibleBlocks
    hNCF.toIsLeftCanonicalBlockFamily
    hNCF.blocks_not_equiv
    j k hjk

/-- A normal-canonical-form decomposition with BNT separation yields a valid `IsBNT`
structure once the equivalent blockwise `IsNormal` witnesses (eventual block injectivity) are
supplied explicitly.

**Scope restriction (one-copy-per-sector):** The hypothesis
`IsNormalCanonicalFormBNT` is the separated, already grouped variant documented
in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma isBNT [∀ k, NeZero (dim k)]
    (hNCF : IsNormalCanonicalFormBNT μ A)
    (hNormal : ∀ j, IsNormal (A j)) :
    IsBNT (toTensorFromBlocks μ A) r dim A :=
  isBNT_of_separated_normal_bnt_data μ A
    hNCF.toIsNormalCanonicalForm
    hNormal
    hNCF.blocks_not_equiv

end IsNormalCanonicalFormBNT

end MPSTensor
