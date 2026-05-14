/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.Basic
import TNLean.MPS.FundamentalTheorem.PaperBNT.EqualModulus

/-!
# Executable examples for `IsBNTCanonicalForm`

This file collects concrete `SectorDecomposition` constructions and
instantiates the paper-faithful `IsBNTCanonicalForm` on each.  All three
core examples have a single BNT basis sector (`basisCount = 1`):

* **Example 1** — single sector, single copy: `weight = (1,)`.
* **Example 2** — `C ⊕ (-C)`: single sector, two copies with raw weights
  `(1, -1)`; the coefficient is `1 + (-1)^N`, which is *not* a scalar
  power.  This is the CPSV16 §II motivating example recorded in the
  audit memo and in issue #1678.
* **Example 3** — `C ⊕ e^{iθ}C`: single sector, two copies with raw
  weights `(1, e^{iθ})`; the coefficient is `1 + e^{iNθ}`, illustrating
  equal-modulus grouping with a non-trivial phase.
* **Example 5** — `C ⊕ (1/2)C` (`halvedDecomp`): single sector, two
  copies with raw weights `(1, 1/2)`.  Demonstrates that unequal-modulus
  copies are admissible by the CPSV16 §II.A line-246 normalization
  (`weight_norm_le_one` holds because both `1` and `1/2` have modulus
  `≤ 1`; `weight_unit_exists` is witnessed by the first copy).

A fourth example exercises the **optional** equal-modulus layer
`HasEqualModulusWeightLayer` on top of `signFlipDecomp`, demonstrating
that the equal-modulus subclass is non-empty.  Following the audit
counter-example `C ⊕ (1/2)C` (`audits/2026-05-13_cpsv16_paper_bnt_phase_1_multiplicity_audit.md`
§Q4), the `halvedDecomp` construction below admits `IsBNTCanonicalForm`
but does not admit `HasEqualModulusWeightLayer` (its two copies have
unequal moduli, ruling out a single per-sector spectral level).

Each example takes the per-block normality data (injectivity,
irreducibility, left-canonical, self-overlap, eventual linear
independence) of `C` as hypotheses; this avoids reproving the underlying
analytic facts here and keeps the file's focus on instantiating the new
structure.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor
namespace PaperBNT.Examples

variable {d D : ℕ}

/-! ## Example 1 — single sector, single copy -/

/-- The trivial single-sector single-copy decomposition of `C`. -/
@[reducible] noncomputable def singletonDecomp (C : MPSTensor d D) :
    SectorDecomposition d where
  basisCount := 1
  basisDim := fun _ => D
  basis := fun _ => C
  sectors :=
    { copies := fun _ => 1
      copies_pos := fun _ => Nat.one_pos
      weight := fun _ _ => 1
      weight_ne_zero := fun _ _ => one_ne_zero }

/-- **Example 1**: a single BNT sector with a single copy and weight `1`. -/
noncomputable example
    (C : MPSTensor d D) (hDpos : 0 < D)
    (hCInj : IsInjective C) (hCIrr : IsIrreducibleTensor C)
    (hCLeft : IsLeftCanonical C)
    (hCSelf : Tendsto (fun N : ℕ => mpvOverlap (d := d) C C N) atTop (𝓝 1))
    (hCNonzero : ∃ N0 : ℕ, ∀ N > N0, mpvState C N ≠ 0) :
    IsBNTCanonicalForm (singletonDecomp C) where
  basis_dim_pos := fun _ => hDpos
  basis_injective := fun _ => hCInj
  basis_irreducible := fun _ => hCIrr
  basis_left_canonical := fun _ => hCLeft
  basis_normalized_self_overlap := fun _ => hCSelf
  bnt_data := by
    classical
    obtain ⟨N0, hN0⟩ := hCNonzero
    refine ⟨N0, fun N hN => ?_⟩
    exact LinearIndependent.of_subsingleton (i := (0 : Fin 1)) (hN0 N hN)
  basis_distinct := fun j k hjk _ =>
    absurd (Subsingleton.elim j k) hjk
  -- CPSV16 line 246: the unique weight `μ = 1` has `‖μ‖ = 1 ≤ 1`.
  weight_norm_le_one := by
    intro _ _
    change ‖(1 : ℂ)‖ ≤ 1
    simp
  -- CPSV16 line 246: the unique weight is the unit-modulus witness.
  weight_unit_exists := by
    refine ⟨0, 0, ?_⟩
    change ‖(1 : ℂ)‖ = 1
    simp

/-! ## Example 2 — `C ⊕ (-C)` -/

/-- The single-sector two-copy decomposition of `C` with raw weights
`(1, -1)`. -/
@[reducible] noncomputable def signFlipDecomp (C : MPSTensor d D) :
    SectorDecomposition d where
  basisCount := 1
  basisDim := fun _ => D
  basis := fun _ => C
  sectors :=
    { copies := fun _ => 2
      copies_pos := fun _ => Nat.succ_pos 1
      weight := fun _ q => if q = 0 then (1 : ℂ) else -1
      weight_ne_zero := by
        intro _ q
        split_ifs with hq
        · exact one_ne_zero
        · exact neg_ne_zero.mpr one_ne_zero }

/-- **Example 2** — `C ⊕ (-C)`: a single BNT sector with two copies of
raw weights `(1, -1)`.  The sector coefficient is `1 + (-1)^N`, which is
*not* a scalar power; this is the motivating example of issue #1678 and
the audit memo. -/
noncomputable example
    (C : MPSTensor d D) (hDpos : 0 < D)
    (hCInj : IsInjective C) (hCIrr : IsIrreducibleTensor C)
    (hCLeft : IsLeftCanonical C)
    (hCSelf : Tendsto (fun N : ℕ => mpvOverlap (d := d) C C N) atTop (𝓝 1))
    (hCNonzero : ∃ N0 : ℕ, ∀ N > N0, mpvState C N ≠ 0) :
    IsBNTCanonicalForm (signFlipDecomp C) where
  basis_dim_pos := fun _ => hDpos
  basis_injective := fun _ => hCInj
  basis_irreducible := fun _ => hCIrr
  basis_left_canonical := fun _ => hCLeft
  basis_normalized_self_overlap := fun _ => hCSelf
  bnt_data := by
    classical
    obtain ⟨N0, hN0⟩ := hCNonzero
    refine ⟨N0, fun N hN => ?_⟩
    exact LinearIndependent.of_subsingleton (i := (0 : Fin 1)) (hN0 N hN)
  basis_distinct := fun j k hjk _ =>
    absurd (Subsingleton.elim j k) hjk
  -- CPSV16 line 246: both weights `(1, -1)` have unit modulus.
  weight_norm_le_one := by
    intro _ q
    change ‖(if q = 0 then (1 : ℂ) else -1)‖ ≤ 1
    split_ifs with hq
    · simp
    · simp
  -- CPSV16 line 246: the first copy `q = 0` carries weight `μ = 1`.
  weight_unit_exists := by
    refine ⟨0, 0, ?_⟩
    change ‖(if (0 : Fin 2) = 0 then (1 : ℂ) else -1)‖ = 1
    simp

/-! ## Example 3 — `C ⊕ e^{iθ} C` -/

/-- The single-sector two-copy decomposition of `C` with raw weights
`(1, e^{iθ})`, illustrating equal-modulus grouping with a non-trivial
phase. -/
@[reducible] noncomputable def phaseDecomp (C : MPSTensor d D) (θ : ℝ) :
    SectorDecomposition d where
  basisCount := 1
  basisDim := fun _ => D
  basis := fun _ => C
  sectors :=
    { copies := fun _ => 2
      copies_pos := fun _ => Nat.succ_pos 1
      weight := fun _ q =>
        if q = 0 then (1 : ℂ) else Complex.exp (Complex.I * θ)
      weight_ne_zero := by
        intro _ q
        split_ifs with hq
        · exact one_ne_zero
        · exact Complex.exp_ne_zero _ }

/-- **Example 3** — `C ⊕ e^{iθ}C`: a single BNT sector with two copies of
raw weights `(1, e^{iθ})`.  The sector coefficient is `1 + e^{iNθ}`,
illustrating equal-modulus grouping (CPSV16 §II / issue #1678). -/
noncomputable example
    (C : MPSTensor d D) (θ : ℝ) (hDpos : 0 < D)
    (hCInj : IsInjective C) (hCIrr : IsIrreducibleTensor C)
    (hCLeft : IsLeftCanonical C)
    (hCSelf : Tendsto (fun N : ℕ => mpvOverlap (d := d) C C N) atTop (𝓝 1))
    (hCNonzero : ∃ N0 : ℕ, ∀ N > N0, mpvState C N ≠ 0) :
    IsBNTCanonicalForm (phaseDecomp C θ) where
  basis_dim_pos := fun _ => hDpos
  basis_injective := fun _ => hCInj
  basis_irreducible := fun _ => hCIrr
  basis_left_canonical := fun _ => hCLeft
  basis_normalized_self_overlap := fun _ => hCSelf
  bnt_data := by
    classical
    obtain ⟨N0, hN0⟩ := hCNonzero
    refine ⟨N0, fun N hN => ?_⟩
    exact LinearIndependent.of_subsingleton (i := (0 : Fin 1)) (hN0 N hN)
  basis_distinct := fun j k hjk _ =>
    absurd (Subsingleton.elim j k) hjk
  -- CPSV16 line 246: both weights `(1, exp(I·θ))` have unit modulus.
  weight_norm_le_one := by
    intro _ q
    -- Unfold the `phaseDecomp.weight` to its `if`.
    change ‖(if q = 0 then (1 : ℂ) else Complex.exp (Complex.I * θ))‖ ≤ 1
    split_ifs with hq
    · simp
    · -- `‖exp (I·θ)‖ = 1`; here `θ` is a real (cast to ℂ).
      rw [Complex.norm_exp]
      have : (Complex.I * ↑θ).re = 0 := by
        simp [Complex.mul_re]
      rw [this]
      simp
  -- CPSV16 line 246: the first copy `q = 0` carries weight `μ = 1`.
  weight_unit_exists := by
    refine ⟨0, 0, ?_⟩
    change ‖(if (0 : Fin 2) = 0 then (1 : ℂ) else Complex.exp (Complex.I * θ))‖ = 1
    simp

/-! ## Example 4 — equal-modulus weight layer on `signFlipDecomp`

This example exercises the **optional** equal-modulus layer
`HasEqualModulusWeightLayer` on top of `signFlipDecomp`, demonstrating
that the equal-modulus subclass is non-empty.

Note (audit §Q4 counter-example): replacing the weight `-1` by `1/2` in
`signFlipDecomp` would give a decomposition `C ⊕ (1/2)C` that is still a
valid `IsBNTCanonicalForm` (a single BNT basis tensor with coefficient
`1 + (1/2)^N` and raw weights `(1, 1/2)`), but it would NOT extend to
`HasEqualModulusWeightLayer`: the two copies have unequal moduli, so no
choice of `spectral_level 0` makes both quotients unit-modulus.  The
equal-modulus layer is therefore strictly stronger than the core BNT
predicate; this is the central point of the audit. -/

/-- **Example 4** — equal-modulus weight layer on `signFlipDecomp`:
the factorization `(1, -1) = 1 · (1, -1)` with `spectral_level = 1`
and `phase_weight = (1, -1)` lifts `signFlipDecomp C` to
`HasEqualModulusWeightLayer`. -/
noncomputable example
    (C : MPSTensor d D) :
    HasEqualModulusWeightLayer (signFlipDecomp C) where
  spectral_level := fun _ => 1
  spectral_level_ne_zero := fun _ => one_ne_zero
  spectral_level_antitone := by
    intro a b _
    simp
  spectral_level_dom_norm_one := fun _ => by simp
  phase_weight := fun _ q => if q = 0 then (1 : ℂ) else -1
  phase_weight_norm_one := by
    intro _ q
    split_ifs with hq
    · simp
    · simp
  weight_factor := by
    intro _ q
    change (if q = 0 then (1 : ℂ) else -1) =
        1 * (if q = 0 then (1 : ℂ) else -1)
    rw [one_mul]

/-! ## Example 5 — `C ⊕ (1/2)C`, unequal-modulus admissibility

This example demonstrates that the strengthened `IsBNTCanonicalForm`
predicate (with the CPSV16 §II.A line-246 fields `weight_norm_le_one`
and `weight_unit_exists`) admits decompositions whose copies have
**unequal** moduli: the construction below has one unit-modulus copy
and one `1/2`-modulus copy.  This is exactly the
`audits/2026-05-13_cpsv16_paper_bnt_phase_1_multiplicity_audit.md` §Q4
counter-example, here written as a positive example: the strengthened
predicate is paper-faithful (line 246 verbatim) and admits the example.

The decomposition does NOT admit `HasEqualModulusWeightLayer`: the
optional equal-modulus layer of `PaperBNT/EqualModulus.lean` would
require a single per-sector `spectral_level` with all phase weights of
unit modulus, which fails here because `|1| ≠ |1/2|`. -/

/-- The single-sector two-copy decomposition of `C` with raw weights
`(1, 1/2)`, demonstrating admissibility of unequal-modulus copies. -/
@[reducible] noncomputable def halvedDecomp (C : MPSTensor d D) :
    SectorDecomposition d where
  basisCount := 1
  basisDim := fun _ => D
  basis := fun _ => C
  sectors :=
    { copies := fun _ => 2
      copies_pos := fun _ => Nat.succ_pos 1
      weight := fun _ q => if q = 0 then (1 : ℂ) else (1 / 2 : ℂ)
      weight_ne_zero := by
        intro _ q
        split_ifs with hq
        · exact one_ne_zero
        · norm_num }

/-- **Example 5** — `C ⊕ (1/2)C`: a single BNT sector with two copies of
raw weights `(1, 1/2)`.  The sector coefficient is `1 + (1/2)^N → 1`,
not a scalar power.  Demonstrates that the strengthened
`IsBNTCanonicalForm` admits unequal-modulus copies: `weight_norm_le_one`
holds because `‖1‖ ≤ 1` and `‖1/2‖ = 1/2 ≤ 1`, and `weight_unit_exists`
is witnessed by the first copy with weight `1`.

Paper anchor: CPSV16 §II.A line 246, the line-246 normalization
convention permits any `|μ_{j,q}| ≤ 1` provided at least one of them
equals `1`.  See also
`audits/2026-05-13_cpsv16_paper_bnt_phase_1_multiplicity_audit.md` §Q4
for the original counter-example. -/
noncomputable example
    (C : MPSTensor d D) (hDpos : 0 < D)
    (hCInj : IsInjective C) (hCIrr : IsIrreducibleTensor C)
    (hCLeft : IsLeftCanonical C)
    (hCSelf : Tendsto (fun N : ℕ => mpvOverlap (d := d) C C N) atTop (𝓝 1))
    (hCNonzero : ∃ N0 : ℕ, ∀ N > N0, mpvState C N ≠ 0) :
    IsBNTCanonicalForm (halvedDecomp C) where
  basis_dim_pos := fun _ => hDpos
  basis_injective := fun _ => hCInj
  basis_irreducible := fun _ => hCIrr
  basis_left_canonical := fun _ => hCLeft
  basis_normalized_self_overlap := fun _ => hCSelf
  bnt_data := by
    classical
    obtain ⟨N0, hN0⟩ := hCNonzero
    refine ⟨N0, fun N hN => ?_⟩
    exact LinearIndependent.of_subsingleton (i := (0 : Fin 1)) (hN0 N hN)
  basis_distinct := fun j k hjk _ =>
    absurd (Subsingleton.elim j k) hjk
  -- CPSV16 line 246: `‖1‖ = 1 ≤ 1` and `‖1/2‖ = 1/2 ≤ 1`.
  weight_norm_le_one := by
    intro _ q
    change ‖(if q = 0 then (1 : ℂ) else (1 / 2 : ℂ))‖ ≤ 1
    split_ifs with hq
    · simp
    · simp; norm_num
  -- CPSV16 line 246: the first copy `q = 0` carries the unit weight.
  weight_unit_exists := by
    refine ⟨0, 0, ?_⟩
    change ‖(if (0 : Fin 2) = 0 then (1 : ℂ) else (1 / 2 : ℂ))‖ = 1
    simp

end PaperBNT.Examples
end MPSTensor
