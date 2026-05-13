/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.Basic

/-!
# Executable examples for `IsBNTCanonicalForm`

This file collects three concrete `SectorDecomposition` constructions and
instantiates `IsBNTCanonicalForm` on each.  All three examples have a
single BNT sector (`basisCount = 1`):

* **Example 1** — single sector, single copy: `weight = (1,)`.
* **Example 2** — `C ⊕ (-C)`: single sector, two copies with
  phases `(1, -1)`; the coefficient is `1 + (-1)^N`, which is *not* a
  scalar power.  This is the CPSV16 §II motivating example recorded in
  the user's recommendation memo and in issue #1678.
* **Example 3** — `C ⊕ e^{iθ}C`: single sector, two copies with
  phases `(1, e^{iθ})`; the coefficient is `1 + e^{iNθ}`, illustrating
  the equal-modulus grouping that the one-copy specialization cannot
  represent.

Each example takes the per-block normality data (injectivity,
irreducibility, left-canonical, self-overlap, eventual linear
independence) of `C` as hypotheses; this avoids reproving the
underlying analytic facts here and keeps the file's focus on
instantiating the new structure.
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
    (C : MPSTensor d D)
    (hCInj : IsInjective C) (hCIrr : IsIrreducibleTensor C)
    (hCLeft : IsLeftCanonical C)
    (hCSelf : Tendsto (fun N : ℕ => mpvOverlap (d := d) C C N) atTop (𝓝 1))
    (hCNonzero : ∃ N0 : ℕ, ∀ N > N0, mpvState C N ≠ 0) :
    IsBNTCanonicalForm (singletonDecomp C) where
  spectralLevel := fun _ => 1
  spectralLevel_ne_zero := fun _ => one_ne_zero
  spectralLevel_strict_anti := by
    intro a b hab
    exact absurd (Subsingleton.elim a b) (ne_of_lt hab)
  spectralLevel_dom_norm_one := fun _ => by simp
  phaseWeight := fun _ _ => 1
  phaseWeight_norm_one := fun _ _ => by simp
  weight_factor := fun _ _ => by simp
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

/-! ## Example 2 — `C ⊕ (-C)` -/

/-- The single-sector two-copy decomposition of `C` with weights `(1, -1)`. -/
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
weights `(1, -1)`.  The sector coefficient is `1 + (-1)^N`, which is
*not* a scalar power; this is the motivating example of issue #1678. -/
noncomputable example
    (C : MPSTensor d D)
    (hCInj : IsInjective C) (hCIrr : IsIrreducibleTensor C)
    (hCLeft : IsLeftCanonical C)
    (hCSelf : Tendsto (fun N : ℕ => mpvOverlap (d := d) C C N) atTop (𝓝 1))
    (hCNonzero : ∃ N0 : ℕ, ∀ N > N0, mpvState C N ≠ 0) :
    IsBNTCanonicalForm (signFlipDecomp C) where
  spectralLevel := fun _ => 1
  spectralLevel_ne_zero := fun _ => one_ne_zero
  spectralLevel_strict_anti := by
    intro a b hab
    exact absurd (Subsingleton.elim a b) (ne_of_lt hab)
  spectralLevel_dom_norm_one := fun _ => by simp
  phaseWeight := fun _ q => if q = 0 then (1 : ℂ) else -1
  phaseWeight_norm_one := by
    intro _ q
    split_ifs with hq
    · simp
    · simp
  weight_factor := by
    intro _ q
    change (if q = 0 then (1 : ℂ) else -1) = 1 * (if q = 0 then (1 : ℂ) else -1)
    rw [one_mul]
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

/-! ## Example 3 — `C ⊕ e^{iθ} C` -/

/-- The single-sector two-copy decomposition of `C` with weights
`(1, e^{iθ})`, illustrating equal-modulus grouping. -/
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
weights `(1, e^{iθ})`.  The sector coefficient is `1 + e^{iNθ}`,
illustrating the equal-modulus grouping recorded in the user's
recommendation memo (CPSV16 §II / issue #1678). -/
noncomputable example
    (C : MPSTensor d D) (θ : ℝ)
    (hCInj : IsInjective C) (hCIrr : IsIrreducibleTensor C)
    (hCLeft : IsLeftCanonical C)
    (hCSelf : Tendsto (fun N : ℕ => mpvOverlap (d := d) C C N) atTop (𝓝 1))
    (hCNonzero : ∃ N0 : ℕ, ∀ N > N0, mpvState C N ≠ 0) :
    IsBNTCanonicalForm (phaseDecomp C θ) where
  spectralLevel := fun _ => 1
  spectralLevel_ne_zero := fun _ => one_ne_zero
  spectralLevel_strict_anti := by
    intro a b hab
    exact absurd (Subsingleton.elim a b) (ne_of_lt hab)
  spectralLevel_dom_norm_one := fun _ => by simp
  phaseWeight := fun _ q =>
    if q = 0 then (1 : ℂ) else Complex.exp (Complex.I * θ)
  phaseWeight_norm_one := by
    intro _ q
    split_ifs with hq
    · simp
    · -- `‖exp(I · θ)‖ = exp((I · θ).re) = exp 0 = 1` for real `θ`.
      have hre : (Complex.I * (θ : ℂ)).re = 0 := by
        simp [Complex.mul_re]
      rw [Complex.norm_exp, hre, Real.exp_zero]
  weight_factor := by
    intro _ q
    change (if q = 0 then (1 : ℂ) else Complex.exp (Complex.I * θ)) =
        1 * (if q = 0 then (1 : ℂ) else Complex.exp (Complex.I * θ))
    rw [one_mul]
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

end PaperBNT.Examples
end MPSTensor
