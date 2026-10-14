/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact

/-!
# Continuity of the regularized patch minimum

The independent regional density matrices form a fixed compact set. The ordered
filtered norm is jointly continuous in these densities and the radius, since
the positive scalar shift keeps each local matrix positive definite. Taking
the minimum therefore preserves continuity. For nonnegative weights and an
original unit vector, the minimum is positive, so its logarithm is continuous.

No continuous choice of minimizing tuples is required. The continuity proved
here supplies the regularity needed for a one-sided comparison of the minimum;
the uniform Lipschitz bound and the derivative estimate are separate results.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 421–466; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Set Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

/-- The original regularized norm minimum is continuous in the radius, for
arbitrary real weights and input vector. Compactness of the same feasible set
replaces any choice of a continuous family of minimizers.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 421–451. -/
theorem continuous_regularizedPatchMinimum_exp_neg (a : Fin m → ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
    Continuous (fun R : ℝ ↦ regularizedPatchMinimum regions a (Real.exp (-R)) Ω) := by
  classical
  let K := ↥(regularizedPatchDomain (Out := Out) regions)
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp (isCompact_regularizedPatchDomain regions)
  have hfilter (j : Fin m) :
      Continuous (fun z : ℝ × K ↦
        regularizedPatchFilter regions a (Real.exp (-z.1)) z.2.val j) := by
    have hshift : Continuous (fun z : ℝ × K ↦
        z.2.val j + Real.exp (-z.1) •
          (1 : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)) :=
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)).add
        ((Real.continuous_exp.comp continuous_fst.neg).smul continuous_const)
    exact (continuous_dependentRegionOperatorLift (regions j)).comp
      ((CFC.continuousOn_rpow (-(a j) / 2)).comp_continuous hshift fun z ↦
        ((z.2.property j).1.add_smul_one_posDef (Real.exp_pos (-z.1))).isStrictlyPositive)
  have hoperator : Continuous (fun z : ℝ × K ↦
      regularizedPatchOperator regions a (Real.exp (-z.1)) z.2.val) := by
    simpa only [regularizedPatchOperator, List.map_reverse, List.map_ofFn,
      Function.id_def, Function.comp_def] using
      continuous_list_prod (List.ofFn (id : Fin m → Fin m)).reverse
        (fun j _ ↦ hfilter j)
  have heval : Continuous (fun M : Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
      ((v : (Finset.univ : Finset V)) → Out v.1) ℂ ↦ WithLp.toLp 2 (M *ᵥ Ω)) :=
    (PiLp.continuous_toLp _ _).comp (continuous_id.matrix_mulVec continuous_const)
  have hobjective : Continuous (fun z : ℝ × K ↦
      regularizedPatchObjective regions a (Real.exp (-z.1)) Ω z.2.val) :=
    heval.norm.comp hoperator
  have hminimum := (isCompact_univ : IsCompact (univ : Set K)).continuous_sInf
    (f := fun R (x : K) ↦ regularizedPatchObjective regions a (Real.exp (-R)) Ω x.val)
    hobjective
  have himage (R : ℝ) :
      (fun x : K ↦ regularizedPatchObjective regions a (Real.exp (-R)) Ω x.val) '' univ =
        regularizedPatchObjective regions a (Real.exp (-R)) Ω ''
          regularizedPatchDomain regions := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  simpa only [himage, regularizedPatchMinimum] using hminimum

/-- The logarithm of the original positive patch minimum is continuous in the
radius. The densities, weights, regions and original unit vector are unchanged.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 421–451. -/
theorem continuous_log_regularizedPatchMinimum_exp_neg
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (hΩ : ‖Ω‖ = 1) :
    Continuous (fun R : ℝ ↦ Real.log
      (regularizedPatchMinimum regions a (Real.exp (-R)) Ω)) :=
  (continuous_regularizedPatchMinimum_exp_neg regions a Ω).log fun R ↦
    (regularizedPatchMinimum_pos regions a ha (Real.exp_pos (-R)) Ω hΩ).ne'

end TNLean.PEPS
