/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.Placement.RegionPlacement
import QICLean.Analysis.FunctionalCalculus.ShiftedDensityPowers
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TNLean.PEPS.AreaLaw.RegionalStates.Regions.Cylinder
import QICLean.Spectral.Projection.ShiftedDensityTruncation

/-!
# Minimum norm of regularized regional filters

Independent trace-one positive semidefinite matrices parametrize each region.
Their positive identity shifts define negative-power filters, applied in the
specified order to a unit Euclidean vector. The parameter set is compact,
the norm objective is continuous and attains a positive minimum.

Source: OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
`03-patches.tex`, lines 51–114, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The finite-dimensional minimum argument needs neither nested regions nor
commutation between filters. It does not include stationarity or energy estimates.

## The logarithm of the regularized patch minimum

The positive minimum of the original filtered norm is also an attained minimum
after taking logarithms. Both attainment and the comparison with every feasible
density tuple follow from the established norm minimum. No new positivity
assumption or choice of minimizers is imposed.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 425–481, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This result does not establish the derivative or growth of that minimum.

It also contains the following results.

* `TNLean.PEPS.exists_mem_iSup_dependentRegionCylinder_norm_sub_le`: approximation by cylinders from
  ordered inverse filters.
* `TNLean.PEPS.continuous_regularizedPatchMinimum_exp_neg`,
  `TNLean.PEPS.continuous_log_regularizedPatchMinimum_exp_neg`: continuity of the regularized patch
  minimum.
-/

section RegularizedPatchMinimum

section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)] [∀ v, DecidableEq (Out v)]

variable {m : ℕ} (regions : Fin m → Finset V)

/-- Independent density matrices, one for each occurrence of a region.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
def regularizedPatchDomain :
    Set (∀ j, Matrix ((v : regions j) → Out v.1)
      ((v : regions j) → Out v.1) ℂ) :=
  {x | ∀ j, (x j).PosSemidef ∧ (x j).trace = 1}

/-- A local full-space regularized power, extended by the identity outside its region.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def regularizedPatchFilter (a : Fin m → ℝ) (b : ℝ)
    (x : ∀ j, Matrix ((v : regions j) → Out v.1)
      ((v : regions j) → Out v.1) ℂ) (j : Fin m) :
    Matrix ((v : V) → Out v)
      ((v : V) → Out v) ℂ := by
  classical
  exact ManyBody.place (regions j) ((x j + b • 1) ^ (-(a j) / 2))

/-- The ordered matrix product `L_(m-1) ⋯ L_0`.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def regularizedPatchOperator (a : Fin m → ℝ) (b : ℝ)
    (x : ∀ j, Matrix ((v : regions j) → Out v.1)
      ((v : regions j) → Out v.1) ℂ) :
    Matrix ((v : V) → Out v)
      ((v : V) → Out v) ℂ := by
  classical
  exact ((List.ofFn fun j ↦ regularizedPatchFilter regions a b x j).reverse).prod

/-- The filtered vector in the Euclidean configuration space.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def regularizedPatchOutput (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1)
      ((v : regions j) → Out v.1) ℂ) :
    EuclideanSpace ℂ ((v : V) → Out v) :=
  WithLp.toLp 2 (regularizedPatchOperator regions a b x *ᵥ Ω)

/-- The norm minimized over independent regional densities.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def regularizedPatchObjective (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1)
      ((v : regions j) → Out v.1) ℂ) : ℝ :=
  ‖regularizedPatchOutput regions a b Ω x‖

omit [Fintype V] [∀ v, DecidableEq (Out v)] in
/-- The feasible space of independent regional densities is compact. -/
theorem isCompact_regularizedPatchDomain :
    IsCompact (regularizedPatchDomain (Out := Out) regions) :=
  isCompact_pi_infinite fun _ ↦ Matrix.isCompact_setOf_posSemidef_trace_eq_one

omit [∀ v, DecidableEq (Out v)] in
/-- A unit global vector supplies a configuration in every region, so the
feasible space is nonempty without an extra local-dimension hypothesis. -/
theorem regularizedPatchDomain_nonempty
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1) :
    (regularizedPatchDomain (Out := Out) regions).Nonempty := by
  have hΩne : Ω ≠ 0 := norm_ne_zero_iff.mp (hΩ.trans_ne one_ne_zero)
  obtain ⟨σ, _⟩ := Function.ne_iff.mp (show (Ω : _ → ℂ) ≠ 0 from by
    intro h; apply hΩne; simpa using congrArg (WithLp.toLp 2) h)
  have hn (j : Fin m) : Nonempty ((v : regions j) → Out v.1) :=
    ⟨fun v ↦ σ v.1⟩
  choose x hx using fun j ↦ @Matrix.setOf_posSemidef_trace_eq_one_nonempty
    ((v : regions j) → Out v.1) inferInstance (hn j)
  exact ⟨x, hx⟩

/-- Each full-space regularized regional filter depends continuously on all densities. -/
theorem continuousOn_regularizedPatchFilter (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (j : Fin m) :
    ContinuousOn (fun x ↦ regularizedPatchFilter (Out := Out) regions a b x j)
      (regularizedPatchDomain regions) := by
  classical
  exact (continuous_place (regions j)).comp_continuousOn
    ((Matrix.continuousOn_add_smul_one_rpow hb (-(a j) / 2)).comp
      (continuous_apply j).continuousOn fun x hx ↦ (hx j).1)

/-- The norm objective is continuous on the density-matrix feasible set. -/
theorem continuousOn_regularizedPatchObjective (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) :
    ContinuousOn (regularizedPatchObjective regions a b Ω) (regularizedPatchDomain regions) := by
  classical
  have hp : ContinuousOn (regularizedPatchOperator (Out := Out) regions a b)
      (regularizedPatchDomain regions) := by
    unfold regularizedPatchOperator
    simpa only [regularizedPatchOperator, List.map_reverse, List.map_ofFn,
      Function.id_def, Function.comp_def] using
      continuousOn_list_prod (List.ofFn (id : Fin m → Fin m)).reverse
        (fun j _ ↦ continuousOn_regularizedPatchFilter regions a hb j)
  have hc : Continuous (fun M : Matrix ((v : V) → Out v)
      ((v : V) → Out v) ℂ ↦ WithLp.toLp 2 (M *ᵥ Ω)) :=
    (PiLp.continuous_toLp _ _).comp (continuous_id.matrix_mulVec continuous_const)
  exact hc.norm.comp_continuousOn hp

/-- The feasible minimum exists; continuity and nonemptiness are proved,
not assumed. Source: OpenAI `03-patches.tex`, lines 68–99. -/
theorem exists_isMinOn_regularizedPatchObjective (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1) :
    ∃ x ∈ regularizedPatchDomain regions,
      IsMinOn (regularizedPatchObjective regions a b Ω) (regularizedPatchDomain regions) x :=
  (isCompact_regularizedPatchDomain regions).exists_isMinOn
    (regularizedPatchDomain_nonempty regions Ω hΩ)
    (continuousOn_regularizedPatchObjective regions a hb Ω)

/-- Every local filter has the stated upper and lower Euclidean bounds. The lower
bound uses cancellation with the positive power of the same shifted density. -/
theorem regularizedPatchFilter_norm_bounds (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (j : Fin m)
    (ξ : EuclideanSpace ℂ ((v : V) → Out v)) :
    (1 + b) ^ (-a j / 2) * ‖ξ‖ ≤
        ‖WithLp.toLp 2 (regularizedPatchFilter regions a b x j *ᵥ ξ)‖ ∧
      ‖WithLp.toLp 2 (regularizedPatchFilter regions a b x j *ᵥ ξ)‖ ≤
        b ^ (-a j / 2) * ‖ξ‖ := by
  classical
  have hd := (hx j).1.add_smul_one_posDef hb
  have hp := (hx j).1.l2_opNorm_add_smul_one_rpow_le_of_nonneg (hx j).2 hb
    (div_nonneg (ha j) (by norm_num) : 0 ≤ a j / 2)
  have hn := (hx j).1.l2_opNorm_add_smul_one_rpow_le_of_nonpos (hx j).2 hb
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (ha j)) (by norm_num) : -a j / 2 ≤ 0)
  have hcancel : ManyBody.place (regions j) ((x j + b • 1) ^ (a j / 2)) *
      regularizedPatchFilter regions a b x j = 1 := by
    rw [regularizedPatchFilter, ← ManyBody.place_mul,
      neg_div, CFC.rpow_mul_rpow_neg _ hd.isStrictlyPositive]
    exact ManyBody.place_one (X := Out)
  have hinv := (norm_place_mulVec_le (regions j)
    ((x j + b • 1) ^ (a j / 2))
    (WithLp.toLp 2 (regularizedPatchFilter regions a b x j *ᵥ ξ))).trans
      (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have heq : ManyBody.place (regions j) ((x j + b • 1) ^ (a j / 2)) *ᵥ
      (regularizedPatchFilter regions a b x j *ᵥ ξ) = ξ := by
    rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  change ‖WithLp.toLp 2 (ManyBody.place (regions j)
    ((x j + b • 1) ^ (a j / 2)) *ᵥ (regularizedPatchFilter regions a b x j *ᵥ ξ))‖ ≤ _ at hinv
  rw [heq] at hinv
  constructor
  · rw [neg_div, Real.rpow_neg (by positivity)]
    exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr hinv
  · exact (norm_place_mulVec_le (regions j) _ ξ).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

open Classical in
private theorem regularizedPatchProduct_norm_bounds (a : Fin m → ℝ)
    (ha : ∀ j, 0 ≤ a j) {b : ℝ} (hb : 0 < b)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (l : List (Fin m))
    (ξ : EuclideanSpace ℂ ((v : V) → Out v)) :
    (1 + b) ^ (l.map (fun j ↦ -a j / 2)).sum * ‖ξ‖ ≤
        ‖WithLp.toLp 2 ((l.map (regularizedPatchFilter regions a b x)).prod *ᵥ ξ)‖ ∧
      ‖WithLp.toLp 2 ((l.map (regularizedPatchFilter regions a b x)).prod *ᵥ ξ)‖ ≤
        b ^ (l.map (fun j ↦ -a j / 2)).sum * ‖ξ‖ := by
  classical
  induction l with
  | nil => simp
  | cons j l ih =>
    have hstep := regularizedPatchFilter_norm_bounds regions a ha hb hx j
      (WithLp.toLp 2 ((l.map (regularizedPatchFilter regions a b x)).prod *ᵥ ξ))
    simp only [List.map_cons, List.sum_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      Real.rpow_add (show 0 < 1 + b by positivity), Real.rpow_add hb, mul_assoc]
    constructor
    · exact (mul_le_mul_of_nonneg_left ih.1 (Real.rpow_nonneg (by positivity) _)).trans
        hstep.1
    · exact hstep.2.trans
        (mul_le_mul_of_nonneg_left ih.2 (Real.rpow_nonneg hb.le _))

/-- The elementary norm bounds hold for every feasible tuple, in the specified
order, including repeated regions and noncommuting filters.
Source: OpenAI `03-patches.tex`, lines 80–99. -/
theorem regularizedPatchObjective_bounds (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) :
    (1 + b) ^ (-(∑ j, a j) / 2) ≤ regularizedPatchObjective regions a b Ω x ∧
      regularizedPatchObjective regions a b Ω x ≤ b ^ (-(∑ j, a j) / 2) := by
  have h := regularizedPatchProduct_norm_bounds regions a ha hb hx
    (List.ofFn (id : Fin m → Fin m)).reverse Ω
  simpa only [List.map_reverse, List.map_ofFn, Function.comp_def, Function.id_def,
    List.sum_reverse, List.sum_ofFn, ← Finset.sum_div, ← Finset.sum_neg_distrib,
    hΩ, mul_one, regularizedPatchObjective, regularizedPatchOutput,
    regularizedPatchOperator] using h

/-- The common minimum value of the norm objective.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def regularizedPatchMinimum (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) : ℝ :=
  sInf (regularizedPatchObjective regions a b Ω '' regularizedPatchDomain regions)

/-- Every feasible minimizer has exactly the same minimum value. -/
theorem regularizedPatchObjective_eq_minimum (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v))
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions)
    (hmin : IsMinOn (regularizedPatchObjective regions a b Ω) (regularizedPatchDomain regions) x) :
    regularizedPatchObjective regions a b Ω x = regularizedPatchMinimum regions a b Ω := by
  apply Eq.symm
  apply IsLeast.csInf_eq
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hmin hy

/-- The attained minimum satisfies the same quantitative bounds as every feasible tuple. -/
theorem regularizedPatchMinimum_bounds (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1) :
    (1 + b) ^ (-(∑ j, a j) / 2) ≤ regularizedPatchMinimum regions a b Ω ∧
      regularizedPatchMinimum regions a b Ω ≤ b ^ (-(∑ j, a j) / 2) := by
  obtain ⟨x, hx, hmin⟩ := exists_isMinOn_regularizedPatchObjective regions a hb Ω hΩ
  rw [← regularizedPatchObjective_eq_minimum regions a b Ω hx hmin]
  exact regularizedPatchObjective_bounds regions a ha hb Ω hΩ hx

/-- Every feasible filtered output is nonzero, including outputs from singular densities. -/
theorem regularizedPatchObjective_pos (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) :
    0 < regularizedPatchObjective regions a b Ω x :=
  (Real.rpow_pos_of_pos (by positivity) _).trans_le
    (regularizedPatchObjective_bounds regions a ha hb Ω hΩ hx).1

/-- The minimum is strictly positive. -/
theorem regularizedPatchMinimum_pos (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1) :
    0 < regularizedPatchMinimum regions a b Ω :=
  (Real.rpow_pos_of_pos (by positivity) _).trans_le
    (regularizedPatchMinimum_bounds regions a ha hb Ω hΩ).1

/-- Normalize a filtered vector by its positive norm.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def normalizedRegularizedPatchOutput (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :
    EuclideanSpace ℂ ((v : V) → Out v) :=
  (regularizedPatchObjective regions a b Ω x)⁻¹ • regularizedPatchOutput regions a b Ω x

/-- Normalization gives a unit Euclidean vector for every feasible density tuple. -/
theorem norm_normalizedRegularizedPatchOutput (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) :
    ‖normalizedRegularizedPatchOutput regions a b Ω x‖ = 1 := by
  have hp := regularizedPatchObjective_pos regions a ha hb Ω hΩ hx
  rw [normalizedRegularizedPatchOutput, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  exact inv_mul_cancel₀ hp.ne'

/-- At every minimizer, normalization can equivalently use the common minimum value. -/
theorem normalizedRegularizedPatchOutput_eq_minimum_smul (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v))
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions)
    (hmin : IsMinOn (regularizedPatchObjective regions a b Ω) (regularizedPatchDomain regions) x) :
    normalizedRegularizedPatchOutput regions a b Ω x =
      (regularizedPatchMinimum regions a b Ω)⁻¹ • regularizedPatchOutput regions a b Ω x := by
  rw [normalizedRegularizedPatchOutput, regularizedPatchObjective_eq_minimum regions a b Ω hx hmin]

/-- The source regularization `b = exp(-R)` gives an exponential upper bound for
all feasible tuples, for every real `R`.
Source: OpenAI `03-patches.tex`, lines 80–99. -/
theorem regularizedPatchObjective_exp_bounds (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    (R : ℝ) (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) :
    (1 + Real.exp (-R)) ^ (-(∑ j, a j) / 2) ≤
        regularizedPatchObjective regions a (Real.exp (-R)) Ω x ∧
      regularizedPatchObjective regions a (Real.exp (-R)) Ω x ≤
        Real.exp (R * (∑ j, a j) / 2) := by
  have h := regularizedPatchObjective_bounds regions a ha (Real.exp_pos (-R)) Ω hΩ hx
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- For nonnegative regulator, the attained minimum has a uniform positive lower
bound and the source exponential upper bound. -/
theorem regularizedPatchMinimum_exp_bounds (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {R : ℝ} (hR : 0 ≤ R)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1) :
    (2 : ℝ) ^ (-(∑ j, a j) / 2) ≤ regularizedPatchMinimum regions a (Real.exp (-R)) Ω ∧
      regularizedPatchMinimum regions a (Real.exp (-R)) Ω ≤
        Real.exp (R * (∑ j, a j) / 2) := by
  obtain ⟨x, hx, hmin⟩ :=
    exists_isMinOn_regularizedPatchObjective regions a (Real.exp_pos (-R)) Ω hΩ
  rw [← regularizedPatchObjective_eq_minimum regions a (Real.exp (-R)) Ω hx hmin]
  have h := regularizedPatchObjective_exp_bounds regions a ha R Ω hΩ hx
  refine ⟨?_, h.2⟩
  apply le_trans ?_ h.1
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
  · have he : Real.exp (-R) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hR)
    linarith
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Finset.sum_nonneg fun j _ ↦ ha j))
      (by norm_num)

end TNLean.PEPS

end

section

open Set Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, DecidableEq (Out v)] [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

/-- Taking the logarithm preserves the attained norm minimum of the original
ordered regional filters. Source: OpenAI `03-patches.tex`, lines 425–451. -/
theorem isLeast_log_regularizedPatchObjective (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) (hΩ : ‖Ω‖ = 1) :
    IsLeast ((fun x ↦ Real.log (regularizedPatchObjective regions a b Ω x)) ''
      regularizedPatchDomain regions) (Real.log (regularizedPatchMinimum regions a b Ω)) :=
  match exists_isMinOn_regularizedPatchObjective regions a hb Ω hΩ with
  | ⟨x, hx, hmin⟩ =>
    ⟨⟨x, hx, congrArg Real.log (regularizedPatchObjective_eq_minimum regions a b Ω hx hmin)⟩,
      fun _ hy ↦
        match hy with
        | ⟨y, hy, heq⟩ =>
          (Real.log_le_log (regularizedPatchMinimum_pos regions a ha hb Ω hΩ)
            (calc
              regularizedPatchMinimum regions a b Ω = regularizedPatchObjective regions a b Ω x :=
                (regularizedPatchObjective_eq_minimum regions a b Ω hx hmin).symm
              _ ≤ regularizedPatchObjective regions a b Ω y := hmin hy)).trans_eq heq⟩

end TNLean.PEPS

end

end RegularizedPatchMinimum

section RegularizedPatchInverseCylinder

/-!
## Approximation by cylinders from ordered inverse filters

The inverse of the descending filter product is expanded in ascending order
according to the first factor contributing its spectral head. The preceding
tails act inside the current region, so their action does not increase the
inside dimension. The term containing only tails controls the approximation
error.

Source: OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
`03-patches.tex`, lines 484–532, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

/-- Expanding an ordered product according to its first head preserves the order
of every factor. The remaining term contains only tails.

Source: OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
`03-patches.tex`, lines 504–514, equation `eq:patch-first-head-expansion`. -/
private theorem prod_ofFn_add_eq_sum_first_head_add_prod
    {A : Type*} [Semiring A] {n : ℕ} (H T : Fin n → A) :
    (List.ofFn (fun j ↦ H j + T j)).prod =
      (∑ j : Fin n,
        ((List.ofFn T).take j.val).prod * H j *
          ((List.ofFn (fun i ↦ H i + T i)).drop (j.val + 1)).prod) +
        (List.ofFn T).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, Fin.val_zero,
      List.take_zero, List.prod_nil, one_mul, List.drop_succ_cons,
      List.drop_zero, Fin.val_succ, List.take_succ_cons]
    simpa only [add_mul, mul_add, Finset.mul_sum, mul_assoc, add_assoc] using
      congrArg (fun z ↦ H 0 * (List.ofFn fun i ↦ H i.succ + T i.succ).prod + T 0 * z)
        (ih (fun i ↦ H i.succ) (fun i ↦ T i.succ))

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, DecidableEq (Out v)] [∀ v, Fintype (Out v)] {m : ℕ}

/-- A feasible ordered filter tuple gives an approximation in a sum of regional
cylinders. Each inside dimension is at most the reciprocal spectral threshold.
The error is controlled by the norm of this same tuple's filtered output.

Source: OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
`03-patches.tex`, lines 484–532, equations `eq:patch-head-tail-bounds` and
`eq:patch-first-head-expansion`, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The assertion applies before minimizing the output norm. It includes repeated
regions, zero weights, singular densities, and an empty family of filters. -/
theorem exists_mem_iSup_dependentRegionCylinder_norm_sub_le
    (regions : Fin m → Finset V) (hregions : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v))
    (_hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((w : regions j) → Out w.1)
      ((w : regions j) → Out w.1) ℂ}
    (hx : x ∈ regularizedPatchDomain (Out := Out) regions) :
    ∃ (S : (j : Fin m) → Submodule ℂ (((w : regions j) → Out w.1) → ℂ))
      (v : EuclideanSpace ℂ ((v : V) → Out v)),
      (∀ j, (Module.finrank ℂ (S j) : ℝ) ≤ 1 / b) ∧
      (v : (((v : V) → Out v) → ℂ)) ∈
        (⨆ j, dependentRegionCylinder (Out := Out) (regions j) (S j)) ∧
      ‖Ω - v‖ ≤ regularizedPatchObjective regions a b Ω x *
        (2 * b) ^ ((∑ j, a j) / 2) := by
  classical
  let H (j : Fin m) := Matrix.shiftedPowerHead (x j) b (a j / 2)
  let T (j : Fin m) := Matrix.shiftedPowerTail (x j) b (a j / 2)
  let P (j : Fin m) :=
    (List.ofFn fun i : Fin j.val ↦
      ManyBody.subregionPlace
        (hregions (Fin.le_iff_val_le_val.mpr (Nat.le_of_lt i.isLt)))
        (T ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)).prod
  let S (j : Fin m) := ((P j * H j).mulVecLin).range
  have hS (j : Fin m) : (Module.finrank ℂ (S j) : ℝ) ≤ 1 / b :=
    (show ((P j * H j).rank : ℝ) ≤ (H j).rank from
      Nat.cast_le.mpr (Matrix.rank_mul_le_right (P j) (H j))).trans
        ((hx j).1.rank_shiftedPowerHead_le (hx j).2 hb (a j / 2))
  let lift (j : Fin m) :
      Matrix ((w : regions j) → Out w.1) ((w : regions j) → Out w.1) ℂ →*
        Matrix ((v : V) → Out v)
          ((v : V) → Out v) ℂ :=
    { toFun := ManyBody.place (X := Out) (regions j)
      map_one' := ManyBody.place_one (X := Out)
      map_mul' := fun K L ↦ ManyBody.place_mul (X := Out) K L }
  have hP (j : Fin m) : lift j (P j) =
      (List.ofFn fun i : Fin j.val ↦
        ManyBody.place (regions ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)
          (T ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)).prod := by
    simp only [P, map_list_prod, List.map_ofFn, Function.comp_def, lift,
      MonoidHom.coe_mk, OneHom.coe_mk, ManyBody.place_subregionPlace]
  have hrange (j : Fin m) : (lift j (P j * H j)).mulVecLin.range =
      dependentRegionCylinder (Out := Out) (regions j) (S j) :=
    range_place (Out := Out) (regions j) (P j * H j)
  have hcancel (j : Fin m) :
      ManyBody.place (X := Out) (regions j)
          ((x j + b • 1) ^ (a j / 2)) *
        regularizedPatchFilter regions a b x j = 1 := by
    rw [regularizedPatchFilter, ← ManyBody.place_mul, neg_div,
      (hx j).1.add_smul_one_rpow_mul_neg hb (a j / 2),
      ManyBody.place_one (X := Out)]
  let F (j : Fin m) := ManyBody.place (X := Out) (regions j)
    ((x j + b • 1) ^ (a j / 2))
  have hcancelList (l : List (Fin m)) : (l.map F).prod *
      ((l.map (regularizedPatchFilter regions a b x)).reverse).prod = 1 := by
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.reverse_cons, List.prod_cons, List.prod_append,
        List.prod_nil, mul_one]
      calc
        _ = F j * ((l.map F).prod *
            ((l.map (regularizedPatchFilter regions a b x)).reverse).prod) *
            regularizedPatchFilter regions a b x j := by simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hcancel]
  have hundo : (List.ofFn F).prod * regularizedPatchOperator regions a b x = 1 := by
    simpa only [List.ofFn_eq_map, regularizedPatchOperator] using
      hcancelList (List.finRange m)
  have hsplit (j : Fin m) : lift j (H j) + lift j (T j) = F j := by
    change ManyBody.place (X := Out) (regions j) (H j) +
      ManyBody.place (X := Out) (regions j) (T j) =
      ManyBody.place (X := Out) (regions j) _
    rw [← Matrix.shiftedPowerHead_add_shiftedPowerTail, ← eq_sub_iff_add_eq,
      ← ManyBody.place_sub, add_sub_cancel_right]
  have hexpand := prod_ofFn_add_eq_sum_first_head_add_prod
    (fun j ↦ lift j (H j)) (fun j ↦ lift j (T j))
  simp only [hsplit] at hexpand
  have hPtake (j : Fin m) :
      ((List.ofFn fun i ↦ lift i (T i)).take j.val).prod = lift j (P j) := by
    rw [hP]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_take, List.getElem_ofFn]
      rfl
  let G (j : Fin m) := lift j (P j * H j) *
    ((List.ofFn F).drop (j.val + 1)).prod
  have hsum : (List.ofFn F).prod = (∑ j, G j) +
      (List.ofFn fun j ↦ lift j (T j)).prod := by
    simpa only [G, hPtake, map_mul] using hexpand
  let ξ := regularizedPatchOutput regions a b Ω x
  let v : EuclideanSpace ℂ ((v : V) → Out v) :=
    WithLp.toLp 2 ((∑ j, G j) *ᵥ ξ)
  have hv : (v : (((v : V) → Out v) → ℂ)) ∈
      (⨆ j, dependentRegionCylinder (Out := Out) (regions j) (S j)) := by
    change ((∑ j, G j) *ᵥ ξ) ∈ _
    rw [Matrix.sum_mulVec]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.mem_iSup_of_mem j
    rw [← hrange]
    refine ⟨((List.ofFn F).drop (j.val + 1)).prod *ᵥ ξ, ?_⟩
    exact Matrix.mulVec_mulVec _ _ _
  have hrecover : (Ω : _ → ℂ) = (List.ofFn F).prod *ᵥ ξ := by
    change (Ω : _ → ℂ) = (List.ofFn F).prod *ᵥ
      (regularizedPatchOperator regions a b x *ᵥ Ω)
    rw [Matrix.mulVec_mulVec, hundo, Matrix.one_mulVec]
  have herr : Ω - v = WithLp.toLp 2
      ((List.ofFn fun j ↦ lift j (T j)).prod *ᵥ ξ) := by
    rw [hsum, Matrix.add_mulVec, add_comm] at hrecover
    ext η
    exact congrFun (sub_eq_iff_eq_add.mpr hrecover) η
  have hT (j : Fin m)
      (ζ : EuclideanSpace ℂ ((v : V) → Out v)) :
      ‖WithLp.toLp 2 (lift j (T j) *ᵥ ζ)‖ ≤ (2 * b) ^ (a j / 2) * ‖ζ‖ :=
    (norm_place_mulVec_le (regions j) (T j) ζ).trans
      (mul_le_mul_of_nonneg_right
        ((hx j).1.l2_opNorm_shiftedPowerTail_le hb (div_nonneg (ha j) (by positivity)))
        (norm_nonneg ζ))
  have htail (l : List (Fin m))
      (ζ : EuclideanSpace ℂ ((v : V) → Out v)) :
      ‖WithLp.toLp 2 ((l.map fun j ↦ lift j (T j)).prod *ᵥ ζ)‖ ≤
        (l.map fun j ↦ (2 * b) ^ (a j / 2)).prod * ‖ζ‖ := by
    induction l generalizing ζ with
    | nil => simp
    | cons j l ih =>
      calc
        _ ≤ (2 * b) ^ (a j / 2) *
            ‖WithLp.toLp 2 ((l.map fun i ↦ lift i (T i)).prod *ᵥ ζ)‖ := by
          simpa only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
            WithLp.ofLp_toLp] using
            hT j (WithLp.toLp 2 ((l.map fun i ↦ lift i (T i)).prod *ᵥ ζ))
        _ ≤ (2 * b) ^ (a j / 2) *
            ((l.map fun i ↦ (2 * b) ^ (a i / 2)).prod * ‖ζ‖) :=
          mul_le_mul_of_nonneg_left (ih ζ) (Real.rpow_nonneg (by positivity) _)
        _ = _ := by simp only [List.map_cons, List.prod_cons, mul_assoc]
  refine ⟨S, v, hS, hv, ?_⟩
  rw [herr]
  have ht := htail (List.finRange m) ξ
  simp only [← List.ofFn_eq_map, List.prod_ofFn] at ht
  rw [← Real.rpow_sum_of_pos (show 0 < 2 * b by positivity), ← Finset.sum_div] at ht
  simpa only [regularizedPatchObjective, ξ, mul_comm] using ht

end TNLean.PEPS

end RegularizedPatchInverseCylinder

section RegularizedPatchMinimumContinuity

/-!
## Continuity of the regularized patch minimum

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
variable {Out : V → Type*} [∀ v, DecidableEq (Out v)] [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

/-- The original regularized norm minimum is continuous in the radius, for
arbitrary real weights and input vector. Compactness of the same feasible set
replaces any choice of a continuous family of minimizers.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 421–451. -/
theorem continuous_regularizedPatchMinimum_exp_neg (a : Fin m → ℝ)
    (Ω : EuclideanSpace ℂ ((v : V) → Out v)) :
    Continuous (fun R : ℝ ↦ regularizedPatchMinimum regions a (Real.exp (-R)) Ω) := by
  classical
  let K := ↥(regularizedPatchDomain (Out := Out) regions)
  let : CompactSpace K :=
    isCompact_iff_compactSpace.mp (isCompact_regularizedPatchDomain regions)
  have hfilter (j : Fin m) :
      Continuous (fun z : ℝ × K ↦
        regularizedPatchFilter regions a (Real.exp (-z.1)) z.2.val j) := by
    have hshift : Continuous (fun z : ℝ × K ↦
        z.2.val j + Real.exp (-z.1) •
          (1 : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)) :=
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)).add
        ((Real.continuous_exp.comp continuous_fst.neg).smul continuous_const)
    exact (continuous_place (regions j)).comp
      ((CFC.continuousOn_rpow (-(a j) / 2)).comp_continuous hshift fun z ↦
        ((z.2.property j).1.add_smul_one_posDef (Real.exp_pos (-z.1))).isStrictlyPositive)
  have hoperator : Continuous (fun z : ℝ × K ↦
      regularizedPatchOperator regions a (Real.exp (-z.1)) z.2.val) := by
    simpa only [regularizedPatchOperator, List.map_reverse, List.map_ofFn,
      Function.id_def, Function.comp_def] using
      continuous_list_prod (List.ofFn (id : Fin m → Fin m)).reverse
        (fun j _ ↦ hfilter j)
  have heval : Continuous (fun M : Matrix ((v : V) → Out v)
      ((v : V) → Out v) ℂ ↦ WithLp.toLp 2 (M *ᵥ Ω)) :=
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
    (Ω : EuclideanSpace ℂ ((v : V) → Out v))
    (hΩ : ‖Ω‖ = 1) :
    Continuous (fun R : ℝ ↦ Real.log
      (regularizedPatchMinimum regions a (Real.exp (-R)) Ω)) :=
  (continuous_regularizedPatchMinimum_exp_neg regions a Ω).log fun R ↦
    (regularizedPatchMinimum_pos regions a ha (Real.exp_pos (-R)) Ω hΩ).ne'

end TNLean.PEPS

end RegularizedPatchMinimumContinuity
