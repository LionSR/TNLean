/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.DependentRegionOperatorLift
import QICLean.Analysis.ShiftedDensityPowers
import QICLean.Analysis.MatrixFramePerturbation
import Mathlib.Topology.Order.Compact

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
-/

/-
Source: September 24, 2026, 03-patches.tex, lines 51–114.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex
sec:patches, prop:patch, eq:patch-variational-problem, eq:patch-elementary-norm-bounds.
Independently formalized; no upstream Lean proof text reused.
Manuscript commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The results here concern the regularized finite-dimensional minimum only.
They do not include stationarity, energy estimates or the full Proposition 4.1.
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.norm_dependentregionoperatorlift_mulvec_le
Downstream declaration: TNLean.PEPS.norm_dependentRegionOperatorLift_mulVec_le
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.continuous_dependentregionoperatorlift
Downstream declaration: TNLean.PEPS.continuous_dependentRegionOperatorLift
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchdomain
Downstream declaration: TNLean.PEPS.regularizedPatchDomain
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchfilter
Downstream declaration: TNLean.PEPS.regularizedPatchFilter
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchoperator
Downstream declaration: TNLean.PEPS.regularizedPatchOperator
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchoutput
Downstream declaration: TNLean.PEPS.regularizedPatchOutput
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchobjective
Downstream declaration: TNLean.PEPS.regularizedPatchObjective
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.iscompact_regularizedpatchdomain
Downstream declaration: TNLean.PEPS.isCompact_regularizedPatchDomain
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchdomain_nonempty
Downstream declaration: TNLean.PEPS.regularizedPatchDomain_nonempty
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.continuouson_regularizedpatchfilter
Downstream declaration: TNLean.PEPS.continuousOn_regularizedPatchFilter
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.continuouson_regularizedpatchobjective
Downstream declaration: TNLean.PEPS.continuousOn_regularizedPatchObjective
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.exists_isminon_regularizedpatchobjective
Downstream declaration: TNLean.PEPS.exists_isMinOn_regularizedPatchObjective
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchfilter_norm_bounds
Downstream declaration: TNLean.PEPS.regularizedPatchFilter_norm_bounds
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchobjective_bounds
Downstream declaration: TNLean.PEPS.regularizedPatchObjective_bounds
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchminimum
Downstream declaration: TNLean.PEPS.regularizedPatchMinimum
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchobjective_eq_minimum
Downstream declaration: TNLean.PEPS.regularizedPatchObjective_eq_minimum
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchminimum_bounds
Downstream declaration: TNLean.PEPS.regularizedPatchMinimum_bounds
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchobjective_pos
Downstream declaration: TNLean.PEPS.regularizedPatchObjective_pos
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchminimum_pos
Downstream declaration: TNLean.PEPS.regularizedPatchMinimum_pos
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.normalizedregularizedpatchoutput
Downstream declaration: TNLean.PEPS.normalizedRegularizedPatchOutput
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.norm_normalizedregularizedpatchoutput
Downstream declaration: TNLean.PEPS.norm_normalizedRegularizedPatchOutput
Provenance-ID: regularizedpatchminimum8767-normalized-output-minimum-smul
Downstream declaration: TNLean.PEPS.normalizedRegularizedPatchOutput_eq_minimum_smul
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchobjective_exp_bounds
Downstream declaration: TNLean.PEPS.regularizedPatchObjective_exp_bounds
Provenance-ID: regularizedpatchminimum8767-tnlean.peps.regularizedpatchminimum_exp_bounds
Downstream declaration: TNLean.PEPS.regularizedPatchMinimum_exp_bounds
-/

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]

open Classical in
/-- The existing regional lift obeys its local Euclidean operator bound. -/
theorem norm_dependentRegionOperatorLift_mulVec_le (R : Finset V)
    (K : Matrix ((v : R) → Out v.1)
      ((v : R) → Out v.1) ℂ)
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
    ‖WithLp.toLp 2 (dependentRegionOperatorLift R K *ᵥ ξ)‖ ≤ ‖K‖ * ‖ξ‖ := by
  classical
  let e := dependentRegionConfigEquiv (Out := Out) R
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  have hmul : E (WithLp.toLp 2 (dependentRegionOperatorLift R K *ᵥ ξ)) =
      WithLp.toLp 2 ((K ⊗ₖ 1) *ᵥ E ξ) := by
    ext p
    change (dependentRegionOperatorLift R K *ᵥ ξ) (e.symm p) = _
    simp only [dependentRegionOperatorLift, Matrix.reindex_apply, Matrix.mulVec,
      dotProduct, Equiv.symm_symm]
    rw [← e.symm.sum_comp]
    simp [E, e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  rw [← E.norm_map, hmul]
  exact (Matrix.l2_opNorm_kronecker_one_mulVec_le K (E ξ)).trans_eq
    (congrArg (‖K‖ * ·) (E.norm_map ξ))

omit [∀ v, Fintype (Out v)] in
/-- Lifting regional matrices is continuous. -/
theorem continuous_dependentRegionOperatorLift (R : Finset V) :
    Continuous (dependentRegionOperatorLift (Out := Out) R) := by
  classical
  unfold dependentRegionOperatorLift
  exact (continuous_id.matrix_kronecker continuous_const).matrix_reindex _ _

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
    Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
      ((v : (Finset.univ : Finset V)) → Out v.1) ℂ := by
  classical
  exact dependentRegionOperatorLift (regions j) ((x j + b • 1) ^ (-(a j) / 2))

/-- The ordered matrix product `L_(m-1) ⋯ L_0`.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def regularizedPatchOperator (a : Fin m → ℝ) (b : ℝ)
    (x : ∀ j, Matrix ((v : regions j) → Out v.1)
      ((v : regions j) → Out v.1) ℂ) :
    Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
      ((v : (Finset.univ : Finset V)) → Out v.1) ℂ := by
  classical
  exact ((List.ofFn fun j ↦ regularizedPatchFilter regions a b x j).reverse).prod

/-- The filtered vector in the Euclidean configuration space.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def regularizedPatchOutput (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1)
      ((v : regions j) → Out v.1) ℂ) :
    EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1) :=
  WithLp.toLp 2 (regularizedPatchOperator regions a b x *ᵥ Ω)

/-- The norm minimized over independent regional densities.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def regularizedPatchObjective (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1)
      ((v : regions j) → Out v.1) ℂ) : ℝ :=
  ‖regularizedPatchOutput regions a b Ω x‖

omit [Fintype V] in
/-- The feasible space of independent regional densities is compact. -/
theorem isCompact_regularizedPatchDomain :
    IsCompact (regularizedPatchDomain (Out := Out) regions) :=
  isCompact_pi_infinite fun _ ↦ Matrix.isCompact_setOf_posSemidef_trace_eq_one

/-- A unit global vector supplies a configuration in every region, so the
feasible space is nonempty without an extra local-dimension hypothesis. -/
theorem regularizedPatchDomain_nonempty
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1) :
    (regularizedPatchDomain (Out := Out) regions).Nonempty := by
  have hΩne : Ω ≠ 0 := by
    exact norm_ne_zero_iff.mp (hΩ.trans_ne one_ne_zero)
  obtain ⟨σ, _⟩ := Function.ne_iff.mp (show (Ω : _ → ℂ) ≠ 0 from by
    intro h; apply hΩne; simpa using congrArg (WithLp.toLp 2) h)
  have hn (j : Fin m) : Nonempty ((v : regions j) → Out v.1) :=
    ⟨fun v ↦ σ ⟨v.1, Finset.mem_univ _⟩⟩
  choose x hx using fun j ↦ @Matrix.setOf_posSemidef_trace_eq_one_nonempty
    ((v : regions j) → Out v.1) inferInstance (hn j)
  exact ⟨x, hx⟩


/-- Each full-space regularized regional filter depends continuously on all densities. -/
theorem continuousOn_regularizedPatchFilter (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (j : Fin m) :
    ContinuousOn (fun x ↦ regularizedPatchFilter (Out := Out) regions a b x j)
      (regularizedPatchDomain regions) := by
  classical
  exact (continuous_dependentRegionOperatorLift (regions j)).comp_continuousOn
    ((Matrix.continuousOn_add_smul_one_rpow hb (-(a j) / 2)).comp
      (continuous_apply j).continuousOn fun x hx ↦ (hx j).1)

/-- The norm objective is continuous on the density-matrix feasible set. -/
theorem continuousOn_regularizedPatchObjective (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
    ContinuousOn (regularizedPatchObjective regions a b Ω) (regularizedPatchDomain regions) := by
  classical
  have hp : ContinuousOn (regularizedPatchOperator (Out := Out) regions a b)
      (regularizedPatchDomain regions) := by
    unfold regularizedPatchOperator
    simpa only [regularizedPatchOperator, List.map_reverse, List.map_ofFn,
      Function.id_def, Function.comp_def] using
      continuousOn_list_prod (List.ofFn (id : Fin m → Fin m)).reverse
        (fun j _ ↦ continuousOn_regularizedPatchFilter regions a hb j)
  have hc : Continuous (fun M : Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
      ((v : (Finset.univ : Finset V)) → Out v.1) ℂ ↦ WithLp.toLp 2 (M *ᵥ Ω)) :=
    (PiLp.continuous_toLp _ _).comp (continuous_id.matrix_mulVec continuous_const)
  exact hc.norm.comp_continuousOn hp

/-- The feasible minimum exists; continuity and nonemptiness are proved,
not assumed. Source: OpenAI `03-patches.tex`, lines 68–99. -/
theorem exists_isMinOn_regularizedPatchObjective (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1) :
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
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
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
  have hcancel : dependentRegionOperatorLift (regions j) ((x j + b • 1) ^ (a j / 2)) *
      regularizedPatchFilter regions a b x j = 1 := by
    rw [regularizedPatchFilter, ← dependentRegionOperatorLift_mul,
      neg_div, CFC.rpow_mul_rpow_neg _ hd.isStrictlyPositive]
    exact dependentRegionOperatorLift_one (Out := Out) _
  have hinv := (norm_dependentRegionOperatorLift_mulVec_le (regions j)
    ((x j + b • 1) ^ (a j / 2))
    (WithLp.toLp 2 (regularizedPatchFilter regions a b x j *ᵥ ξ))).trans
      (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have heq : dependentRegionOperatorLift (regions j) ((x j + b • 1) ^ (a j / 2)) *ᵥ
      (regularizedPatchFilter regions a b x j *ᵥ ξ) = ξ := by
    rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  change ‖WithLp.toLp 2 (dependentRegionOperatorLift (regions j)
    ((x j + b • 1) ^ (a j / 2)) *ᵥ (regularizedPatchFilter regions a b x j *ᵥ ξ))‖ ≤ _ at hinv
  rw [heq] at hinv
  constructor
  · rw [neg_div, Real.rpow_neg (by positivity)]
    exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr hinv
  · exact (norm_dependentRegionOperatorLift_mulVec_le (regions j) _ ξ).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

open Classical in
private theorem regularizedPatchProduct_norm_bounds (a : Fin m → ℝ)
    (ha : ∀ j, 0 ≤ a j) {b : ℝ} (hb : 0 < b)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (l : List (Fin m))
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
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
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1)
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
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) : ℝ :=
  sInf (regularizedPatchObjective regions a b Ω '' regularizedPatchDomain regions)

/-- Every feasible minimizer has exactly the same minimum value. -/
theorem regularizedPatchObjective_eq_minimum (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
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
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1) :
    (1 + b) ^ (-(∑ j, a j) / 2) ≤ regularizedPatchMinimum regions a b Ω ∧
      regularizedPatchMinimum regions a b Ω ≤ b ^ (-(∑ j, a j) / 2) := by
  obtain ⟨x, hx, hmin⟩ := exists_isMinOn_regularizedPatchObjective regions a hb Ω hΩ
  rw [← regularizedPatchObjective_eq_minimum regions a b Ω hx hmin]
  exact regularizedPatchObjective_bounds regions a ha hb Ω hΩ hx

/-- Every feasible filtered output is nonzero, including outputs from singular densities. -/
theorem regularizedPatchObjective_pos (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) :
    0 < regularizedPatchObjective regions a b Ω x :=
  (Real.rpow_pos_of_pos (by positivity) _).trans_le
    (regularizedPatchObjective_bounds regions a ha hb Ω hΩ hx).1

/-- The minimum is strictly positive. -/
theorem regularizedPatchMinimum_pos (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1) :
    0 < regularizedPatchMinimum regions a b Ω :=
  (Real.rpow_pos_of_pos (by positivity) _).trans_le
    (regularizedPatchMinimum_bounds regions a ha hb Ω hΩ).1

/-- Normalize a filtered vector by its positive norm.
Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def normalizedRegularizedPatchOutput (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :
    EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1) :=
  (regularizedPatchObjective regions a b Ω x)⁻¹ • regularizedPatchOutput regions a b Ω x

/-- Normalization gives a unit Euclidean vector for every feasible density tuple. -/
theorem norm_normalizedRegularizedPatchOutput (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) :
    ‖normalizedRegularizedPatchOutput regions a b Ω x‖ = 1 := by
  have hp := regularizedPatchObjective_pos regions a ha hb Ω hΩ hx
  rw [normalizedRegularizedPatchOutput, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  exact inv_mul_cancel₀ hp.ne'

/-- At every minimizer, normalization can equivalently use the common minimum value. -/
theorem normalizedRegularizedPatchOutput_eq_minimum_smul (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
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
    (R : ℝ) (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1)
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
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1) :
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
