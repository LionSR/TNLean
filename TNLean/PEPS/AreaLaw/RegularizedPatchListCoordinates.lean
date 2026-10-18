/- Private diagnostic using the exact public patch definitions. -/
import TNLean.PEPS.AreaLaw.RegularizedPatchStationarity
import TNLean.PEPS.AreaLaw.RegularizedPatchMarginal
import TNLean.PEPS.AreaLaw.Geometry.NestedPatches
import QICLean.Entropy.FilterStationarity
import QICLean.Analysis.ShiftedDensityCommutation
import QICLean.Analysis.OperatorMean.MatrixPowers

open Complex Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- A factor of the ordered patch objective: a region, a positive exponent, and a matrix on the
region. PEPS manuscript, `03-patches.tex`, `eq:patch-variational-problem`. -/
structure PatchFactor (n : V → ℕ) where
  /-- The region `X_j`. -/
  region : Finset V
  /-- The exponent `a_j`. -/
  exponent : ℝ
  /-- The variable `x_j`, a density matrix at feasible points. -/
  density : Matrix (RegionConfig n region) (RegionConfig n region) ℂ

/-- The regularized filter `L_j = (x_j + b 1)^{-a_j/2}` of a factor, as a regional filter. -/
noncomputable def PatchFactor.filter (b : ℝ) (f : PatchFactor n) : RegionFilter n :=
  ⟨f.region, (f.density + b • 1) ^ (-f.exponent / 2)⟩

/-- The output `L_m ⋯ L_1 Ω` of an ordered list of factors; the head of the list is applied
last. PEPS manuscript, `03-patches.tex`, `eq:patch-variational-problem`. -/
noncomputable def patchOutput (b : ℝ) (l : List (PatchFactor n))
    (Ω : EuclideanSpace ℂ (SiteConfig n)) : EuclideanSpace ℂ (SiteConfig n) :=
  toEuclideanLin (liftProd (l.map (PatchFactor.filter b))) Ω

/-- The normalized output `φ = L_m ⋯ L_1 Ω / ‖L_m ⋯ L_1 Ω‖` (zero if the output vanishes). -/
noncomputable def patchState (b : ℝ) (l : List (PatchFactor n))
    (Ω : EuclideanSpace ℂ (SiteConfig n)) : EuclideanSpace ℂ (SiteConfig n) :=
  ((‖patchOutput b l Ω‖⁻¹ : ℝ) : ℂ) • patchOutput b l Ω

/-- `l` minimizes the ordered patch objective among lists with the same regions and exponents
whose matrices are density matrices. PEPS manuscript, `03-patches.tex`,
`eq:patch-variational-problem`. -/
def IsPatchMinimizer (b : ℝ) (l : List (PatchFactor n)) (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    Prop :=
  ∀ l' : List (PatchFactor n), l'.map PatchFactor.region = l.map PatchFactor.region →
    l'.map PatchFactor.exponent = l.map PatchFactor.exponent →
    (∀ f ∈ l', f.density.PosSemidef ∧ f.density.trace = 1) →
    ‖patchOutput b l Ω‖ ≤ ‖patchOutput b l' Ω‖

end Entropy

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- The factors in the order in which their matrices occur in the patch
operator, with the outermost factor first.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99,
`eq:patch-variational-problem`. -/
def regularizedPatchFactorList (regions : Fin m → Finset V) (a : Fin m → ℝ)
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ) : List (Entropy.PatchFactor n) :=
  (List.ofFn fun j ↦ ⟨regions j, a j, x j⟩).reverse

/-- The canonical configuration identification takes the ordered native output
to the ordered patch-list output.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99. -/
theorem dependentGlobalConfigIsometry_regularizedPatchOutput
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ) :
    dependentGlobalConfigIsometry
        (regularizedPatchOutput (Out := fun v ↦ Fin (n v)) regions a b Ω x) =
      Entropy.patchOutput b (regularizedPatchFactorList regions a x)
        (dependentGlobalConfigIsometry Ω) := by
  classical
  have hL (j : Fin m) :
      Matrix.reindex (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
          (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
          (regularizedPatchFilter (Out := fun v ↦ Fin (n v)) regions a b x j) =
        Entropy.localLift (regions j)
          (Entropy.PatchFactor.filter b ⟨regions j, a j, x j⟩).2 := by
    unfold regularizedPatchFilter Entropy.PatchFactor.filter
    convert! reindex_dependentRegionOperatorLift (fun v ↦ Equiv.refl (Fin (n v)))
      (regions j) ((x j + b • 1) ^ (-(a j) / 2)) using 1
    have hp (d₁ d₂ : DecidableEq (Entropy.RegionConfig n (regions j))) :
        (letI := d₁; (x j + b • 1) ^ (-(a j) / 2)) =
          (letI := d₂; (x j + b • 1) ^ (-(a j) / 2)) := by
      exact congrArg
        (fun d : DecidableEq (Entropy.RegionConfig n (regions j)) ↦
          letI := d; (x j + b • 1) ^ (-(a j) / 2)) (Subsingleton.elim d₁ d₂)
    apply congrArg (fun K : Matrix (Entropy.RegionConfig n (regions j))
        (Entropy.RegionConfig n (regions j)) ℂ ↦
      Matrix.reindex (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
        (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
        (dependentRegionOperatorLift (Out := fun v ↦ Fin (n v)) (regions j) K))
    exact hp _ _
  have hprod :
      Matrix.reindexAlgEquiv ℂ ℂ (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v)))
          (regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x) =
        Entropy.liftProd ((regularizedPatchFactorList regions a x).map
          (Entropy.PatchFactor.filter b)) := by
    let : DecidableEq ((v : (Finset.univ : Finset V)) → Fin (n v.1)) :=
      @Fintype.decidablePiFintype (Finset.univ : Finset V)
        (fun v ↦ Fin (n v.1))
        (fun _ u w ↦ Classical.propDecidable (u = w)) inferInstance
    simpa only [regularizedPatchOperator, Entropy.liftProd, regularizedPatchFactorList,
      List.map_reverse, List.map_ofFn, Function.comp_def, Matrix.coe_reindexAlgEquiv, hL,
      Entropy.PatchFactor.filter] using
      map_list_prod (Matrix.reindexAlgEquiv ℂ ℂ
        (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))))
        ((List.ofFn fun j ↦ regularizedPatchFilter (Out := fun v ↦ Fin (n v))
          regions a b x j).reverse)
  rw [regularizedPatchOutput, Entropy.patchOutput, ← hprod]
  ext σ
  change (regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x *ᵥ Ω)
      ((dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm σ) =
    ((regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x).submatrix
        (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm
        (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm *ᵥ
      (fun τ ↦ Ω ((dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm τ))) σ
  simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using
    (congrFun (Matrix.submatrix_mulVec_equiv
      (regularizedPatchOperator (Out := fun v ↦ Fin (n v)) regions a b x)
      (fun τ ↦ Ω ((dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm τ))
      (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm
      (dependentGlobalConfigEquiv (Out := fun v ↦ Fin (n v))).symm) σ).symm

/-- The two ordered patch objectives have the same value.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 68–99,
`eq:patch-variational-problem`. -/
theorem regularizedPatchObjective_eq_norm_patchOutput
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ) :
    regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω x =
      ‖Entropy.patchOutput b (regularizedPatchFactorList regions a x)
        (dependentGlobalConfigIsometry Ω)‖ := by
  simpa only [regularizedPatchObjective, LinearIsometryEquiv.norm_map] using
    congrArg norm (dependentGlobalConfigIsometry_regularizedPatchOutput regions a b Ω x)

/-- A minimum of the ordered patch objective over independent regional density
matrices also minimizes the norm among all patch lists with the same positional
regions and exponents. Repeated regions retain independent density matrices.
No feasibility or nonvanishing condition on the distinguished tuple is needed
for this comparison statement.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 68–99 and 130–205,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`;
`Entropy.IsPatchMinimizer` and `Entropy.patch_stationarity` at QICLean
`5f76b263e3a1c418645102d90f7bef6b92f04cf3` (unchanged at `e44381d9`). -/
theorem isPatchMinimizer_regularizedPatchFactorList
    (regions : Fin m → Finset V) (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (x : ∀ j, Matrix (Entropy.RegionConfig n (regions j))
      (Entropy.RegionConfig n (regions j)) ℂ)
    (hmin : IsMinOn
      (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a b Ω)
      (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x) :
    Entropy.IsPatchMinimizer b (regularizedPatchFactorList regions a x)
      (dependentGlobalConfigIsometry Ω) := by
  intro l' hregions hexponents hfeasible
  obtain ⟨⟨r, g⟩, hg⟩ := List.equivSigmaTuple.symm.surjective l'.reverse
  change List.ofFn g = l'.reverse at hg
  have hl : (List.ofFn g).reverse = l' := by
    simpa only [List.reverse_reverse] using congrArg List.reverse hg
  subst l'
  have hr : r = m := by
    simpa only [regularizedPatchFactorList, List.length_map, List.length_reverse,
      List.length_ofFn] using congrArg List.length hregions
  subst r
  have hR : (fun j ↦ (g j).region) = regions := List.ofFn_injective <| by
    simpa only [regularizedPatchFactorList, List.map_reverse, List.reverse_reverse,
      List.map_ofFn, Function.comp_def] using congrArg List.reverse hregions
  have ha : (fun j ↦ (g j).exponent) = a := List.ofFn_injective <| by
    simpa only [regularizedPatchFactorList, List.map_reverse, List.reverse_reverse,
      List.map_ofFn, Function.comp_def] using congrArg List.reverse hexponents
  subst regions
  subst a
  have hf : regularizedPatchFactorList (fun j ↦ (g j).region)
      (fun j ↦ (g j).exponent) (fun j ↦ (g j).density) = (List.ofFn g).reverse := rfl
  rw [← hf, ← regularizedPatchObjective_eq_norm_patchOutput,
    ← regularizedPatchObjective_eq_norm_patchOutput]
  apply hmin
  intro j
  exact hfeasible (g j) (List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩))

#print axioms isPatchMinimizer_regularizedPatchFactorList

end TNLean.PEPS
