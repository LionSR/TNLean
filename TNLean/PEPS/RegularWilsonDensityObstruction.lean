/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCycleFluxMeasurement
import TNLean.PEPS.RegularPhysicalCutColumnAction
import TNLean.PEPS.RegularTwistedStateNonzero
import TNLean.PEPS.TorusNativeFluxHolonomy
import TNLean.PEPS.RegionBlock.AbsorbedEquality

/-!
# Closed-walk holonomy obstructs equality of observed densities

On any connected physical observation region, the existing complete
closed-walk measurement distinguishes actual regular insertions with
different holonomy conjugacy classes. Its action on every open boundary
column passes to the actual closed coefficient cut. A projector retaining
one nonzero cut and annihilating the other forces their trace-normalized
row Grams to differ. Both cuts are derived nonzero.

This gives a physical Wilson-loop obstruction relevant to annular
observations in SCP10, arXiv:1001.3807v3, Lemma 6.14 and Theorem 6.15,
lines 2199–2267. It assumes an actual observed closed walk with different
computed holonomy classes; it does not infer such a walk from endpoint
exclusion, classify annular geometry or assert the converse.
See `docs/paper-gaps/scp10_wilson_density_obstruction.tex`.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace TNLean.PEPS

private theorem normalized_gram_ne_of_left_action
    {P Q : Type*} [Fintype P] [Fintype Q]
    (M N : Matrix P Q ℂ) (L : Matrix P P ℂ)
    (hM : M ≠ 0) (hLM : L * M = M) (hLN : L * N = 0) :
    (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) ≠
      (N * N.conjTranspose).trace⁻¹ • (N * N.conjTranspose) := by
  have ht : (M * M.conjTranspose).trace ≠ 0 :=
    mt Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hM
  intro he
  have h := congrArg (fun K => L * K) he
  rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hLM, hLN, Matrix.zero_mul, smul_zero] at h
  have hz := (smul_eq_zero.mp h).resolve_left (inv_ne_zero ht)
  exact hM (Matrix.self_mul_conjTranspose_eq_zero.mp hz)

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

omit [DecidableEq G] in
private theorem cut_ne_zero
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V) (u : Edge Γ → G) :
    regularPhysicalCutMatrix (regularTwistedSite a u) R ≠ 0 := by
  intro hz
  apply stateCoeff_regularTwistedSite_ne_zero_of_isGInjective a
    (fun v => (ha v).toIsGInjective) u
  funext σ
  have h := congrFun (congrFun hz (fun v => σ v.1)) (fun v => σ v.1)
  simpa only [regularPhysicalCutMatrix, assembleRegionσ_restrict,
    Matrix.zero_apply, Pi.zero_apply] using h

omit [DecidableEq G] in
/-- Different conjugacy classes of holonomy on an actual observed closed
walk force different normalized observed densities of the actual regular
PEPS cuts. Both cuts are derived nonzero. The region need only be connected;
neither its complement nor its closed-cell realization is restricted.
Source: SCP10, physical flux detection in Theorem 6.15. -/
theorem regularPhysicalCutMatrix_normalized_reduced_ne_of_closedWalk_holonomy
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (o : {v : V // v ∈ R}) (p : (Γ.induce (R : Set V)).Walk o o)
    (u v : Edge Γ → G)
    (hc : ConjClasses.mk (regularWalkHolonomy (regularRegionInternalOperators R u) p) ≠
      ConjClasses.mk (regularWalkHolonomy (regularRegionInternalOperators R v) p)) :
    let M := regularPhysicalCutMatrix (regularTwistedSite a u) R
    let N := regularPhysicalCutMatrix (regularTwistedSite a v) R
    M ≠ 0 ∧ N ≠ 0 ∧
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) ≠
        (N * N.conjTranspose).trace⁻¹ • (N * N.conjTranspose) := by
  classical
  obtain ⟨Q, _, _, _, hQ⟩ := exists_regularClosedWalkClass_physicalMeasurement a ha R hR o p
  let C := some (ConjClasses.mk (regularWalkHolonomy (regularRegionInternalOperators R u) p))
  have hu : Q C * regularPhysicalCutMatrix (regularTwistedSite a u) R =
      regularPhysicalCutMatrix (regularTwistedSite a u) R := by
    have h := mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen
      (regularTwistedSite a u) R (Q C) _ (fun θ => hQ u θ C)
    simpa only [C, ite_true] using h
  have hv : Q C * regularPhysicalCutMatrix (regularTwistedSite a v) R = 0 := by
    have h := mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen
      (regularTwistedSite a v) R (Q C) _ (fun θ => hQ v θ C)
    simpa only [C, Option.some.injEq, ite_eq_right hc] using h
  exact ⟨cut_ne_zero a ha R u, cut_ne_zero a ha R v,
    normalized_gram_ne_of_left_action _ _ (Q C) (cut_ne_zero a ha R u) hu hv⟩

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance wilsonWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance wilsonHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The closed-walk obstruction acts on the actual native inserted-matrix
cuts. Different computed holonomy classes on an observed closed walk imply
different normalized native densities, even for observations with holes.
Source: SCP10, Theorem 6.15; no density inequality is supplied as a premise. -/
theorem IsGIsometric.torusBond_normalized_density_ne_of_closedWalk_holonomy
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (o : {v : X // v ∈ R}) (w : ((Γₜ).induce (R : Set X)).Walk o o)
    (p q : TorusBondLabels width height G)
    (hc : ConjClasses.mk (regularWalkHolonomy
        (regularRegionInternalOperators R (torusGraphRegularLabels p.1 p.2)) w) ≠
      ConjClasses.mk (regularWalkHolonomy
        (regularRegionInternalOperators R (torusGraphRegularLabels q.1 q.2)) w)) :
    let M := torusBondRegularPhysicalCutMatrix A p R
    let N := torusBondRegularPhysicalCutMatrix A q R
    M ≠ 0 ∧ N ≠ 0 ∧
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) ≠
        (N * N.conjTranspose).trace⁻¹ • (N * N.conjTranspose) := by
  simpa only [torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix] using
    regularPhysicalCutMatrix_normalized_reduced_ne_of_closedWalk_holonomy
      (torusIncidentSite A) (fun v => hA.isGIsometric_torusIncidentSite v)
      R hR o w (torusGraphRegularLabels p.1 p.2) (torusGraphRegularLabels q.1 q.2) hc

end TNLean.PEPS
