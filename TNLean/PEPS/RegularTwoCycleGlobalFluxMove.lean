/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoCyclePhysicalFluxMove
import TNLean.PEPS.RegularCoherentGlobalTransport
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian
import TNLean.PEPS.RegularRegionGaugeContraction
import QICLean.Algebra.MatrixReindexUnitary

/-!
# The global contraction consequence of the two-cycle flux operation

A unitary on a physical region extends by the identity on its complement.
The native boundary contraction sum then carries an identity on every open
column to an identity between the actual globally contracted states. The
complementary site coefficients may be arbitrary. A second formulation leaves
all exterior and crossing bond operators arbitrary and common: an identity
vertex gauge transfers the crossing operators to the same boundary labels on
both sides, while the complementary tensors remain equal.

The physical unitary is chosen before the flux element and all exterior data.
Thus linearity also permits coherent superpositions of unknown flux labels.
The region/complement factorization and boundary transport are derived from
the actual finite contractions; no coefficient or Gram identity is assumed.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, `thm:anyons:move-fluxons`,
lines 2270–2301, with the finite cut contraction in lines 1935–1957.

**Scope restriction (chosen two-cycle block):** The region has a supplied
spanning tree and two distinct non-tree internal bonds. The concrete six-vertex
geometry and broader open-string statement are separate. No energy or
parent-Hamiltonian membership assertion is made; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) :=
  {e : RI (Γ := Γ) R // ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}

/-- Keep the prescribed sites in a region and arbitrary common site coefficients
outside it. Source: SCP10, the exterior contraction in Theorem 6.16, lines 2270–2301. -/
def regularRegionSiteExtension (R : Finset V)
    (a b : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (v : V) : (IncidentEdge Γ v → G) → Fin d → ℂ :=
  if v ∈ R then a v else b v

/-- A regional unitary tensored with the complementary identity is globally unitary.
Source: SCP10, the local physical operation in Theorem 6.16, lines 2270–2301. -/
theorem regionLocalTerm_mem_unitaryGroup (R : Finset V)
    (W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ) :
    regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ := by
  classical
  exact Matrix.reindex_mem_unitaryGroup (regionConfigEquiv (d := d) R).symm _
    (Matrix.kronecker_mem_unitary hW (one_mem _))

omit [Group G] in
private theorem openWeight_congr (R : Finset V)
    (a b : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (hab : ∀ v ∈ R, a v = b v)
    (μ : {f : Edge Γ // IsRegionBoundaryEdge R f} → Fin (Fintype.card G)) :
    openRegionWeight (groupBondTensor a) R μ =
      openRegionWeight (groupBondTensor b) R μ := by
  funext σ
  unfold openRegionWeight
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  unfold regionIncidentWeight
  apply Finset.prod_congr rfl
  intro v _
  exact congrFun (congrFun (hab v v.2) _) _

variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
/-- One identity-extended unitary maps the actual one-insertion state to the
two-insertion state for every flux element and arbitrary common exterior sites.
Source: SCP10, Theorem 6.16, lines 2270–2301, in the chosen two-cycle block. -/
theorem exists_unitary_regularTwoCycleGlobalFluxMove
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      ∀ (g : G) (b : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor
          (regularRegionSiteExtension R (regularTwistedSite a
            (regularTreeCycleAssignment R T (fun e => if e = e₀ then g else 1))) b)) =
        stateCoeff (groupBondTensor
          (regularRegionSiteExtension R (regularTwistedSite a
            (regularTreeCycleAssignment R T
              (fun e => if e = e₀ ∨ e = e₁ then g else 1))) b)) := by
  classical
  obtain ⟨W, hW, hmove⟩ :=
    exists_unitary_regularTwoCyclePhysicalFluxMove R T a ha hT htree o e₀ e₁ hne
  refine ⟨W, hW, regionLocalTerm_mem_unitaryGroup R W hW, ?_⟩
  intro g b
  let a₀ := regularTwistedSite a
    (regularTreeCycleAssignment R T (fun e => if e = e₀ then g else 1))
  let a₁ := regularTwistedSite a
    (regularTreeCycleAssignment R T (fun e => if e = e₀ ∨ e = e₁ then g else 1))
  apply regionLocalTerm_mulVec_stateCoeff_of_openColumns
  · intro μ
    rw [openWeight_congr R (regularRegionSiteExtension R a₀ b) a₀
      (fun v hv => by simp only [regularRegionSiteExtension, ite_eq_left hv]),
      openWeight_congr R (regularRegionSiteExtension R a₁ b) a₁
      (fun v hv => by simp only [regularRegionSiteExtension, ite_eq_left hv])]
    simpa only [Equiv.apply_symm_apply] using
      hmove g (fun f => (Fintype.equivFin G).symm (μ f))
  · intro v hv
    simp only [regularRegionSiteExtension, ite_eq_right hv]


/-- Prescribe operators on internal region bonds and retain the common assignment
on all other bonds, including crossings. Source: SCP10, Theorem 6.16, lines 2270–2301. -/
def regularRegionBondExtension (R : Finset V) (inside outside : Edge Γ → G) : Edge Γ → G :=
  fun e => if e.1.1 ∈ R ∧ e.1.2 ∈ R then inside e else outside e

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
private theorem gauge_one_bondExtension
    (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G) :
    regularRegionGaugeEdgeOperators R (fun _ => 1)
        (regularRegionBondExtension R (regularTreeCycleAssignment R T ω) u) =
      regularTreeCycleAssignment R T ω := by
  funext e
  simp only [regularRegionGaugeEdgeOperators, regularRegionGaugeResidual,
    regularRegionBondExtension, regularTreeCycleAssignment, inv_one, one_mul, mul_one]
  split_ifs <;> first | rfl | grind

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
private theorem boundary_bondExtension (s u : Edge Γ → G) :
    regularRegionBoundaryTransport R (fun _ => (1 : G)) (regularRegionBondExtension R s u) =
      regularRegionBoundaryTransport R (fun _ => 1) u := by
  apply Equiv.ext
  intro θ
  funext e
  have hn : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
    rcases e.2 with h | h
    · exact fun he => h.2 he.2
    · exact fun he => h.1 he.1
  have hu : regularRegionBondExtension R s u e.1 = u e.1 := by
    simp only [regularRegionBondExtension, ite_eq_right hn]
  simp only [regularRegionBoundaryTransport, Equiv.piCongrRight_apply, Pi.map_apply,
    Equiv.mulLeft, hu]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Changing only internal region bond operators leaves every exterior original
site coefficient unchanged. Source: SCP10, Theorems 6.16–6.17, lines 2270–2340. -/
theorem regularTwistedSite_regularRegionBondExtension_eq_outside
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (s t u : Edge Γ → G) (v : V) (hv : v ∉ R) :
    regularTwistedSite a (regularRegionBondExtension R s u) v =
      regularTwistedSite a (regularRegionBondExtension R t u) v := by
  funext η p
  unfold regularTwistedSite
  congr 1
  funext e
  have hn : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
    rcases e.2 with h | h
    · exact fun he => hv (h ▸ he.1)
    · exact fun he => hv (h ▸ he.2)
  simp only [regularTwistedLabels, regularRegionBondExtension, ite_eq_right hn]

/-- An identity vertex gauge derives the same boundary transport for every
internal tree-cycle assignment with common exterior and crossing operators.
Source: SCP10, lines 1765–1920 and Theorems 6.16–6.17, lines 2270–2340. -/
theorem openRegionWeight_regularTreeCycleBondExtension
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (hinv : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    openRegionWeight (groupBondTensor (regularTwistedSite a
      (regularRegionBondExtension R (regularTreeCycleAssignment R T ω) u))) R
      (fun f => Fintype.equivFin G (θ f)) =
    openRegionWeight (groupBondTensor (regularTwistedSite a
      (regularTreeCycleAssignment R T ω))) R
      (fun f => Fintype.equivFin G
        (regularRegionBoundaryTransport R (fun _ => 1) u θ f)) := by
  funext σ
  rw [openRegionWeight_regularRegionGauge a hinv R (fun _ => 1),
    gauge_one_bondExtension, boundary_bondExtension]

/-- The fixed global physical unitary extends the insertion to both cycle bonds
with arbitrary common exterior and crossing operators. Their boundary transport
is derived, not supplied. Source: SCP10, Theorem 6.16, lines 2270–2301. -/
theorem exists_unitary_regularTwoCycleGlobalFluxMove_bondOperators
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      ∀ (g : G) (u : Edge Γ → G),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R
            (regularTreeCycleAssignment R T (fun e => if e = e₀ then g else 1)) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R
            (regularTreeCycleAssignment R T
              (fun e => if e = e₀ ∨ e = e₁ then g else 1)) u))) := by
  classical
  obtain ⟨W, hW, hmove⟩ :=
    exists_unitary_regularTwoCyclePhysicalFluxMove R T a ha hT htree o e₀ e₁ hne
  have hinv : ∀ g v η s, a v (fun e => g * η e) s = a v η s := by
    intro g v η s
    exact (ha v).toIsGInjective.regularSiteMap_translation g η s
  refine ⟨W, hW, regionLocalTerm_mem_unitaryGroup R W hW, ?_⟩
  intro g u
  apply regionLocalTerm_mulVec_stateCoeff_of_openColumns
  · intro μ
    let θ := fun f => (Fintype.equivFin G).symm (μ f)
    have hμ : μ = fun f => Fintype.equivFin G (θ f) := by
      funext f
      exact (Fintype.equivFin G).apply_symm_apply (μ f) |>.symm
    rw [hμ, openRegionWeight_regularTreeCycleBondExtension R T a hinv,
      openRegionWeight_regularTreeCycleBondExtension R T a hinv]
    exact hmove g (regularRegionBoundaryTransport R (fun _ => 1) u θ)
  · exact regularTwistedSite_regularRegionBondExtension_eq_outside R a _ _ u

end TNLean.PEPS
