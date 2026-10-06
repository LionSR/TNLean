/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCyclePermutation

/-!
# Transporting the two-cycle flux operation to original physical tensors

The controlled cycle permutation commutes with independent vertex translations
in the actual spanning-tree coordinates. Averaging these translations gives the
product of the local regular invariant projectors. The permutation therefore
preserves the genuine canonical physical support. Local G-isometry gives the
product physical map a scalar-projector Gram matrix, so the existing physical
unitary extension theorem implements this permutation on the original spins.

One fixed physical unitary carries the actual one-bond inserted region state
to the actual two-bond inserted region state, uniformly in the inserted group
element and every boundary configuration. The original/canonical equality is
derived from the native contraction and local G-injectivity, not assumed.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, `thm:anyons:move-fluxons`,
lines 2270–2301, and physical accessibility, lines 1729–1820.

**Scope restriction (chosen two-cycle block):** The theorem takes a spanning tree
and two distinct non-tree internal bonds. The concrete six-vertex lattice
geometry is separate. This is a physical realization of the auxiliary two-cycle
operation, not an unrestricted statement about arbitrary string deformations
or parent-Hamiltonian excitations; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) :=
  {e : RI (Γ := Γ) R // ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}
variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] [DecidableRel T.Adj] in
/-- The controlled cycle multiplication commutes with independent vertex translations
in the actual root-normalized coordinates. Source: SCP10, Theorem 6.16,
lines 2270–2301, and accessible regular coordinates, lines 1765–1920. -/
theorem regularRegionTwoCycleMove_coordinateTranslation (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁)
    (ℓ : RV R → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    regularRegionTwoCycleMove R T o e₀ e₁ hne (regularRegionCoordinateTranslation R T o ℓ c) =
      regularRegionCoordinateTranslation R T o ℓ (regularRegionTwoCycleMove R T o e₀ e₁ hne c) := by
  exact regularRegionCyclePermutation_coordinateTranslation R T o
    (regularTwoCycleMove e₀ e₁ hne) (regularTwoCycleMove_conjugation e₀ e₁ hne) ℓ c

/-- The native physical two-cycle permutation commutes with every independent
vertex translation. Source: SCP10, the local operation in Theorem 6.16. -/
theorem regularRegionTwoCyclePhysicalMove_commute_vertexTranslation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) (ℓ : RV R → G) :
    Commute (Matrix.permMatrixHom (R := ℂ)
      (regularRegionTwoCyclePhysicalMove R T hT htree o e₀ e₁ hne))
      (regularRegionVertexTranslationMatrix (Γ := Γ) R ℓ) := by
  exact regularRegionCyclePhysicalPermutation_commute_vertexTranslation R T hT htree o
    (regularTwoCycleMove e₀ e₁ hne) (regularTwoCycleMove_conjugation e₀ e₁ hne) ℓ

/-- The actual two-cycle operation commutes with the product of local regular
averaging projectors. Source: SCP10, accessible physical systems, lines 1765–1820,
and Theorem 6.16, lines 2270–2301. -/
theorem regularRegionTwoCyclePhysicalMove_commute_localProjector
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    Commute (Matrix.permMatrixHom (R := ℂ)
      (regularRegionTwoCyclePhysicalMove R T hT htree o e₀ e₁ hne))
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) := by
  exact commute_regionLocalProjector_of_vertexTranslation R _ (fun ℓ =>
    regularRegionTwoCyclePhysicalMove_commute_vertexTranslation R T hT htree o e₀ e₁ hne ℓ)

variable {d : ℕ}
omit [DecidableEq G] in
/-- One unitary on the original physical block extends the insertion from one chosen
cycle bond to both, uniformly in its group element and every boundary label.
The actual contraction identity is derived from local G-isometry.
Source: SCP10, Theorem 6.16, lines 2270–2301; the chosen geometry is auxiliary. -/
theorem exists_unitary_regularTwoCyclePhysicalFluxMove
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      ∀ (g : G) (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T (fun e => if e = e₀ then g else 1)))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T (fun e => if e = e₀ ∨ e = e₁ then g else 1)))) R
          (fun f => Fintype.equivFin G (θ f)) := by
  classical
  let Q := Matrix.permMatrixHom (R := ℂ)
    (regularRegionTwoCyclePhysicalMove (G := G) R T hT htree o e₀ e₁ hne)
  obtain ⟨W, hW, hWA⟩ := exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute
    a ha R Q (regularRegionTwoCyclePhysicalMove_matrix_mem_unitaryGroup R T hT htree o e₀ e₁ hne)
    (regularRegionTwoCyclePhysicalMove_commute_localProjector R T hT htree o e₀ e₁ hne).eq
  refine ⟨W, hW, ?_⟩
  intro g θ
  have hcan := regularProjectorTwistedRegionMatrix_twoCyclePhysicalMove R T hT htree o e₀ e₁ hne
    (fun e => if e = e₀ then g else 1) θ
  have hmove : regularTwoCycleMove e₀ e₁ hne (fun e => if e = e₀ then g else 1) =
      (fun e => if e = e₀ ∨ e = e₁ then g else 1) := by
    funext e
    simp only [regularTwoCycleMove, Equiv.coe_fn_mk,
      regularTweezerEquiv_symm_apply, inv_one, mul_one]
    split_ifs <;> grind
  rw [hmove] at hcan
  rw [← regionPhysicalMap_regularProjectorTwistedRegionMatrix a (fun v => (ha v).toIsGInjective),
    ← regionPhysicalMap_regularProjectorTwistedRegionMatrix a (fun v => (ha v).toIsGInjective)]
  change W *ᵥ (_ *ᵥ _) = _ *ᵥ _
  rw [Matrix.mulVec_mulVec, hWA, ← Matrix.mulVec_mulVec, hcan]
end TNLean.PEPS
