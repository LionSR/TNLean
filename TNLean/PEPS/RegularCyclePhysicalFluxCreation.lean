/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularFluxCreationState
import TNLean.PEPS.RegularTwoCycleFluxMove
import TNLean.PEPS.RegularCycleControlledSupport


import TNLean.Algebra.PermutationMatrixCommutation

/-!
# Coherent flux creation in an actual regular region

Choose a spanning tree in a finite region and an internal bond outside that
tree. The genuine tree-coordinate equivalence isolates its cycle coordinate.
Acting by the conjugation-equivariant class creation matrix on this coordinate,
and by the identity on every other coordinate, gives a unitary on the original
half-edge physical space. It commutes with independent vertex translations
and hence with the product of local regular invariant projectors.

The original canonical contraction determines its exact action on every boundary
column: an identity assignment becomes the normalized coherent sum of assignments
with z g z⁻¹ on the chosen bond. Local G-isometry then yields a unitary on the
original spins, chosen before every boundary label. This physical unitary depends
on the requested conjugacy class g; no coefficient or Gram equality is assumed.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Theorem 6.17,
`eq:anyons:make-chargeless-fluxon`, local source lines 2304–2340, and accessible
regular coordinates, lines 1765–1920. The normalization is the exact one derived
in `RegularFluxCreationState`.

**Scope restriction (chosen cycle block):** The theorem takes a spanning tree
and a chosen internal bond outside that tree. The concrete two-plaquette geometry
and global identity extension are separate assertions. This is the actual local
coherent contraction identity, without an energy or parent-Hamiltonian claim;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) := RegionCycleEdge (Γ := Γ) R T
private abbrev Rest (R : Finset V) (T : SimpleGraph (RV R)) (o : RV R)
    (e : RC (Γ := Γ) R T) :=
  ({f : Edge Γ // IsRegionBoundaryEdge R f} → G) ×
  ({f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) ×
  RootedGroupLabels (G := G) o × ({f : RC (Γ := Γ) R T // f ≠ e} → G)
variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
private def restCoordinates (o : RV R) (e : RC (Γ := Γ) R T)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) : Rest (G := G) R T o e :=
  (c.1, c.2.1, c.2.2.1, fun f => c.2.2.2 f)
private def cycleSplit (o : RV R) (e : RC (Γ := Γ) R T) :
    RegularRegionCoordinates (Γ := Γ) (G := G) R T o ≃ G × Rest (G := G) R T o e where
  toFun c := (c.2.2.2 e, restCoordinates R T o e c)
  invFun c := (c.2.1, c.2.2.1, c.2.2.2.1, (Equiv.funSplitAt e G).symm (c.1,c.2.2.2.2))
  left_inv c :=
    congrArg (fun z : RC (Γ := Γ) R T → G => (c.1,c.2.1,c.2.2.1,z))
      ((Equiv.funSplitAt e G).symm_apply_apply c.2.2.2)
  right_inv c := by
    rcases c with ⟨t,y,a,r,z⟩
    simp only [restCoordinates, Equiv.funSplitAt, Equiv.piSplitAt,
      Equiv.coe_fn_mk, Equiv.symm_mk, dite_true, Prod.mk.injEq, true_and]
    funext f
    simp only [dite_eq_right f.2]

private theorem creation_conjugation_entry (g x t s : G) :
    regularFluxCreationMatrix g (x*t*x⁻¹) (x*s*x⁻¹) = regularFluxCreationMatrix g t s := by
  have hinj : Function.Injective (fun t : G => x*t*x⁻¹) := (MulAut.conj x).injective
  have hone (t : G) : x*t*x⁻¹ = 1 ↔ t = 1 := by
    simpa only [mul_one, mul_inv_cancel] using hinj.eq_iff (a := t) (b := 1)
  simp only [regularFluxCreationMatrix, Matrix.unitaryVectorSwap, Matrix.sub_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.star_apply,
    Pi.single_apply, normalizedRegularFluxClassVector_conjugation, hinj.eq_iff, hone]

private def restTranslation (o : RV R) (e : RC (Γ := Γ) R T) (ℓ : RV R → G) :
    Equiv.Perm (Rest (G := G) R T o e) where
  toFun c := (fun f => ℓ o * c.1 f, fun f => ℓ o * c.2.1 f,
    ⟨fun v => ℓ v * c.2.2.1.1 v * (ℓ o)⁻¹, by simp [c.2.2.1.2]⟩,
    fun f => ℓ o * c.2.2.2 f * (ℓ o)⁻¹)
  invFun c := (fun f => (ℓ o)⁻¹ * c.1 f, fun f => (ℓ o)⁻¹ * c.2.1 f,
    ⟨fun v => (ℓ v)⁻¹ * c.2.2.1.1 v * ℓ o, by simp [c.2.2.1.2]⟩,
    fun f => (ℓ o)⁻¹ * c.2.2.2 f * ℓ o)
  left_inv c := by
    apply Prod.ext
    · funext f; simp only [inv_mul_cancel_left]
    · apply Prod.ext
      · funext f; simp only [inv_mul_cancel_left]
      · apply Prod.ext
        · apply Subtype.ext; funext v; dsimp; group
        · funext f; dsimp; group
  right_inv c := by
    apply Prod.ext
    · funext f; simp only [mul_inv_cancel_left]
    · apply Prod.ext
      · funext f; simp only [mul_inv_cancel_left]
      · apply Prod.ext
        · apply Subtype.ext; funext v; dsimp; group
        · funext f; dsimp; group

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableRel T.Adj] in
private def coordinateCreation (o : RV R) (e : RC (Γ := Γ) R T) (g : G) :
    Matrix (RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
      (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) ℂ := by
  classical
  exact Matrix.of fun c d => regularFluxCreationMatrix g (c.2.2.2 e) (d.2.2.2 e) *
    (@ite ℂ (restCoordinates R T o e c = restCoordinates R T o e d)
      (Classical.propDecidable _) 1 0)


omit [Fintype V] [DecidableRel Γ.Adj] [DecidableRel T.Adj] in
private theorem coordinateCreation_translation (o : RV R) (e : RC (Γ := Γ) R T)
    (g : G) (ℓ : RV R → G)
    (c d : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    coordinateCreation R T o e g (regularRegionCoordinateTranslation R T o ℓ c)
        (regularRegionCoordinateTranslation R T o ℓ d) = coordinateCreation R T o e g c d := by
  classical
  have hc : restCoordinates R T o e (regularRegionCoordinateTranslation R T o ℓ c) =
      restTranslation R T o e ℓ (restCoordinates R T o e c) := rfl
  have hd : restCoordinates R T o e (regularRegionCoordinateTranslation R T o ℓ d) =
      restTranslation R T o e ℓ (restCoordinates R T o e d) := rfl
  have hi : restCoordinates R T o e (regularRegionCoordinateTranslation R T o ℓ c) =
      restCoordinates R T o e (regularRegionCoordinateTranslation R T o ℓ d) ↔
      restCoordinates R T o e c = restCoordinates R T o e d := by
    rw [hc, hd]
    exact (restTranslation R T o e ℓ).injective.eq_iff
  exact congrArg₂ (fun a b : ℂ => a*b)
    (creation_conjugation_entry g (ℓ o) (c.2.2.2 e) (d.2.2.2 e))
    (@if_congr ℂ _ _ (Classical.propDecidable _) (Classical.propDecidable _)
      1 0 1 0 hi rfl rfl)


/-- Apply the equivariant class creation matrix to one actual cycle coordinate.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
def regularRegionFluxCreationMatrix (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree)
    (o : RV R) (e : RC (Γ := Γ) R T) (g : G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  (coordinateCreation R T o e g).submatrix
    (regularRegionCoordinatesEquiv R T hT htree o)
    (regularRegionCoordinatesEquiv R T hT htree o)

/-- The cycle operation is unitary on the full native half-edge physical space.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularRegionFluxCreationMatrix_mem_unitaryGroup
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree)
    (o : RV R) (e : RC (Γ := Γ) R T) (g : G) :
    regularRegionFluxCreationMatrix R T hT htree o e g ∈
      Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ := by
  classical
  let _ := Fintype.ofFinite (RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
  let _ := Fintype.ofFinite (Rest (G := G) R T o e)
  have h := Matrix.reindex_mem_unitaryGroup (cycleSplit R T o e).symm _
    (Matrix.kronecker_mem_unitary (regularFluxCreationMatrix_mem_unitaryGroup g)
      (Matrix.unitaryGroup (Rest (G := G) R T o e) ℂ).one_mem)
  have hcoord : coordinateCreation R T o e g ∈
      Matrix.unitaryGroup (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) ℂ := by
    convert h using 1
    ext c d
    rfl
  exact Matrix.reindex_mem_unitaryGroup
    (m := RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (n := RegionHalfEdgeConfig (Γ := Γ) G R)
    (regularRegionCoordinatesEquiv R T hT htree o).symm
    (coordinateCreation R T o e g) hcoord

/-- Creation commutes with every independent vertex translation.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularRegionFluxCreationMatrix_commute_vertexTranslation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree)
    (o : RV R) (e : RC (Γ := Γ) R T) (g : G) (ℓ : RV R → G) :
    Commute (regularRegionFluxCreationMatrix R T hT htree o e g)
      (regularRegionVertexTranslationMatrix (Γ := Γ) R ℓ) := by
  classical
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let τ : Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) :=
    regularRegionGaugePhysicalLabels (Γ := Γ) R (fun v => (ℓ v)⁻¹)
  have hE (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
      E (τ α) = regularRegionCoordinateTranslation R T o ℓ (E α) := by
    apply E.symm.injective
    rw [E.symm_apply_apply, regularRegionCoordinatesEquiv_symm_coordinateTranslation,
      E.symm_apply_apply]
  have hi (α β : RegionHalfEdgeConfig (Γ := Γ) G R) :
      regularRegionFluxCreationMatrix R T hT htree o e g (τ α) (τ β) =
        regularRegionFluxCreationMatrix R T hT htree o e g α β := by
    change coordinateCreation R T o e g (E (τ α)) (E (τ β)) =
      coordinateCreation R T o e g (E α) (E β)
    rw [hE, hE, coordinateCreation_translation]
  change Commute _ ((τ⁻¹).permMatrix ℂ)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro α β
  simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using
    (hi (τ.symm α) (τ.symm β)).symm

/-- Creation preserves the actual product of local regular invariant projectors.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularRegionFluxCreationMatrix_commute_localProjector
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree)
    (o : RV R) (e : RC (Γ := Γ) R T) (g : G) :
    Commute (regularRegionFluxCreationMatrix R T hT htree o e g)
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) := by
  exact commute_regionLocalProjector_of_vertexTranslation R _ (fun ℓ =>
    regularRegionFluxCreationMatrix_commute_vertexTranslation R T hT htree o e g ℓ)

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G]
  [DecidableRel T.Adj] in
private theorem conjugated_single_split (e : RC (Γ := Γ) R T) (x t : G) :
    Equiv.funSplitAt e G (fun f => x * (if f = e then t else 1) * x⁻¹) =
      (x*t*x⁻¹, fun _ => 1) := by
  classical
  apply Prod.ext
  · simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · funext f
    simp [Equiv.funSplitAt, Equiv.piSplitAt, f.2]

private theorem column_split
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RC (Γ := Γ) R T) (t s : G) (b : Rest (G := G) R T o e)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regularProjectorTwistedRegionMatrix R
      (regularTreeCycleAssignment R T (fun f => if f = e then t else 1))
      ((regularRegionCoordinatesEquiv R T hT htree o).symm
        ((cycleSplit R T o e).symm (s,b))) θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ x : G,
        (if b.1 = (fun f => x * θ f) ∧ b.2.2.2 = (fun _ => 1) then (1 : ℂ) else 0) *
        (if s = x*t*x⁻¹ then 1 else 0) := by
  classical
  have h := regularProjectorTwistedRegionMatrix_treeCycleAssignment_coordinates
    (G := G) R T hT htree o (fun f => if f = e then t else 1)
    ((cycleSplit R T o e).symm (s,b)) θ
  refine h.trans ?_
  apply congrArg (fun a : ℂ => (Fintype.card G : ℂ)⁻¹ ^ R.card * a)
  apply Finset.sum_congr rfl
  intro x _
  have hcycle : ((cycleSplit R T o e).symm (s,b)).2.2.2 =
      (fun f => x * (if f = e then t else 1) * x⁻¹) ↔
      s = x*t*x⁻¹ ∧ b.2.2.2 = (fun _ => 1) := by
    rw [← (Equiv.funSplitAt e G).injective.eq_iff]
    change Equiv.funSplitAt e G ((Equiv.funSplitAt e G).symm (s,b.2.2.2)) = _ ↔ _
    rw [Equiv.apply_symm_apply, conjugated_single_split R T]
    simp only [Prod.mk.injEq]
  have hy : ((cycleSplit R T o e).symm (s,b)).1 = b.1 := rfl
  simp only [hy, hcycle]
  split_ifs <;> simp_all

omit [Fintype V] [DecidableRel Γ.Adj] in
open scoped Classical in
private theorem creation_eq_kronecker
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RC (Γ := Γ) R T) (g : G) :
    regularRegionFluxCreationMatrix R T hT htree o e g =
      (regularFluxCreationMatrix g ⊗ₖ (1 : Matrix (Rest (G := G) R T o e)
        (Rest (G := G) R T o e) ℂ)).submatrix
        ((regularRegionCoordinatesEquiv R T hT htree o).trans (cycleSplit R T o e))
        ((regularRegionCoordinatesEquiv R T hT htree o).trans (cycleSplit R T o e)) := by
  classical
  ext α β
  rfl

private theorem creation_slice
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RC (Γ := Γ) R T) (g s : G) (b : Rest (G := G) R T o e)
    (ψ : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ) :
    (regularRegionFluxCreationMatrix R T hT htree o e g *ᵥ ψ)
      (((regularRegionCoordinatesEquiv R T hT htree o).trans
        (cycleSplit R T o e)).symm (s,b)) =
      ∑ t : G, regularFluxCreationMatrix g s t *
        ψ (((regularRegionCoordinatesEquiv R T hT htree o).trans
          (cycleSplit R T o e)).symm (t,b)) := by
  classical
  let _ := Fintype.ofFinite (Rest (G := G) R T o e)
  let E := (regularRegionCoordinatesEquiv (G := G) R T hT htree o).trans
    (cycleSplit R T o e)
  rw [creation_eq_kronecker]
  change (∑ α, (regularFluxCreationMatrix g ⊗ₖ (1 : Matrix (Rest (G := G) R T o e)
    (Rest (G := G) R T o e) ℂ)) (E (E.symm (s,b))) (E α) * ψ α) = _
  rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply, Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_eq_single b]
  · simp [E]
  · intro d _ hd
    simp only [ite_eq_right (Ne.symm hd)]
  · intro hb
    exact (hb (Finset.mem_univ b)).elim

private theorem column_initial_split
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RC (Γ := Γ) R T) (s : G) (b : Rest (G := G) R T o e)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regularProjectorTwistedRegionMatrix R
      (regularTreeCycleAssignment R T (fun _ => 1))
      (((regularRegionCoordinatesEquiv R T hT htree o).trans
        (cycleSplit R T o e)).symm (s,b)) θ =
      (if s = 1 then (1 : ℂ) else 0) *
        ((Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ x : G,
          if b.1 = (fun f => x * θ f) ∧ b.2.2.2 = (fun _ => 1) then (1 : ℂ) else 0) := by
  classical
  have hω : (fun f : RC (Γ := Γ) R T => if f = e then (1 : G) else 1) =
      (fun _ => 1) := by funext f; simp
  have h := column_split R T hT htree o e 1 s b θ
  rw [hω] at h
  refine h.trans ?_
  simp only [mul_one, mul_inv_cancel, ← Finset.sum_mul]
  ring

private theorem conjugated_class_sum (g x s : G) :
    (∑ z : G, if s = x * (z*g*z⁻¹) * x⁻¹ then (1 : ℂ) else 0) =
      regularFluxClassVector g s := by
  rw [← Equiv.sum_comp (Equiv.mulLeft x⁻¹)]
  unfold regularFluxClassVector
  apply Finset.sum_congr rfl
  intro z _
  have he : x * ((x⁻¹*z)*g*(x⁻¹*z)⁻¹) * x⁻¹ = z*g*z⁻¹ := by group
  simp only [Equiv.coe_mulLeft, he]

private theorem column_class_sum
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RC (Γ := Γ) R T) (g s : G) (b : Rest (G := G) R T o e)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    (∑ z : G, regularProjectorTwistedRegionMatrix R
      (regularTreeCycleAssignment R T (fun f => if f = e then z*g*z⁻¹ else 1))
      (((regularRegionCoordinatesEquiv R T hT htree o).trans
        (cycleSplit R T o e)).symm (s,b)) θ) =
      (Fintype.card G : ℂ)⁻¹ ^ R.card *
        (∑ x : G, if b.1 = (fun f => x * θ f) ∧ b.2.2.2 = (fun _ => 1)
          then (1 : ℂ) else 0) * regularFluxClassVector g s := by
  classical
  simp_rw [Equiv.symm_trans_apply, column_split]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hsum : (∑ x : G, ∑ z : G,
      (if b.1 = (fun f => x*θ f) ∧ b.2.2.2 = (fun _ => 1) then (1 : ℂ) else 0) *
        (if s = x*(z*g*z⁻¹)*x⁻¹ then 1 else 0)) =
      (∑ x : G, if b.1 = (fun f => x*θ f) ∧ b.2.2.2 = (fun _ => 1)
        then (1 : ℂ) else 0) * regularFluxClassVector g s := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, conjugated_class_sum]
  rw [hsum, mul_assoc]

/-- The actual canonical identity column becomes the normalized coherent class sum.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularProjectorTwistedRegionMatrix_fluxCreation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RC (Γ := Γ) R T) (g : G)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regularRegionFluxCreationMatrix R T hT htree o e g *ᵥ
      (fun α => regularProjectorTwistedRegionMatrix R
        (regularTreeCycleAssignment R T (fun _ => 1)) α θ) =
      (Real.sqrt ((Fintype.card G : ℝ) *
        Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹ •
        (∑ z : G, fun α => regularProjectorTwistedRegionMatrix R
          (regularTreeCycleAssignment R T (fun f => if f = e then z*g*z⁻¹ else 1)) α θ) := by
  classical
  let E := (regularRegionCoordinatesEquiv (G := G) R T hT htree o).trans
    (cycleSplit R T o e)
  funext α
  obtain ⟨⟨s,b⟩, rfl⟩ := E.symm.surjective α
  rw [creation_slice]
  simp_rw [column_initial_split]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hU := congrFun (regularFluxCreationMatrix_mulVec_single g) s
  rw [Matrix.mulVec_single_one] at hU
  change regularFluxCreationMatrix g s 1 = normalizedRegularFluxClassVector g s at hU
  rw [hU]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [column_class_sum]
  simp only [normalizedRegularFluxClassVector, Pi.smul_apply, smul_eq_mul]
  ring

variable {d : ℕ}
omit [DecidableEq G] in
/-- For each requested class, one original-spin unitary creates its coherent insertion
sum uniformly in every boundary column, using local G-isometry alone.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem exists_unitary_regularCyclePhysicalFluxCreation
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RC (Γ := Γ) R T) (g : G) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      ∀ (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T (fun _ => 1)))) R
          (fun f => Fintype.equivFin G (θ f)) =
        (Real.sqrt ((Fintype.card G : ℝ) *
          Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹ •
          ∑ z : G, openRegionWeight (groupBondTensor (regularTwistedSite a
            (regularTreeCycleAssignment R T (fun f => if f = e then z*g*z⁻¹ else 1)))) R
            (fun f => Fintype.equivFin G (θ f)) := by
  classical
  let Q := regularRegionFluxCreationMatrix (G := G) R T hT htree o e g
  obtain ⟨W,hW,hWA⟩ := exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute
    a ha R Q (regularRegionFluxCreationMatrix_mem_unitaryGroup R T hT htree o e g)
    (regularRegionFluxCreationMatrix_commute_localProjector R T hT htree o e g).eq
  refine ⟨W,hW,?_⟩
  intro θ
  rw [← regionPhysicalMap_regularProjectorTwistedRegionMatrix a
    (fun v => (ha v).toIsGInjective) R (regularTreeCycleAssignment R T (fun _ => 1)) θ]
  change W *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, hWA, ← Matrix.mulVec_mulVec]
  rw [regularProjectorTwistedRegionMatrix_fluxCreation]
  change regionPhysicalMap R (fun v => Matrix.of (fun s α => a v α s)) (_ • _) = _
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  exact regionPhysicalMap_regularProjectorTwistedRegionMatrix a
    (fun v => (ha v).toIsGInjective) R
    (regularTreeCycleAssignment R T (fun f => if f = e then z*g*z⁻¹ else 1)) θ
end TNLean.PEPS
