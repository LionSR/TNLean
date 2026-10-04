/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargeFluxPhysicalTransport
import TNLean.PEPS.RegularWeightedChargeContraction

/-!
# Moving a literal electric charge by an original-spin unitary

Swapping two internal reference registers moves a diagonal character insertion.
The swap commutes with all independent vertex translations and hence lifts to
one unitary on the original spins, before the character, parameter, boundary
labels or group-valued background are chosen. In a nontrivial background the
parameter changes by the derived tree transport between the two ordered tails.

Source: SCP10, arXiv:1001.3807, `eq:anyons:chargeon-move-setting`, lines 2489–2507,
and the accessible coordinates of lines 1765–1920.
**Scope restriction (finite block):** The background-dependent auxiliary
statement uses a chosen spanning tree; the untwisted consumer chooses this tree
from actual induced connectivity. Both use two internal bonds and supply a physical operation,
without asserting that it is a product of the two column operations drawn in
the source. Native four-site geometry is separate; see
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
variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]

/-- Exchange the two selected reference registers, retaining every other register.
Source: SCP10, `eq:anyons:chargeon-move-setting`, lines 2489–2507. -/
def regularChargeMoveCoordinatePermutation (o : RV R) (e f : RI (Γ := Γ) R) :
    Equiv.Perm (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) where
  toFun c := (c.1, fun i => c.2.1 (Equiv.swap e f i), c.2.2)
  invFun c := (c.1, fun i => c.2.1 (Equiv.swap e f i), c.2.2)
  left_inv c := by
    dsimp only
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        simp only [Equiv.swap_apply_self]
      · rfl
  right_inv c := by
    dsimp only
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        simp only [Equiv.swap_apply_self]
      · rfl

/-- The actual tree transport required by a reference-register swap.
Source: SCP10, lines 2489–2507 and accessible coordinates, lines 1765–1920. -/
def regularChargeMoveParameter
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e f : RI (Γ := Γ) R) (u : Edge Γ → G) (p : G) : G :=
  let k := (regularRegionTreeGauge R T hT htree o u).1
  p * k ⟨e.1.1.1, e.2.1⟩ * (k ⟨f.1.1.1, f.2.1⟩)⁻¹

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G]
  [DecidableRel T.Adj] in
/-- The reference swap is equivariant under actual independent vertex translations.
Source: SCP10, lines 1765–1920 and 2489–2507. -/
theorem regularChargeMoveCoordinatePermutation_coordinateTranslation (o : RV R)
    (e f : RI (Γ := Γ) R) (ℓ : RV R → G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    regularChargeMoveCoordinatePermutation R T o e f
        (regularRegionCoordinateTranslation R T o ℓ c) =
      regularRegionCoordinateTranslation R T o ℓ
        (regularChargeMoveCoordinatePermutation R T o e f c) := rfl

omit [Fintype G] [DecidableEq G] in
private theorem move_weight (χ : G → ℂ) (p k l x a : G) :
    χ ((p * k * l⁻¹) * (l * x⁻¹ * a)) = χ (p * (k * x⁻¹ * a)) := by
  congr 1
  group

private theorem weighted_coordinates
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e f : RI (Γ := Γ) R) (u : Edge Γ → G) (χ : G → ℂ) (p : G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {b : Edge Γ // IsRegionBoundaryEdge R b} → G) :
    regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (regularChargeMoveParameter R T hT htree o e f u p *
          η ⟨f.1, Or.inl f.2.1⟩))
        ((regularRegionCoordinatesEquiv R T hT htree o).symm
          (regularChargeMoveCoordinatePermutation R T o e f c)) θ =
      regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩))
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ := by
  rw [regularProjectorWeightedTwistedRegionMatrix_internalCharge_coordinates,
    regularProjectorWeightedTwistedRegionMatrix_internalCharge_coordinates]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp only [regularChargeMoveCoordinatePermutation, Equiv.coe_fn_mk,
    Equiv.swap_apply_right]
  split_ifs
  · exact move_weight χ p _ _ _ _
  · rfl

private theorem weighted_mulVec
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e f : RI (Γ := Γ) R) (u : Edge Γ → G) (χ : G → ℂ) (p : G)
    (θ : {b : Edge Γ // IsRegionBoundaryEdge R b} → G) :
    Matrix.permMatrixHom (R := ℂ)
        (regularRegionCoordinatePhysicalPermutation R T hT htree o
          (regularChargeMoveCoordinatePermutation R T o e f)) *ᵥ
      (fun α => regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩)) α θ) =
      (fun α => regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (regularChargeMoveParameter R T hT htree o e f u p *
          η ⟨f.1, Or.inl f.2.1⟩)) α θ) := by
  funext α
  rw [Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  have h := weighted_coordinates R T hT htree o e f u χ p
    ((regularChargeMoveCoordinatePermutation R T o e f).symm
      ((regularRegionCoordinatesEquiv R T hT htree o) α)) θ
  simpa only [regularRegionCoordinatePhysicalPermutation, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.Perm.inv_def, Function.comp_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.symm_symm] using h.symm

/-- One original-spin unitary moves the literal charge between two internal bonds.
It precedes the actual background, coefficient function, parameter and boundary.
Source: SCP10, `eq:anyons:chargeon-move-setting`, lines 2489–2507. -/
theorem exists_unitary_regularPhysicalChargeMotion {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e f : RI (Γ := Γ) R) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      ∀ (u : Edge Γ → G) (χ : G → ℂ) (p : G)
        (θ : {b : Edge Γ // IsRegionBoundaryEdge R b} → G),
        W *ᵥ regularWeightedOpenRegionWeight a R u
          (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩)) θ =
        regularWeightedOpenRegionWeight a R u
          (fun η => χ (regularChargeMoveParameter R T hT htree o e f u p *
            η ⟨f.1, Or.inl f.2.1⟩)) θ := by
  classical
  let C := regularChargeMoveCoordinatePermutation (G := G) R T o e f
  let Q := Matrix.permMatrixHom (R := ℂ)
    (regularRegionCoordinatePhysicalPermutation R T hT htree o C)
  have hQ : Q ∈ Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
    (regularRegionCoordinatePhysicalPermutation R T hT htree o C)⁻¹
      |>.permMatrix_mem_unitaryGroup
  have hcomm := regularRegionCoordinatePhysicalPermutation_commute_localProjector
    R T hT htree o C
    (fun ℓ c => regularChargeMoveCoordinatePermutation_coordinateTranslation R T o e f ℓ c)
  obtain ⟨W,hW,hWA⟩ := exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute
    a ha R Q hQ hcomm.eq
  refine ⟨W,hW,?_⟩
  intro u χ p θ
  have hcan := weighted_mulVec R T hT htree o e f u χ p θ
  rw [← regionPhysicalMap_regularProjectorWeightedTwistedRegionMatrix a
      (fun v => (ha v).toIsGInjective),
    ← regionPhysicalMap_regularProjectorWeightedTwistedRegionMatrix a
      (fun v => (ha v).toIsGInjective)]
  change W *ᵥ (_ *ᵥ _) = _ *ᵥ _
  rw [Matrix.mulVec_mulVec, hWA, ← Matrix.mulVec_mulVec, hcan]

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
/-- Identity bond operators have the identity rooted tree gauge.
Source: SCP10, untwisted charge-motion diagram, lines 2489–2507. -/
theorem regularRegionTreeGauge_one
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R) :
    regularRegionTreeGauge (G := G) R T hT htree o (fun _ => 1) =
      ⟨fun _ => 1, rfl⟩ := by
  apply (rootedTreeGradientEquiv T htree o).injective
  simp only [regularRegionTreeGauge, Equiv.apply_symm_apply]
  funext i
  change (1 : G) = 1 * 1⁻¹
  simp only [inv_one, mul_one]

omit [DecidableEq G] in
/-- An original-spin unitary moves a charge between actual internal bonds of a
connected finite block, retaining its character and parameter. The tree and
root are chosen internally. Source: SCP10, lines 2489–2507. -/
theorem exists_unitary_regularPhysicalChargeMotion_of_connected {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hR : (Γ.induce (R : Set V)).Connected) (e f : RI (Γ := Γ) R) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      ∀ (χ : G → ℂ) (p : G)
        (θ : {b : Edge Γ // IsRegionBoundaryEdge R b} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularEdgeCharacterSite a e.1 χ p)) R
          (fun b => Fintype.equivFin G (θ b)) =
        openRegionWeight (groupBondTensor (regularEdgeCharacterSite a f.1 χ p)) R
          (fun b => Fintype.equivFin G (θ b)) := by
  classical
  obtain ⟨S,hS,htree⟩ := hR.exists_isTree_le
  let : DecidableRel S.Adj := Classical.decRel _
  let o := hR.nonempty.some
  obtain ⟨W,hW,hact⟩ := exists_unitary_regularPhysicalChargeMotion R S a ha hS htree o e f
  refine ⟨W,hW,?_⟩
  intro χ p θ
  rw [← regularWeightedOpenRegionWeight_eq_openRegionWeight_regularEdgeCharacterSite a R e,
    ← regularWeightedOpenRegionWeight_eq_openRegionWeight_regularEdgeCharacterSite a R f]
  simpa only [regularChargeMoveParameter, regularRegionTreeGauge_one,
    inv_one, mul_one] using hact (fun _ => 1) χ p θ
end TNLean.PEPS
