/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwistedRegionProjectorCoordinates
import TNLean.PEPS.RegularBoundaryUntwisting

/-!
# A fixed two-cycle operation on the actual regular block contraction

Choose a spanning tree in a finite region and two distinct internal bonds outside
that tree. Assign group operators only to the non-tree internal bonds, leaving
tree and crossing bonds untwisted. The actual canonical block coefficients then
have unchanged boundary labels and cycle labels simultaneously conjugate to the
inserted operators. Multiplying the second physical cycle coordinate by the first
is the existing controlled tweezer permutation with one reference label fixed.
It gives a unitary on the original half-edge physical coordinates, uniformly in
all inserted group operators and every boundary column.

In particular, one fixed unitary changes an assignment equal to g on the first
chosen bond into an assignment equal to g on both chosen bonds. This is an actual
local contraction identity; no state equality or Gram identity is assumed.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, `thm:anyons:move-fluxons`,
lines 2270–2301, using the controlled permutation of lines 1961–1966.

**Scope restriction (two-cycle block operation):** The statements take a chosen
spanning tree and two distinct non-tree internal bonds. Instantiating the native
six-vertex geometry and transporting the operation through arbitrary original
G-isometric physical tensors remain separate. These auxiliary statements are
not the full physical flux-moving theorem; see
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

/-- Assign prescribed operators to the internal bonds outside the tree and the
identity to every other native bond. Source: SCP10, flux-moving construction,
Theorem 6.16, lines 2270–2301. -/
def regularTreeCycleAssignment (ω : RC (Γ := Γ) R T → G) : Edge Γ → G := fun e =>
  if ht : e.1.1 ∈ R then
    if hh : e.1.2 ∈ R then
      if hnt : ¬ T.Adj ⟨e.1.1, ht⟩ ⟨e.1.2, hh⟩ then ω ⟨⟨e, ht, hh⟩, hnt⟩ else 1
    else 1
  else 1

/-- A native assignment supported on the selected non-tree bonds is recovered
by restricting it to those coordinates. Auxiliary to SCP10, lines 1765–1920. -/
theorem regularTreeCycleAssignment_eq_of_support {V : Type*} [LinearOrder V]
    {Γ : SimpleGraph V} {G : Type*} [Group G] (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj] (u : Edge Γ → G)
    (hs : ∀ e, u e ≠ 1 → ∃ f :
      {f : {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} //
        ¬ T.Adj ⟨f.1.1.1, f.2.1⟩ ⟨f.1.1.2, f.2.2⟩}, f.1.1 = e) :
    regularTreeCycleAssignment R T (fun f => u f.1.1) = u := by
  classical
  funext e
  simp only [regularTreeCycleAssignment]
  split_ifs <;> first | rfl | skip
  all_goals
    symm
    by_contra he
    obtain ⟨f, rfl⟩ := hs _ he
    have ht := f.1.2.1
    have hh := f.1.2.2
    have hn := f.2
    simp_all

omit [Fintype G] [DecidableEq G] in
/-- Extending a two-coordinate cycle assignment by the identity agrees with its
literal native-edge support. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem regularTreeCycleAssignment_twoSupport
    {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
    (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (e₀ e₁ : {e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
      ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩})
    (extend : Bool) (g : G) :
    regularTreeCycleAssignment R T
      (fun e => if e = e₀ ∨ (extend = true ∧ e = e₁) then g else 1) =
      (fun e => if e = e₀.1.1 ∨ (extend = true ∧ e = e₁.1.1) then g else 1) := by
  classical
  let u := fun e : Edge Γ =>
    if e = e₀.1.1 ∨ (extend = true ∧ e = e₁.1.1) then g else 1
  have hs : ∀ e, u e ≠ 1 → ∃ f :
      {f : {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} //
        ¬ T.Adj ⟨f.1.1.1, f.2.1⟩ ⟨f.1.1.2, f.2.2⟩}, f.1.1 = e := by
    intro e he
    have hp : e = e₀.1.1 ∨ (extend = true ∧ e = e₁.1.1) := by
      by_contra hn
      exact he (by simp only [u, ite_eq_right hn])
    rcases hp with h | ⟨_, h⟩
    · exact ⟨e₀, h.symm⟩
    · exact ⟨e₁, h.symm⟩
  simpa only [u, Subtype.ext_iff] using regularTreeCycleAssignment_eq_of_support R T u hs

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem assignment_tree (ω : RC (Γ := Γ) R T → G)
    (e : RI (Γ := Γ) R)
    (he : T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩) :
    regularTreeCycleAssignment R T ω e.1 = 1 := by
  simp only [regularTreeCycleAssignment, dite_eq_left e.2.1, dite_eq_left e.2.2,
    dite_eq_right (not_not.mpr he)]

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem assignment_gauge (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree)
    (o : RV R) (ω : RC (Γ := Γ) R T → G) :
    regularRegionTreeGauge R T hT htree o (regularTreeCycleAssignment R T ω) =
      ⟨fun _ => 1, rfl⟩ := by
  apply (rootedTreeGradientEquiv T htree o).injective
  rw [regularRegionTreeGauge, Equiv.apply_symm_apply]
  funext e
  change _ = (1 : G) * 1⁻¹
  simp only [inv_one, mul_one]
  exact assignment_tree R T ω
    ⟨⟨(e.1.1.1,e.1.2.1), e.2.1, hT e.2.2⟩, e.1.1.2, e.1.2.2⟩ e.2.2

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem assignment_residual (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree)
    (o : RV R) (ω : RC (Γ := Γ) R T → G) :
    regularRegionTreeCycleResidual R T hT htree o (regularTreeCycleAssignment R T ω) = ω := by
  funext e
  simp only [regularRegionTreeCycleResidual, assignment_gauge, regularRegionGaugeResidual,
    inv_one, one_mul, mul_one, regularTreeCycleAssignment,
    dite_eq_left e.1.2.1, dite_eq_left e.1.2.2, dite_eq_left e.2]

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem assignment_boundary (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree)
    (o : RV R) (ω : RC (Γ := Γ) R T → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularRegionBoundaryTransport R
      (regularRegionTreeGauge R T hT htree o (regularTreeCycleAssignment R T ω)).1
      (regularTreeCycleAssignment R T ω) θ = θ := by
  funext e
  rw [assignment_gauge]
  rcases e.2 with h | h
  · simp [regularRegionBoundaryTransport, h.1]
  · simp [regularRegionBoundaryTransport, regularTreeCycleAssignment, h.1]

/-- The actual canonical contraction with operators supported outside the tree has
untwisted boundary labels and simultaneously conjugated cycle coordinates.
Source: SCP10, accessible-coordinate argument, lines 1765–1920, and Theorem 6.16. -/
theorem regularProjectorTwistedRegionMatrix_treeCycleAssignment_coordinates
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (ω : RC (Γ := Γ) R T → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorTwistedRegionMatrix R (regularTreeCycleAssignment R T ω)
      ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ x : G,
        if c.1 = (fun e => x * θ e) ∧ c.2.2.2 = (fun e => x * ω e * x⁻¹)
        then 1 else 0 := by
  rw [regularProjectorTwistedRegionMatrix_coordinates,
    assignment_residual, assignment_boundary]
  rfl
variable {J : Type*} [DecidableEq J]
/-- The controlled tweezer operation multiplies one cycle coordinate by another.
Source: SCP10, Theorem 6.16, lines 2292–2301; it is the existing inverse
three-coordinate permutation with its third reference label equal to the identity. -/
def regularTwoCycleMove (e₀ e₁ : J) (hne : e₀ ≠ e₁) : Equiv.Perm (J → G) where
  toFun z e := if e = e₁ then (regularTweezerEquiv.symm (z e₁, z e₀, 1)).1 else z e
  invFun z e := if e = e₁ then (regularTweezerEquiv (z e₁, z e₀, 1)).1 else z e
  left_inv z := by
    funext e
    by_cases he : e = e₁
    · subst e
      simp [hne, regularTweezerEquiv_symm_apply, regularTweezerEquiv_apply]
    · simp [he]
  right_inv z := by
    funext e
    by_cases he : e = e₁
    · subst e
      simp [hne, regularTweezerEquiv_symm_apply, regularTweezerEquiv_apply]
    · simp [he]

omit [Fintype G] [DecidableEq G] in
/-- Controlled cycle multiplication commutes with simultaneous conjugation.
Source: SCP10, Theorem 6.16, lines 2292–2301. -/
theorem regularTwoCycleMove_conjugation
    (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G) (x : G) :
    regularTwoCycleMove e₀ e₁ hne (fun e => x * z e * x⁻¹) =
      fun e => x * regularTwoCycleMove e₀ e₁ hne z e * x⁻¹ := by
  funext e
  by_cases he : e = e₁
  · simp only [regularTwoCycleMove, Equiv.coe_fn_mk, he, ite_true,
      regularTweezerEquiv_symm_apply, inv_one, mul_one]
    group
  · simp only [regularTwoCycleMove, Equiv.coe_fn_mk, he, ite_false]

/-- Apply the two-cycle operation while retaining the boundary, internal reference,
and root-normalized vertex coordinates. Source: SCP10, Theorem 6.16, lines 2270–2301. -/
def regularRegionTwoCycleMove (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    Equiv.Perm (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.refl _) (regularTwoCycleMove e₀ e₁ hne)))

/-- The controlled cycle operation intertwines two actual native canonical block
contractions, retaining every boundary column. Source: SCP10, Theorem 6.16,
lines 2270–2301. -/
theorem regularProjectorTwistedRegionMatrix_twoCycleMove
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁)
    (ω : RC (Γ := Γ) R T → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorTwistedRegionMatrix R
      (regularTreeCycleAssignment R T (regularTwoCycleMove e₀ e₁ hne ω))
      ((regularRegionCoordinatesEquiv R T hT htree o).symm
        (regularRegionTwoCycleMove R T o e₀ e₁ hne c)) θ =
    regularProjectorTwistedRegionMatrix R (regularTreeCycleAssignment R T ω)
      ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ := by
  rw [regularProjectorTwistedRegionMatrix_treeCycleAssignment_coordinates,
    regularProjectorTwistedRegionMatrix_treeCycleAssignment_coordinates]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  change (if c.1 = (fun e => x * θ e) ∧
      regularTwoCycleMove e₀ e₁ hne c.2.2.2 =
        (fun e => x * regularTwoCycleMove e₀ e₁ hne ω e * x⁻¹) then 1 else 0) = _
  rw [← regularTwoCycleMove_conjugation]
  simp only [Equiv.apply_eq_iff_eq]

/-- Transport the fixed cycle permutation to the original native physical half-edge
coordinates. Source: SCP10, the accessible physical operation in Theorem 6.16. -/
def regularRegionTwoCyclePhysicalMove
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) :=
  (regularRegionCoordinatesEquiv R T hT htree o).trans
    ((regularRegionTwoCycleMove R T o e₀ e₁ hne).trans
      (regularRegionCoordinatesEquiv R T hT htree o).symm)

/-- The two-cycle operation is a unitary on the entire canonical physical block space.
Source: SCP10, the local unitary construction in Theorem 6.16, lines 2270–2301. -/
theorem regularRegionTwoCyclePhysicalMove_matrix_mem_unitaryGroup
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    Matrix.permMatrixHom (R := ℂ)
      (regularRegionTwoCyclePhysicalMove R T hT htree o e₀ e₁ hne) ∈
      Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  (regularRegionTwoCyclePhysicalMove R T hT htree o e₀ e₁ hne)⁻¹
    |>.permMatrix_mem_unitaryGroup

/-- One fixed native physical unitary gives the actual two-cycle coefficient identity,
uniformly in all cycle operators and boundary labels. Source: SCP10, Theorem 6.16. -/
theorem regularProjectorTwistedRegionMatrix_twoCyclePhysicalMove
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁)
    (ω : RC (Γ := Γ) R T → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    Matrix.permMatrixHom (R := ℂ)
        (regularRegionTwoCyclePhysicalMove R T hT htree o e₀ e₁ hne) *ᵥ
      (fun α => regularProjectorTwistedRegionMatrix R
        (regularTreeCycleAssignment R T ω) α θ) =
    (fun α => regularProjectorTwistedRegionMatrix R
      (regularTreeCycleAssignment R T (regularTwoCycleMove e₀ e₁ hne ω)) α θ) := by
  funext α
  rw [Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  have h := regularProjectorTwistedRegionMatrix_twoCycleMove R T hT htree o e₀ e₁ hne ω
    ((regularRegionTwoCycleMove R T o e₀ e₁ hne).symm
      ((regularRegionCoordinatesEquiv R T hT htree o) α)) θ
  simpa only [regularRegionTwoCyclePhysicalMove, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.Perm.inv_def, Function.comp_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.symm_symm] using h.symm

omit [Fintype G] [DecidableEq G] in
/-- Controlled multiplication extends a single insertion to two distinct cycle
coordinates. Source: SCP10, Theorem 6.16, lines 2292–2301. -/
theorem regularTwoCycleMove_single (e₀ e₁ : J) (hne : e₀ ≠ e₁) (g : G) :
    regularTwoCycleMove e₀ e₁ hne (fun e => if e = e₀ then g else 1) =
      (fun e => if e = e₀ ∨ e = e₁ then g else 1) := by
  funext e
  by_cases h₁ : e = e₁
  · subst e
    simp [regularTwoCycleMove, Ne.symm hne]
  · by_cases h₀ : e = e₀
    · subst e
      simp [regularTwoCycleMove, hne]
    · simp [regularTwoCycleMove, h₀, h₁]

/-- One fixed physical unitary extends a one-bond insertion to the two chosen bonds,
uniformly in its group element and boundary configuration. Source: SCP10,
Theorem 6.16, lines 2270–2301. The conclusion concerns the actual canonical
region contraction; no coefficient identity or G-injectivity hypothesis is supplied. -/
theorem exists_unitary_regularTwoCycleFluxMove
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    ∃ Q : Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ,
      Q ∈ Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ ∧
      ∀ (g : G) (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        Q *ᵥ (fun α => regularProjectorTwistedRegionMatrix R
          (regularTreeCycleAssignment R T (fun e => if e = e₀ then g else 1)) α θ) =
        (fun α => regularProjectorTwistedRegionMatrix R
          (regularTreeCycleAssignment R T (fun e => if e = e₀ ∨ e = e₁ then g else 1)) α θ) := by
  refine ⟨Matrix.permMatrixHom (R := ℂ)
    (regularRegionTwoCyclePhysicalMove R T hT htree o e₀ e₁ hne),
    regularRegionTwoCyclePhysicalMove_matrix_mem_unitaryGroup R T hT htree o e₀ e₁ hne, ?_⟩
  intro g θ
  simpa only [regularTwoCycleMove_single] using
    regularProjectorTwistedRegionMatrix_twoCyclePhysicalMove R T hT htree o e₀ e₁ hne
      (fun e => if e = e₀ then g else 1) θ

end TNLean.PEPS
