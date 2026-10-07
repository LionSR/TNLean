/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularClosedGauge
import TNLean.PEPS.RegularProjectorTwistedRegion

/-!
# Supported orbit expansions of regular half-edge functions

A function of the independent half-edge labels which is invariant under
vertex left translations and simultaneous right translations on each bond
is a linear combination of the actual inserted regular-projector closed
coefficients. The coefficient at a bond assignment is the function evaluated
at its canonical half-edge representative. Consequently a support condition
on the bond quotient restricts the expansion before any summation occurs.
In particular, flat support gives an expansion using only flat assignments;
no conclusion about individual summands is inferred from a vanishing sum.

Source: SCP10, arXiv:1001.3807, proof of Theorem 5.5, lines 1440–1514,
and accessible regular coordinates, lines 1765–1920. This is the regular
representation orbit calculation, not the full semiregular closure theorem.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V]
variable {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- One independent regular group label at each end of each graph edge.
Source: SCP10, accessible regular coordinates, lines 1765–1820. -/
abbrev RegularHalfEdgeConfig (Γ : SimpleGraph V) (G : Type*) :=
  (v : V) → IncidentEdge Γ v → G

/-- Independent left translations at the vertices.
Source: SCP10, regular invariant virtual coordinates, lines 1765–1820. -/
def regularHalfEdgeLeftMul (k : V → G) (α : RegularHalfEdgeConfig Γ G) :
    RegularHalfEdgeConfig Γ G := fun v e => k v * α v e

/-- The same right translation on the two ends of each edge.
Source: SCP10, shared regular reference labels, lines 1765–1920. -/
def regularHalfEdgeRightMul (r : Edge Γ → G) (α : RegularHalfEdgeConfig Γ G) :
    RegularHalfEdgeConfig Γ G := fun v e => α v e * r e.1

/-- The oriented quotient of the head and tail half-edge labels.
Source: SCP10, group-valued closure constraints, lines 1470–1514. -/
def regularHalfEdgeOperators (α : RegularHalfEdgeConfig Γ G) : Edge Γ → G :=
  fun e => α e.1.2 ⟨e, Or.inr rfl⟩ * (α e.1.1 ⟨e, Or.inl rfl⟩)⁻¹

/-- The labels obtained from an inserted operator and a shared bond label.
Source: SCP10, inserted regular operators, lines 1515–1525. -/
def regularHalfEdgeOfBonds (u η : Edge Γ → G) : RegularHalfEdgeConfig Γ G :=
  fun v => regularTwistedLabels u v (fun e => η e.1)

/-- The canonical representative has identity tail labels.
Source: SCP10, regular reference coordinates, lines 1765–1920. -/
def regularHalfEdgeOfOperators (u : Edge Γ → G) : RegularHalfEdgeConfig Γ G :=
  regularHalfEdgeOfBonds u (fun _ => 1)

@[simp]
theorem regularHalfEdgeOfBonds_tail (u η : Edge Γ → G) (e : Edge Γ) :
    regularHalfEdgeOfBonds u η e.1.1 ⟨e, Or.inl rfl⟩ = η e := by
  simp [regularHalfEdgeOfBonds, regularTwistedLabels, ne_of_lt e.2.1]

@[simp]
theorem regularHalfEdgeOfBonds_head (u η : Edge Γ → G) (e : Edge Γ) :
    regularHalfEdgeOfBonds u η e.1.2 ⟨e, Or.inr rfl⟩ = u e * η e := by
  simp [regularHalfEdgeOfBonds, regularTwistedLabels]

@[simp]
theorem regularHalfEdgeOperators_ofBonds (u η : Edge Γ → G) :
    regularHalfEdgeOperators (regularHalfEdgeOfBonds u η) = u := by
  funext e
  simp [regularHalfEdgeOperators]

@[simp]
theorem regularHalfEdgeOperators_ofOperators (u : Edge Γ → G) :
    regularHalfEdgeOperators (regularHalfEdgeOfOperators u) = u :=
  regularHalfEdgeOperators_ofBonds u _

/-- Operator and reference labels parametrize all half-edge configurations
bijectively. Source: SCP10, regular coordinates, lines 1765–1920. -/
def regularHalfEdgeConfigEquivOperatorsBonds :
    ((Edge Γ → G) × (Edge Γ → G)) ≃ RegularHalfEdgeConfig Γ G where
  toFun p := regularHalfEdgeOfBonds p.1 p.2
  invFun α := (regularHalfEdgeOperators α, fun e => α e.1.1 ⟨e, Or.inl rfl⟩)
  left_inv p := by
    apply Prod.ext
    · exact regularHalfEdgeOperators_ofBonds p.1 p.2
    · funext e
      exact regularHalfEdgeOfBonds_tail p.1 p.2 e
  right_inv α := by
    funext v e
    simp only [regularHalfEdgeOfBonds, regularTwistedLabels, regularHalfEdgeOperators]
    rcases e with ⟨e, h | h⟩
    · subst v
      simp [ne_of_lt e.2.1]
    · subst v
      simp

/-- Shared right translations do not change the bond quotient.
Source: SCP10, shared regular references, lines 1765–1920. -/
@[simp]
theorem regularHalfEdgeOperators_rightMul (r : Edge Γ → G)
    (α : RegularHalfEdgeConfig Γ G) :
    regularHalfEdgeOperators (regularHalfEdgeRightMul r α) = regularHalfEdgeOperators α := by
  funext e
  simp [regularHalfEdgeOperators, regularHalfEdgeRightMul, mul_assoc]

/-- Vertex left translations act on quotients by the endpoint gauge rule.
Source: SCP10, closure-string deformation, lines 1622–1647. -/
theorem regularHalfEdgeOperators_leftMul (k : V → G) (α : RegularHalfEdgeConfig Γ G) :
    regularHalfEdgeOperators (regularHalfEdgeLeftMul k α) =
      regularVertexGaugeOperators (fun v => (k v)⁻¹) (regularHalfEdgeOperators α) := by
  funext e
  simp [regularHalfEdgeOperators, regularHalfEdgeLeftMul, regularVertexGaugeOperators,
    mul_assoc]

/-- The bond reference labels act by shared right multiplication on the
canonical representative. Source: SCP10, lines 1765–1920. -/
theorem regularHalfEdgeOfBonds_eq_rightMul (u η : Edge Γ → G) :
    regularHalfEdgeOfBonds u η = regularHalfEdgeRightMul η (regularHalfEdgeOfOperators u) := by
  funext v e
  simp only [regularHalfEdgeOfBonds, regularHalfEdgeRightMul, regularHalfEdgeOfOperators,
    regularTwistedLabels]
  split_ifs <;> simp

variable [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G]

/-- Full-region and global half-edge coordinates differ only by membership
proofs. Source: SCP10, full regular contraction, lines 1515–1525. -/
def fullRegionHalfEdgeConfigEquiv :
    RegionHalfEdgeConfig (Γ := Γ) G Finset.univ ≃ RegularHalfEdgeConfig Γ G where
  toFun α v := α ⟨v, Finset.mem_univ v⟩
  invFun α w := α w.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual closed contraction of canonical regular averaging projectors
with the prescribed inserted bond operators. Source: SCP10, closure and
accessible regular coordinates, lines 1515–1525 and 1765–1920. -/
noncomputable def regularProjectorClosedState (u : Edge Γ → G) :
    RegularHalfEdgeConfig Γ G → ℂ := fun α =>
  ∑ η : Edge Γ → G, ∏ v, regularLegProjector (IncidentEdge Γ v)
    (α v) (regularHalfEdgeOfBonds u η v)

private theorem regularProjectorProduct_apply (α β : RegularHalfEdgeConfig Γ G) :
    (∏ v, regularLegProjector (IncidentEdge Γ v) (α v) (β v)) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∑ k : V → G, if α = regularHalfEdgeLeftMul k β then 1 else 0 := by
  classical
  simp only [regularLegProjector_apply, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]
  rw [Fintype.prod_sum_boole]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [funext_iff, regularHalfEdgeLeftMul, Pi.smul_apply, smul_eq_mul]

/-- A gauge-invariant condition on operator assignments is preserved by each
canonical closed vector whose assignment satisfies it. Source: SCP10,
regular closure constraints and string deformation, lines 1440–1514
and 1622–1647. -/
theorem regularProjectorClosedState_eq_zero_of_not_support
    (P : (Edge Γ → G) → Prop)
    (hP : ∀ k u, P u → P (regularVertexGaugeOperators k u))
    {u : Edge Γ → G} (hu : P u) (α : RegularHalfEdgeConfig Γ G)
    (hα : ¬ P (regularHalfEdgeOperators α)) :
    regularProjectorClosedState u α = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro η _
  rw [regularProjectorProduct_apply]
  have hne (k : V → G) : α ≠ regularHalfEdgeLeftMul k (regularHalfEdgeOfBonds u η) := by
    intro heq
    apply hα
    rw [heq, regularHalfEdgeOperators_leftMul, regularHalfEdgeOperators_ofBonds]
    exact hP _ _ hu
  simp only [hne, ↓reduceIte, Finset.sum_const_zero, mul_zero]

private theorem sum_regularProjectorProduct_eq
    (f : RegularHalfEdgeConfig Γ G → ℂ)
    (hleft : ∀ k α, f (regularHalfEdgeLeftMul k α) = f α)
    (α : RegularHalfEdgeConfig Γ G) :
    (∑ β, f β * ∏ v, regularLegProjector (IncidentEdge Γ v) (α v) (β v)) = f α := by
  classical
  simp_rw [regularProjectorProduct_apply]
  simp_rw [← mul_assoc, mul_comm (f _) ((Fintype.card G : ℂ)⁻¹ ^ _), mul_assoc]
  rw [← Finset.mul_sum]
  have hswap :
      (∑ β : RegularHalfEdgeConfig Γ G, f β *
        ∑ k : V → G, if α = regularHalfEdgeLeftMul k β then 1 else 0) =
      ∑ k : V → G, ∑ β : RegularHalfEdgeConfig Γ G,
        f β * if α = regularHalfEdgeLeftMul k β then 1 else 0 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  have hinner (k : V → G) :
      (∑ β : RegularHalfEdgeConfig Γ G,
        f β * if α = regularHalfEdgeLeftMul k β then 1 else 0) = f α := by
    have heq (β : RegularHalfEdgeConfig Γ G) :
        α = regularHalfEdgeLeftMul k β ↔
          β = regularHalfEdgeLeftMul (fun v => (k v)⁻¹) α := by
      constructor
      · intro h
        funext v e
        have hv := congrFun (congrFun h v) e
        dsimp [regularHalfEdgeLeftMul] at hv ⊢
        rw [hv, inv_mul_cancel_left]
      · rintro rfl
        funext v e
        simp [regularHalfEdgeLeftMul]
    simp_rw [heq, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq']
    exact hleft _ _
  simp_rw [hinner]
  simp [← Nat.cast_pow]

/-- Every left-vertex- and right-bond-invariant half-edge function is the
explicit sum of canonical inserted closed coefficients, with coefficients
given by evaluation on the canonical representatives. Source: SCP10,
regular-coordinate closure calculation, lines 1440–1514 and 1765–1920. -/
theorem eq_sum_regularProjectorClosedState_of_invariant
    (f : RegularHalfEdgeConfig Γ G → ℂ)
    (hleft : ∀ k α, f (regularHalfEdgeLeftMul k α) = f α)
    (hright : ∀ r α, f (regularHalfEdgeRightMul r α) = f α) :
    f = ∑ u : Edge Γ → G,
      f (regularHalfEdgeOfOperators u) • regularProjectorClosedState u := by
  classical
  funext α
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, regularProjectorClosedState]
  symm
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun p : (Edge Γ → G) × (Edge Γ → G) =>
    f (regularHalfEdgeOfOperators p.1) * ∏ v,
      regularLegProjector (IncidentEdge Γ v) (α v) (regularHalfEdgeOfBonds p.1 p.2 v))]
  have hcoeff (p : (Edge Γ → G) × (Edge Γ → G)) :
      f (regularHalfEdgeOfOperators p.1) = f (regularHalfEdgeOfBonds p.1 p.2) := by
    rw [regularHalfEdgeOfBonds_eq_rightMul, hright]
  simp_rw [hcoeff]
  change (∑ p : (Edge Γ → G) × (Edge Γ → G),
    f (regularHalfEdgeConfigEquivOperatorsBonds p) *
      ∏ v, regularLegProjector (IncidentEdge Γ v) (α v)
        (regularHalfEdgeConfigEquivOperatorsBonds p v)) = f α
  exact (Equiv.sum_comp regularHalfEdgeConfigEquivOperatorsBonds
    (fun β => f β * ∏ v, regularLegProjector (IncidentEdge Γ v) (α v) (β v))).trans
    (sum_regularProjectorProduct_eq f hleft α)

open scoped Classical in
/-- A pointwise support condition restricts the constructed expansion to the
supported operator assignments themselves. No summand-wise inference from a
vanishing sum is needed. Source: SCP10, regular closure constraints,
lines 1440–1514 and 1765–1920. -/
theorem eq_sum_supported_regularProjectorClosedState_of_invariant
    (P : (Edge Γ → G) → Prop) (f : RegularHalfEdgeConfig Γ G → ℂ)
    (hleft : ∀ k α, f (regularHalfEdgeLeftMul k α) = f α)
    (hright : ∀ r α, f (regularHalfEdgeRightMul r α) = f α)
    (hsupport : ∀ α, ¬ P (regularHalfEdgeOperators α) → f α = 0) :
    f = ∑ u : {u : Edge Γ → G // P u},
      f (regularHalfEdgeOfOperators u.1) • regularProjectorClosedState u.1 := by
  classical
  trans ∑ u : Edge Γ → G,
    f (regularHalfEdgeOfOperators u) • regularProjectorClosedState u
  · exact eq_sum_regularProjectorClosedState_of_invariant f hleft hright
  refine Finset.sum_congr_set {u | P u} _ _ (fun _ _ => rfl) ?_
  intro u hnot
  have hz := hsupport (regularHalfEdgeOfOperators u)
  simp only [regularHalfEdgeOperators_ofOperators] at hz
  rw [hz hnot, zero_smul]

open scoped Classical in
/-- The supported orbit expansion gives membership in the span of the actual
inserted canonical closed vectors with supported operator assignments.
Source: SCP10, regular closure calculation, lines 1440–1514 and 1765–1920. -/
theorem mem_span_supported_regularProjectorClosedState_of_invariant
    (P : (Edge Γ → G) → Prop) (f : RegularHalfEdgeConfig Γ G → ℂ)
    (hleft : ∀ k α, f (regularHalfEdgeLeftMul k α) = f α)
    (hright : ∀ r α, f (regularHalfEdgeRightMul r α) = f α)
    (hsupport : ∀ α, ¬ P (regularHalfEdgeOperators α) → f α = 0) :
    f ∈ Submodule.span ℂ
      (Set.range (fun u : {u : Edge Γ → G // P u} => regularProjectorClosedState u.1)) := by
  classical
  rw [eq_sum_supported_regularProjectorClosedState_of_invariant P f hleft hright hsupport]
  apply Submodule.sum_mem
  intro u _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self u))

/-- The closed projector vector is the full-region column of the existing
canonical inserted-region contraction, in global half-edge coordinates.
Source: SCP10, regular closure contraction, lines 1515–1525 and 1765–1920. -/
theorem regularProjectorClosedState_eq_twistedRegionMatrix
    (u : Edge Γ → G) (α : RegularHalfEdgeConfig Γ G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge (Finset.univ : Finset V) e} → G) :
    regularProjectorClosedState u α =
      regularProjectorTwistedRegionMatrix Finset.univ u
        (fullRegionHalfEdgeConfigEquiv.symm α) θ := by
  classical
  let E : (Edge Γ → G) ≃
      ({e : Edge Γ // IsRegionIncidentEdge (Finset.univ : Finset V) e} → G) :=
    { toFun := fun η e => η e.1
      invFun := fun η e => η ⟨e, Or.inl (Finset.mem_univ _)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold regularProjectorClosedState regularProjectorTwistedRegionMatrix
  refine Fintype.sum_equiv E _ _ ?_
  intro η
  have hb : (fun e : {e : Edge Γ // IsRegionBoundaryEdge (Finset.univ : Finset V) e} =>
      E η ⟨e.1, isRegionBoundaryEdge_touches _ e.2⟩) = θ := by
    funext e
    exact False.elim (by simpa [IsRegionBoundaryEdge] using e.2)
  rw [ite_eq_left hb]
  exact Finset.prod_subtype Finset.univ (fun _ => Iff.rfl)
    (fun v => regularLegProjector (IncidentEdge Γ v) (α v) (regularHalfEdgeOfBonds u η v))

/-- Applying the original site tensors to the canonical inserted closed
vector recovers the actual inserted physical PEPS contraction.
Source: SCP10, inverse regular coordinates and closure contraction,
lines 1515–1525 and 1765–1820. -/
theorem sum_regularProjectorClosedState_eq_stateCoeff {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (u : Edge Γ → G) (σ : V → Fin d) :
    (∑ α : RegularHalfEdgeConfig Γ G, (∏ v, a v (α v) (σ v)) *
      regularProjectorClosedState u α) =
      stateCoeff (groupBondTensor (regularTwistedSite a u)) σ := by
  classical
  simp only [regularProjectorClosedState, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.prod_mul_distrib]
  have hlocal (η : Edge Γ → G) :
      (∑ α : RegularHalfEdgeConfig Γ G,
        ∏ v, a v (α v) (σ v) * regularLegProjector (IncidentEdge Γ v)
          (α v) (regularHalfEdgeOfBonds u η v)) =
      ∏ v, a v (regularHalfEdgeOfBonds u η v) (σ v) := by
    rw [← Fintype.prod_sum (fun (v : V) (β : IncidentEdge Γ v → G) =>
      a v β (σ v) * regularLegProjector (IncidentEdge Γ v) β (regularHalfEdgeOfBonds u η v))]
    apply Finset.prod_congr rfl
    intro v _
    exact (ha v).regularSiteMap_projector_coefficients _ _
  simp_rw [hlocal]
  let E : (Edge Γ → G) ≃ VirtualConfig (groupBondTensor (regularTwistedSite a u)) :=
    Equiv.piCongrRight fun _ => Fintype.equivFin G
  unfold stateCoeff
  refine Fintype.sum_equiv E _ _ ?_
  intro η
  apply Finset.prod_congr rfl
  intro v _
  simp only [groupBondTensor, E, Equiv.piCongrRight_apply, Pi.map_apply,
    Equiv.symm_apply_apply, regularTwistedSite, regularHalfEdgeOfBonds]

end TNLean.PEPS
