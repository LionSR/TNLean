/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargePairSectors

/-!
# Two-spin charge outcomes of a correlated regional pair

The two-bond weight remains inside the actual contraction. Splitting one shared
bond and its two physical endpoint factors expresses every column as a sum of
literal two-site character columns. The complete detector therefore selects the
original charge on the first bond and its contragredient on the second, while
leaving every other physical spin fixed.

Source: SCP10, arXiv:1001.3807, charge-pair creation, lines 2505–2558.
**Scope restriction (auxiliary finite-region readout):** The bonds are distinct
internal bonds of a finite simple graph with regular local G-isometric sites.
No native lattice geometry or parent-Hamiltonian membership is asserted here.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
open scoped BigOperators Matrix ComplexOrder
noncomputable section
namespace TNLean.PEPS
variable {W : Type*} [Fintype W] [DecidableEq W]
private abbrev PairRest (w₀ w₁ : W) (hne : w₀ ≠ w₁) :=
  {w : {w : W // w ≠ w₀} // w ≠ ⟨w₁,hne.symm⟩}
private theorem prod_split_two (w₀ w₁ : W) (hne : w₀ ≠ w₁) (f : W → ℂ) :
    ∏ w, f w = f w₀ * f w₁ * ∏ w : PairRest w₀ w₁ hne, f w.1.1 := by
  classical
  have h₀ := Fintype.prod_subtype_mul_prod_subtype (fun w : W => w = w₀) f
  have h₁ := Fintype.prod_subtype_mul_prod_subtype
    (fun w : {w : W // w ≠ w₀} => w = ⟨w₁,hne.symm⟩) (fun w => f w.1)
  simp only [Fintype.prod_unique] at h₀ h₁
  have hd₀ := (default : {w : W // w = w₀}).property
  have hd₁ := congrArg Subtype.val
    (default : {w : {w : W // w ≠ w₀} // w = ⟨w₁,hne.symm⟩}).property
  rw [hd₀] at h₀
  rw [hd₁] at h₁
  rw [← h₀, ← h₁, ← mul_assoc]


variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev RI (R : Finset V) := {e : Edge Γ // IsRegionIncidentEdge R e}
private abbrev RE (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private def bondIndex (R : Finset V) (e : RE (Γ := Γ) R) : RI (Γ := Γ) R :=
  ⟨e.1,Or.inl e.2.1⟩
private def splitLabels (R : Finset V) (e : RE (Γ := Γ) R)
    (ξ : {f : RI (Γ := Γ) R // f ≠ bondIndex R e} → G) (k : G) :
    RI (Γ := Γ) R → G := (Equiv.funSplitAt (bondIndex R e) G).symm (k,ξ)
omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
private theorem splitLabels_same (R : Finset V) (e : RE (Γ := Γ) R)
    (ξ : {f : RI (Γ := Γ) R // f ≠ bondIndex R e} → G) (k l : G)
    (f : RI (Γ := Γ) R) (hf : f ≠ bondIndex R e) :
    splitLabels R e ξ k f = splitLabels R e ξ l f := by
  simp [splitLabels, Equiv.funSplitAt, Equiv.piSplitAt, hf]
omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
private theorem splitLabels_bond (R : Finset V) (e : RE (Γ := Γ) R)
    (ξ : {f : RI (Γ := Γ) R // f ≠ bondIndex R e} → G) (k : G) :
    splitLabels R e ξ k (bondIndex R e) = k := by
  exact congrArg Prod.fst ((Equiv.funSplitAt (bondIndex R e) G).apply_symm_apply (k,ξ))
private def tailVertex (R : Finset V) (e : RE (Γ := Γ) R) : {v // v ∈ R} :=
  ⟨e.1.1.1,e.2.1⟩
private def headVertex (R : Finset V) (e : RE (Γ := Γ) R) : {v // v ∈ R} :=
  ⟨e.1.1.2,e.2.2⟩
private def tailLeg (e : RE (Γ := Γ) R) : IncidentEdge Γ e.1.1.1 := ⟨e.1,Or.inl rfl⟩
private def headLeg (e : RE (Γ := Γ) R) : IncidentEdge Γ e.1.1.2 := ⟨e.1,Or.inr rfl⟩
omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem endpoints_ne (R : Finset V) (e : RE (Γ := Γ) R) :
    tailVertex R e ≠ headVertex R e :=
  fun h => (ne_of_lt e.1.2.1) (congrArg Subtype.val h)
private def replacePair (R : Finset V) (e : RE (Γ := Γ) R)
    (s : {v // v ∈ R} → Fin d) (t : Fin d × Fin d) : {v // v ∈ R} → Fin d :=
  fun w => if w = tailVertex R e then t.1 else if w = headVertex R e then t.2 else s w
private def labelsAt (R : Finset V) (η : RI (Γ := Γ) R → G)
    (w : {v // v ∈ R}) : IncidentEdge Γ w.1 → G :=
  fun f => η ⟨f.1,isRegionIncidentEdge_of_regionVertex R w f⟩
private def pairBoundary (R : Finset V) (e : RE (Γ := Γ) R)
    (ξ : {f : RI (Γ := Γ) R // f ≠ bondIndex R e} → G) :
    ({f : IncidentEdge Γ e.1.1.1 // f ≠ tailLeg e} → G) ×
    ({f : IncidentEdge Γ e.1.1.2 // f ≠ headLeg e} → G) :=
  (fun f => labelsAt R (splitLabels R e ξ 1) (tailVertex R e) f.1,
   fun f => labelsAt R (splitLabels R e ξ 1) (headVertex R e) f.1)
omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem endpointLabels (R : Finset V) (e : RE (Γ := Γ) R)
    (ξ : {f : RI (Γ := Γ) R // f ≠ bondIndex R e} → G) (k : G) :
    labelsAt R (splitLabels R e ξ k) (tailVertex R e) =
      (Equiv.funSplitAt (tailLeg e) G).symm (k,(pairBoundary R e ξ).1) ∧
    labelsAt R (splitLabels R e ξ k) (headVertex R e) =
      (Equiv.funSplitAt (headLeg e) G).symm (k,(pairBoundary R e ξ).2) := by
  constructor
  · apply (Equiv.funSplitAt (tailLeg e) G).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact splitLabels_bond R e ξ k
    · funext f
      exact splitLabels_same R e ξ k 1 _
        (fun h => f.2 (Subtype.ext (congrArg (fun b : RI (Γ := Γ) R => b.1) h)))
  · apply (Equiv.funSplitAt (headLeg e) G).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact splitLabels_bond R e ξ k
    · funext f
      exact splitLabels_same R e ξ k 1 _
        (fun h => f.2 (Subtype.ext (congrArg (fun b : RI (Γ := Γ) R => b.1) h)))


private def weightedColumn
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    (e f : RE (Γ := Γ) R) (weight : G → G → ℂ)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G)
    (s : {v // v ∈ R} → Fin d) : ℂ :=
  ∑ η : RI (Γ := Γ) R → G,
    if (fun b : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
        η ⟨b.1,isRegionBoundaryEdge_touches R b.2⟩) = θ then
      weight (η (bondIndex R e)) (η (bondIndex R f)) *
        ∏ w : {v // v ∈ R}, a w.1 (labelsAt R η w) (s w)
    else 0
private def restCoefficient
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    (e : RE (Γ := Γ) R) (ξ : {f : RI (Γ := Γ) R // f ≠ bondIndex R e} → G)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G)
    (s : {v // v ∈ R} → Fin d) : ℂ :=
  if (fun b : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      splitLabels R e ξ 1 ⟨b.1,isRegionBoundaryEdge_touches R b.2⟩) = θ then
    ∏ w : PairRest (tailVertex R e) (headVertex R e) (endpoints_ne R e),
      a w.1.1.1 (labelsAt R (splitLabels R e ξ 1) w.1.1) (s w.1.1)
  else 0
private theorem shared_expansion
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    (e f : RE (Γ := Γ) R) (hne : e ≠ f) (weight : G → G → ℂ)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G)
    (s : {v // v ∈ R} → Fin d) (t : Fin d × Fin d) :
    weightedColumn a R e f weight θ (replacePair R e s t) =
      ∑ ξ : {b : RI (Γ := Γ) R // b ≠ bondIndex R e} → G,
        restCoefficient a R e ξ θ s *
          regularTwoSitePhysicalChargeColumn (tailLeg e) (headLeg e)
            (a e.1.1.1) (a e.1.1.2)
            (fun k => weight k (splitLabels R e ξ 1 (bondIndex R f))) 1
            (pairBoundary R e ξ) t := by
  classical
  unfold weightedColumn
  rw [← (Equiv.funSplitAt (bondIndex R e) G).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  simp only [regularTwoSitePhysicalChargeColumn, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hb : (fun b : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      splitLabels R e ξ k ⟨b.1,isRegionBoundaryEdge_touches R b.2⟩) =
      (fun b : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      splitLabels R e ξ 1 ⟨b.1,isRegionBoundaryEdge_touches R b.2⟩) := by
    funext b
    apply splitLabels_same
    intro h
    have he : b.1 = e.1 := congrArg Subtype.val h
    have hbad := b.2
    rw [he] at hbad
    rcases hbad with hbad | hbad
    · exact hbad.2 e.2.2
    · exact hbad.1 e.2.1
  have hf : bondIndex R f ≠ bondIndex R e :=
    fun h => hne (Subtype.ext (congrArg Subtype.val h).symm)
  have hl := endpointLabels R e ξ k
  have hr (w : PairRest (tailVertex R e) (headVertex R e) (endpoints_ne R e)) :
      labelsAt R (splitLabels R e ξ k) w.1.1 =
        labelsAt R (splitLabels R e ξ 1) w.1.1 := by
    funext b
    apply splitLabels_same
    intro h
    have he : b.1 = e.1 := congrArg Subtype.val h
    have hinc := b.2
    rw [he] at hinc
    rcases hinc with hinc | hinc
    · exact w.1.2 (Subtype.ext hinc.symm)
    · exact w.2 (Subtype.ext (Subtype.ext hinc.symm))
  change (if (fun b => splitLabels R e ξ k ⟨b.1,_⟩) = θ then _ else 0) = _
  rw [hb]
  unfold restCoefficient
  split_ifs
  · change weight (splitLabels R e ξ k (bondIndex R e))
        (splitLabels R e ξ k (bondIndex R f)) *
        (∏ w, a w.1 (labelsAt R (splitLabels R e ξ k) w) (replacePair R e s t w)) = _
    rw [splitLabels_bond, splitLabels_same R e ξ k 1 _ hf,
      prod_split_two (tailVertex R e) (headVertex R e) (endpoints_ne R e)]
    simp only [replacePair, ite_true, endpoints_ne R e, ite_false, hl.1, hl.2]
    have hrest : (∏ w : PairRest (tailVertex R e) (headVertex R e) (endpoints_ne R e),
        a w.1.1.1 (labelsAt R (splitLabels R e ξ k) w.1.1)
          (if w.1.1 = tailVertex R e then t.1
           else if w.1.1 = headVertex R e then t.2 else s w.1.1)) =
        ∏ w : PairRest (tailVertex R e) (headVertex R e) (endpoints_ne R e),
          a w.1.1.1 (labelsAt R (splitLabels R e ξ 1) w.1.1) (s w.1.1) := by
      apply Finset.prod_congr rfl
      intro w _
      rw [ite_eq_right w.1.2, ite_eq_right (fun h => w.2 (Subtype.ext h)), hr]
    rw [hrest]
    simp only [(endpoints_ne R e).symm, ite_false]
    dsimp only [tailVertex, headVertex]
    ring
  · simp


omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem replacePair_current (R : Finset V) (e : RE (Γ := Γ) R)
    (s : {v // v ∈ R} → Fin d) :
    replacePair R e s (s (tailVertex R e),s (headVertex R e)) = s := by
  funext w
  simp only [replacePair]
  split_ifs <;> subst_vars <;> rfl
private theorem action_of_shared_slices
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    (e f : RE (Γ := Γ) R) (hne : e ≠ f) (weight : G → G → ℂ)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G)
    (Q : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (selected : Prop) [Decidable selected]
    (hact : ∀ ξ : {b : RI (Γ := Γ) R // b ≠ bondIndex R e} → G,
      Q *ᵥ regularTwoSitePhysicalChargeColumn (tailLeg e) (headLeg e)
        (a e.1.1.1) (a e.1.1.2)
        (fun k => weight k (splitLabels R e ξ 1 (bondIndex R f))) 1 (pairBoundary R e ξ) =
      if selected then regularTwoSitePhysicalChargeColumn (tailLeg e) (headLeg e)
        (a e.1.1.1) (a e.1.1.2)
        (fun k => weight k (splitLabels R e ξ 1 (bondIndex R f))) 1 (pairBoundary R e ξ)
      else 0)
    (s : {v // v ∈ R} → Fin d) :
    (∑ t : Fin d × Fin d, Q (s (tailVertex R e),s (headVertex R e)) t *
      weightedColumn a R e f weight θ (replacePair R e s t)) =
      if selected then weightedColumn a R e f weight θ s else 0 := by
  classical
  simp_rw [shared_expansion a R e f hne]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hcurrent := shared_expansion a R e f hne weight θ s
    (s (tailVertex R e),s (headVertex R e))
  rw [replacePair_current] at hcurrent
  rw [hcurrent]
  have hs (ξ : {b : RI (Γ := Γ) R // b ≠ bondIndex R e} → G) :
      (∑ t, Q (s (tailVertex R e),s (headVertex R e)) t *
        (restCoefficient a R e ξ θ s * regularTwoSitePhysicalChargeColumn
          (tailLeg e) (headLeg e) (a e.1.1.1) (a e.1.1.2)
          (fun k => weight k (splitLabels R e ξ 1 (bondIndex R f))) 1
          (pairBoundary R e ξ) t)) =
      restCoefficient a R e ξ θ s * (Q *ᵥ regularTwoSitePhysicalChargeColumn
        (tailLeg e) (headLeg e) (a e.1.1.1) (a e.1.1.2)
        (fun k => weight k (splitLabels R e ξ 1 (bondIndex R f))) 1
        (pairBoundary R e ξ)) (s (tailVertex R e),s (headVertex R e)) := by
    change (Q *ᵥ (restCoefficient a R e ξ θ s • _)) _ = _
    rw [Matrix.mulVec_smul]
    rfl
  simp_rw [hs, hact]
  by_cases h : selected <;> simp [h]

/-- Apply a two-spin operator at the ordered endpoints of one actual internal
bond, leaving every other physical spin fixed. Source: SCP10, the two local
charge readouts after charge-pair preparation, lines 2514–2558. -/
def regularChargePairEndpointAction (R : Finset V)
    (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R})
    (Q : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ψ : ({v // v ∈ R} → Fin d) → ℂ) (s : {v // v ∈ R} → Fin d) : ℂ :=
  ∑ t : Fin d × Fin d, Q (s ⟨e.1.1.1,e.2.1⟩,s ⟨e.1.1.2,e.2.2⟩) t *
    ψ (replacePair R e s t)

open scoped Classical in
/-- The actual correlated two-bond contraction lies in the original charge
sector on its first bond and the contragredient sector on its second bond.
Each complete measurement acts only on the two endpoint spins of its bond.
Both measurements precede all charge, internal and boundary labels.
Source: SCP10, charge-pair preparation and its two charge outcomes,
lines 2505–2558; auxiliary finite-region form. -/
theorem exists_regularChargePairEndpointMeasurements
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (e₀ e₁ : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) (hne : e₀ ≠ e₁) :
    ∃ Q : Bool → Option (regularChargeLabels (G := G)) →
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      (∀ n r, (Q n r).IsHermitian ∧ (Q n r).PosSemidef) ∧
      (∀ n r s, Q n r * Q n s = if r = s then Q n r else 0) ∧
      (∀ n, ∑ r, Q n r = 1) ∧
      ∀ n (χ : regularChargeLabels (G := G)) r p θ,
        regularChargePairEndpointAction R (if n then e₁ else e₀) (Q n r)
            (fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ χ.val p s θ) =
          if r = some (if n then regularDualChargeLabel χ else χ) then
            (fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ χ.val p s θ) else 0 := by
  obtain ⟨Q₀,hH₀,hO₀,hI₀,hT₀,_⟩ :=
    exists_regularPhysicalChargePairSliceMeasurement (tailLeg e₀) (headLeg e₀)
      (a e₀.1.1.1) (a e₀.1.1.2) (ha _) (ha _)
  obtain ⟨Q₁,hH₁,hO₁,hI₁,_,hT₁⟩ :=
    exists_regularPhysicalChargePairSliceMeasurement (tailLeg e₁) (headLeg e₁)
      (a e₁.1.1.1) (a e₁.1.1.2) (ha _) (ha _)
  let Q := fun n : Bool => if n then Q₁ else Q₀
  refine ⟨Q,?_,?_,?_,?_⟩
  · intro n
    cases n <;> simp only [Q,Bool.false_eq_true,ite_false,ite_true] <;> assumption
  · intro n
    cases n <;> simp only [Q,Bool.false_eq_true,ite_false,ite_true] <;> assumption
  · intro n
    cases n with
    | false =>
      change (∑ r, Q₀ r) = 1
      refine hI₀.trans ?_
      ext x y
      simp only [Matrix.one_apply]
      split_ifs <;> rfl
    | true =>
      change (∑ r, Q₁ r) = 1
      refine hI₁.trans ?_
      ext x y
      simp only [Matrix.one_apply]
      split_ifs <;> rfl
  · intro n χ r p θ
    funext s
    cases n with
    | false =>
      change (∑ t, Q₀ r (s (tailVertex R e₀),s (headVertex R e₀)) t *
        weightedColumn a R e₀ e₁ (fun k m => χ.val (p * m⁻¹ * k)) θ
          (replacePair R e₀ s t)) = _
      have h := action_of_shared_slices a R e₀ e₁ hne
        (fun k m => χ.val (p * m⁻¹ * k)) θ (Q₀ r) (r = some χ)
        (fun ξ => hT₀ χ r p (splitLabels R e₀ ξ 1 (bondIndex R e₁))
          (pairBoundary R e₀ ξ)) s
      simp only [Bool.false_eq_true,ite_false,ite_apply,Pi.zero_apply]
      convert h using 1
      rfl
    | true =>
      change (∑ t, Q₁ r (s (tailVertex R e₁),s (headVertex R e₁)) t *
        weightedColumn a R e₁ e₀ (fun k m => χ.val (p * k⁻¹ * m)) θ
          (replacePair R e₁ s t)) = _
      have h := action_of_shared_slices a R e₁ e₀ hne.symm
        (fun k m => χ.val (p * k⁻¹ * m)) θ (Q₁ r)
        (r = some (regularDualChargeLabel χ))
        (fun ξ => hT₁ χ r p (splitLabels R e₁ ξ 1 (bondIndex R e₀))
          (pairBoundary R e₁ ξ)) s
      simp only [ite_true,ite_apply,Pi.zero_apply]
      convert h using 1
      rfl
end TNLean.PEPS
