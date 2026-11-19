import TNLean.PEPS.RegionBlock.PartitionTensor

/-! # Contraction indices for partition blocking -/

open ManyBody (Edge)
open scoped BigOperators
namespace TNLean.PEPS.PartitionBonds
variable {V B : Type*} [Fintype V] [LinearOrder V] [Fintype B] [LinearOrder B]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (block : V → B) {d D : ℕ}
variable (A : Tensor G d)

abbrev CrossLabels := (e : Crossing block) → Fin (A.bondDim e.1)
abbrev InnerLabels (b : B) :=
  (e : {e : Internal (G := G) block // block e.1.1.1 = b}) → Fin (A.bondDim e.1.1)

def innerByBlock :
    ((e : Internal block) → Fin (A.bondDim e.1)) ≃ ((b : B) → InnerLabels block A b) where
  toFun x _ e := x e.1
  invFun y e := y _ ⟨e, rfl⟩
  left_inv _ := rfl
  right_inv y := by
    funext b e
    obtain ⟨e, rfl⟩ := e
    rfl

noncomputable def coarseLabels :
    ((q : Edge (G.map block)) → Fin (bundleDim block A q)) ≃ CrossLabels block A :=
  (Equiv.piCongrRight (decode block A)).trans
    (crossingLabels block (fun e => Fin (A.bondDim e))).symm

def restrictCross (x : CrossLabels block A) (b : B) :
    RegionBoundaryConfig A (sites block b) :=
  boundaryLabels block A b (fun q => crossingLabels block (fun e => Fin (A.bondDim e)) x q.1)

variable [DecidableRel (G.map block).Adj]
variable (phys : ∀ b, Fin D ≃ RegionPhysicalConfig (d := d) (sites block b))

omit [Fintype B] [DecidableRel (G.map block).Adj] in
theorem sharedBoundary (x : CrossLabels block A) (b : B) :
    legs block A b (fun q => (coarseLabels block A).symm x q.1) = restrictCross block A x b := by
  change boundaryLabels block A b
    (fun q => decode block A q.1 ((coarseLabels block A).symm x q.1)) = _
  unfold restrictCross
  apply congrArg (boundaryLabels block A b)
  funext q
  exact (decode block A q.1).apply_symm_apply _

theorem coarse_sum (s : B → Fin D) :
    stateCoeff (coarseTensor block A phys) s =
      ∑ x : CrossLabels block A, ∏ b,
        openRegionWeight A (sites block b) (restrictCross block A x b) (phys b (s b)) := by
  classical
  unfold stateCoeff
  let f (z : (q : Edge (G.map block)) → Fin (bundleDim block A q)) :=
    ∏ b, openRegionWeight A (sites block b) (legs block A b (fun q => z q.1)) (phys b (s b))
  change (∑ z, f z) = _
  apply ((coarseLabels block A).symm.sum_comp f).symm.trans
  apply Finset.sum_congr rfl
  intro x _
  unfold f
  apply Finset.prod_congr rfl
  intro b _
  rw [sharedBoundary]


/-- Assemble a fine assignment by taking each internal label from its unique block
and every crossing label from the common global tuple. -/
def assemble :
    CrossLabels block A × ((b : B) → InnerLabels block A b) ≃ VirtualConfig A :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongr (innerByBlock block A).symm
      (crossingLabels block (fun e => Fin (A.bondDim e)))).trans
        (globalLabels block (fun e => Fin (A.bondDim e))).symm)

noncomputable def physical (s : B → Fin D) (v : V) : Fin d :=
  phys (block v) (s (block v)) ⟨v, by simp [sites]⟩

omit [DecidableRel (G.map block).Adj] in
/-- Reindex the fine coefficient by a shared crossing assignment and a family of
internal assignments indexed by their unique blocks. -/
theorem fine_sum (s : B → Fin D) :
    stateCoeff A (physical block phys s) =
      ∑ x : CrossLabels block A, ∑ y : (b : B) → InnerLabels block A b,
        ∏ b, ∏ v : {v // v ∈ sites block b},
          A.component v.1 (fun e => assemble block A (x, y) e.1) (phys b (s b) v) := by
  classical
  let f (z : VirtualConfig A) :=
    ∏ v, A.component v (fun e => z e.1) (physical block phys s v)
  change (∑ z, f z) = _
  apply ((assemble block A).sum_comp f).symm.trans
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  let vEquiv : (Σ b, {v // v ∈ sites block b}) ≃ V :=
    { toFun := fun p => p.2.1
      invFun := fun v => ⟨block v, v, by simp [sites]⟩
      right_inv := fun _ => rfl
      left_inv := by
        rintro ⟨b, v, h⟩
        obtain rfl : block v = b := (Finset.mem_filter.mp h).2
        rfl }
  unfold f
  rw [← vEquiv.prod_comp, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro b _
  apply Finset.prod_congr rfl
  rintro ⟨v, hv⟩ _
  obtain rfl : block v = b := (Finset.mem_filter.mp hv).2
  rfl

/-- At a fine vertex only the internal assignment of its own block is needed. -/
def localLeg (x : CrossLabels block A) (b : B) (y : InnerLabels block A b)
    (v : {v // v ∈ sites block b}) (e : IncidentEdge G v.1) : Fin (A.bondDim e.1) :=
  if h : block e.1.1.1 = block e.1.1.2 then
    y ⟨⟨e.1, h⟩, by
      have hv := (Finset.mem_filter.mp v.2).2
      rcases e.2 with he | he
      · exact (congrArg block he).trans hv
      · exact h.trans ((congrArg block he).trans hv)⟩
  else x ⟨e.1, h⟩

omit [Fintype B] [DecidableRel (G.map block).Adj] in
theorem assemble_local (x : CrossLabels block A) (y : (b : B) → InnerLabels block A b)
    (b : B) (v : {v // v ∈ sites block b}) (e : IncidentEdge G v.1) :
    assemble block A (x, y) e.1 = localLeg block A x b (y b) v e := by
  unfold localLeg
  split
  next h =>
    have he : block e.1.1.1 = b := by
      have hv := (Finset.mem_filter.mp v.2).2
      rcases e.2 with z | z
      · exact (congrArg block z).trans hv
      · exact h.trans ((congrArg block z).trans hv)
    have aux (z : Internal (G := G) block) (b : B) (hz : block z.1.1.1 = b) :
        y (block z.1.1.1) ⟨z, rfl⟩ = y b ⟨z, hz⟩ := by subst b; rfl
    simpa [assemble, globalLabels, Equiv.piEquivPiSubtypeProd, innerByBlock, h] using
      aux ⟨e.1, h⟩ b he
  next h =>
    simp [assemble, globalLabels, Equiv.piEquivPiSubtypeProd, crossingLabels, h]

omit [DecidableRel (G.map block).Adj] in
/-- Pull the internal sums inside the block product, leaving just one global sum
over crossing configurations. -/
theorem fine_factored (s : B → Fin D) :
    stateCoeff A (physical block phys s) =
      ∑ x : CrossLabels block A, ∏ b, ∑ y : InnerLabels block A b,
        ∏ v : {v // v ∈ sites block b},
          A.component v.1 (localLeg block A x b y v) (phys b (s b) v) := by
  classical
  rw [fine_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro b _
  apply Finset.prod_congr rfl
  intro v _
  rw [show (fun e : IncidentEdge G v.1 => assemble block A (x, y) e.1) =
    localLeg block A x b (y b) v from funext (assemble_local block A x y b v)]

omit [Fintype B] [DecidableRel G.Adj] [DecidableRel (G.map block).Adj] in
private theorem endpoints (b : B) (e : Edge G) (h : IsRegionIncidentEdge (sites block b) e) :
    block e.1.1 = b ∨ block e.1.2 = b := by
  simpa [IsRegionIncidentEdge, sites] using h

omit [Fintype B] [DecidableRel G.Adj] [DecidableRel (G.map block).Adj] in
private theorem cross_ne (b : B) (e : Edge G) (h : IsRegionBoundaryEdge (sites block b) e) :
    block e.1.1 ≠ block e.1.2 := by
  simp only [IsRegionBoundaryEdge, sites, Finset.mem_filter, Finset.mem_univ, true_and] at h
  grind

private def splitLocal (b : B) : RegionIncidentConfig A (sites block b) ≃
    InnerLabels block A b × RegionBoundaryConfig A (sites block b) where
  toFun z := (fun e => z ⟨e.1.1, Or.inl (by simpa [sites] using e.2)⟩,
    regionIncidentBoundaryLabel A (sites block b) z)
  invFun p e :=
    if h : block e.1.1.1 = block e.1.1.2 then
      p.1 ⟨⟨e.1, h⟩, by
        rcases endpoints block b _ e.2 with z | z
        · exact z
        · exact h.trans z⟩
    else
      p.2 ⟨e.1, e.2.isRegionBoundaryEdge (by
        simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and]
        grind)⟩
  left_inv z := by
    funext e
    by_cases h : block e.1.1.1 = block e.1.1.2
    · exact dite_eq_left h
    · exact dite_eq_right h
  right_inv p := by
    apply Prod.ext
    · funext e
      exact dite_eq_left e.1.2
    · funext e
      exact dite_eq_right (cross_ne block b e.1 e.2)

omit [Fintype B] [DecidableRel (G.map block).Adj] in
theorem local_weight (b : B) (x : CrossLabels block A) (s : RegionPhysicalConfig (d := d)
    (sites block b)) :
    openRegionWeight A (sites block b) (restrictCross block A x b) s =
      ∑ y : InnerLabels block A b, ∏ v : {v // v ∈ sites block b},
        A.component v.1 (localLeg block A x b y v) (s v) := by
  classical
  unfold openRegionWeight
  rw [← (splitLocal block A b).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  have hb (t : RegionBoundaryConfig A (sites block b)) :
      regionIncidentBoundaryLabel A _ ((splitLocal block A b).symm (y, t)) = t :=
    congrArg Prod.snd ((splitLocal block A b).apply_symm_apply (y, t))
  simp_rw [hb]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold regionIncidentWeight
  apply Finset.prod_congr rfl
  intro v _
  congr 1

theorem stateCoeff_coarseTensor (s : B → Fin D) :
    stateCoeff (coarseTensor block A phys) s = stateCoeff A (physical block phys s) := by
  classical
  rw [coarse_sum, fine_factored]
  simp_rw [local_weight]

end TNLean.PEPS.PartitionBonds
