import TNLean.PEPS.VertexComplement.Basic

/-!
# Kernel descent for the vertex-complement block

This file proves that the vertex-complement tensor family of
`VertexComplement.Basic` is linearly independent, by the finite kernel-descent
device of `EdgeMiddlePhysical.KernelDescent` adapted to the vertex star
`IncidentEdge G v` as the open boundary.

The contraction region is $V\setminus\{v\}$. Deleting one complement vertex
$j\ne v$ at a time uses the one-sided inverse at $j$
(`IsVertexInjective.localCoeff_eq_zero_of_contract_zero`); the terminal empty
region forces every boundary coefficient to vanish, using positive bond
dimensions to fill the interior virtual indices.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, lines 205--250 and 1205--1210](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Star-bond split equivalence at a complement vertex -/

/-- The predicate on edges singling out those incident to a complement vertex
`j`. -/
def IsIncidentEdge (j : V) (f : Edge G) : Prop :=
  f.1.1 = j ∨ f.1.2 = j

instance (j : V) (f : Edge G) : Decidable (IsIncidentEdge (G := G) j f) := by
  unfold IsIncidentEdge; infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- For a vertex `j` and an incident edge `ie` at `j`, the underlying edge is
incident to `j`. -/
theorem isIncidentEdge_of_incident (j : V) (ie : IncidentEdge G j) :
    IsIncidentEdge (G := G) j ie.1 := ie.2

/-- The split equivalence at a complement vertex `j`: a global virtual
configuration is the local configuration at `j` together with the configuration
on the edges not incident to `j`. -/
noncomputable def vertexConfigSplitAt (A : Tensor G d) (j : V) :
    VirtualConfig A ≃
      LocalVirtualConfig A j ×
        ((f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1)) where
  toFun ζ :=
    (fun ie : IncidentEdge G j => ζ ie.1, fun f => ζ f.1)
  invFun x := fun f =>
    if h : IsIncidentEdge (G := G) j f then
      x.1 ⟨f, h⟩
    else
      x.2 ⟨f, h⟩
  left_inv ζ := by
    funext f
    dsimp only
    by_cases h : IsIncidentEdge (G := G) j f
    · rw [dif_pos h]
    · rw [dif_neg h]
  right_inv x := by
    apply Prod.ext
    · funext ie
      have h : IsIncidentEdge (G := G) j ie.1 := ie.2
      dsimp only
      rw [dif_pos h]
    · funext f
      have h : ¬ IsIncidentEdge (G := G) j f.1 := f.2
      dsimp only
      rw [dif_neg h]

omit [Fintype V] in
@[simp] theorem vertexConfigSplitAt_fst (A : Tensor G d) (j : V) (ζ : VirtualConfig A)
    (ie : IncidentEdge G j) :
    (vertexConfigSplitAt (G := G) A j ζ).1 ie = ζ ie.1 := rfl

omit [Fintype V] in
@[simp] theorem vertexConfigSplitAt_symm_apply_incident (A : Tensor G d) (j : V)
    (η : LocalVirtualConfig A j)
    (r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1))
    (ie : IncidentEdge G j) :
    (vertexConfigSplitAt (G := G) A j).symm (η, r) ie.1 = η ie := by
  have h : IsIncidentEdge (G := G) j ie.1 := ie.2
  change (if hh : IsIncidentEdge (G := G) j ie.1 then η ⟨ie.1, hh⟩ else r ⟨ie.1, hh⟩) =
    η ie
  rw [dif_pos h]

/-! ### Kernel condition -/

/-- The exposed-agreement indicator at stage `S`: `1` if `ζ` agrees with `ζ₀` on
every edge that touches no vertex of `S`, and `0` otherwise. -/
noncomputable def vcExposedIndicator (A : Tensor G d) (S : Finset V)
    (ζ ζ₀ : VirtualConfig A) : ℂ :=
  if (∀ f : Edge G, f.1.1 ∉ S → f.1.2 ∉ S → ζ f = ζ₀ f) then 1 else 0

/-- The guarded local factor at `w` in the kernel condition: the tensor at `w`
contracted along the global configuration when `w \ne v`, and `1` at `v`. -/
noncomputable def vcFactor (A : Tensor G d) (v : V) (w : V)
    (ζ : VirtualConfig A) (τ : V → Fin d) : ℂ :=
  if w ≠ v then A.component w (fun ie => ζ ie.1) (τ w) else 1

/-- The kernel condition at stage `S` for the coefficient family `c`. -/
noncomputable def vertexComplementKernelCondition (A : Tensor G d) (v : V)
    (c : LocalVirtualConfig A v →₀ ℂ) (S : Finset V) : Prop :=
  ∀ (ζ₀ : VirtualConfig A) (τ : V → Fin d),
    ∑ ζ : VirtualConfig A,
      vcExposedIndicator (G := G) A S ζ ζ₀ *
        c (vertexStarLabel (G := G) A v ζ) *
        ∏ w ∈ S, vcFactor (G := G) A v w ζ τ = 0

/-! ### Kernel-condition descent: the erase-vertex step -/

variable (A : Tensor G d) (v : V)

/-- The extra-agreement indicator on the `j`-incident edges newly exposed when
`j` is removed from `S`. -/
noncomputable def vcExtraIndicator (S : Finset V) (j : V)
    (ζ ζ₀ : VirtualConfig A) : ℂ :=
  if (∀ f : Edge G, (f.1.1 = j ∨ f.1.2 = j) →
      f.1.1 ∉ S.erase j → f.1.2 ∉ S.erase j → ζ f = ζ₀ f) then 1 else 0

/-- Removing `j` from `S` factors the exposed indicator into the `S`-indicator
and the extra-agreement indicator on the `j`-incident edges. -/
theorem vcExposedIndicator_erase (S : Finset V) (j : V) (ζ ζ₀ : VirtualConfig A) :
    vcExposedIndicator (G := G) A (S.erase j) ζ ζ₀ =
      vcExposedIndicator (G := G) A S ζ ζ₀ * vcExtraIndicator (G := G) A S j ζ ζ₀ := by
  classical
  unfold vcExposedIndicator vcExtraIndicator
  by_cases hAll : ∀ f : Edge G, f.1.1 ∉ S.erase j → f.1.2 ∉ S.erase j → ζ f = ζ₀ f
  · rw [if_pos hAll]
    have hS : ∀ f : Edge G, f.1.1 ∉ S → f.1.2 ∉ S → ζ f = ζ₀ f := by
      intro f hf1 hf2
      exact hAll f
        (fun h => hf1 (Finset.mem_of_mem_erase h))
        (fun h => hf2 (Finset.mem_of_mem_erase h))
    have hE : ∀ f : Edge G, (f.1.1 = j ∨ f.1.2 = j) →
        f.1.1 ∉ S.erase j → f.1.2 ∉ S.erase j → ζ f = ζ₀ f := by
      intro f _ hf1 hf2
      exact hAll f hf1 hf2
    rw [if_pos hS, if_pos hE, one_mul]
  · rw [if_neg hAll]
    by_cases hS : ∀ f : Edge G, f.1.1 ∉ S → f.1.2 ∉ S → ζ f = ζ₀ f
    · rw [if_pos hS, one_mul, if_neg]
      intro hE
      apply hAll
      intro f hf1 hf2
      by_cases hj1 : f.1.1 = j
      · exact hE f (Or.inl hj1) hf1 hf2
      · by_cases hj2 : f.1.2 = j
        · exact hE f (Or.inr hj2) hf1 hf2
        · have h1 : f.1.1 ∉ S := fun h => hf1 (Finset.mem_erase.mpr ⟨hj1, h⟩)
          have h2 : f.1.2 ∉ S := fun h => hf2 (Finset.mem_erase.mpr ⟨hj2, h⟩)
          exact hS f h1 h2
    · rw [if_neg hS, zero_mul]

/-- The extra indicator on a split configuration depends only on the local
configuration `η` at `j`. -/
noncomputable def vcExtraIndicatorη (S : Finset V) {j : V}
    (η : LocalVirtualConfig A j) (ζ₀ : VirtualConfig A) : ℂ :=
  if (∀ f : Edge G, (h : f.1.1 = j ∨ f.1.2 = j) →
      f.1.1 ∉ S.erase j → f.1.2 ∉ S.erase j →
        η ⟨f, h⟩ = ζ₀ f) then 1 else 0

theorem vcExtraIndicator_split (S : Finset V) {j : V}
    (η : LocalVirtualConfig A j)
    (r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1))
    (ζ₀ : VirtualConfig A) :
    vcExtraIndicator (G := G) A S j ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ =
      vcExtraIndicatorη (G := G) A S η ζ₀ := by
  classical
  unfold vcExtraIndicator vcExtraIndicatorη
  have hval : ∀ (f : Edge G) (hinc : f.1.1 = j ∨ f.1.2 = j),
      (vertexConfigSplitAt (G := G) A j).symm (η, r) f = η ⟨f, hinc⟩ := by
    intro f hinc
    have hIs : IsIncidentEdge (G := G) j f := hinc
    change (if hh : IsIncidentEdge (G := G) j f then η ⟨f, hh⟩ else r ⟨f, hh⟩) =
      η ⟨f, hinc⟩
    rw [dif_pos hIs]
  congr 1
  apply propext
  constructor
  · intro h f hinc hf1 hf2
    rw [← hval f hinc]
    exact h f hinc hf1 hf2
  · intro h f hinc hf1 hf2
    rw [hval f hinc]
    exact h f hinc hf1 hf2

omit [Fintype V] in
/-- On a split configuration, the guarded local factor at `j \ne v` is the tensor
at `j` evaluated on the local virtual configuration `η`. -/
theorem vcFactor_split_mid {j : V} (hjv : j ≠ v)
    (η : LocalVirtualConfig A j)
    (r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1))
    (τ : V → Fin d) :
    vcFactor (G := G) A v j ((vertexConfigSplitAt (G := G) A j).symm (η, r)) τ =
      A.component j η (τ j) := by
  classical
  unfold vcFactor
  rw [if_pos hjv]
  congr 1
  funext ie
  exact vertexConfigSplitAt_symm_apply_incident (G := G) A j η r ie

/-- The marginal coefficient family at `j` obtained from the kernel condition at
`S` by summing over the non-`j` star coordinates. -/
noncomputable def vcMarginal
    (c : LocalVirtualConfig A v →₀ ℂ) (S : Finset V) (j : V)
    (ζ₀ : VirtualConfig A) (τ : V → Fin d) (η : LocalVirtualConfig A j) : ℂ :=
  ∑ r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1),
    vcExposedIndicator (G := G) A S ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
      c (vertexStarLabel (G := G) A v ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
      ∏ w ∈ S.erase j, vcFactor (G := G) A v w
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) τ

/-- The marginal coefficient family vanishes, by injectivity at `j` and the
kernel condition at `S`. -/
theorem vcMarginal_eq_zero (hA : IsVertexInjective A)
    (c : LocalVirtualConfig A v →₀ ℂ) (S : Finset V) (j : V)
    (hjv : j ≠ v) (hjS : j ∈ S)
    (hK : vertexComplementKernelCondition (G := G) A v c S)
    (ζ₀ : VirtualConfig A) (τ : V → Fin d) :
    vcMarginal (G := G) A v c S j ζ₀ τ = 0 := by
  classical
  apply hA.localCoeff_eq_zero_of_contract_zero j
  intro τj'
  have hKS := hK ζ₀ (Function.update τ j τj')
  rw [← Equiv.sum_comp (vertexConfigSplitAt (G := G) A j).symm,
      Fintype.sum_prod_type] at hKS
  rw [← hKS]
  refine Finset.sum_congr rfl ?_
  intro η _
  unfold vcMarginal
  rw [smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro r _
  have hAj : A.component j η τj' =
      vcFactor (G := G) A v j ((vertexConfigSplitAt (G := G) A j).symm (η, r))
        (Function.update τ j τj') := by
    rw [vcFactor_split_mid (G := G) A v hjv η r (Function.update τ j τj')]
    rw [Function.update_self]
  have hProdErase : ∀ x : VirtualConfig A,
      (∏ w ∈ S.erase j, vcFactor (G := G) A v w x τ) =
        ∏ w ∈ S.erase j, vcFactor (G := G) A v w x (Function.update τ j τj') := by
    intro x
    refine Finset.prod_congr rfl ?_
    intro w hw
    have hwj : w ≠ j := Finset.ne_of_mem_erase hw
    unfold vcFactor
    by_cases hwv : w ≠ v
    · rw [if_pos hwv, if_pos hwv, Function.update_of_ne hwj]
    · rw [if_neg hwv, if_neg hwv]
  rw [hProdErase, hAj]
  rw [show (vcExposedIndicator (G := G) A S
        ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
      c (vertexStarLabel (G := G) A v ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
      ∏ w ∈ S.erase j, vcFactor (G := G) A v w
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) (Function.update τ j τj')) *
      vcFactor (G := G) A v j
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) (Function.update τ j τj') =
      vcExposedIndicator (G := G) A S
        ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
      c (vertexStarLabel (G := G) A v ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
      ((∏ w ∈ S.erase j, vcFactor (G := G) A v w
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) (Function.update τ j τj')) *
        vcFactor (G := G) A v j
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) (Function.update τ j τj'))
      by ring]
  rw [Finset.prod_erase_mul S _ hjS]

/-- The kernel condition descends when a complement vertex `j \ne v` in `S` is
removed. -/
theorem vertexComplementKernelCondition_erase (hA : IsVertexInjective A)
    (c : LocalVirtualConfig A v →₀ ℂ) (S : Finset V) {j : V}
    (hjv : j ≠ v) (hjS : j ∈ S)
    (hK : vertexComplementKernelCondition (G := G) A v c S) :
    vertexComplementKernelCondition (G := G) A v c (S.erase j) := by
  classical
  intro ζ₀ τ
  rw [← Equiv.sum_comp (vertexConfigSplitAt (G := G) A j).symm,
      Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro η _
  have hMarg := vcMarginal_eq_zero (G := G) A v hA c S j hjv hjS hK ζ₀ τ
  have hpull :
      (∑ r, vcExposedIndicator (G := G) A (S.erase j)
            ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
          c (vertexStarLabel (G := G) A v ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
          ∏ w ∈ S.erase j, vcFactor (G := G) A v w
            ((vertexConfigSplitAt (G := G) A j).symm (η, r)) τ) =
      vcExtraIndicatorη (G := G) A S η ζ₀ * vcMarginal (G := G) A v c S j ζ₀ τ η := by
    unfold vcMarginal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [vcExposedIndicator_erase (G := G) A S j,
      vcExtraIndicator_split (G := G) A S η r]
    ring
  change (∑ r, vcExposedIndicator (G := G) A (S.erase j)
        ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
      c (vertexStarLabel (G := G) A v ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
      ∏ w ∈ S.erase j, vcFactor (G := G) A v w
        ((vertexConfigSplitAt (G := G) A j).symm (η, r)) τ) = 0
  rw [hpull, congrFun hMarg η, Pi.zero_apply, mul_zero]

/-! ### The terminal relation -/

/-- A global virtual configuration witnessing a given v-star label, filling the
non-star edges with the bottom index using positive bond dimensions. -/
noncomputable def starWitness (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (ρ : LocalVirtualConfig A v) : VirtualConfig A :=
  fun f =>
    if h : f.1.1 = v ∨ f.1.2 = v then
      ρ ⟨f, h⟩
    else
      ⟨0, hpos f⟩

omit [Fintype V] in
/-- The v-star label of the witness configuration is the given label. -/
theorem vertexStarLabel_starWitness (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (ρ : LocalVirtualConfig A v) :
    vertexStarLabel (G := G) A v (starWitness (G := G) A v hpos ρ) = ρ := by
  funext ie
  change starWitness (G := G) A v hpos ρ ie.1 = ρ ie
  have h : ie.1.1.1 = v ∨ ie.1.1.2 = v := ie.2
  rw [starWitness, dif_pos h]

/-- The kernel condition at the empty region forces the coefficient family to
vanish. -/
theorem vertexComplementKernelCondition_empty_eq_zero (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (c : LocalVirtualConfig A v →₀ ℂ)
    (hK : vertexComplementKernelCondition (G := G) A v c ∅) :
    c = 0 := by
  classical
  obtain ⟨τ0⟩ : Nonempty (Fin d) := by
    have hne : Nonempty (LocalVirtualConfig A v) := ⟨fun ie => ⟨0, hpos ie.1⟩⟩
    obtain ⟨η₀⟩ := hne
    have hnz : A.component v η₀ ≠ 0 := (hA v).ne_zero η₀
    by_contra hc
    rw [not_nonempty_iff] at hc
    exact hnz (Subsingleton.elim _ _)
  ext ρ
  have hKρ := hK (starWitness (G := G) A v hpos ρ) (fun _ => τ0)
  rw [show (∑ ζ : VirtualConfig A,
        vcExposedIndicator (G := G) A ∅ ζ (starWitness (G := G) A v hpos ρ) *
          c (vertexStarLabel (G := G) A v ζ) *
          ∏ w ∈ (∅ : Finset V), vcFactor (G := G) A v w ζ (fun _ => τ0)) =
      ∑ ζ : VirtualConfig A,
        vcExposedIndicator (G := G) A ∅ ζ (starWitness (G := G) A v hpos ρ) *
          c (vertexStarLabel (G := G) A v ζ) from by
    refine Finset.sum_congr rfl ?_
    intro ζ _
    rw [Finset.prod_empty, mul_one]] at hKρ
  have hExp : ∀ ζ : VirtualConfig A,
      vcExposedIndicator (G := G) A ∅ ζ (starWitness (G := G) A v hpos ρ) =
        if ζ = starWitness (G := G) A v hpos ρ then 1 else 0 := by
    intro ζ
    unfold vcExposedIndicator
    congr 1
    apply propext
    constructor
    · intro h
      funext f
      exact h f (by simp) (by simp)
    · intro h _ _ _
      rw [h]
  simp_rw [hExp, ite_mul, one_mul, zero_mul] at hKρ
  rw [Finset.sum_ite_eq' Finset.univ (starWitness (G := G) A v hpos ρ)
      (fun ζ => c (vertexStarLabel (G := G) A v ζ))] at hKρ
  simp only [Finset.mem_univ, if_true] at hKρ
  rw [vertexStarLabel_starWitness (G := G) A v hpos ρ] at hKρ
  simpa using hKρ

/-! ### The initial relation -/

/-- Restrict a global physical configuration to the complement region. -/
def vertexComplementPhysicalConfigOf (v : V) (τ : V → Fin d) :
    VertexComplementPhysicalConfig (V := V) (d := d) v :=
  fun w => τ w.1

/-- At the full complement region, the exposed indicator is identically `1`: no
edge has both endpoints outside `V\{v}` (that would force both to equal `v`). -/
theorem vcExposedIndicator_vertexComplementVertices (ζ ζ₀ : VirtualConfig A) :
    vcExposedIndicator (G := G) A (vertexComplementVertices (V := V) v) ζ ζ₀ = 1 := by
  classical
  unfold vcExposedIndicator
  rw [if_pos]
  intro f hf1 hf2
  simp only [mem_vertexComplementVertices_iff, not_not] at hf1 hf2
  exact absurd (hf1.trans hf2.symm) (ne_of_lt f.2.1)

/-- The kernel-condition product over the full complement region equals the
complement-family product. -/
theorem vcProd_eq_family_prod (ζ : VirtualConfig A) (τ : V → Fin d) :
    (∏ w ∈ vertexComplementVertices (V := V) v, vcFactor (G := G) A v w ζ τ) =
      ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w.1) := by
  classical
  rw [Finset.prod_subtype (F := inferInstance) (s := vertexComplementVertices (V := V) v)
    (p := fun w => w ≠ v)
    (h := by intro w; exact mem_vertexComplementVertices_iff (V := V) v w)
    (f := fun w => vcFactor (G := G) A v w ζ τ)]
  refine Finset.prod_congr rfl ?_
  intro w _
  unfold vcFactor
  rw [if_pos w.2]

/-- The complement tensor family as a fibered sum over global configurations with
a given star label. -/
theorem vertexComplementTensorFamily_eq_fiber_sum
    (ρ : LocalVirtualConfig A v) (τ : V → Fin d) :
    vertexComplementTensorFamily (G := G) A v ρ
        (vertexComplementPhysicalConfigOf (V := V) (d := d) v τ) =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A => vertexStarLabel (G := G) A v ζ = ρ),
        ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w.1) := by
  rfl

/-- A vanishing linear combination of the complement tensor family gives the
kernel condition at the full complement region. -/
theorem vertexComplement_initial_kernelCondition (c : LocalVirtualConfig A v →₀ ℂ)
    (hc : Finsupp.linearCombination ℂ (vertexComplementTensorFamily (G := G) A v) c = 0) :
    vertexComplementKernelCondition (G := G) A v c (vertexComplementVertices (V := V) v) := by
  classical
  intro ζ₀ τ
  have hstep : (∑ ζ : VirtualConfig A,
        vcExposedIndicator (G := G) A (vertexComplementVertices (V := V) v) ζ ζ₀ *
          c (vertexStarLabel (G := G) A v ζ) *
          ∏ w ∈ vertexComplementVertices (V := V) v, vcFactor (G := G) A v w ζ τ) =
      ∑ ζ : VirtualConfig A,
        c (vertexStarLabel (G := G) A v ζ) *
          ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w.1) := by
    refine Finset.sum_congr rfl ?_
    intro ζ _
    rw [vcExposedIndicator_vertexComplementVertices A v ζ ζ₀, one_mul,
      vcProd_eq_family_prod A v ζ τ]
  rw [hstep]
  rw [← Finset.sum_fiberwise Finset.univ
      (fun ζ : VirtualConfig A => vertexStarLabel (G := G) A v ζ)
      (fun ζ => c (vertexStarLabel (G := G) A v ζ) *
        ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w.1))]
  have hfib : ∀ ρ : LocalVirtualConfig A v,
      (∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A => vertexStarLabel (G := G) A v ζ = ρ),
        c (vertexStarLabel (G := G) A v ζ) *
          ∏ w : {w : V // w ≠ v}, A.component w.1 (fun ie => ζ ie.1) (τ w.1)) =
        c ρ * vertexComplementTensorFamily (G := G) A v ρ
          (vertexComplementPhysicalConfigOf (V := V) (d := d) v τ) := by
    intro ρ
    rw [vertexComplementTensorFamily_eq_fiber_sum A v ρ τ, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ζ hζ
    rw [Finset.mem_filter] at hζ
    rw [hζ.2]
  simp_rw [hfib]
  have hval : (∑ ρ : LocalVirtualConfig A v,
        c ρ * vertexComplementTensorFamily (G := G) A v ρ
          (vertexComplementPhysicalConfigOf (V := V) (d := d) v τ)) =
      (Finsupp.linearCombination ℂ (vertexComplementTensorFamily (G := G) A v) c)
        (vertexComplementPhysicalConfigOf (V := V) (d := d) v τ) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    · intro i; simp
  rw [hval, hc]
  rfl

/-! ### Kernel-descent datum and complement injectivity -/

/-- The finite kernel-descent datum for the vertex-complement block, restricting
the kernel condition to the complement vertices and erasing one at a time. -/
noncomputable def vertexComplementKernelDescent (hA : IsVertexInjective A)
    (c : LocalVirtualConfig A v →₀ ℂ) : FiniteRegionKernelDescent V where
  kernelCondition S :=
    vertexComplementKernelCondition (G := G) A v c (S ∩ vertexComplementVertices (V := V) v)
  erase_vertex := by
    intro S j hjS hK
    rw [Finset.erase_inter]
    by_cases hjv : j ≠ v
    · exact vertexComplementKernelCondition_erase (G := G) A v hA c
        (S ∩ vertexComplementVertices (V := V) v) hjv
        (Finset.mem_inter.mpr ⟨hjS,
          (mem_vertexComplementVertices_iff (V := V) v j).mpr hjv⟩) hK
    · rw [not_not] at hjv
      rw [Finset.erase_eq_of_notMem (fun h => by
        exact ((mem_vertexComplementVertices_iff (V := V) v j).mp
          (Finset.mem_inter.mp h).2) hjv)]
      exact hK

/-- The vertex-complement tensor family is linearly independent: a contraction of
injective tensors over the complement region $V\setminus\{v\}$ is injective.

**Positive-bond hypothesis (faithfulness fix).** The source works with injective
PEPS, whose virtual bond spaces are nonzero-dimensional. Without the positivity
assumption the complement tensor can vanish when an interior virtual space is
empty, breaking linear independence. The hypothesis `∀ f, 0 < A.bondDim f`
restores the source assumption; the gap is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, a contraction of injective tensors is
injective (`Papers/1804.04964/paper_normal.tex`, lines 205--250), applied to the
complement block of the one-vertex-versus-complement comparison (lines
1205--1210). -/
theorem vertexComplementTensorInjective_of_isVertexInjective
    (hA : IsVertexInjective A) (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    VertexComplementTensorInjective (G := G) A v := by
  rw [VertexComplementTensorInjective, linearIndependent_iff]
  intro c hc
  have hInit : vertexComplementKernelCondition (G := G) A v c
      (vertexComplementVertices (V := V) v) :=
    vertexComplement_initial_kernelCondition (G := G) A v c hc
  set descent := vertexComplementKernelDescent (G := G) A v hA c with hdescent
  have hStart : descent.kernelCondition (vertexComplementVertices (V := V) v) := by
    change vertexComplementKernelCondition (G := G) A v c
      (vertexComplementVertices (V := V) v ∩ vertexComplementVertices (V := V) v)
    rwa [Finset.inter_self]
  have hEmpty : descent.kernelCondition ∅ := descent.descend_to_empty hStart
  have hEmpty' : vertexComplementKernelCondition (G := G) A v c ∅ := by
    have heq : (∅ : Finset V) ∩ vertexComplementVertices (V := V) v = ∅ :=
      Finset.empty_inter _
    have hE2 : vertexComplementKernelCondition (G := G) A v c
        ((∅ : Finset V) ∩ vertexComplementVertices (V := V) v) := hEmpty
    rwa [heq] at hE2
  exact vertexComplementKernelCondition_empty_eq_zero (G := G) A v hA hpos c hEmpty'

end PEPS
end TNLean
