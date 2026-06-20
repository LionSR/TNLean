import TNLean.PEPS.RegionBlock.Basic
import TNLean.PEPS.VertexComplement.KernelDescent

/-!
# Kernel descent for the blocked-region tensor

This file proves that the blocked-region tensor family of an arbitrary finite
region `R` is linearly independent, by finite kernel descent. The descent
generalizes the vertex-complement descent of
`TNLean.PEPS.VertexComplement.KernelDescent` from the region `V\{v}` to an
arbitrary region `R`.

The contraction region is `R`. Deleting one vertex `j ∈ R` at a time uses the
one-sided inverse at `j`; the terminal empty region forces every boundary
coefficient to vanish, using positive bond dimensions to fill the interior and
exterior virtual indices.

The open boundary is the family of edges crossing the boundary of `R`. The
agreement indicator guards only the edges with at least one endpoint in `R`:
the edges entirely outside `R` carry no tensor and are summed freely.

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

/-! ### Kernel condition for a region

The agreement indicator at stage `S` constrains every edge that touches `R` and
has both endpoints outside `S`. Edges entirely outside `R` are never
constrained: they carry no tensor and are summed freely. -/

/-- The exposed-agreement indicator at stage `S` for the region `R`: `1` if `ζ`
agrees with `ζ₀` on every edge that touches `R` (at least one endpoint in `R`)
and lies outside `S` (both endpoints outside `S`), and `0` otherwise. -/
noncomputable def rbExposedIndicator (A : Tensor G d) (R S : Finset V)
    (ζ ζ₀ : VirtualConfig A) : ℂ :=
  if (∀ f : Edge G, (f.1.1 ∈ R ∨ f.1.2 ∈ R) →
      f.1.1 ∉ S → f.1.2 ∉ S → ζ f = ζ₀ f) then 1 else 0

/-- The guarded local factor at `w` in the kernel condition: the tensor at `w`
contracted along the global configuration when `w ∈ R`, and `1` otherwise. -/
noncomputable def rbFactor (A : Tensor G d) (R : Finset V) (w : V)
    (ζ : VirtualConfig A) (τ : V → Fin d) : ℂ :=
  if w ∈ R then A.component w (fun ie => ζ ie.1) (τ w) else 1

/-- The kernel condition at stage `S` for the coefficient family `c`. -/
noncomputable def regionKernelCondition (A : Tensor G d) (R : Finset V)
    (c : RegionBoundaryConfig (G := G) A R →₀ ℂ) (S : Finset V) : Prop :=
  ∀ (ζ₀ : VirtualConfig A) (τ : V → Fin d),
    ∑ ζ : VirtualConfig A,
      rbExposedIndicator (G := G) A R S ζ ζ₀ *
        c (regionBoundaryLabel (G := G) A R ζ) *
        ∏ w ∈ S, rbFactor (G := G) A R w ζ τ = 0

/-! ### Kernel-condition descent: the erase-vertex step -/

variable (A : Tensor G d) (R : Finset V)

/-- The extra-agreement indicator on the `j`-incident edges newly exposed when
`j` is removed from `S`. Only edges touching `R` are constrained. -/
noncomputable def rbExtraIndicator (S : Finset V) (j : V)
    (ζ ζ₀ : VirtualConfig A) : ℂ :=
  if (∀ f : Edge G, (f.1.1 ∈ R ∨ f.1.2 ∈ R) → (f.1.1 = j ∨ f.1.2 = j) →
      f.1.1 ∉ S.erase j → f.1.2 ∉ S.erase j → ζ f = ζ₀ f) then 1 else 0

/-- Removing `j` from `S` factors the exposed indicator into the `S`-indicator
and the extra-agreement indicator on the `j`-incident edges. -/
theorem rbExposedIndicator_erase (S : Finset V) (j : V) (ζ ζ₀ : VirtualConfig A) :
    rbExposedIndicator (G := G) A R (S.erase j) ζ ζ₀ =
      rbExposedIndicator (G := G) A R S ζ ζ₀ *
        rbExtraIndicator (G := G) A R S j ζ ζ₀ := by
  classical
  unfold rbExposedIndicator rbExtraIndicator
  by_cases hAll : ∀ f : Edge G, (f.1.1 ∈ R ∨ f.1.2 ∈ R) →
      f.1.1 ∉ S.erase j → f.1.2 ∉ S.erase j → ζ f = ζ₀ f
  · rw [if_pos hAll]
    have hS : ∀ f : Edge G, (f.1.1 ∈ R ∨ f.1.2 ∈ R) →
        f.1.1 ∉ S → f.1.2 ∉ S → ζ f = ζ₀ f := by
      intro f hR hf1 hf2
      exact hAll f hR
        (fun h => hf1 (Finset.mem_of_mem_erase h))
        (fun h => hf2 (Finset.mem_of_mem_erase h))
    have hE : ∀ f : Edge G, (f.1.1 ∈ R ∨ f.1.2 ∈ R) → (f.1.1 = j ∨ f.1.2 = j) →
        f.1.1 ∉ S.erase j → f.1.2 ∉ S.erase j → ζ f = ζ₀ f := by
      intro f hR _ hf1 hf2
      exact hAll f hR hf1 hf2
    rw [if_pos hS, if_pos hE, one_mul]
  · rw [if_neg hAll]
    by_cases hS : ∀ f : Edge G, (f.1.1 ∈ R ∨ f.1.2 ∈ R) →
        f.1.1 ∉ S → f.1.2 ∉ S → ζ f = ζ₀ f
    · rw [if_pos hS, one_mul, if_neg]
      intro hE
      apply hAll
      intro f hR hf1 hf2
      by_cases hj1 : f.1.1 = j
      · exact hE f hR (Or.inl hj1) hf1 hf2
      · by_cases hj2 : f.1.2 = j
        · exact hE f hR (Or.inr hj2) hf1 hf2
        · have h1 : f.1.1 ∉ S := fun h => hf1 (Finset.mem_erase.mpr ⟨hj1, h⟩)
          have h2 : f.1.2 ∉ S := fun h => hf2 (Finset.mem_erase.mpr ⟨hj2, h⟩)
          exact hS f hR h1 h2
    · rw [if_neg hS, zero_mul]

/-- The extra indicator on a split configuration depends only on the local
configuration `η` at `j`. -/
noncomputable def rbExtraIndicatorη (S : Finset V) {j : V}
    (η : LocalVirtualConfig A j) (ζ₀ : VirtualConfig A) : ℂ :=
  if (∀ f : Edge G, (f.1.1 ∈ R ∨ f.1.2 ∈ R) → (h : f.1.1 = j ∨ f.1.2 = j) →
      f.1.1 ∉ S.erase j → f.1.2 ∉ S.erase j →
        η ⟨f, h⟩ = ζ₀ f) then 1 else 0

/-- After splitting a virtual boundary configuration into the labels incident to
`j` and the complementary labels, the extra compatibility factor for erasing `j`
is determined only by the incident labels. -/
theorem rbExtraIndicator_split (S : Finset V) {j : V}
    (η : LocalVirtualConfig A j)
    (r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1))
    (ζ₀ : VirtualConfig A) :
    rbExtraIndicator (G := G) A R S j ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ =
      rbExtraIndicatorη (G := G) A R S η ζ₀ := by
  classical
  unfold rbExtraIndicator rbExtraIndicatorη
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
  · intro h f hR hinc hf1 hf2
    rw [← hval f hinc]
    exact h f hR hinc hf1 hf2
  · intro h f hR hinc hf1 hf2
    rw [hval f hinc]
    exact h f hR hinc hf1 hf2

omit [Fintype V] in
/-- On a split configuration, the guarded local factor at `j ∈ R` is the tensor
at `j` evaluated on the local virtual configuration `η`. -/
theorem rbFactor_split_mid {j : V} (hjR : j ∈ R)
    (η : LocalVirtualConfig A j)
    (r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1))
    (τ : V → Fin d) :
    rbFactor (G := G) A R j ((vertexConfigSplitAt (G := G) A j).symm (η, r)) τ =
      A.component j η (τ j) := by
  classical
  unfold rbFactor
  rw [if_pos hjR]
  congr 1
  funext ie
  exact vertexConfigSplitAt_symm_apply_incident (G := G) A j η r ie

/-- The marginal coefficient family at `j` obtained from the kernel condition at
`S` by summing over the non-`j` star coordinates. -/
noncomputable def rbMarginal
    (c : RegionBoundaryConfig (G := G) A R →₀ ℂ) (S : Finset V) (j : V)
    (ζ₀ : VirtualConfig A) (τ : V → Fin d) (η : LocalVirtualConfig A j) : ℂ :=
  ∑ r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1),
    rbExposedIndicator (G := G) A R S ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
      c (regionBoundaryLabel (G := G) A R ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
      ∏ w ∈ S.erase j, rbFactor (G := G) A R w
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) τ

/-- The marginal coefficient family vanishes, by injectivity at `j` and the
kernel condition at `S`. -/
theorem rbMarginal_eq_zero (hA : IsVertexInjective A)
    (c : RegionBoundaryConfig (G := G) A R →₀ ℂ) (S : Finset V) (j : V)
    (hjR : j ∈ R) (hjS : j ∈ S)
    (hK : regionKernelCondition (G := G) A R c S)
    (ζ₀ : VirtualConfig A) (τ : V → Fin d) :
    rbMarginal (G := G) A R c S j ζ₀ τ = 0 := by
  classical
  apply hA.localCoeff_eq_zero_of_contract_zero j
  intro τj'
  have hKS := hK ζ₀ (Function.update τ j τj')
  rw [← Equiv.sum_comp (vertexConfigSplitAt (G := G) A j).symm,
      Fintype.sum_prod_type] at hKS
  rw [← hKS]
  refine Finset.sum_congr rfl ?_
  intro η _
  unfold rbMarginal
  rw [smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro r _
  have hAj : A.component j η τj' =
      rbFactor (G := G) A R j ((vertexConfigSplitAt (G := G) A j).symm (η, r))
        (Function.update τ j τj') := by
    rw [rbFactor_split_mid (G := G) A R hjR η r (Function.update τ j τj')]
    rw [Function.update_self]
  have hProdErase : ∀ x : VirtualConfig A,
      (∏ w ∈ S.erase j, rbFactor (G := G) A R w x τ) =
        ∏ w ∈ S.erase j, rbFactor (G := G) A R w x (Function.update τ j τj') := by
    intro x
    refine Finset.prod_congr rfl ?_
    intro w hw
    have hwj : w ≠ j := Finset.ne_of_mem_erase hw
    unfold rbFactor
    by_cases hwR : w ∈ R
    · rw [if_pos hwR, if_pos hwR, Function.update_of_ne hwj]
    · rw [if_neg hwR, if_neg hwR]
  rw [hProdErase, hAj]
  rw [show (rbExposedIndicator (G := G) A R S
        ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
      c (regionBoundaryLabel (G := G) A R ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
      ∏ w ∈ S.erase j, rbFactor (G := G) A R w
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) (Function.update τ j τj')) *
      rbFactor (G := G) A R j
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) (Function.update τ j τj') =
      rbExposedIndicator (G := G) A R S
        ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
      c (regionBoundaryLabel (G := G) A R ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
      ((∏ w ∈ S.erase j, rbFactor (G := G) A R w
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) (Function.update τ j τj')) *
        rbFactor (G := G) A R j
          ((vertexConfigSplitAt (G := G) A j).symm (η, r)) (Function.update τ j τj'))
      by ring]
  rw [Finset.prod_erase_mul S _ hjS]

/-- The kernel condition descends when a region vertex `j ∈ R` in `S` is
removed. -/
theorem regionKernelCondition_erase (hA : IsVertexInjective A)
    (c : RegionBoundaryConfig (G := G) A R →₀ ℂ) (S : Finset V) {j : V}
    (hjR : j ∈ R) (hjS : j ∈ S)
    (hK : regionKernelCondition (G := G) A R c S) :
    regionKernelCondition (G := G) A R c (S.erase j) := by
  classical
  intro ζ₀ τ
  rw [← Equiv.sum_comp (vertexConfigSplitAt (G := G) A j).symm,
      Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro η _
  have hMarg := rbMarginal_eq_zero (G := G) A R hA c S j hjR hjS hK ζ₀ τ
  have hpull :
      (∑ r, rbExposedIndicator (G := G) A R (S.erase j)
            ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
          c (regionBoundaryLabel (G := G) A R ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
          ∏ w ∈ S.erase j, rbFactor (G := G) A R w
            ((vertexConfigSplitAt (G := G) A j).symm (η, r)) τ) =
      rbExtraIndicatorη (G := G) A R S η ζ₀ * rbMarginal (G := G) A R c S j ζ₀ τ η := by
    unfold rbMarginal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [rbExposedIndicator_erase (G := G) A R S j,
      rbExtraIndicator_split (G := G) A R S η r]
    ring
  change (∑ r, rbExposedIndicator (G := G) A R (S.erase j)
        ((vertexConfigSplitAt (G := G) A j).symm (η, r)) ζ₀ *
      c (regionBoundaryLabel (G := G) A R ((vertexConfigSplitAt (G := G) A j).symm (η, r))) *
      ∏ w ∈ S.erase j, rbFactor (G := G) A R w
        ((vertexConfigSplitAt (G := G) A j).symm (η, r)) τ) = 0
  rw [hpull, congrFun hMarg η, Pi.zero_apply, mul_zero]

/-! ### The terminal relation -/

/-- A global virtual configuration witnessing a given boundary label, filling the
non-crossing edges with the bottom index using positive bond dimensions. -/
noncomputable def regionBoundaryWitness (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (ρ : RegionBoundaryConfig (G := G) A R) : VirtualConfig A :=
  fun f =>
    if h : IsRegionBoundaryEdge (G := G) R f then
      ρ ⟨f, h⟩
    else
      ⟨0, hpos f⟩

omit [Fintype V] in
/-- The boundary label of the witness configuration is the given label. -/
theorem regionBoundaryLabel_regionBoundaryWitness (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (ρ : RegionBoundaryConfig (G := G) A R) :
    regionBoundaryLabel (G := G) A R (regionBoundaryWitness (G := G) A R hpos ρ) = ρ := by
  funext f
  change regionBoundaryWitness (G := G) A R hpos ρ f.1 = ρ f
  have h : IsRegionBoundaryEdge (G := G) R f.1 := f.2
  rw [regionBoundaryWitness, dif_pos h]

/-- An edge touches `R` when at least one of its endpoints lies in `R`. The edges
touching `R` are the crossing edges together with the internal edges of `R`. -/
def IsTouchingEdge (R : Finset V) (f : Edge G) : Prop :=
  f.1.1 ∈ R ∨ f.1.2 ∈ R

instance (R : Finset V) (f : Edge G) : Decidable (IsTouchingEdge (G := G) R f) := by
  unfold IsTouchingEdge; infer_instance

/-- Labels on the edges touching `R`. The terminal kernel condition fixes these. -/
abbrev TouchConfig (A : Tensor G d) (R : Finset V) : Type _ :=
  (f : {f : Edge G // IsTouchingEdge (G := G) R f}) → Fin (A.bondDim f.1)

instance instFintypeTouchConfig (A : Tensor G d) (R : Finset V) :
    Fintype (TouchConfig (G := G) A R) :=
  inferInstance

/-- Labels on the edges entirely outside `R` (neither endpoint in `R`). The
terminal kernel condition leaves these free. -/
abbrev ExteriorConfig (A : Tensor G d) (R : Finset V) : Type _ :=
  (f : {f : Edge G // ¬ IsTouchingEdge (G := G) R f}) → Fin (A.bondDim f.1)

instance instFintypeExteriorConfig (A : Tensor G d) (R : Finset V) :
    Fintype (ExteriorConfig (G := G) A R) :=
  inferInstance

/-- A global virtual configuration is the labels on the edges touching `R`
together with the labels on the edges entirely outside `R`. -/
noncomputable def regionTouchSplit (A : Tensor G d) (R : Finset V) :
    VirtualConfig A ≃ TouchConfig (G := G) A R × ExteriorConfig (G := G) A R :=
  Equiv.piEquivPiSubtypeProd (fun f : Edge G => IsTouchingEdge (G := G) R f)
    (fun f => Fin (A.bondDim f))

omit [Fintype V] in
@[simp] theorem regionTouchSplit_symm_apply_touch (A : Tensor G d) (R : Finset V)
    (t : TouchConfig (G := G) A R) (x : ExteriorConfig (G := G) A R)
    (f : {f : Edge G // IsTouchingEdge (G := G) R f}) :
    (regionTouchSplit (G := G) A R).symm (t, x) f.1 = t f := by
  rw [regionTouchSplit, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos f.2]

omit [Fintype V] in
/-- The boundary label of a split configuration depends only on the touching
part: every crossing edge touches `R`. -/
theorem regionBoundaryLabel_regionTouchSplit_symm (A : Tensor G d) (R : Finset V)
    (t : TouchConfig (G := G) A R) (x x' : ExteriorConfig (G := G) A R) :
    regionBoundaryLabel (G := G) A R ((regionTouchSplit (G := G) A R).symm (t, x)) =
      regionBoundaryLabel (G := G) A R ((regionTouchSplit (G := G) A R).symm (t, x')) := by
  funext f
  have ht : IsTouchingEdge (G := G) R f.1 := isRegionBoundaryEdge_touches (G := G) R f.2
  change (regionTouchSplit (G := G) A R).symm (t, x) f.1 =
    (regionTouchSplit (G := G) A R).symm (t, x') f.1
  rw [regionTouchSplit_symm_apply_touch (G := G) A R t x ⟨f.1, ht⟩,
    regionTouchSplit_symm_apply_touch (G := G) A R t x' ⟨f.1, ht⟩]

/-- The kernel condition at the empty region forces the coefficient family to
vanish.

At the empty region the agreement indicator constrains exactly the edges
touching `R`. The boundary witness pins those edges, so the sum collapses to a
positive multiple (the number of exterior configurations) of the coefficient at
the given boundary label, and the multiplicity is nonzero because every bond
dimension is positive. -/
theorem regionKernelCondition_empty_eq_zero (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (c : RegionBoundaryConfig (G := G) A R →₀ ℂ)
    (hK : regionKernelCondition (G := G) A R c ∅) :
    c = 0 := by
  classical
  have hτ : Nonempty (V → Fin d) := by
    rcases isEmpty_or_nonempty V with hV | hV
    · exact ⟨fun v => (hV.false v).elim⟩
    · obtain ⟨v⟩ := hV
      obtain ⟨η₀⟩ : Nonempty (LocalVirtualConfig A v) := ⟨fun ie => ⟨0, hpos ie.1⟩⟩
      have hnz : A.component v η₀ ≠ 0 := (hA v).ne_zero η₀
      obtain ⟨τ0⟩ : Nonempty (Fin d) := by
        by_contra hc
        rw [not_nonempty_iff] at hc
        exact hnz (Subsingleton.elim _ _)
      exact ⟨fun _ => τ0⟩
  obtain ⟨τ⟩ := hτ
  ext ρ
  set W := regionBoundaryWitness (G := G) A R hpos ρ with hW
  set tW : TouchConfig (G := G) A R := fun f => W f.1 with htW
  have hKρ := hK W τ
  -- The product over the empty region is `1`.
  have hKρ' : (∑ ζ : VirtualConfig A,
      rbExposedIndicator (G := G) A R ∅ ζ W *
        c (regionBoundaryLabel (G := G) A R ζ)) = 0 := by
    rw [← hKρ]
    refine Finset.sum_congr rfl ?_
    intro ζ _
    rw [Finset.prod_empty, mul_one]
  -- Split the sum over the touching/exterior parts of the configuration.
  rw [← Equiv.sum_comp (regionTouchSplit (G := G) A R).symm, Fintype.sum_prod_type] at hKρ'
  -- The exposed indicator at `∅` constrains exactly the touching edges, so it
  -- depends only on the touching part `t`.
  have hExp : ∀ (t : TouchConfig (G := G) A R) (x : ExteriorConfig (G := G) A R),
      rbExposedIndicator (G := G) A R ∅
          ((regionTouchSplit (G := G) A R).symm (t, x)) W =
        if t = tW then 1 else 0 := by
    intro t x
    unfold rbExposedIndicator
    congr 1
    apply propext
    constructor
    · intro h
      funext f
      have ht : IsTouchingEdge (G := G) R f.1 := f.2
      have := h f.1 ht (by simp) (by simp)
      rwa [regionTouchSplit_symm_apply_touch (G := G) A R t x f] at this
    · intro h f hf _ _
      have ht : IsTouchingEdge (G := G) R f := hf
      rw [regionTouchSplit_symm_apply_touch (G := G) A R t x ⟨f, ht⟩]
      exact congrFun h ⟨f, ht⟩
  -- The boundary label of the split configuration depends only on `t`; pin it.
  have hBdry : ∀ (x : ExteriorConfig (G := G) A R),
      regionBoundaryLabel (G := G) A R
          ((regionTouchSplit (G := G) A R).symm (tW, x)) = ρ := by
    intro x
    rw [regionBoundaryLabel_regionTouchSplit_symm (G := G) A R tW x
      (fun f => ⟨0, hpos f.1⟩)]
    have hWlabel : regionBoundaryLabel (G := G) A R W = ρ :=
      regionBoundaryLabel_regionBoundaryWitness (G := G) A R hpos ρ
    rw [← hWlabel]
    funext f
    have ht : IsTouchingEdge (G := G) R f.1 :=
      isRegionBoundaryEdge_touches (G := G) R f.2
    change (regionTouchSplit (G := G) A R).symm (tW, _) f.1 = W f.1
    rw [regionTouchSplit_symm_apply_touch (G := G) A R tW _ ⟨f.1, ht⟩]
  -- Carry out the inner exterior sum to expose the multiplicity.
  simp_rw [hExp] at hKρ'
  -- Factor the configuration-independent indicator out of the inner sum.
  rw [show (∑ t : TouchConfig (G := G) A R, ∑ x : ExteriorConfig (G := G) A R,
        (if t = tW then (1 : ℂ) else 0) *
          c (regionBoundaryLabel (G := G) A R
            ((regionTouchSplit (G := G) A R).symm (t, x)))) =
      ∑ t : TouchConfig (G := G) A R,
        (if t = tW then (1 : ℂ) else 0) *
          ∑ x : ExteriorConfig (G := G) A R,
            c (regionBoundaryLabel (G := G) A R
              ((regionTouchSplit (G := G) A R).symm (t, x))) from by
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [Finset.mul_sum]] at hKρ'
  simp_rw [ite_mul, one_mul, zero_mul] at hKρ'
  rw [Finset.sum_ite_eq' Finset.univ tW
      (fun t => ∑ x : ExteriorConfig (G := G) A R,
        c (regionBoundaryLabel (G := G) A R
          ((regionTouchSplit (G := G) A R).symm (t, x))))] at hKρ'
  simp only [Finset.mem_univ, if_true] at hKρ'
  -- After pinning `t`, every summand equals `c ρ`.
  rw [show (∑ x : ExteriorConfig (G := G) A R,
        c (regionBoundaryLabel (G := G) A R
          ((regionTouchSplit (G := G) A R).symm (tW, x)))) =
      ∑ _x : ExteriorConfig (G := G) A R, c ρ from by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [hBdry x]] at hKρ'
  rw [Finset.sum_const, nsmul_eq_mul] at hKρ'
  -- The multiplicity is a positive natural number, hence nonzero in `ℂ`.
  have hcard : (Finset.univ : Finset (ExteriorConfig (G := G) A R)).Nonempty :=
    ⟨fun f => ⟨0, hpos f.1⟩, Finset.mem_univ _⟩
  have hmul : ((Finset.univ : Finset (ExteriorConfig (G := G) A R)).card : ℂ) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]
    exact Finset.card_ne_zero_of_mem hcard.choose_spec
  have hcρ : c ρ = 0 := by
    rcases mul_eq_zero.mp hKρ' with h | h
    · exact absurd h hmul
    · exact h
  simpa using hcρ

/-! ### The initial relation -/

/-- Restrict a global physical configuration to the region `R`. -/
def regionPhysicalConfigOf (R : Finset V) (τ : V → Fin d) :
    RegionPhysicalConfig (V := V) (d := d) R :=
  fun w => τ w.1

/-- At the full region `R`, the exposed indicator is identically `1`: no edge
touches `R` while having both endpoints outside `R`. -/
theorem rbExposedIndicator_full (ζ ζ₀ : VirtualConfig A) :
    rbExposedIndicator (G := G) A R R ζ ζ₀ = 1 := by
  classical
  unfold rbExposedIndicator
  rw [if_pos]
  intro f hR hf1 hf2
  rcases hR with h | h
  · exact absurd h hf1
  · exact absurd h hf2

omit [Fintype V] in
/-- The kernel-condition product over the full region equals the blocked-region
family product. -/
theorem rbProd_eq_family_prod (ζ : VirtualConfig A) (τ : V → Fin d) :
    (∏ w ∈ R, rbFactor (G := G) A R w ζ τ) =
      ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (τ w.1) := by
  classical
  rw [Finset.prod_subtype (F := inferInstance) (s := R) (p := fun w => w ∈ R)
    (h := by intro w; rfl) (f := fun w => rbFactor (G := G) A R w ζ τ)]
  refine Finset.prod_congr rfl ?_
  intro w _
  unfold rbFactor
  rw [if_pos w.2]

/-- The blocked-region family as a fibered sum over global configurations with a
given boundary label. -/
theorem regionBlockedTensorFamily_eq_fiber_sum
    (ρ : RegionBoundaryConfig (G := G) A R) (τ : V → Fin d) :
    regionBlockedTensorFamily (G := G) A R ρ
        (regionPhysicalConfigOf (V := V) (d := d) R τ) =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = ρ),
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (τ w.1) := by
  rfl

/-- A vanishing linear combination of the blocked-region family gives the kernel
condition at the full region. -/
theorem region_initial_kernelCondition (c : RegionBoundaryConfig (G := G) A R →₀ ℂ)
    (hc : Finsupp.linearCombination ℂ (regionBlockedTensorFamily (G := G) A R) c = 0) :
    regionKernelCondition (G := G) A R c R := by
  classical
  intro ζ₀ τ
  have hstep : (∑ ζ : VirtualConfig A,
        rbExposedIndicator (G := G) A R R ζ ζ₀ *
          c (regionBoundaryLabel (G := G) A R ζ) *
          ∏ w ∈ R, rbFactor (G := G) A R w ζ τ) =
      ∑ ζ : VirtualConfig A,
        c (regionBoundaryLabel (G := G) A R ζ) *
          ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (τ w.1) := by
    refine Finset.sum_congr rfl ?_
    intro ζ _
    rw [rbExposedIndicator_full A R ζ ζ₀, one_mul, rbProd_eq_family_prod A R ζ τ]
  rw [hstep]
  rw [← Finset.sum_fiberwise Finset.univ
      (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ)
      (fun ζ => c (regionBoundaryLabel (G := G) A R ζ) *
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (τ w.1))]
  have hfib : ∀ ρ : RegionBoundaryConfig (G := G) A R,
      (∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = ρ),
        c (regionBoundaryLabel (G := G) A R ζ) *
          ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (τ w.1)) =
        c ρ * regionBlockedTensorFamily (G := G) A R ρ
          (regionPhysicalConfigOf (V := V) (d := d) R τ) := by
    intro ρ
    rw [regionBlockedTensorFamily_eq_fiber_sum A R ρ τ, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ζ hζ
    rw [Finset.mem_filter] at hζ
    rw [hζ.2]
  simp_rw [hfib]
  have hval : (∑ ρ : RegionBoundaryConfig (G := G) A R,
        c ρ * regionBlockedTensorFamily (G := G) A R ρ
          (regionPhysicalConfigOf (V := V) (d := d) R τ)) =
      (Finsupp.linearCombination ℂ (regionBlockedTensorFamily (G := G) A R) c)
        (regionPhysicalConfigOf (V := V) (d := d) R τ) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    · intro i; simp
  rw [hval, hc]
  rfl

/-! ### Kernel-descent datum and region injectivity -/

/-- The finite kernel-descent datum for the blocked region, restricting the
kernel condition to the vertices of `R` and erasing one at a time. -/
noncomputable def regionKernelDescent (hA : IsVertexInjective A)
    (c : RegionBoundaryConfig (G := G) A R →₀ ℂ) : FiniteRegionKernelDescent V where
  kernelCondition S := regionKernelCondition (G := G) A R c (S ∩ R)
  erase_vertex := by
    intro S j hjS hK
    rw [Finset.erase_inter]
    by_cases hjR : j ∈ R
    · exact regionKernelCondition_erase (G := G) A R hA c (S ∩ R) hjR
        (Finset.mem_inter.mpr ⟨hjS, hjR⟩) hK
    · rw [Finset.erase_eq_of_notMem (fun h => hjR (Finset.mem_inter.mp h).2)]
      exact hK

/-- The blocked-region tensor family is linearly independent: a contraction of
injective tensors over any finite region `R` is injective.

**Positive-bond hypothesis (faithfulness fix).** The source works with injective
PEPS, whose virtual bond spaces are nonzero-dimensional. Without the positivity
assumption the blocked tensor can vanish when an interior virtual space is empty,
breaking linear independence. The hypothesis `∀ f, 0 < A.bondDim f` restores the
source assumption; the gap is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, a contraction of injective tensors is
injective (`Papers/1804.04964/paper_normal.tex`, lines 205--250), applied to the
blocked region of the one-region-versus-complement comparison (lines
1205--1210). -/
theorem regionBlockedTensorInjective_of_isVertexInjective
    (hA : IsVertexInjective A) (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    RegionBlockedTensorInjective (G := G) A R := by
  rw [RegionBlockedTensorInjective, linearIndependent_iff]
  intro c hc
  have hInit : regionKernelCondition (G := G) A R c R :=
    region_initial_kernelCondition (G := G) A R c hc
  set descent := regionKernelDescent (G := G) A R hA c with hdescent
  have hStart : descent.kernelCondition R := by
    change regionKernelCondition (G := G) A R c (R ∩ R)
    rwa [Finset.inter_self]
  have hEmpty : descent.kernelCondition ∅ := descent.descend_to_empty hStart
  have hEmpty' : regionKernelCondition (G := G) A R c ∅ := by
    have hE2 : regionKernelCondition (G := G) A R c ((∅ : Finset V) ∩ R) := hEmpty
    rwa [Finset.empty_inter] at hE2
  exact regionKernelCondition_empty_eq_zero (G := G) A R hA hpos c hEmpty'

end PEPS
end TNLean
