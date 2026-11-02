/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.IndependentLegContraction
import TNLean.PEPS.TorusCommonTensorCoordinates

/-!
# Native torus edges and independent incidence products

Rightward and downward edges are indexed by their native initial vertex.
Independent incidence coordinates identify the contraction with a product of
invertible edge matrices. This identification also treats edges crossing a
coordinate seam, where the stored endpoint order may be reversed. Translating
the incidence coordinates translates every position in this full product.

Source: arXiv:1804.04964, Applications, lines 1891–1894.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS

/-- The four anisotropic virtual legs as direction-indexed incoming and
outgoing ports. False denotes the horizontal direction or an incoming port;
true denotes the vertical direction or an outgoing port.
Supporting coordinates for arXiv:1804.04964, lines 1891–1894. -/
def fourLegConfigEquivDirectionPorts (Dh Dv : ℕ) :
    ((i : Fin 4) → Fin (![Dv, Dh, Dv, Dh] i)) ≃
      ((r : Bool) → Bool → Fin (if r then Dv else Dh)) where
  toFun x r b := by
    cases r <;> cases b
    · exact x 3
    · exact x 1
    · exact x 0
    · exact x 2
  invFun x :=
    Fin.cases (x true false)
      (Fin.cases (x false true)
        (Fin.cases (x true true)
          (Fin.cases (x false false) (fun i => Fin.elim0 i))))
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    funext r b
    cases r <;> cases b <;> rfl

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d Dh Dv : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Index every actual torus edge by its horizontal or vertical direction and
native outgoing vertex. False means rightward, true means downward.
Supporting geometry for arXiv:1804.04964, lines 1891–1894. -/
def torusOutgoingEdgeEquiv :
    Bool × TorusVertex width height ≃ Edge (torusGraph width height) :=
  (Equiv.boolProdEquivSum (TorusVertex width height)).trans
    ((Equiv.sumCongr (Equiv.refl (TorusVertex width height)) (translateEquiv 0 (-1))).trans
      torusEdgeEquiv)

/-- Horizontal outgoing bonds are the actual right edges.
Supporting geometry for arXiv:1804.04964, lines 1891–1894. -/
@[simp] theorem torusOutgoingEdgeEquiv_horizontal (p : TorusVertex width height) :
    torusOutgoingEdgeEquiv (false, p) = torusRightEdge p := rfl

/-- Vertical outgoing bonds are the actual down edges.
Supporting geometry for arXiv:1804.04964, lines 1891–1894. -/
@[simp] theorem torusOutgoingEdgeEquiv_vertical (p : TorusVertex width height) :
    torusOutgoingEdgeEquiv (true, p) = torusDownEdge p := by
  change torusUpEdge (p.1 + 0, p.2 + -1) = torusDownEdge p
  simp only [add_zero, torusDownEdge, sub_eq_add_neg]

/-- The outgoing edge coordinates retain the original direction-dependent
bond dimensions. Supporting coordinates for arXiv:1804.04964,
lines 1891–1894. -/
theorem bondDim_torusOutgoingEdgeEquiv
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim Dh Dv)
    (z : Bool × TorusVertex width height) :
    A.bondDim (torusOutgoingEdgeEquiv z) = if z.1 then Dv else Dh := by
  rcases z with ⟨r, p⟩
  cases r
  · rw [torusOutgoingEdgeEquiv_horizontal]
    exact hU.1 _ (isHorizontalTorusEdge_torusRightEdge p)
  · rw [torusOutgoingEdgeEquiv_vertical]
    exact hU.2 _ (isVerticalTorusEdge_torusUpEdge (p.1, p.2 - 1))

end TNLean.PEPS

namespace TNLean.PEPS

/-- Reorganize outgoing and incoming ports into independent endpoint pairs.
The two coordinates on each edge remain independent. Supporting coordinates
for arXiv:1804.04964, lines 1891–1894. -/
private def independentPortConfigEquivEdgePair
    {Direction Position : Type*} {X : Direction → Type*}
    (ν : Direction → Equiv.Perm Position) :
    ((p : Position) → (r : Direction) → Bool → X r) ≃
      ((r : Direction) → Position → X r × X r) where
  toFun x r p := (x p r true, x (ν r p) r false)
  invFun a p r b := if b then (a r p).1 else (a r ((ν r).symm p)).2
  left_inv x := by
    funext p r b
    cases b <;> simp
  right_inv a := by
    funext r p
    apply Prod.ext <;> simp

/-- Commuting site and neighbor permutations preserve outgoing/incoming
endpoint order. Supporting calculation for arXiv:1804.04964,
lines 1891–1894. -/
private theorem independentPortConfigEquivEdgePair_translate
    {Direction Position : Type*} {X : Direction → Type*}
    (ν : Direction → Equiv.Perm Position) (τ : Equiv.Perm Position)
    (hcomm : ∀ r p, τ (ν r p) = ν r (τ p))
    (x : (p : Position) → (r : Direction) → Bool → X r) :
    independentPortConfigEquivEdgePair ν (fun p => x (τ p)) =
      fun r p => independentPortConfigEquivEdgePair ν x r (τ p) := by
  funext r p
  change (x (τ p) r true, x (τ (ν r p)) r false) =
    (x (τ p) r true, x (ν r (τ p)) r false)
  rw [hcomm r p]

/-- The product of native edge factors in independent port coordinates.
Supporting coefficient function for arXiv:1804.04964, lines 1891–1894. -/
def independentPortProduct
    {Direction Position : Type*} [Fintype Direction] [Fintype Position]
    {X : Direction → Type*}
    (ν : Direction → Equiv.Perm Position)
    (E : (r : Direction) → Position → X r → X r → ℂ)
    (x : (p : Position) → (r : Direction) → Bool → X r) : ℂ :=
  ∏ z : Direction × Position, E z.1 z.2 (x z.2 z.1 true) (x (ν z.1 z.2) z.1 false)

/-- Invariance in port coordinates gives equality with translated edge
factors on every independent pair assignment. The commutation condition is
an explicit geometric identity, not compatibility of chosen gauge matrices.
Supporting calculation for arXiv:1804.04964, lines 1891–1894. -/
private theorem prod_translate_eq_of_independentPortProduct_invariant
    {Direction Position : Type*} [Fintype Direction] [Fintype Position]
    {X : Direction → Type*}
    (ν : Direction → Equiv.Perm Position) (τ : Equiv.Perm Position)
    (hcomm : ∀ r p, τ (ν r p) = ν r (τ p))
    (E : (r : Direction) → Position → X r → X r → ℂ)
    (hTI : ∀ x : (p : Position) → (r : Direction) → Bool → X r,
      independentPortProduct ν E (fun p => x (τ p)) = independentPortProduct ν E x)
    (a : (r : Direction) → Position → X r × X r) :
    (∏ z : Direction × Position, E z.1 z.2 (a z.1 z.2).1 (a z.1 z.2).2) =
      ∏ z : Direction × Position,
        E z.1 (τ z.2) (a z.1 z.2).1 (a z.1 z.2).2 := by
  classical
  let e := independentPortConfigEquivEdgePair (X := X) ν
  let Q (b : (r : Direction) → Position → X r × X r) : ℂ :=
    ∏ z : Direction × Position, E z.1 z.2 (b z.1 z.2).1 (b z.1 z.2).2
  have hQ (b : (r : Direction) → Position → X r × X r) :
      Q (fun r p => b r (τ p)) = Q b := by
    have h := hTI (e.symm b)
    change Q (e (fun p => e.symm b (τ p))) = Q (e (e.symm b)) at h
    have he : e (fun p => e.symm b (τ p)) = fun r p => b r (τ p) := by
      change independentPortConfigEquivEdgePair ν (fun p => e.symm b (τ p)) = _
      rw [independentPortConfigEquivEdgePair_translate ν τ hcomm]
      change (fun r p => e (e.symm b) r (τ p)) = _
      rw [e.apply_symm_apply]
    rw [he, e.apply_symm_apply] at h
    exact h
  calc
    _ = Q a := rfl
    _ = Q (fun r p => a r (τ.symm p)) := by
      simpa only [Equiv.symm_apply_apply] using hQ (fun r p => a r (τ.symm p))
    _ = _ := by
      refine Fintype.prod_equiv (Equiv.prodCongr (Equiv.refl Direction) τ.symm) _ _ ?_
      rintro ⟨r, p⟩
      change E r p (a r (τ.symm p)).1 (a r (τ.symm p)).2 =
        E r (τ (τ.symm p)) (a r (τ.symm p)).1 (a r (τ.symm p)).2
      rw [τ.apply_symm_apply]

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- Rightward and downward native neighbors, indexed by horizontal=false
and vertical=true. Supporting geometry for arXiv:1804.04964,
lines 1891–1894, in the library's outgoing-leg convention. -/
def torusOutgoingNeighbor (r : Bool) : Equiv.Perm (TorusVertex width height) :=
  if r then translateEquiv 0 (-1) else translateEquiv 1 0

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
/-- Native outgoing neighbors commute with every torus translation.
This is a geometric identity, independent of all chosen tensor gauges.
Supporting geometry for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusOutgoingNeighbor_translate (a : ZMod width) (b : ZMod height)
    (r : Bool) (p : TorusVertex width height) :
    translateEquiv a b (torusOutgoingNeighbor r p) =
      torusOutgoingNeighbor r (translateEquiv a b p) := by
  cases r <;> ext <;>
    simp [torusOutgoingNeighbor, translateEquiv_apply, add_assoc, add_comm]

omit [Fact (1 < width)] [Fact (1 < height)] in
/-- Full port-product invariance on the actual torus gives the translated
factor identity used for direction-wise normalization. The right/down
neighbor commutation is proved internally. This is a supporting coordinate
step for arXiv:1804.04964, lines 1891–1894; the identification with the actual
PEPS coefficient function is still required before applying it. -/
theorem torus_prod_translate_eq_of_portProduct_invariant
    {X : Bool → Type*}
    (E : (r : Bool) → TorusVertex width height → X r → X r → ℂ)
    (hTI : ∀ (a : ZMod width) (b : ZMod height)
      (x : (p : TorusVertex width height) → (r : Bool) → Bool → X r),
      independentPortProduct torusOutgoingNeighbor E
          (fun p => x (translateEquiv a b p)) =
        independentPortProduct torusOutgoingNeighbor E x)
    (t : TorusVertex width height)
    (c : (z : Bool × TorusVertex width height) → X z.1 × X z.1) :
    (∏ z : Bool × TorusVertex width height, E z.1 z.2 (c z).1 (c z).2) =
      ∏ z : Bool × TorusVertex width height,
        E z.1 (z.2 + t) (c z).1 (c z).2 := by
  simpa only [translateEquiv_apply, Prod.mk.eta, Prod.add_def] using
    prod_translate_eq_of_independentPortProduct_invariant
      (torusOutgoingNeighbor (width := width) (height := height))
      (translateEquiv t.1 t.2)
      (torusOutgoingNeighbor_translate t.1 t.2) E (hTI t.1 t.2)
      (fun r p => c (r, p))

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d Dh Dv : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The outgoing edge has native endpoints p and its right/down neighbor,
independently of its stored endpoint order.
Supporting geometry for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusOutgoingEdgeEquiv_endpoints (z : Bool × TorusVertex width height) :
    ((torusOutgoingEdgeEquiv z).1.1 = z.2 ∧
      (torusOutgoingEdgeEquiv z).1.2 = torusOutgoingNeighbor z.1 z.2) ∨
    ((torusOutgoingEdgeEquiv z).1.1 = torusOutgoingNeighbor z.1 z.2 ∧
      (torusOutgoingEdgeEquiv z).1.2 = z.2) := by
  rcases z with ⟨r, p⟩
  cases r
  · simpa [torusOutgoingNeighbor, torusRightEdge, translateEquiv_apply] using
      Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2)
  · rw [torusOutgoingEdgeEquiv_vertical]
    have hhead : torusOutgoingNeighbor true p = (p.1, p.2 - 1) := by
      simp [torusOutgoingNeighbor, translateEquiv_apply, sub_eq_add_neg]
    rw [hhead]
    change ((torusUpEdge (p.1, p.2 - 1)).1.1 = p ∧
      (torusUpEdge (p.1, p.2 - 1)).1.2 = (p.1, p.2 - 1)) ∨
      ((torusUpEdge (p.1, p.2 - 1)).1.1 = (p.1, p.2 - 1) ∧
        (torusUpEdge (p.1, p.2 - 1)).1.2 = p)
    rcases Edge.ofAdj_endpoints (torusGraph_adj_up p.1 (p.2 - 1)) with h | h
    · exact Or.inr ⟨h.1, by simpa [torusUpEdge] using h.2⟩
    · exact Or.inl ⟨by simpa [torusUpEdge] using h.1, h.2⟩

/-- The tail incidence of an actual native edge.
Supporting coordinates for arXiv:1804.04964, lines 1891–1894. -/
def torusOutgoingTailIncident (z : Bool × TorusVertex width height) :
    IncidentEdge (torusGraph width height) z.2 :=
  ⟨torusOutgoingEdgeEquiv z,
    (torusOutgoingEdgeEquiv_endpoints z).elim
      (fun h => Or.inl h.1) (fun h => Or.inr h.2)⟩

/-- The head incidence of an actual native edge.
Supporting coordinates for arXiv:1804.04964, lines 1891–1894. -/
def torusOutgoingHeadIncident (z : Bool × TorusVertex width height) :
    IncidentEdge (torusGraph width height) (torusOutgoingNeighbor z.1 z.2) :=
  ⟨torusOutgoingEdgeEquiv z,
    (torusOutgoingEdgeEquiv_endpoints z).elim
      (fun h => Or.inr h.2) (fun h => Or.inl h.1)⟩

/-- The actual independent endpoint matrices give an invertible native factor
on the appropriate horizontal or vertical reference space.
Supporting construction for arXiv:1804.04964, lines 1891–1894. -/
noncomputable def torusNativeIndependentEdgeKernel
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim Dh Dv)
    (K : (p : TorusVertex width height) → (ie : IncidentEdge (torusGraph width height) p) →
      GL (Fin (A.bondDim ie.1)) ℂ)
    (z : Bool × TorusVertex width height) : GL (Fin (if z.1 then Dv else Dh)) ℂ :=
  glReindex (bondDim_torusOutgoingEdgeEquiv A hU z)
    (glTranspose (show GL (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ from
        K z.2 (torusOutgoingTailIncident z)) *
      (show GL (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ from
        K (torusOutgoingNeighbor z.1 z.2) (torusOutgoingHeadIncident z)))

/-- A native factor is precisely the contraction of its endpoint kernels,
with both external indices transported by the canonical finite cast.
Supporting coefficient identity for arXiv:1804.04964, lines 1891–1894. -/
theorem torusNativeIndependentEdgeKernel_apply
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim Dh Dv)
    (K : (p : TorusVertex width height) → (ie : IncidentEdge (torusGraph width height) p) →
      GL (Fin (A.bondDim ie.1)) ℂ)
    (z : Bool × TorusVertex width height) (a b : Fin (if z.1 then Dv else Dh)) :
    (torusNativeIndependentEdgeKernel A hU K z :
      Matrix (Fin (if z.1 then Dv else Dh)) (Fin (if z.1 then Dv else Dh)) ℂ) a b =
      ∑ j : Fin (A.bondDim (torusOutgoingEdgeEquiv z)),
        ((show GL (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ from
          K z.2 (torusOutgoingTailIncident z)) :
          Matrix (Fin (A.bondDim (torusOutgoingEdgeEquiv z)))
            (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ)
          j (Fin.cast (bondDim_torusOutgoingEdgeEquiv A hU z).symm a) *
        ((show GL (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ from
          K (torusOutgoingNeighbor z.1 z.2) (torusOutgoingHeadIncident z)) :
          Matrix (Fin (A.bondDim (torusOutgoingEdgeEquiv z)))
            (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ)
          j (Fin.cast (bondDim_torusOutgoingEdgeEquiv A hU z).symm b) := by
  rfl

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The canonical actual-star coordinates, reorganized as horizontal/vertical
incoming/outgoing ports. Supporting coordinates for arXiv:1804.04964,
lines 1891–1894. -/
noncomputable def torusDirectionPortConfigEquiv
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (p : TorusVertex width height) :
    ((r : Bool) → Bool → Fin (if r then A.bondDim (torusUpEdge 0)
      else A.bondDim (torusRightEdge 0))) ≃ LocalVirtualConfig A p :=
  (fourLegConfigEquivDirectionPorts (A.bondDim (torusRightEdge 0))
      (A.bondDim (torusUpEdge 0))).symm.trans (torusFourLegConfigEquiv A hU p)

/-- Outgoing port values are unchanged by the canonical finite casts.
Supporting coefficient coordinates for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusDirectionPortConfigEquiv_tail_val
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (x : TorusVertex width height → (r : Bool) → Bool →
      Fin (if r then A.bondDim (torusUpEdge 0) else A.bondDim (torusRightEdge 0)))
    (z : Bool × TorusVertex width height) :
    (torusDirectionPortConfigEquiv A hU z.2 (x z.2) (torusOutgoingTailIncident z)).val =
      (x z.2 z.1 true).val := by
  rcases z with ⟨r, p⟩
  let y := (fourLegConfigEquivDirectionPorts (A.bondDim (torusRightEdge 0))
    (A.bondDim (torusUpEdge 0))).symm (x p)
  cases r
  · have htail : torusOutgoingTailIncident (false, p) = torusRightLeg p := by
      apply Subtype.ext
      exact torusOutgoingEdgeEquiv_horizontal p
    change (torusFourLegConfigEquiv A hU p y
      (torusOutgoingTailIncident (false, p))).val = _
    rw [htail]
    have hval := congrArg Fin.val (torusFourLegConfigEquiv_apply_leg A hU p y 1)
    change (torusFourLegConfigEquiv A hU p y (torusRightLeg p)).val =
      (x p false true).val at hval
    exact hval
  · have htail : torusOutgoingTailIncident (true, p) = torusDownLeg p := by
      apply Subtype.ext
      exact torusOutgoingEdgeEquiv_vertical p
    change (torusFourLegConfigEquiv A hU p y
      (torusOutgoingTailIncident (true, p))).val = _
    rw [htail]
    have hval := congrArg Fin.val (torusFourLegConfigEquiv_apply_leg A hU p y 2)
    change (torusFourLegConfigEquiv A hU p y (torusDownLeg p)).val =
      (x p true true).val at hval
    exact hval

/-- Incoming port values at the native head are unchanged by the canonical
finite casts. Supporting coordinates for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusDirectionPortConfigEquiv_head_val
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (x : TorusVertex width height → (r : Bool) → Bool →
      Fin (if r then A.bondDim (torusUpEdge 0) else A.bondDim (torusRightEdge 0)))
    (z : Bool × TorusVertex width height) :
    (torusDirectionPortConfigEquiv A hU (torusOutgoingNeighbor z.1 z.2)
      (x (torusOutgoingNeighbor z.1 z.2)) (torusOutgoingHeadIncident z)).val =
      (x (torusOutgoingNeighbor z.1 z.2) z.1 false).val := by
  rcases z with ⟨r, p⟩
  cases r
  · let q := torusOutgoingNeighbor false p
    let y := (fourLegConfigEquivDirectionPorts (A.bondDim (torusRightEdge 0))
      (A.bondDim (torusUpEdge 0))).symm (x q)
    have hhead : torusOutgoingHeadIncident (false, p) = torusLeftLeg q := by
      apply Subtype.ext
      change torusOutgoingEdgeEquiv (false, p) = torusLeftEdge q
      simp [q, torusOutgoingNeighbor, torusLeftEdge, translateEquiv_apply]
    change (torusFourLegConfigEquiv A hU q y
      (torusOutgoingHeadIncident (false, p))).val = _
    rw [hhead]
    have hval := congrArg Fin.val (torusFourLegConfigEquiv_apply_leg A hU q y 3)
    change (torusFourLegConfigEquiv A hU q y (torusLeftLeg q)).val =
      (x q false false).val at hval
    exact hval
  · let q := torusOutgoingNeighbor true p
    let y := (fourLegConfigEquivDirectionPorts (A.bondDim (torusRightEdge 0))
      (A.bondDim (torusUpEdge 0))).symm (x q)
    have hhead : torusOutgoingHeadIncident (true, p) = torusTopLeg q := by
      apply Subtype.ext
      change torusOutgoingEdgeEquiv (true, p) = torusUpEdge q
      simp [q, torusOutgoingNeighbor, torusDownEdge, translateEquiv_apply, sub_eq_add_neg]
    change (torusFourLegConfigEquiv A hU q y
      (torusOutgoingHeadIncident (true, p))).val = _
    rw [hhead]
    have hval := congrArg Fin.val (torusFourLegConfigEquiv_apply_leg A hU q y 0)
    change (torusFourLegConfigEquiv A hU q y (torusTopLeg q)).val =
      (x q true false).val at hval
    exact hval

/-- The actual graph coefficient equals the native product on every independent
port assignment. In particular, this does not restrict to the original diagonal
bond configurations. Supporting composition for arXiv:1804.04964,
lines 1891–1894. -/
theorem independentLegEdgeCoefficient_eq_torusNativeProduct
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (K : (p : TorusVertex width height) → (ie : IncidentEdge (torusGraph width height) p) →
      GL (Fin (A.bondDim ie.1)) ℂ)
    (x : TorusVertex width height → (r : Bool) → Bool →
      Fin (if r then A.bondDim (torusUpEdge 0) else A.bondDim (torusRightEdge 0))) :
    independentLegEdgeCoefficient A
        (fun p ie => (K p ie : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ))
        (fun p => torusDirectionPortConfigEquiv A hU p (x p)) =
      independentPortProduct torusOutgoingNeighbor
        (fun r p => (torusNativeIndependentEdgeKernel A hU K (r, p) :
          Matrix (Fin (if r then A.bondDim (torusUpEdge 0)
            else A.bondDim (torusRightEdge 0)))
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ)) x := by
  classical
  let M := fun p ie => (K p ie :
    Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
  let ξ := fun p => torusDirectionPortConfigEquiv A hU p (x p)
  let S (e : Edge (torusGraph width height)) : ℂ :=
    ((show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
        M e.1.1 (edgeLeftIncident e))ᵀ *
      (show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
        M e.1.2 (edgeRightIncident e)))
        (leftIncidentValue A ξ e) (rightIncidentValue A ξ e)
  change (∏ e, S e) = _
  calc
    _ = ∏ z : Bool × TorusVertex width height, S (torusOutgoingEdgeEquiv z) :=
      (torusOutgoingEdgeEquiv.prod_comp S).symm
    _ = _ := by
      refine Finset.prod_congr rfl ?_
      rintro ⟨r, p⟩ hz
      let z : Bool × TorusVertex width height := (r, p)
      have hne : z.2 ≠ torusOutgoingNeighbor z.1 z.2 := by
        intro hpq
        apply ne_of_lt (torusOutgoingEdgeEquiv z).2.1
        rcases torusOutgoingEdgeEquiv_endpoints z with h | h
        · exact h.1.trans (hpq.trans h.2.symm)
        · exact h.1.trans (hpq.symm.trans h.2.symm)
      have horder := independentLegKernel_edge_eq_of_endpoints A M ξ
        (torusOutgoingEdgeEquiv z) (torusOutgoingTailIncident z).2
        (torusOutgoingHeadIncident z).2 hne
      have htail : ξ z.2 (torusOutgoingTailIncident z) =
          Fin.cast (bondDim_torusOutgoingEdgeEquiv A hU z).symm (x z.2 z.1 true) := by
        apply Fin.ext
        exact torusDirectionPortConfigEquiv_tail_val A hU x z
      have hhead : ξ (torusOutgoingNeighbor z.1 z.2) (torusOutgoingHeadIncident z) =
          Fin.cast (bondDim_torusOutgoingEdgeEquiv A hU z).symm
            (x (torusOutgoingNeighbor z.1 z.2) z.1 false) := by
        apply Fin.ext
        exact torusDirectionPortConfigEquiv_head_val A hU x z
      let T : Matrix (Fin (A.bondDim (torusOutgoingEdgeEquiv z)))
          (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ :=
        ((show GL (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ from
          K z.2 (torusOutgoingTailIncident z)) : Matrix _ _ ℂ)
      let H : Matrix (Fin (A.bondDim (torusOutgoingEdgeEquiv z)))
          (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ :=
        ((show GL (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ from
          K (torusOutgoingNeighbor z.1 z.2) (torusOutgoingHeadIncident z)) : Matrix _ _ ℂ)
      let a₀ : Fin (A.bondDim (torusOutgoingEdgeEquiv z)) := ξ z.2 (torusOutgoingTailIncident z)
      let b₀ : Fin (A.bondDim (torusOutgoingEdgeEquiv z)) :=
        ξ (torusOutgoingNeighbor z.1 z.2) (torusOutgoingHeadIncident z)
      have hord : S (torusOutgoingEdgeEquiv z) = ∑ j, T j a₀ * H j b₀ := by
        exact horder
      have ha : a₀ = Fin.cast (bondDim_torusOutgoingEdgeEquiv A hU z).symm
          (x z.2 z.1 true) := htail
      have hb : b₀ = Fin.cast (bondDim_torusOutgoingEdgeEquiv A hU z).symm
          (x (torusOutgoingNeighbor z.1 z.2) z.1 false) := hhead
      calc
        S (torusOutgoingEdgeEquiv z) = ∑ j, T j a₀ * H j b₀ := hord
        _ = ∑ j, T j (Fin.cast (bondDim_torusOutgoingEdgeEquiv A hU z).symm
              (x z.2 z.1 true)) *
              H j (Fin.cast (bondDim_torusOutgoingEdgeEquiv A hU z).symm
                (x (torusOutgoingNeighbor z.1 z.2) z.1 false)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact congrArg₂ (fun u v : ℂ => u * v)
            (congrArg (fun u : Fin (A.bondDim (torusOutgoingEdgeEquiv z)) => T j u) ha)
            (congrArg (fun v : Fin (A.bondDim (torusOutgoingEdgeEquiv z)) => H j v) hb)
        _ = _ := (torusNativeIndependentEdgeKernel_apply A hU K z
          (x z.2 z.1 true) (x (torusOutgoingNeighbor z.1 z.2) z.1 false)).symm

end TNLean.PEPS
