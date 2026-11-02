/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import TNLean.PEPS.TorusIncidentCoordinates
import TNLean.PEPS.TorusSingletonRegion
import TNLean.PEPS.TorusStateTranslationInvariant

/-!
# Four-leg coordinates, repeated tensors and the local translation orbit

The four virtual spaces are ordered top, right, down, left, with dimensions
vertical, horizontal, vertical, horizontal. A common array in these coordinates
defines an actual translation-invariant tensor with the original bond dimensions.
For an injective state invariant under translations, the Fundamental Theorem
expresses every local tensor as independent invertible changes of the origin
array. Both torus periods are at least three.

Source: arXiv:1804.04964, Theorem 2, lines 1207–1212, and Applications,
lines 1891–1894.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The four reference dimensions in top, right, down, left order.
Source: arXiv:1804.04964, orientation-wise dimensions in lines 1891–1894. -/
def torusFourLegBondDim (A : Tensor (torusGraph width height) d) : Fin 4 → ℕ :=
  ![A.bondDim (torusUpEdge 0), A.bondDim (torusRightEdge 0),
    A.bondDim (torusUpEdge 0), A.bondDim (torusRightEdge 0)]

/-- Orientation-uniform dimensions identify each actual incident virtual space
with its corresponding reference space. Source: arXiv:1804.04964,
Applications, lines 1891–1894. -/
theorem bondDim_torusIncidentLeg_eq_fourLegBondDim
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (p : TorusVertex width height) (i : Fin 4) :
    A.bondDim (torusIncidentLeg p i).1 = torusFourLegBondDim A i := by
  fin_cases i
  · change A.bondDim (torusUpEdge p) = A.bondDim (torusUpEdge 0)
    exact hU.2 _ (isVerticalTorusEdge_torusUpEdge p)
  · change A.bondDim (torusRightEdge p) = A.bondDim (torusRightEdge 0)
    exact hU.1 _ (isHorizontalTorusEdge_torusRightEdge p)
  · change A.bondDim (torusUpEdge (p.1, p.2 - 1)) = A.bondDim (torusUpEdge 0)
    exact hU.2 _ (isVerticalTorusEdge_torusUpEdge (p.1, p.2 - 1))
  · change A.bondDim (torusRightEdge (p.1 - 1, p.2)) = A.bondDim (torusRightEdge 0)
    exact hU.1 _ (isHorizontalTorusEdge_torusRightEdge (p.1 - 1, p.2))

/-- The canonical four-port coordinates on an actual anisotropic torus star.
Only the port bijection and the equalities of finite dimensions are used.
Source: arXiv:1804.04964, Applications, lines 1891–1894. -/
def torusFourLegConfigEquiv
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (p : TorusVertex width height) :
    ((i : Fin 4) → Fin (torusFourLegBondDim A i)) ≃ LocalVirtualConfig A p :=
  (torusIncidentLegEquiv p).piCongr
    (fun i ↦ finCongr (bondDim_torusIncidentLeg_eq_fourLegBondDim A hU p i).symm)

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Translation preserves the number of each of the four native incident legs. -/
private theorem translateEdge_torusIncidentLeg (a : ZMod width) (b : ZMod height)
    (p : TorusVertex width height) (i : Fin 4) :
    translateEdge a b (torusIncidentLeg p i).1 =
      (torusIncidentLeg (translate a b p) i).1 := by
  fin_cases i
  · change translateEdge a b (torusUpEdge p) = torusUpEdge (translate a b p)
    simpa only [translate_apply] using translateEdge_torusUpEdge a b p
  · change translateEdge a b (torusRightEdge p) = torusRightEdge (translate a b p)
    simpa only [translate_apply] using translateEdge_torusRightEdge a b p
  · change translateEdge a b (torusDownEdge p) = torusDownEdge (translate a b p)
    simp only [torusDownEdge, translateEdge_torusUpEdge, translate_apply,
      sub_add_eq_add_sub]
  · change translateEdge a b (torusLeftEdge p) = torusLeftEdge (translate a b p)
    simp only [torusLeftEdge, translateEdge_torusRightEdge, translate_apply,
      sub_add_eq_add_sub]

/-- The graph edge map preserves the same four native incident-leg numbers. -/
private theorem map_translate_torusIncidentLeg (a : ZMod width) (b : ZMod height)
    (p : TorusVertex width height) (i : Fin 4) :
    Edge.map (translate a b) (torusIncidentLeg p i).1 =
      (torusIncidentLeg (translate a b p) i).1 := by
  simpa only [translateEdge_eq_map] using translateEdge_torusIncidentLeg a b p i

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The canonical four-port coordinates evaluate by the corresponding finite cast.
This is coordinate transport for arXiv:1804.04964, Applications, lines 1891–1894. -/
theorem torusFourLegConfigEquiv_apply_leg
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (p : TorusVertex width height)
    (x : (i : Fin 4) → Fin (torusFourLegBondDim A i)) (i : Fin 4) :
    torusFourLegConfigEquiv A hU p x (torusIncidentLeg p i) =
      finCongr (bondDim_torusIncidentLeg_eq_fourLegBondDim A hU p i).symm (x i) := by
  exact Equiv.piCongr_apply_apply
    (W := fun j : Fin 4 ↦ Fin (torusFourLegBondDim A j))
    (Z := fun ie : IncidentEdge (torusGraph width height) p ↦ Fin (A.bondDim ie.1))
    (torusIncidentLegEquiv p)
    (fun j ↦ finCongr (bondDim_torusIncidentLeg_eq_fourLegBondDim A hU p j).symm) x i

/-- Canonical four-port reindexing preserves the actual vertex tensor's injectivity.
In particular, the origin supplies the injective reference tensor in the construction
of arXiv:1804.04964, Applications, lines 1891–1894; it is not an extra datum. -/
theorem linearIndependent_component_torusFourLegConfigEquiv
    (A : Tensor (torusGraph width height) d) (hInj : A.IsInjective)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (p : TorusVertex width height) :
    LinearIndependent ℂ
      (fun x : (i : Fin 4) → Fin (torusFourLegBondDim A i) ↦
        A.component p (torusFourLegConfigEquiv A hU p x)) := by
  exact (hInj.isVertexInjective p).comp (torusFourLegConfigEquiv A hU p)
    (torusFourLegConfigEquiv A hU p).injective

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Pulling back the canonical four-port configuration preserves every port value.
Source: arXiv:1804.04964, Applications, injective two-dimensional translation
invariance at lines 1891–1894. -/
private theorem localVirtualConfigPullback_torusFourLegConfigEquiv
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (a : ZMod width) (b : ZMod height)
    (hDim : (A.transport (translate a b)).bondDim = A.bondDim)
    (p : TorusVertex width height)
    (x : (i : Fin 4) → Fin (torusFourLegBondDim A i)) :
    localVirtualConfigPullback A (translate a b) p
      (((torusFourLegConfigEquiv A hU p).trans
        (castLocalVirtualConfig (A.transport (translate a b)) A hDim p).symm) x) =
      torusFourLegConfigEquiv A hU ((translate a b).symm p) x := by
  let ξ : LocalVirtualConfig (A.transport (translate a b)) p :=
    (castLocalVirtualConfig (A.transport (translate a b)) A hDim p).symm
      (torusFourLegConfigEquiv A hU p x)
  funext ie
  obtain ⟨i, rfl⟩ :=
    (torusIncidentLegEquiv ((translate a b).symm p)).surjective ie
  have hleg :
      IncidentEdge.toSymm (translate a b) p
        (torusIncidentLeg ((translate a b).symm p) i) = torusIncidentLeg p i := by
    apply Subtype.ext
    change Edge.map (translate a b)
      (torusIncidentLeg ((translate a b).symm p) i).1 = (torusIncidentLeg p i).1
    have hp : translate a b ((translate a b).symm p) = p := by
      change ((p.1 - a + a, p.2 - b + b) : TorusVertex width height) = p
      simp
    exact (map_translate_torusIncidentLeg a b ((translate a b).symm p) i).trans
      (congrArg (fun q : TorusVertex width height ↦ (torusIncidentLeg q i).1) hp)
  have hcast :
      castLocalVirtualConfig (A.transport (translate a b)) A hDim p ξ =
        torusFourLegConfigEquiv A hU p x :=
    (castLocalVirtualConfig (A.transport (translate a b)) A hDim p).apply_symm_apply
      (torusFourLegConfigEquiv A hU p x)
  have hval := congrArg
    (fun η : LocalVirtualConfig A p ↦ (η (torusIncidentLeg p i)).val) hcast
  change (ξ (torusIncidentLeg p i)).val =
    (torusFourLegConfigEquiv A hU p x (torusIncidentLeg p i)).val at hval
  apply Fin.ext
  change
    (ξ (IncidentEdge.toSymm (translate a b) p
      (torusIncidentLeg ((translate a b).symm p) i))).val =
    (torusFourLegConfigEquiv A hU ((translate a b).symm p) x
      (torusIncidentLeg ((translate a b).symm p) i)).val
  rw [hleg]
  calc
    (ξ (torusIncidentLeg p i)).val =
        (torusFourLegConfigEquiv A hU p x (torusIncidentLeg p i)).val := hval
    _ = (x i).val := by
      simpa only [finCongr_apply, Fin.val_cast] using
        congrArg Fin.val (torusFourLegConfigEquiv_apply_leg A hU p x i)
    _ = (torusFourLegConfigEquiv A hU ((translate a b).symm p) x
        (torusIncidentLeg ((translate a b).symm p) i)).val := by
      symm
      simpa only [finCongr_apply, Fin.val_cast] using
        congrArg Fin.val
          (torusFourLegConfigEquiv_apply_leg A hU ((translate a b).symm p) x i)


end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d Dh Dv : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Orientation-uniform bond dimensions are invariant under translations.
Only the horizontal and vertical edge classes are used. This is the elementary
converse to orientation-wise constancy in the translation-invariance application
of arXiv:1804.04964, local `paper_normal.tex` lines 1891–1894. -/
private theorem bondDim_translateEdge_of_torusUniformBondDim
    (bd : Edge (torusGraph width height) → ℕ) (hU : TorusUniformBondDim bd Dh Dv)
    (a : ZMod width) (b : ZMod height) (e : Edge (torusGraph width height)) :
    bd (translateEdge a b e) = bd e := by
  obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e
  · change bd (translateEdge a b (torusRightEdge v)) = bd (torusRightEdge v)
    rw [translateEdge_torusRightEdge]
    exact (hU.1 _ (isHorizontalTorusEdge_torusRightEdge (v.1 + a, v.2 + b))).trans
      (hU.1 _ (isHorizontalTorusEdge_torusRightEdge v)).symm
  · change bd (translateEdge a b (torusUpEdge v)) = bd (torusUpEdge v)
    rw [translateEdge_torusUpEdge]
    exact (hU.2 _ (isVerticalTorusEdge_torusUpEdge (v.1 + a, v.2 + b))).trans
      (hU.2 _ (isVerticalTorusEdge_torusUpEdge v)).symm

/-- Transport by a torus translation preserves an orientation-uniform
bond-dimension function. No invariance of the tensor or its state is required.
Source: arXiv:1804.04964, orientation-wise dimensions at local
`paper_normal.tex` lines 1891–1894. -/
private theorem transport_bondDim_eq_of_torusUniformBondDim
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim Dh Dv)
    (a : ZMod width) (b : ZMod height) :
    (A.transport (translate a b)).bondDim = A.bondDim := by
  funext e
  rw [Tensor.transport_bondDim]
  have h := bondDim_translateEdge_of_torusUniformBondDim A.bondDim hU a b
    (Edge.map (translate a b).symm e)
  rw [translateEdge_eq_map, Edge.map_map_symm] at h
  exact h.symm

end TNLean.PEPS

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Equal bond dimensions and equal coefficients in the canonical cast coordinates
identify the actual tensor records. -/
private theorem tensor_eq_of_bondDim_eq_component_cast
    (C B : Tensor G d) (hDim : C.bondDim = B.bondDim)
    (hcomp : ∀ (v : V) (η : LocalVirtualConfig C v) (σ : Fin d),
      B.component v (castLocalVirtualConfig C B hDim v η) σ =
        C.component v η σ) :
    C = B := by
  cases C with
  | mk D c =>
    cases B with
    | mk D' b =>
      change D = D' at hDim
      subst D'
      have hcomponent : c = b := by
        funext v η σ
        simpa [castLocalVirtualConfig] using (hcomp v η σ).symm
      exact congrArg (Tensor.mk D) hcomponent

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Inverse four-port coordinates identify pullback of a translated local
configuration with the dimension-cast configuration at the original vertex.
This is the inverse form of the coordinate transport in arXiv:1804.04964,
Applications, local `paper_normal.tex` lines 1891–1894. -/
private theorem torusFourLegConfigEquiv_symm_pullback
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (a : ZMod width) (b : ZMod height)
    (hDim : (A.transport (translate a b)).bondDim = A.bondDim)
    (p : TorusVertex width height)
    (η : LocalVirtualConfig (A.transport (translate a b)) p) :
    (torusFourLegConfigEquiv A hU ((translate a b).symm p)).symm
      (localVirtualConfigPullback A (translate a b) p η) =
        (torusFourLegConfigEquiv A hU p).symm
          (castLocalVirtualConfig (A.transport (translate a b)) A hDim p η) := by
  let E := torusFourLegConfigEquiv A hU p
  let Eprev := torusFourLegConfigEquiv A hU ((translate a b).symm p)
  let q := castLocalVirtualConfig (A.transport (translate a b)) A hDim p
  let x := E.symm (q η)
  have hinput : (E.trans q.symm) x = η := by
    change q.symm (E (E.symm (q η))) = η
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  have h := localVirtualConfigPullback_torusFourLegConfigEquiv A hU a b hDim p x
  change localVirtualConfigPullback A (translate a b) p ((E.trans q.symm) x) =
    Eprev x at h
  rw [hinput] at h
  change Eprev.symm (localVirtualConfigPullback A (translate a b) p η) = x
  calc
    Eprev.symm (localVirtualConfigPullback A (translate a b) p η) =
        Eprev.symm (Eprev x) := congrArg Eprev.symm h
    _ = x := Eprev.symm_apply_apply x

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Repeat a single four-leg tensor in the canonical coordinates at every vertex,
retaining the original horizontal and vertical bond dimensions. Source:
arXiv:1804.04964, Applications, local `paper_normal.tex` lines 1891–1894. -/
def torusFourLegTensor
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ) :
    Tensor (torusGraph width height) d where
  bondDim := A.bondDim
  component p η := F ((torusFourLegConfigEquiv A hU p).symm η)

/-- The repeated tensor has exactly the original bond dimensions. Source:
arXiv:1804.04964, Applications, local `paper_normal.tex` lines 1891–1894. -/
@[simp] theorem torusFourLegTensor_bondDim
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ) :
    (torusFourLegTensor A hU F).bondDim = A.bondDim :=
  rfl

/-- Each component is the common four-leg tensor in the canonical coordinates.
Source: arXiv:1804.04964, Applications, local `paper_normal.tex` lines 1891–1894. -/
@[simp] theorem torusFourLegTensor_component
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ)
    (p : TorusVertex width height) (η : LocalVirtualConfig A p) :
    (torusFourLegTensor A hU F).component p η =
      F ((torusFourLegConfigEquiv A hU p).symm η) :=
  rfl

/-- Injectivity of the common four-leg tensor implies vertex injectivity at
all sites. Source: arXiv:1804.04964, Applications, local `paper_normal.tex`
lines 1891–1894. -/
private theorem isVertexInjective_torusFourLegTensor
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ)
    (hF : LinearIndependent ℂ F) :
    IsVertexInjective (torusFourLegTensor A hU F) := by
  intro p
  change LinearIndependent ℂ
    (fun η : LocalVirtualConfig A p ↦ F ((torusFourLegConfigEquiv A hU p).symm η))
  exact hF.comp (torusFourLegConfigEquiv A hU p).symm
    (torusFourLegConfigEquiv A hU p).symm.injective

/-- With nonzero original bond spaces, an injective common four-leg tensor gives
an injective tensor on the torus. Source: arXiv:1804.04964, Section 3 and
Applications, local `paper_normal.tex` lines 979–981 and 1891–1894. -/
theorem isInjective_torusFourLegTensor
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ)
    (hF : LinearIndependent ℂ F) (hPos : ∀ e, 0 < A.bondDim e) :
    (torusFourLegTensor A hU F).IsInjective := by
  exact ⟨isVertexInjective_torusFourLegTensor A hU F hF, hPos⟩

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- A single four-leg tensor repeated in the canonical coordinates is fixed by
transport under every torus translation. No invariance of the original tensor
or its state is required. Source: arXiv:1804.04964, Applications, local
`paper_normal.tex` lines 1891–1894. -/
theorem isTorusTranslationInvariant_torusFourLegTensor
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ) :
    IsTorusTranslationInvariant (torusFourLegTensor A hU F) := by
  intro a b
  let B := torusFourLegTensor A hU F
  have hDim : (A.transport (translate a b)).bondDim = A.bondDim :=
    transport_bondDim_eq_of_torusUniformBondDim A hU a b
  have hDimB : (B.transport (translate a b)).bondDim = B.bondDim := hDim
  apply tensor_eq_of_bondDim_eq_component_cast (B.transport (translate a b)) B hDimB
  intro p η σ
  change F ((torusFourLegConfigEquiv A hU p).symm
      (castLocalVirtualConfig (A.transport (translate a b)) A hDim p η)) σ =
    F ((torusFourLegConfigEquiv A hU ((translate a b).symm p)).symm
      (localVirtualConfigPullback A (translate a b) p η)) σ
  exact congrArg (fun x ↦ F x σ)
    (torusFourLegConfigEquiv_symm_pullback A hU a b hDim p η).symm

end TNLean.PEPS

namespace TNLean.PEPS


variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- A local edge-gauge equation gives invertible coefficient kernels on the
actual incident virtual spaces. The sum is transported only across the given
bond-dimension equality. This is the local algebra of arXiv:1804.04964,
Theorem `thm:inj`, local `paper_normal.tex` lines 1207–1212. The local gauge
equation is an input; no translation or uniform-dimension assertion is made. -/
private theorem exists_incidentKernel_of_localGaugeEquation
    (A C : Tensor G d) (hDim : C.bondDim = A.bondDim)
    (X : (e : Edge G) → GL (Fin (C.bondDim e)) ℂ) (p : V)
    (hloc : ∀ (η : LocalVirtualConfig C p) (σ : Fin d),
      A.component p (fun ie ↦ Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        gaugeVertex C X p η σ) :
    ∃ K : (ie : IncidentEdge G p) → GL (Fin (A.bondDim ie.1)) ℂ,
      ∀ (ηA : LocalVirtualConfig A p) (σ : Fin d),
        A.component p ηA σ =
          ∑ ξA : LocalVirtualConfig A p,
            (∏ ie : IncidentEdge G p,
              (K ie : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
                (ηA ie) (ξA ie)) *
              C.component p ((castLocalVirtualConfig C A hDim p).symm ξA) σ := by
  classical
  let q := castLocalVirtualConfig C A hDim p
  let Z (ie : IncidentEdge G p) : GL (Fin (C.bondDim ie.1)) ℂ :=
    if ie.1.1.1 = p then X ie.1 else glTranspose ((X ie.1)⁻¹)
  let K (ie : IncidentEdge G p) : GL (Fin (A.bondDim ie.1)) ℂ :=
    glReindex (congr_fun hDim ie.1) (Z ie)
  have harg (ηA : LocalVirtualConfig A p) :
      (fun ie ↦ Fin.cast (congr_fun hDim ie.1) (q.symm ηA ie)) = ηA := by
    funext ie
    have h := congrFun (q.apply_symm_apply ηA) ie
    simpa only [q, castLocalVirtualConfig_apply] using h
  have hq (ηA : LocalVirtualConfig A p) (ie : IncidentEdge G p) :
      q.symm ηA ie = (finCongr (congr_fun hDim ie.1)).symm (ηA ie) := by
    rfl
  have hZ (ie : IncidentEdge G p) :
      (Z ie : Matrix (Fin (C.bondDim ie.1)) (Fin (C.bondDim ie.1)) ℂ) =
        edgeGaugeAt C X p ie := by
    by_cases h : ie.1.1.1 = p
    · simp [Z, edgeGaugeAt, h]
    · simp [Z, edgeGaugeAt, h, glTranspose_coe]
  have hK (ηA ξA : LocalVirtualConfig A p) (ie : IncidentEdge G p) :
      edgeGaugeAt C X p ie (q.symm ηA ie) (q.symm ξA ie) =
        (K ie : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
          (ηA ie) (ξA ie) := by
    change edgeGaugeAt C X p ie (q.symm ηA ie) (q.symm ξA ie) =
      (glReindex (congr_fun hDim ie.1) (Z ie) :
        Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) (ηA ie) (ξA ie)
    rw [glReindex_coe]
    change edgeGaugeAt C X p ie (q.symm ηA ie) (q.symm ξA ie) =
      (Z ie : Matrix (Fin (C.bondDim ie.1)) (Fin (C.bondDim ie.1)) ℂ)
        ((finCongr (congr_fun hDim ie.1)).symm (ηA ie))
        ((finCongr (congr_fun hDim ie.1)).symm (ξA ie))
    rw [hq ηA ie, hq ξA ie, hZ ie]
  refine ⟨K, ?_⟩
  intro ηA σ
  change A.component p ηA σ =
    ∑ ξA : LocalVirtualConfig A p,
      (∏ ie : IncidentEdge G p,
        (K ie : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
          (ηA ie) (ξA ie)) * C.component p (q.symm ξA) σ
  calc
    A.component p ηA σ = gaugeVertex C X p (q.symm ηA) σ := by
      simpa only [harg ηA] using hloc (q.symm ηA) σ
    _ = ∑ ξA : LocalVirtualConfig A p,
        (∏ ie : IncidentEdge G p,
          edgeGaugeAt C X p ie (q.symm ηA ie) (q.symm ξA ie)) *
            C.component p (q.symm ξA) σ := by
      change (∑ ξC : LocalVirtualConfig C p,
        (∏ ie : IncidentEdge G p,
          edgeGaugeAt C X p ie (q.symm ηA ie) (ξC ie)) * C.component p ξC σ) = _
      exact (q.symm.sum_comp (fun ξC : LocalVirtualConfig C p ↦
        (∏ ie : IncidentEdge G p,
          edgeGaugeAt C X p ie (q.symm ηA ie) (ξC ie)) * C.component p ξC σ)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ξA _
      apply congrArg (fun z : ℂ ↦ z * C.component p (q.symm ξA) σ)
      apply Finset.prod_congr rfl
      intro ie _
      exact hK ηA ξA ie

end TNLean.PEPS

namespace TNLean.PEPS


variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The actual-incidence form of the local translation orbit: all leg kernels
act on the original bond spaces, while the physical reference is the origin
tensor in canonical four-port coordinates. The kernels are derived from the
unconditional injective Fundamental Theorem, not supplied as compatibility data.
Source: arXiv:1804.04964, Theorem `thm:inj`, lines 1207–1212, and the injective
two-dimensional translation-invariance corollary, lines 1891–1894. -/
theorem exists_torus_common_local_orbit_incident
    {A : Tensor (torusGraph width height) d}
    (hInj : A.IsInjective)
    (hTI : IsTorusTranslationInvariantState A) :
    let hU := torusUniformBondDim_of_isTorusTranslationInvariantState hInj hTI
    let E := torusFourLegConfigEquiv A hU
    ∃ K : (p : TorusVertex width height) →
        (ie : IncidentEdge (torusGraph width height) p) →
          GL (Fin (A.bondDim ie.1)) ℂ,
      ∀ (p : TorusVertex width height) (η : LocalVirtualConfig A p) (σ : Fin d),
        A.component p η σ =
          ∑ ξ : LocalVirtualConfig A p,
            (∏ ie : IncidentEdge (torusGraph width height) p,
              (K p ie : Matrix (Fin (A.bondDim ie.1))
                (Fin (A.bondDim ie.1)) ℂ) (η ie) (ξ ie)) *
              A.component 0 (E 0 ((E p).symm ξ)) σ := by
  classical
  let hU := torusUniformBondDim_of_isTorusTranslationInvariantState hInj hTI
  let E := torusFourLegConfigEquiv A hU
  have hpoint (p : TorusVertex width height) :
      ∃ K : (ie : IncidentEdge (torusGraph width height) p) →
          GL (Fin (A.bondDim ie.1)) ℂ,
        ∀ (η : LocalVirtualConfig A p) (σ : Fin d),
          A.component p η σ =
            ∑ ξ : LocalVirtualConfig A p,
              (∏ ie : IncidentEdge (torusGraph width height) p,
                (K ie : Matrix (Fin (A.bondDim ie.1))
                  (Fin (A.bondDim ie.1)) ℂ) (η ie) (ξ ie)) *
                A.component 0 (E 0 ((E p).symm ξ)) σ := by
    let τ := translate p.1 p.2
    let C := A.transport τ
    have hGauge : GaugeEquiv C A :=
      fundamentalTheorem_PEPS C A (hInj.transport τ) hInj
        (sameState_transport_of_isTorusTranslationInvariantState hTI p.1 p.2).symm
        (torusGraph_connected (width := width) (height := height))
    obtain ⟨hDim, X, hX⟩ := hGauge
    obtain ⟨K, hK⟩ :=
      exists_incidentKernel_of_localGaugeEquation A C hDim X p (hX p)
    have hrefFour (y : (i : Fin 4) → Fin (torusFourLegBondDim A i)) (σ : Fin d) :
        C.component p
          (((E p).trans (castLocalVirtualConfig C A hDim p).symm) y) σ =
            A.component 0 (E 0 y) σ := by
      change (A.transport τ).component p _ σ = _
      rw [Tensor.transport_component_localVirtualConfigPullback]
      rw [localVirtualConfigPullback_torusFourLegConfigEquiv A hU p.1 p.2 hDim p y]
      have hp0 : τ.symm p = 0 := by
        change ((p.1 - p.1, p.2 - p.2) : TorusVertex width height) = 0
        simp
      rw [hp0]
    have href (ξ : LocalVirtualConfig A p) (σ : Fin d) :
        C.component p ((castLocalVirtualConfig C A hDim p).symm ξ) σ =
          A.component 0 (E 0 ((E p).symm ξ)) σ := by
      simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
        hrefFour ((E p).symm ξ) σ
    refine ⟨K, ?_⟩
    intro η σ
    calc
      A.component p η σ =
          ∑ ξ : LocalVirtualConfig A p,
            (∏ ie : IncidentEdge (torusGraph width height) p,
              (K ie : Matrix (Fin (A.bondDim ie.1))
                (Fin (A.bondDim ie.1)) ℂ) (η ie) (ξ ie)) *
              C.component p ((castLocalVirtualConfig C A hDim p).symm ξ) σ :=
        hK η σ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ξ _
        exact congrArg
          (fun z : ℂ ↦ (∏ ie : IncidentEdge (torusGraph width height) p,
            (K ie : Matrix (Fin (A.bondDim ie.1))
              (Fin (A.bondDim ie.1)) ℂ) (η ie) (ξ ie)) * z)
          (href ξ σ)
  choose K hK using hpoint
  exact ⟨K, hK⟩

end TNLean.PEPS
