/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixDependentEntries
import TNLean.PEPS.TorusNativeEdgeKernels

/-!
# Independent transformations of a repeated four-leg tensor

Changes on the four canonical virtual spaces induce matrices on the actual
incident bond spaces. The resulting edge matrix is the transpose of the
outgoing matrix times the incoming matrix. A common scalar multiplies the
state by its power equal to the number of vertices.

Source: arXiv:1804.04964, Applications, lines 1891–1899.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The canonical reference size of an arbitrary actual incidence.
Supporting coordinates for arXiv:1804.04964, lines 1891–1894. -/
private theorem bondDim_incident_eq_fourLegBondDim
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (p : TorusVertex width height) (ie : IncidentEdge (torusGraph width height) p) :
    A.bondDim ie.1 = torusFourLegBondDim A ((torusIncidentLegEquiv p).symm ie) := by
  have h := congrArg (fun je : IncidentEdge (torusGraph width height) p => A.bondDim je.1)
    ((torusIncidentLegEquiv p).apply_symm_apply ie)
  exact h.symm.trans (bondDim_torusIncidentLeg_eq_fourLegBondDim A hU p _)

/-- Lift the four common leg kernels to the actual incidence spaces.
Supporting construction for arXiv:1804.04964, lines 1891–1894. -/
noncomputable def torusIncidentKernelOfFourLeg
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ)
    (p : TorusVertex width height) (ie : IncidentEdge (torusGraph width height) p) :
    GL (Fin (A.bondDim ie.1)) ℂ :=
  glReindex (bondDim_incident_eq_fourLegBondDim A hU p ie).symm
    (Q ((torusIncidentLegEquiv p).symm ie))

/-- The lifted kernel has exactly the prescribed entries in canonical
four-leg coordinates. Supporting identity for arXiv:1804.04964,
lines 1891–1894. -/
private theorem torusIncidentKernelOfFourLeg_apply_leg
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ)
    (p : TorusVertex width height)
    (x y : (i : Fin 4) → Fin (torusFourLegBondDim A i)) (i : Fin 4) :
    (torusIncidentKernelOfFourLeg A hU Q p (torusIncidentLeg p i) :
      Matrix (Fin (A.bondDim (torusIncidentLeg p i).1))
        (Fin (A.bondDim (torusIncidentLeg p i).1)) ℂ)
      (torusFourLegConfigEquiv A hU p x (torusIncidentLeg p i))
      (torusFourLegConfigEquiv A hU p y (torusIncidentLeg p i)) =
        (Q i : Matrix (Fin (torusFourLegBondDim A i))
          (Fin (torusFourLegBondDim A i)) ℂ) (x i) (y i) := by
  let j := (torusIncidentLegEquiv p).symm (torusIncidentLeg p i)
  let hD := bondDim_incident_eq_fourLegBondDim A hU p (torusIncidentLeg p i)
  let a : Fin (torusFourLegBondDim A j) :=
    Fin.cast hD (torusFourLegConfigEquiv A hU p x (torusIncidentLeg p i))
  let b : Fin (torusFourLegBondDim A j) :=
    Fin.cast hD (torusFourLegConfigEquiv A hU p y (torusIncidentLeg p i))
  have hi : j = i := (torusIncidentLegEquiv p).symm_apply_apply i
  have ha : a ≍ x i := by
    apply (Fin.heq_ext_iff (congrArg (torusFourLegBondDim A) hi)).mpr
    have hval := congrArg Fin.val (torusFourLegConfigEquiv_apply_leg A hU p x i)
    change a.val = (x i).val at hval
    exact hval
  have hb : b ≍ y i := by
    apply (Fin.heq_ext_iff (congrArg (torusFourLegBondDim A) hi)).mpr
    have hval := congrArg Fin.val (torusFourLegConfigEquiv_apply_leg A hU p y i)
    change b.val = (y i).val at hval
    exact hval
  change (Q j : Matrix (Fin (torusFourLegBondDim A j))
      (Fin (torusFourLegBondDim A j)) ℂ) a b = _
  exact Matrix.entry_eq_of_heq
    (fun k : Fin 4 => (Q k : Matrix (Fin (torusFourLegBondDim A k))
      (Fin (torusFourLegBondDim A k)) ℂ)) hi ha hb

/-- The full local product kernel is preserved by the actual incidence
coordinates. Supporting identity for arXiv:1804.04964, lines 1891–1894. -/
private theorem prod_torusIncidentKernelOfFourLeg
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ)
    (p : TorusVertex width height)
    (x y : (i : Fin 4) → Fin (torusFourLegBondDim A i)) :
    (∏ ie : IncidentEdge (torusGraph width height) p,
      (torusIncidentKernelOfFourLeg A hU Q p ie :
        Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
        (torusFourLegConfigEquiv A hU p x ie)
        (torusFourLegConfigEquiv A hU p y ie)) =
      ∏ i : Fin 4, (Q i : Matrix (Fin (torusFourLegBondDim A i))
        (Fin (torusFourLegBondDim A i)) ℂ) (x i) (y i) := by
  classical
  calc
    _ = ∏ i : Fin 4,
        (torusIncidentKernelOfFourLeg A hU Q p (torusIncidentLeg p i) :
          Matrix (Fin (A.bondDim (torusIncidentLeg p i).1))
            (Fin (A.bondDim (torusIncidentLeg p i).1)) ℂ)
          (torusFourLegConfigEquiv A hU p x (torusIncidentLeg p i))
          (torusFourLegConfigEquiv A hU p y (torusIncidentLeg p i)) :=
      ((torusIncidentLegEquiv p).prod_comp (fun ie =>
        (torusIncidentKernelOfFourLeg A hU Q p ie :
          Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
          (torusFourLegConfigEquiv A hU p x ie)
          (torusFourLegConfigEquiv A hU p y ie))).symm
    _ = _ := Finset.prod_congr rfl
      (fun i _ => torusIncidentKernelOfFourLeg_apply_leg A hU Q p x y i)

end TNLean.PEPS


namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Absorb a common matrix on each virtual leg of a physical tensor.
Supporting construction for arXiv:1804.04964, lines 1891–1894. -/
noncomputable def fourLegKernelApply
    (A : Tensor (torusGraph width height) d)
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ)
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ)
    (x : (i : Fin 4) → Fin (torusFourLegBondDim A i)) : Fin d → ℂ :=
  ∑ y : (i : Fin 4) → Fin (torusFourLegBondDim A i),
    (∏ i, (Q i : Matrix (Fin (torusFourLegBondDim A i))
      (Fin (torusFourLegBondDim A i)) ℂ) (x i) (y i)) • F y

/-- The coefficient formula for absorption of the common leg matrices.
Supporting identity for arXiv:1804.04964, lines 1891–1894. -/
theorem fourLegKernelApply_apply
    (A : Tensor (torusGraph width height) d)
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ)
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ)
    (x : (i : Fin 4) → Fin (torusFourLegBondDim A i)) (σ : Fin d) :
    fourLegKernelApply A Q F x σ =
      ∑ y : (i : Fin 4) → Fin (torusFourLegBondDim A i),
        (∏ i, (Q i : Matrix (Fin (torusFourLegBondDim A i))
          (Fin (torusFourLegBondDim A i)) ℂ) (x i) (y i)) * F y σ := by
  simp only [fourLegKernelApply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The absorbed common array has the actual-incidence kernel expansion.
The local coordinate bijection is used on the full sum, with no restriction
on the independent virtual indices.
Supporting identity for arXiv:1804.04964, lines 1891–1894. -/
theorem fourLegKernelApply_eq_sum_incident
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ)
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ)
    (p : TorusVertex width height) (η : LocalVirtualConfig A p) (σ : Fin d) :
    fourLegKernelApply A Q F ((torusFourLegConfigEquiv A hU p).symm η) σ =
      ∑ ξ : LocalVirtualConfig A p,
        (∏ ie : IncidentEdge (torusGraph width height) p,
          (torusIncidentKernelOfFourLeg A hU Q p ie :
            Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) (η ie) (ξ ie)) *
          F ((torusFourLegConfigEquiv A hU p).symm ξ) σ := by
  classical
  let e := torusFourLegConfigEquiv A hU p
  rw [fourLegKernelApply_apply]
  calc
    _ = ∑ y : (i : Fin 4) → Fin (torusFourLegBondDim A i),
        (∏ ie : IncidentEdge (torusGraph width height) p,
          (torusIncidentKernelOfFourLeg A hU Q p ie :
            Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) (η ie) (e y ie)) *
          F (e.symm (e y)) σ := by
      refine Finset.sum_congr rfl ?_
      intro y hy
      have hprod := prod_torusIncidentKernelOfFourLeg A hU Q p (e.symm η) y
      have harg :
          (∏ ie : IncidentEdge (torusGraph width height) p,
            (torusIncidentKernelOfFourLeg A hU Q p ie :
              Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
              (e (e.symm η) ie) (e y ie)) =
            ∏ ie : IncidentEdge (torusGraph width height) p,
              (torusIncidentKernelOfFourLeg A hU Q p ie :
                Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
                (η ie) (e y ie) :=
        congrArg (fun θ : LocalVirtualConfig A p =>
          ∏ ie : IncidentEdge (torusGraph width height) p,
            (torusIncidentKernelOfFourLeg A hU Q p ie :
              Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
              (θ ie) (e y ie)) (e.apply_symm_apply η)
      exact congrArg₂ (fun a b : ℂ => a * b) (hprod.symm.trans harg)
        (congrArg (fun z => F z σ) (e.symm_apply_apply y)).symm
    _ = _ := e.sum_comp (fun ξ : LocalVirtualConfig A p =>
      (∏ ie : IncidentEdge (torusGraph width height) p,
        (torusIncidentKernelOfFourLeg A hU Q p ie :
          Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) (η ie) (ξ ie)) *
        F (e.symm ξ) σ)

end TNLean.PEPS


namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The leg index of a horizontal/vertical incoming/outgoing port.
Source convention for arXiv:1804.04964, lines 1891–1894: top, right,
down, left have indices zero, one, two, three. -/
private def torusDirectionPortLegIndex (r b : Bool) : Fin 4 :=
  if r then (if b then 2 else 0) else (if b then 1 else 3)

/-- Both ports of a direction have the same reference bond dimension.
Supporting coordinates for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusFourLegBondDim_directionPortLegIndex
    (A : Tensor (torusGraph width height) d) (r b : Bool) :
    torusFourLegBondDim A (torusDirectionPortLegIndex r b) =
      if r then A.bondDim (torusUpEdge 0) else A.bondDim (torusRightEdge 0) := by
  cases r <;> cases b <;> rfl

/-- A reference leg matrix in the common dimension of its direction.
Supporting construction for arXiv:1804.04964, lines 1891–1894. -/
noncomputable def torusFourLegKernelOnPort
    (A : Tensor (torusGraph width height) d)
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ) (r b : Bool) :
    GL (Fin (if r then A.bondDim (torusUpEdge 0)
      else A.bondDim (torusRightEdge 0))) ℂ :=
  glReindex (torusFourLegBondDim_directionPortLegIndex A r b)
    (Q (torusDirectionPortLegIndex r b))

/-- The canonical entry formula for a reference port matrix.
Supporting coefficient identity for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusFourLegKernelOnPort_apply
    (A : Tensor (torusGraph width height) d)
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ) (r b : Bool)
    (u v : Fin (if r then A.bondDim (torusUpEdge 0)
      else A.bondDim (torusRightEdge 0))) :
    (torusFourLegKernelOnPort A Q r b : Matrix _ _ ℂ) u v =
      (Q (torusDirectionPortLegIndex r b) : Matrix _ _ ℂ)
        (Fin.cast (torusFourLegBondDim_directionPortLegIndex A r b).symm u)
        (Fin.cast (torusFourLegBondDim_directionPortLegIndex A r b).symm v) := by
  rfl

/-- An actual incidence with a known leg index has the prescribed matrix
entries, with no choice of the other virtual indices.
Supporting coefficient identity for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusIncidentKernelOfFourLeg_apply_of_index
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ)
    (p : TorusVertex width height) (ie : IncidentEdge (torusGraph width height) p)
    (i : Fin 4) (hi : (torusIncidentLegEquiv p).symm ie = i)
    (a b : Fin (A.bondDim ie.1)) :
    let hD := (bondDim_incident_eq_fourLegBondDim A hU p ie).trans
      (congrArg (torusFourLegBondDim A) hi)
    (torusIncidentKernelOfFourLeg A hU Q p ie : Matrix _ _ ℂ) a b =
      (Q i : Matrix _ _ ℂ) (Fin.cast hD a) (Fin.cast hD b) := by
  let j := (torusIncidentLegEquiv p).symm ie
  let h0 := bondDim_incident_eq_fourLegBondDim A hU p ie
  let hD := h0.trans (congrArg (torusFourLegBondDim A) hi)
  let u : Fin (torusFourLegBondDim A j) := Fin.cast h0 a
  let v : Fin (torusFourLegBondDim A j) := Fin.cast h0 b
  have hu : u ≍ Fin.cast hD a :=
    (Fin.heq_ext_iff (congrArg (torusFourLegBondDim A) hi)).mpr rfl
  have hv : v ≍ Fin.cast hD b :=
    (Fin.heq_ext_iff (congrArg (torusFourLegBondDim A) hi)).mpr rfl
  change (Q j : Matrix (Fin (torusFourLegBondDim A j))
      (Fin (torusFourLegBondDim A j)) ℂ) u v =
    (Q i : Matrix (Fin (torusFourLegBondDim A i))
      (Fin (torusFourLegBondDim A i)) ℂ) (Fin.cast hD a) (Fin.cast hD b)
  exact Matrix.entry_eq_of_heq
    (fun k : Fin 4 => (Q k : Matrix (Fin (torusFourLegBondDim A k))
      (Fin (torusFourLegBondDim A k)) ℂ)) hi hu hv

/-- The native tail carries the outgoing leg of its direction.
Supporting geometry for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusOutgoingTailIncident_directionPortLegIndex
    (r : Bool) (p : TorusVertex width height) :
    (torusIncidentLegEquiv p).symm (torusOutgoingTailIncident (r, p)) =
      torusDirectionPortLegIndex r true := by
  cases r
  · have h : torusOutgoingTailIncident (false, p) = torusRightLeg p := by
      apply Subtype.ext
      exact torusOutgoingEdgeEquiv_horizontal p
    exact (congrArg (torusIncidentLegEquiv p).symm h).trans
      ((torusIncidentLegEquiv p).symm_apply_apply 1)
  · have h : torusOutgoingTailIncident (true, p) = torusDownLeg p := by
      apply Subtype.ext
      exact torusOutgoingEdgeEquiv_vertical p
    exact (congrArg (torusIncidentLegEquiv p).symm h).trans
      ((torusIncidentLegEquiv p).symm_apply_apply 2)

/-- The native head carries the incoming leg of its direction.
Supporting geometry for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusOutgoingHeadIncident_directionPortLegIndex
    (r : Bool) (p : TorusVertex width height) :
    (torusIncidentLegEquiv (torusOutgoingNeighbor r p)).symm
        (torusOutgoingHeadIncident (r, p)) = torusDirectionPortLegIndex r false := by
  cases r
  · let q := torusOutgoingNeighbor false p
    have h : torusOutgoingHeadIncident (false, p) = torusLeftLeg q := by
      apply Subtype.ext
      change torusOutgoingEdgeEquiv (false, p) = torusLeftEdge q
      simp [q, torusOutgoingNeighbor, torusLeftEdge, translateEquiv_apply]
    exact (congrArg (torusIncidentLegEquiv q).symm h).trans
      ((torusIncidentLegEquiv q).symm_apply_apply 3)
  · let q := torusOutgoingNeighbor true p
    have h : torusOutgoingHeadIncident (true, p) = torusTopLeg q := by
      apply Subtype.ext
      change torusOutgoingEdgeEquiv (true, p) = torusUpEdge q
      simp [q, torusOutgoingNeighbor, torusDownEdge, translateEquiv_apply, sub_eq_add_neg]
    exact (congrArg (torusIncidentLegEquiv q).symm h).trans
      ((torusIncidentLegEquiv q).symm_apply_apply 0)

/-- The actual native factor of a common leg transformation is the transpose
of its outgoing port matrix times its incoming port matrix.
Supporting absorption identity for arXiv:1804.04964, lines 1891–1894. -/
theorem torusNativeIndependentEdgeKernel_fourLeg
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (Q : (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ)
    (r : Bool) (p : TorusVertex width height) :
    torusNativeIndependentEdgeKernel A hU (torusIncidentKernelOfFourLeg A hU Q) (r, p) =
      glTranspose (torusFourLegKernelOnPort A Q r true) *
        torusFourLegKernelOnPort A Q r false := by
  classical
  apply Units.ext
  apply Matrix.ext
  intro a b
  let z : Bool × TorusVertex width height := (r, p)
  let hD := bondDim_torusOutgoingEdgeEquiv A hU z
  let K := torusIncidentKernelOfFourLeg A hU Q
  let T : Matrix (Fin (A.bondDim (torusOutgoingEdgeEquiv z)))
      (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ :=
    ((show GL (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ from
      K p (torusOutgoingTailIncident z)) : Matrix _ _ ℂ)
  let H : Matrix (Fin (A.bondDim (torusOutgoingEdgeEquiv z)))
      (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ :=
    ((show GL (Fin (A.bondDim (torusOutgoingEdgeEquiv z))) ℂ from
      K (torusOutgoingNeighbor r p) (torusOutgoingHeadIncident z)) : Matrix _ _ ℂ)
  let n := if r then A.bondDim (torusUpEdge 0) else A.bondDim (torusRightEdge 0)
  let U : Matrix (Fin n) (Fin n) ℂ := ↑(torusFourLegKernelOnPort A Q r true)
  let W : Matrix (Fin n) (Fin n) ℂ := ↑(torusFourLegKernelOnPort A Q r false)
  have ht (j : Fin (A.bondDim (torusOutgoingEdgeEquiv z))) :
      T j (Fin.cast hD.symm a) = U (Fin.cast hD j) a := by
    let i := torusDirectionPortLegIndex r true
    have h := torusIncidentKernelOfFourLeg_apply_of_index A hU Q p
      (torusOutgoingTailIncident z) i
      (torusOutgoingTailIncident_directionPortLegIndex r p) j (Fin.cast hD.symm a)
    have hp := torusFourLegKernelOnPort_apply A Q r true (Fin.cast hD j) a
    refine h.trans (Eq.trans ?_ hp.symm)
    exact congrArg₂
      (fun u v : Fin (torusFourLegBondDim A i) =>
        (Q i : Matrix (Fin (torusFourLegBondDim A i))
          (Fin (torusFourLegBondDim A i)) ℂ) u v)
      (Fin.ext rfl) (Fin.ext rfl)
  have hh (j : Fin (A.bondDim (torusOutgoingEdgeEquiv z))) :
      H j (Fin.cast hD.symm b) = W (Fin.cast hD j) b := by
    let i := torusDirectionPortLegIndex r false
    have h := torusIncidentKernelOfFourLeg_apply_of_index A hU Q
      (torusOutgoingNeighbor r p) (torusOutgoingHeadIncident z) i
      (torusOutgoingHeadIncident_directionPortLegIndex r p) j (Fin.cast hD.symm b)
    have hp := torusFourLegKernelOnPort_apply A Q r false (Fin.cast hD j) b
    refine h.trans (Eq.trans ?_ hp.symm)
    exact congrArg₂
      (fun u v : Fin (torusFourLegBondDim A i) =>
        (Q i : Matrix (Fin (torusFourLegBondDim A i))
          (Fin (torusFourLegBondDim A i)) ℂ) u v)
      (Fin.ext rfl) (Fin.ext rfl)
  calc
    _ = ∑ j : Fin (A.bondDim (torusOutgoingEdgeEquiv z)),
          T j (Fin.cast hD.symm a) * H j (Fin.cast hD.symm b) :=
      torusNativeIndependentEdgeKernel_apply A hU K z a b
    _ = ∑ j : Fin (A.bondDim (torusOutgoingEdgeEquiv z)),
          U (Fin.cast hD j) a * W (Fin.cast hD j) b := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact congrArg₂ (fun u v : ℂ => u * v) (ht j) (hh j)
    _ = ∑ k, U k a * W k b :=
      (finCongr hD).sum_comp (fun k => U k a * W k b)
    _ = _ := rfl

end TNLean.PEPS

namespace TNLean.PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Uniform local scaling of the actual repeated tensor has degree equal
to the number of torus vertices. Supporting normalization for
arXiv:1804.04964, lines 1891–1894 and 1899. -/
theorem stateCoeff_torusFourLegTensor_smul
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ)
    (ρ : ℂ) (σ : TorusVertex width height → Fin d) :
    stateCoeff (torusFourLegTensor A hU (fun x => ρ • F x)) σ =
      ρ ^ Fintype.card (TorusVertex width height) *
        stateCoeff (torusFourLegTensor A hU F) σ := by
  classical
  change (∑ η : VirtualConfig A, ∏ p : TorusVertex width height,
      ρ * F ((torusFourLegConfigEquiv A hU p).symm (fun ie => η ie.1)) (σ p)) =
    ρ ^ Fintype.card (TorusVertex width height) *
      ∑ η : VirtualConfig A, ∏ p : TorusVertex width height,
        F ((torusFourLegConfigEquiv A hU p).symm (fun ie => η ie.1)) (σ p)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.mul_sum]

end TNLean.PEPS
