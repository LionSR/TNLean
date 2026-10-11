/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointReducingSectors

/-!
# Four orthogonal corners of the actual joint endpoint support

The first physical row and last physical column split the two-site support
into four orthogonal phase corners. Their selectors act on every virtual
boundary as \(X_x\mapsto P_{b,x}X_xP_{a,x}\), where \(P_{\mathrm{false},x}\)
is the first virtual projection and \(P_{\mathrm{true},x}\) its complement.
The false/false corner is exactly the common canonical endpoint support.

Only the four physical phase summands are separated. Distinct block labels
may overlap within a summand, and all statements concern their joint support.
Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- Select the specified outer row and column phases. False selects the
first phase and true its orthogonal complement. -/
noncomputable def jointMixedOuterCornerProjection
    (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) (p : Bool × Bool) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  (if p.1 then 1 - jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)
    else jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)) *
  (if p.2 then 1 - jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)
    else jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2))

/-- The outer corner selector acts by the product of its two binary
physical phase indicators. -/
theorem jointMixedOuterCornerProjection_apply (p : Bool × Bool)
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2))
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :
    jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ p v σ =
      (if p.1 then 1 - jointMixedRowWeight (σ 0) else jointMixedRowWeight (σ 0)) *
      (if p.2 then 1 - jointMixedColumnWeight (σ 1) else jointMixedColumnWeight (σ 1)) *
        v σ := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;>
    simp [jointMixedOuterCornerProjection, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, PiLp.sub_apply, jointMixedRowSector_apply,
      jointMixedColumnSector_apply] <;> ring

/-- Every outer corner selector is an orthogonal projection. -/
theorem jointMixedOuterCornerProjection_isSymmetricProjection (p : Bool × Bool) :
    (jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ p).IsSymmetricProjection := by
  let R := jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)
  let C := jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)
  have hR : R.IsSymmetricProjection := jointMixedRowSector_isSymmetricProjection 0
  have hC : C.IsSymmetricProjection := jointMixedColumnSector_isSymmetricProjection 1
  have hR' : (1 - R).IsSymmetricProjection :=
    ⟨hR.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hR.isSymmetric⟩
  have hC' : (1 - C).IsSymmetricProjection :=
    ⟨hC.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hC.isSymmetric⟩
  have hRC : Commute R C := jointMixedRowSector_commute_columnSector 0 1
  rcases p with ⟨a, b⟩
  cases a <;> cases b
  · exact hR.mul_of_commute hC hRC
  · exact hR.mul_of_commute hC' ((Commute.one_right R).sub_right hRC)
  · exact hR'.mul_of_commute hC ((Commute.one_left C).sub_left hRC)
  · exact hR'.mul_of_commute hC'
      ((Commute.one_left (1 - C)).sub_left ((Commute.one_right R).sub_right hRC))

/-- The four outer phase selectors sum to the identity on the whole
two-site physical space. -/
theorem sum_jointMixedOuterCornerProjection :
    (∑ p : Bool × Bool, jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ p) = 1 := by
  let R := jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)
  let C := jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  change ((1 - R) * (1 - C) + (1 - R) * C) + (R * (1 - C) + R * C) = 1
  noncomm_ring

/-- Distinct outer phase selectors have zero product, because at least
one physical phase is selected with opposite values. -/
theorem jointMixedOuterCornerProjection_mul_eq_zero
    {p q : Bool × Bool} (hpq : p ≠ q) :
    jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ p *
      jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ q = 0 := by
  ext v σ
  simp only [Module.End.mul_apply, jointMixedOuterCornerProjection_apply,
    LinearMap.zero_apply, PiLp.zero_apply]
  rcases jointMixedRowWeight_eq_zero_or_one (σ 0) with hR | hR <;>
    rcases jointMixedColumnWeight_eq_zero_or_one (σ 1) with hC | hC <;>
    rcases p with ⟨a, b⟩ <;> rcases q with ⟨c, d⟩ <;>
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Each physical outer corner selects the corresponding two virtual
boundary corners, for the actual joint boundary map and any insertion. -/
theorem jointMixedOuterCornerProjection_blockInsertedBoundaryMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (W X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ)
    (p : Bool × Bool) :
    jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ p
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2
        (blockBoundaryEquiv.symm X)) =
      blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2
        (blockBoundaryEquiv.symm fun x =>
          (if p.2 then 1 - bondInterpolationMatrix (D₀ x) (D₁ x) 0
            else bondInterpolationMatrix (D₀ x) (D₁ x) 0) * X x *
          (if p.1 then 1 - bondInterpolationMatrix (D₀ x) (D₁ x) 0
            else bondInterpolationMatrix (D₀ x) (D₁ x) 0)) := by
  let R := jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)
  let C := jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)
  let P := fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0
  let Γ := (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) W 2).toLinearMap.comp
    blockBoundaryEquiv.symm.toLinearMap
  have hR (Y) : R (Γ Y) = Γ (fun x => Y x * P x) :=
    jointMixedRowSector_blockInsertedBoundaryMap A₀ A₁ W Y
  have hC (Y) : C (Γ Y) = Γ (fun x => P x * Y x) :=
    jointMixedColumnSector_blockInsertedBoundaryMap A₀ A₁ W Y
  have hRow (a : Bool) (Y) :
      (if a then 1 - R else R) (Γ Y) = Γ (fun x => Y x * (if a then 1 - P x else P x)) := by
    cases a
    · exact hR Y
    · have hdiff : (fun x => Y x * (1 - P x)) = Y - (fun x => Y x * P x) := by
        funext x
        simp only [Pi.sub_apply, Matrix.mul_sub, Matrix.mul_one]
      change Γ Y - R (Γ Y) = Γ (fun x => Y x * (1 - P x))
      rw [hdiff, map_sub, hR]
  have hColumn (b : Bool) (Y) :
      (if b then 1 - C else C) (Γ Y) = Γ (fun x => (if b then 1 - P x else P x) * Y x) := by
    cases b
    · exact hC Y
    · have hdiff : (fun x => (1 - P x) * Y x) = Y - (fun x => P x * Y x) := by
        funext x
        simp only [Pi.sub_apply, Matrix.sub_mul, Matrix.one_mul]
      change Γ Y - C (Γ Y) = Γ (fun x => (1 - P x) * Y x)
      rw [hdiff, map_sub, hC]
  change (if p.1 then 1 - R else R) ((if p.2 then 1 - C else C) (Γ X)) =
    Γ (fun x => (if p.2 then 1 - P x else P x) * X x *
      (if p.1 then 1 - P x else P x))
  rw [hColumn, hRow]

/-- The selected corner of the actual joint two-site endpoint support. -/
noncomputable def jointMixedEndpointCornerSupport
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (p : Bool × Bool) :
    Submodule ℂ (EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)) :=
  (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.map
      (jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ p)

/-- Every corner lies in the actual full joint support, by its explicit
virtual boundary action. -/
theorem jointMixedEndpointCornerSupport_le
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (p : Bool × Bool) :
    jointMixedEndpointCornerSupport A₀ A₁ p ≤
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
  refine ⟨blockBoundaryEquiv.symm (fun x =>
    (if p.2 then 1 - bondInterpolationMatrix (D₀ x) (D₁ x) 0
      else bondInterpolationMatrix (D₀ x) (D₁ x) 0) * X x *
    (if p.1 then 1 - bondInterpolationMatrix (D₀ x) (D₁ x) 0
      else bondInterpolationMatrix (D₀ x) (D₁ x) 0)), ?_⟩
  exact (jointMixedOuterCornerProjection_blockInsertedBoundaryMap A₀ A₁
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) X p).symm

/-- The actual joint endpoint support is exactly the sum of its four
outer physical phase corners. -/
theorem jointMixedEndpoint_extendedSupport_eq_iSup_corners
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range =
      ⨆ p : Bool × Bool, jointMixedEndpointCornerSupport A₀ A₁ p := by
  apply le_antisymm
  · intro v hv
    have hsum : (∑ p : Bool × Bool,
        jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ p v) = v := by
      simpa only [LinearMap.sum_apply, Module.End.one_apply] using
        LinearMap.congr_fun
          (sum_jointMixedOuterCornerProjection (d₀ := d₀) (d₁ := d₁)
            (D₀ := D₀) (D₁ := D₁)) v
    rw [← hsum]
    apply Submodule.sum_mem
    intro p _
    exact (le_iSup (jointMixedEndpointCornerSupport A₀ A₁) p) ⟨v, hv, rfl⟩
  · exact iSup_le (jointMixedEndpointCornerSupport_le A₀ A₁)

/-- The four physical corners are pairwise orthogonal, irrespective of
overlap between block labels within one corner. -/
theorem jointMixedEndpointCornerSupport_pairwise_isOrtho
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Pairwise fun p q : Bool × Bool =>
      (jointMixedEndpointCornerSupport A₀ A₁ p).IsOrtho
        (jointMixedEndpointCornerSupport A₀ A₁ q) := by
  intro p q hpq
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨u, _, rfl⟩ _ ⟨v, _, rfl⟩
  rw [(jointMixedOuterCornerProjection_isSymmetricProjection p).isSymmetric]
  have hzero : jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ p
      (jointMixedOuterCornerProjection d₀ d₁ D₀ D₁ q v) = 0 :=
    LinearMap.congr_fun (jointMixedOuterCornerProjection_mul_eq_zero hpq) v
  rw [hzero, inner_zero_right]

/-- The false/false phase corner is the full common canonical support of
the embedded first endpoint family. -/
theorem jointMixedEndpointCornerSupport_false_false
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedEndpointCornerSupport A₀ A₁ (false, false) =
      groundSpaceES (toTensorFromBlocks (μ := fun _ => 1)
        (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 := by
  simpa only [jointMixedEndpointCornerSupport, jointMixedOuterCornerProjection,
    Bool.false_eq_true, ite_false, Module.End.mul_eq_comp] using
      jointMixedEndpoint_extendedSupport_outerCorner_eq_groundSpaceES A₀ A₁

end MPSTensor.MPOSymmetry
