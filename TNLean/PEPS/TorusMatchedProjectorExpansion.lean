/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusProjectorExpansion
import TNLean.PEPS.TorusMatchedBondRepresentation

/-!
# Actual projector contractions for independently varying bond representations

A representation is assigned to every oriented horizontal and vertical bond.
Both endpoints use that bond's representation, with inverse transpose at its tail.
Expanding each local averaging projector therefore produces one group variable per
vertex and conjugates each bond operator using that bond's own representation.

These are actual native torus contractions, including periods one and two. Only a
common virtual coordinate alphabet is imposed; the representations may otherwise
vary independently. Distinct bond dimensions remain a separate generalization.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Definition 5.1,
Theorem 5.5, and the projector expansion in Theorem 5.9.
-/

open scoped BigOperators Kronecker Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Independent operators on the top, right, down, and left legs. The right
and down operators are transposed because those legs are outgoing.
Source: SCP10, Definition 5.1 and equation `eq:2d:move-strings`. -/
def torusLegGaugeMatrix (T R B L : Matrix V V ℂ) :
    Matrix (V × V × V × V) (V × V × V × V) ℂ :=
  T ⊗ₖ (R.transpose ⊗ₖ (B.transpose ⊗ₖ L))

omit [Fintype V] [DecidableEq V] in
/-- The four independent leg operators in coordinates. -/
theorem torusLegGaugeMatrix_apply (T R B L : Matrix V V ℂ)
    (c c' : V × V × V × V) :
    torusLegGaugeMatrix T R B L c c' =
      T c.1 c'.1 * R c'.2.1 c.2.1 * B c'.2.2.1 c.2.2.1 * L c.2.2.2 c'.2.2.2 := by
  simp [torusLegGaugeMatrix, mul_assoc]

/-- Absorb four independent operators into a site tensor. -/
def torusLegDress (T R B L : Matrix V V ℂ) (A : (V × V × V × V) → ℂ) :
    (V × V × V × V) → ℂ :=
  Matrix.vecMul A (torusLegGaugeMatrix T R B L)

omit [DecidableEq V] in
/-- Move independently chosen operators between bond ends and site tensors.
Source: SCP10, equation `eq:2d:move-strings`, generalized to distinct operators
on each of the four legs before imposing representation matching. -/
theorem torusBondNetwork_legGauge (A : TorusVertex width height → (V × V × V × V) → ℂ)
    (Oh Ov T R B L : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork A (fun v => L (v.1 + 1, v.2) * Oh v * R v)
        (fun v => T v * Ov v * B (v.1, v.2 + 1)) =
      torusBondNetwork (fun v => torusLegDress (T v) (R v) (B v) (L v) (A v)) Oh Ov := by
  -- The site arguments read from the bond ends.
  set args : (TorusVertex width height → V × V × V × V) →
      TorusVertex width height → V × V × V × V :=
    fun β v => ((β v).2.2.2, (β v).1, (β (v.1, v.2 - 1)).2.2.1, (β (v.1 - 1, v.2)).2.1)
    with hargs
  let φ : (TorusVertex width height → V × V × V × V) ≃
      (TorusVertex width height → V × V × V × V) :=
    { toFun := args
      invFun := fun C v => ((C v).2.1, (C (v.1 + 1, v.2)).2.2.2, (C (v.1, v.2 + 1)).2.2.1,
        (C v).1)
      left_inv := fun β => funext fun v => by simp [hargs]
      right_inv := fun C => funext fun v => by simp [hargs] }
  -- Expanding the products of matrices on the bonds.
  have hL : ∀ β : TorusVertex width height → V × V × V × V,
      (∏ v, (L (v.1 + 1, v.2) * Oh v * R v) (β v).2.1 (β v).1 *
          (T v * Ov v * B (v.1, v.2 + 1)) (β v).2.2.2 (β v).2.2.1) =
        ∑ γ : TorusVertex width height → V × V × V × V, ∏ v,
          (L (v.1 + 1, v.2) (β v).2.1 (γ v).2.1 * Oh v (γ v).2.1 (γ v).1 * R v (γ v).1 (β v).1 *
            (T v (β v).2.2.2 (γ v).2.2.2 * Ov v (γ v).2.2.2 (γ v).2.2.1 *
              B (v.1, v.2 + 1) (γ v).2.2.1 (β v).2.2.1)) := by
    intro β
    refine (Finset.prod_congr rfl fun v _ => mul_comm _ _).trans ?_
    refine (Finset.prod_congr rfl fun v _ => ?_).trans
      (Fintype.prod_sum fun v (γ : V × V × V × V) =>
      L (v.1 + 1, v.2) (β v).2.1 γ.2.1 * Oh v γ.2.1 γ.1 * R v γ.1 (β v).1 *
        (T v (β v).2.2.2 γ.2.2.2 * Ov v γ.2.2.2 γ.2.2.1 * B (v.1, v.2 + 1) γ.2.2.1 (β v).2.2.1))
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  -- Expanding the dressed site tensors.
  have hR : ∀ β : TorusVertex width height → V × V × V × V,
      (∏ v, torusLegDress (T v) (R v) (B v) (L v) (A v) (args β v)) =
        ∑ C : TorusVertex width height → V × V × V × V,
          ∏ v, A v (C v) * torusLegGaugeMatrix (T v) (R v) (B v) (L v) (C v) (args β v) := by
    intro β
    exact Fintype.prod_sum fun v (c : V × V × V × V) =>
      A v c * torusLegGaugeMatrix (T v) (R v) (B v) (L v) c (args β v)
  -- Matching the terms.
  have key : ∀ β γ : TorusVertex width height → V × V × V × V,
      (∏ v, (L (v.1 + 1, v.2) (β v).2.1 (γ v).2.1 * Oh v (γ v).2.1 (γ v).1 *
          R v (γ v).1 (β v).1 * (T v (β v).2.2.2 (γ v).2.2.2 * Ov v (γ v).2.2.2 (γ v).2.2.1 *
            B (v.1, v.2 + 1) (γ v).2.2.1 (β v).2.2.1))) * ∏ v, A v (args β v) =
        (∏ v, Oh v (γ v).2.1 (γ v).1 * Ov v (γ v).2.2.2 (γ v).2.2.1) *
          ∏ v, A v (args β v) *
            torusLegGaugeMatrix (T v) (R v) (B v) (L v) (args β v) (args γ v) := by
    intro β γ
    have hP := prod_torus_sub_fst (width := width) (height := height)
      fun u u' => L u (β u').2.1 (γ u').2.1
    have hQ := prod_torus_sub_snd (width := width) (height := height)
      fun u u' => B u (γ u').2.2.1 (β u').2.2.1
    simp only [hargs, torusLegGaugeMatrix_apply, Finset.prod_mul_distrib, hP, hQ]
    ring
  unfold torusBondNetwork
  simp only [hL, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  change _ = _ * ∏ v, torusLegDress (T v) (R v) (B v) (L v) (A v) (args γ v)
  rw [hR, Finset.mul_sum]
  exact Fintype.sum_equiv φ _ _ fun β => key β γ

variable {G : Type*} [Group G]

omit [NeZero width] [NeZero height] in
/-- The matched four-leg representation acts by its actual matrix. -/
theorem torusMatchedLegRep_apply
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (v : TorusVertex width height) (g : G) (x : (V × V × V × V) → ℂ) :
    torusMatchedLegRep Uh Uv v g x = Matrix.mulVec (torusMatchedLegMatrix Uh Uv v g) x :=
  Matrix.toLinAlgEquiv'_apply _ _

/-- A basis row absorbs the four independent leg operators by selecting their row. -/
theorem torusLegDress_single (T R B L : Matrix V V ℂ) (s : V × V × V × V) :
    torusLegDress T R B L (Pi.single s 1) = torusLegGaugeMatrix T R B L s := by
  ext c
  simp [torusLegDress, Matrix.vecMul]

omit [NeZero width] [NeZero height] in
/-- Local virtual invariance absorbs the matched action even when the four bond
representations differ. Source: SCP10, Definition 5.1(i). -/
theorem vecMul_torusMatchedLegMatrix_of_comp_eq {Phys : Type*}
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (v : TorusVertex width height) (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ g, siteMap a ∘ₗ torusMatchedLegRep Uh Uv v g = siteMap a)
    (g : G) (s : Phys) :
    Matrix.vecMul (fun c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 s)
        (torusMatchedLegMatrix Uh Uv v g) =
      fun c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 s := by
  funext c₀
  have h := congrFun (LinearMap.congr_fun (ha g) (Pi.single c₀ 1)) s
  simpa [siteMap_apply, torusMatchedLegRep_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply, Matrix.vecMul, Finset.mul_sum] using h

/-- A vertex-dependent matched group action leaves an invariant network unchanged.
The same representation is used at both ends of each individual oriented bond.
Source: SCP10, equation `eq:2d:move-strings`. -/
theorem torusBondNetwork_matchedVertexGauge {Phys : Type*}
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusMatchedLegRep Uh Uv v g = siteMap (a v))
    (σ : TorusVertex width height → Phys) (q : TorusVertex width height → G)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ Uh v (q (v.1 + 1, v.2)) * Oh v * Uh v ((q v)⁻¹))
        (fun v ↦ Uv v (q v) * Ov v * Uv v ((q (v.1, v.2 + 1))⁻¹)) =
      torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov := by
  have h := torusBondNetwork_legGauge
    (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov
    (fun v ↦ Uv v (q v)) (fun v ↦ Uh v ((q v)⁻¹))
    (fun v ↦ Uv (v.1, v.2 - 1) ((q v)⁻¹))
    (fun v ↦ Uh (v.1 - 1, v.2) (q v))
  simp only [add_sub_cancel_right] at h
  rw [h]
  congr 1
  funext v
  exact vecMul_torusMatchedLegMatrix_of_comp_eq Uh Uv v (a v) (ha v) (q v) (σ v)

variable [Fintype G]

attribute [local instance] Representation.invertibleFintypeCardComplex

omit [NeZero width] [NeZero height] in
/-- The matched averaging site's coefficients are the average of the actual
four-leg matrices. Source: SCP10, Definition 5.1 and Theorem 5.9. -/
theorem representationAveragingSite_torusMatchedLegRep_apply
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (v : TorusVertex width height) (t r b l : V) (s : V × V × V × V) :
    representationAveragingSite (torusMatchedLegRep Uh Uv v) t r b l s =
      (Fintype.card G : ℂ)⁻¹ * ∑ q : G, torusMatchedLegMatrix Uh Uv v q s (t, r, b, l) := by
  rw [representationAveragingSite, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, torusMatchedLegRep_apply,
    Matrix.mulVec_single_one, Matrix.col_apply, invOf_eq_inv, smul_eq_mul]

/-- The actual matched-projector torus contraction expands over one group label
per vertex. The bond operator is multiplied at its head and tail using that
bond's own independently chosen representation. No unitarity, semi-regularity,
or region Gram assumption is required for this identity.
Source: SCP10, the projector contraction in Theorem 5.9, lines 1582–1621. -/
theorem torusBondNetwork_representationAveragingSite
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (σ : TorusVertex width height → V × V × V × V)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork
        (fun v c ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
          c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height) *
        ∑ q : TorusVertex width height → G, ∏ v,
          (Uh v (q (v.1 + 1, v.2)) * Oh v * Uh v ((q v)⁻¹))
            (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
          (Uv v (q v) * Ov v * Uv v ((q (v.1, v.2 + 1))⁻¹))
            (σ v).1 (σ (v.1, v.2 + 1)).2.2.1 := by
  simp only [representationAveragingSite_torusMatchedLegRep_apply, Prod.eta]
  rw [torusBondNetwork_mul, torusBondNetwork_sum]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 1
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have h := torusBondNetwork_legGauge (fun v ↦ Pi.single (σ v) 1) Oh Ov
    (fun v ↦ Uv v (q v)) (fun v ↦ Uh v ((q v)⁻¹))
    (fun v ↦ Uv (v.1, v.2 - 1) ((q v)⁻¹))
    (fun v ↦ Uh (v.1 - 1, v.2) (q v))
  simp only [add_sub_cancel_right, torusLegDress_single] at h
  exact h.symm.trans (torusBondNetwork_single σ _ _)

end TNLean.PEPS
