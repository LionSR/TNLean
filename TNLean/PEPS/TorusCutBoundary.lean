/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusOperatorString

/-!
# Arbitrary correlated boundary tensors for a cut torus

Cutting one horizontal seam and one vertical seam leaves two independent
endpoints on every cut bond. A boundary condition is an arbitrary function of
all these endpoints, not a product of independently chosen bond matrices.
The cut map contracts the uncut bonds with identity matrices and leaves the
cut endpoints available to this single boundary tensor.

On the two-by-two torus this gives exactly the four boundary spaces in SCP10,
Theorem 5.5, `eq:2d:closure-intersection`, lines 1421–1473. The network retains
all eight bonds, including the two distinct bonds joining each neighboring
pair of sites. It does not use the simple graph of a two-by-two torus.
These definitions allow distinct site tensors at every vertex and do not
assume injectivity or any symmetry. The reverse closure inclusion is not
asserted in this file.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V Phys : Type*} [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Indices of all cut endpoints: one horizontal tail/head pair per row and
one vertical tail/head pair per column. SCP10, Theorem 5.5. -/
abbrev TorusCutBoundaryConfig (width height : ℕ) (V : Type*) :=
  (ZMod height → V × V) × (ZMod width → V × V)

/-- Restrict a full independent-endpoint configuration to the seams with head
column `c` and upper row `r`. The two ends of each cut bond remain distinct. -/
def torusCutBoundaryRestriction (c : ZMod width) (r : ZMod height)
    (β : TorusVertex width height → V × V × V × V) :
    TorusCutBoundaryConfig width height V :=
  (fun y ↦ ((β (c - 1, y)).1, (β (c - 1, y)).2.1),
    fun x ↦ ((β (x, r - 1)).2.2.1, (β (x, r - 1)).2.2.2))

/-- Identity contractions on the uncut bonds; the cut bonds have weight one. -/
def torusCutInteriorWeight (c : ZMod width) (r : ZMod height)
    (β : TorusVertex width height → V × V × V × V) : ℂ :=
  ∏ v, (if v.1 + 1 = c then 1 else (1 : Matrix V V ℂ) (β v).2.1 (β v).1) *
    (if v.2 + 1 = r then 1 else (1 : Matrix V V ℂ) (β v).2.2.2 (β v).2.2.1)

/-- The coefficient of a cut-torus contraction with one arbitrary correlated
boundary tensor. For width and height two, varying `c,r` gives the four
boundary conditions in SCP10, Theorem 5.5. -/
def torusCutCoeff (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ)
    (σ : TorusVertex width height → Phys) : ℂ :=
  ∑ β : TorusVertex width height → V × V × V × V,
    (M (torusCutBoundaryRestriction c r β) * torusCutInteriorWeight c r β) *
      ∏ v, a v (β v).2.2.2 (β v).1 (β (v.1, v.2 - 1)).2.2.1
        (β (v.1 - 1, v.2)).2.1 (σ v)

/-- The linear map from arbitrary boundary tensors to physical vectors.
Its domain includes all correlations among the open endpoints. -/
def torusCutMap (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height) :
    (TorusCutBoundaryConfig width height V → ℂ) →ₗ[ℂ]
      ((TorusVertex width height → Phys) → ℂ) where
  toFun := torusCutCoeff a c r
  map_add' M N := by
    funext σ
    simp [torusCutCoeff, add_mul, Finset.sum_add_distrib]
  map_smul' z M := by
    funext σ
    simp [torusCutCoeff, mul_assoc, Finset.mul_sum]

@[simp]
theorem torusCutMap_apply
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ)
    (σ : TorusVertex width height → Phys) :
    torusCutMap a c r M σ = torusCutCoeff a c r M σ := rfl

/-- One of the boundary spaces whose intersection occurs in SCP10, Theorem 5.5. -/
def torusCutSpace (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height) :
    Submodule ℂ ((TorusVertex width height → Phys) → ℂ) :=
  LinearMap.range (torusCutMap a c r)

/-- Membership means equality to an actual cut contraction with a single
arbitrary boundary tensor, coefficient by coefficient. -/
theorem mem_torusCutSpace_iff
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (ψ : (TorusVertex width height → Phys) → ℂ) :
    ψ ∈ torusCutSpace a c r ↔ ∃ M, ∀ σ, torusCutCoeff a c r M σ = ψ σ := by
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨M, fun _ ↦ rfl⟩
  · rintro ⟨M, hM⟩
    exact ⟨M, funext hM⟩

/-- The intersection of the four genuinely different cuts of the two-by-two
bond network. Each cut opens four of its eight bonds and hence eight endpoints. -/
def fourTorusCutSpace (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ) :
    Submodule ℂ ((TorusVertex 2 2 → Phys) → ℂ) :=
  ⨅ c : ZMod 2, ⨅ r : ZMod 2, torusCutSpace a c r

@[simp]
theorem mem_fourTorusCutSpace_iff
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ψ : (TorusVertex 2 2 → Phys) → ℂ) :
    ψ ∈ fourTorusCutSpace a ↔ ∀ c r, ∃ M, ∀ σ, torusCutCoeff a c r M σ = ψ σ := by
  simp [fourTorusCutSpace, mem_torusCutSpace_iff]

/-- A product of bond matrices is one admissible boundary tensor. This is only
an embedding of factorized boundaries into the full boundary domain. -/
def torusCutBondBoundary (c : ZMod width) (r : ZMod height)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ)
    (η : TorusCutBoundaryConfig width height V) : ℂ :=
  (∏ y, Oh (c - 1, y) (η.1 y).2 (η.1 y).1) *
    ∏ x, Ov (x, r - 1) (η.2 x).2 (η.2 x).1

omit [Fintype V] [DecidableEq V] in
/-- Restricting the bond-end variables gives exactly the product of matrix
entries on the selected seams. -/
theorem torusCutBondBoundary_restriction (c : ZMod width) (r : ZMod height)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ)
    (β : TorusVertex width height → V × V × V × V) :
    torusCutBondBoundary c r Oh Ov (torusCutBoundaryRestriction c r β) =
      ∏ v, (if v.1 + 1 = c then Oh v (β v).2.1 (β v).1 else 1) *
        (if v.2 + 1 = r then Ov v (β v).2.2.2 (β v).2.2.1 else 1) := by
  unfold torusCutBondBoundary torusCutBoundaryRestriction
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp [← eq_sub_iff_add_eq]
  · rw [Fintype.prod_prod_type]
    simp [← eq_sub_iff_add_eq]

/-- Closing the cut with a product boundary inserts its matrices precisely on
the four cut bonds. This identity holds on two-by-two tori without collapsing
parallel bonds and for arbitrary site-dependent tensors. -/
theorem torusCutCoeff_bondBoundary
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ)
    (σ : TorusVertex width height → Phys) :
    torusCutCoeff a c r (torusCutBondBoundary c r Oh Ov) σ =
      torusBondNetwork (fun v t ↦ a v t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
        (fun v ↦ if v.1 + 1 = c then Oh v else 1)
        (fun v ↦ if v.2 + 1 = r then Ov v else 1) := by
  unfold torusCutCoeff torusBondNetwork
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  congr 1
  rw [torusCutBondBoundary_restriction, torusCutInteriorWeight,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  split_ifs <;> simp_all [mul_comm]

/-- The cut map is the linear combination of its fixed-boundary coefficient
vectors with the actual boundary coefficients as weights. -/
theorem torusCutMap_eq_sum_single
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ) :
    torusCutMap a c r M = ∑ η, M η • torusCutMap a c r (Pi.single η 1) := by
  classical
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext η
  simp [Pi.single_apply]

/-- Each cut space is spanned by the contractions with fixed endpoint values;
this is a coefficient characterization of its full correlated-boundary range. -/
theorem torusCutSpace_eq_span_single
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height) :
    torusCutSpace a c r = Submodule.span ℂ
      (Set.range fun η ↦ torusCutMap a c r (Pi.single η 1)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    rw [torusCutMap_eq_sum_single]
    exact Submodule.sum_mem _ fun η _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self η))
  · exact Submodule.span_le.mpr (by rintro _ ⟨η, rfl⟩; exact ⟨Pi.single η 1, rfl⟩)

omit [DecidableEq V] in
/-- A two-by-two cut really has eight independent virtual endpoint indices. -/
theorem card_torusCutBoundaryConfig_two :
    Fintype.card (TorusCutBoundaryConfig 2 2 V) = Fintype.card V ^ 8 := by
  simp only [TorusCutBoundaryConfig, Fintype.card_prod, Fintype.card_fun, ZMod.card]
  ring

end TNLean.PEPS
