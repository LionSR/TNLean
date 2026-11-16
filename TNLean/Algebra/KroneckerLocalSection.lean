/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TNLean.Algebra.NearestKronecker

/-!
# A local section for the action of local unitaries

The unitary part `Q(X) = X (X† X)^{-1/2}` of an invertible complex matrix is
continuous, commutes with left multiplication by unitaries, fixes unitaries and
sends a Kronecker product `A ⊗ B` of invertible matrices to `Q(A) ⊗ Q(B)`.

Fix a unitary `u₀` on a bipartite space. For `u` near the orbit of `u₀` under the
local unitaries `x ⊗ y`, the gauge `g(u) = Q(N(u u₀†))`, built from the nearest
Kronecker product `N` of `TNLean/Algebra/NearestKronecker.lean`, is a product of
local unitaries, and `σ(u) = g(u)† u` is a continuous map on an open set
containing the orbit, invariant under the local unitaries, with `σ(u)` in the
orbit of `u`.

This is step 3 of the cross-section construction that replaces the slice theorem
of Montgomery and Yang in arXiv:1703.09188, proof of Corollary `coruvSF`,
lines 942--947; see `docs/paper-gaps/mpu_standard_form_path_cross_section.tex`.

## Main declarations

* `Matrix.unitaryPart`: the unitary part `Q(X)` of a matrix.
* `Matrix.continuousOn_unitaryPart`, `Matrix.unitaryPart_mem_unitaryGroup`,
  `Matrix.unitaryPart_unitary_mul`, `Matrix.unitaryPart_kronecker`.
* `Matrix.localSection`: the local section `σ`, defined on
  `Matrix.localSectionDomain`.
* `Matrix.continuousOn_localSection`, `Matrix.localSection_kronecker_mul`,
  `Matrix.exists_localSection_eq_kronecker_mul`,
  `Matrix.kronecker_mul_mem_localSectionDomain`.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker

namespace Matrix

/-! ### The unitary part of a matrix -/

section UnitaryPart

variable {p : Type*} [Fintype p] [DecidableEq p]

/-- The inverse square root `(X† X)^{-1/2}` of the Gram matrix, by the real
continuous functional calculus.

Source: the factor `(N†N)^{-1/2}` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def invSqrtGram (X : Matrix p p ℂ) : Matrix p p ℂ :=
  cfc (fun t : ℝ ↦ (Real.sqrt t)⁻¹) (star X * X)

/-- The unitary part `Q(X) = X (X† X)^{-1/2}` of a matrix.

Source: the map `Q` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def unitaryPart (X : Matrix p p ℂ) : Matrix p p ℂ :=
  X * invSqrtGram X

private theorem spectrum_star_mul_self_pos {X : Matrix p p ℂ} (hX : IsUnit X) {t : ℝ}
    (ht : t ∈ spectrum ℝ (star X * X)) : 0 < t :=
  (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp
    ((hX.star.mul hX).isStrictlyPositive (star_mul_self_nonneg X))).2 t ht

private theorem continuousOn_inv_sqrt :
    ContinuousOn (fun t : ℝ ↦ (Real.sqrt t)⁻¹) (Set.Ioi 0) :=
  Real.continuous_sqrt.continuousOn.inv₀ fun _ ht ↦ (Real.sqrt_pos.mpr ht).ne'

theorem isSelfAdjoint_invSqrtGram (X : Matrix p p ℂ) : IsSelfAdjoint (invSqrtGram X) :=
  cfc_predicate _ _

private theorem invSqrtGram_mul_star_mul_self_mul {X : Matrix p p ℂ} (hX : IsUnit X) :
    invSqrtGram X * (star X * X) * invSqrtGram X = 1 := by
  have hG : IsSelfAdjoint (star X * X) := IsSelfAdjoint.star_mul_self X
  have hc := continuousOn_inv_sqrt.mono fun t (ht : t ∈ spectrum ℝ (star X * X)) ↦
    spectrum_star_mul_self_pos hX ht
  rw [invSqrtGram]
  nth_rw 2 [← cfc_id' ℝ (star X * X) hG]
  rw [← cfc_mul (fun t : ℝ ↦ (Real.sqrt t)⁻¹) (fun t : ℝ ↦ t) _ hc continuousOn_id,
    ← cfc_mul (fun t : ℝ ↦ (Real.sqrt t)⁻¹ * t) (fun t : ℝ ↦ (Real.sqrt t)⁻¹) _
      (hc.mul continuousOn_id) hc,
    ← cfc_one ℝ (star X * X) hG]
  refine cfc_congr fun t ht ↦ ?_
  have h0 := spectrum_star_mul_self_pos hX ht
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt h0.le
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
  rw [Pi.one_apply]
  field_simp
  rw [Real.sq_sqrt h0.le]

/-- The unitary part of an invertible matrix is unitary. -/
theorem unitaryPart_mem_unitaryGroup {X : Matrix p p ℂ} (hX : IsUnit X) :
    unitaryPart X ∈ unitaryGroup p ℂ := by
  have hs : star (unitaryPart X) * unitaryPart X = 1 := by
    rw [unitaryPart, star_mul, (isSelfAdjoint_invSqrtGram X).star_eq, Matrix.mul_assoc,
      ← Matrix.mul_assoc (star X), ← Matrix.mul_assoc]
    exact invSqrtGram_mul_star_mul_self_mul hX
  exact (Matrix.mem_unitaryGroup_iff').mpr hs

/-- The unitary part is continuous on the invertible matrices. -/
theorem continuousOn_unitaryPart :
    ContinuousOn (unitaryPart : Matrix p p ℂ → Matrix p p ℂ) {X | IsUnit X} := by
  have hs : Set.Ioi (0 : ℝ) ∈ nhdsSet (⋃ X ∈ {X : Matrix p p ℂ | IsUnit X},
      spectrum ℝ (star X * X)) := by
    rw [isOpen_Ioi.mem_nhdsSet]
    simp only [Set.iUnion_subset_iff]
    exact fun X hX t ht ↦ spectrum_star_mul_self_pos hX ht
  have hinv : ContinuousOn invSqrtGram {X : Matrix p p ℂ | IsUnit X} :=
    ContinuousOn.cfc_of_mem_nhdsSet _ hs (by fun_prop)
      (fun X _ ↦ IsSelfAdjoint.star_mul_self X) continuousOn_inv_sqrt
  exact continuousOn_id.mul hinv

/-- **Equivariance of the unitary part.** For a unitary `U`, `Q(U X) = U Q(X)`. -/
theorem unitaryPart_unitary_mul {U : Matrix p p ℂ} (hU : U ∈ unitaryGroup p ℂ)
    (X : Matrix p p ℂ) : unitaryPart (U * X) = U * unitaryPart X := by
  have : star (U * X) * (U * X) = star X * X := by
    rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star U), Unitary.star_mul_self_of_mem hU,
      Matrix.one_mul]
  rw [unitaryPart, unitaryPart, invSqrtGram, invSqrtGram, this, Matrix.mul_assoc]

/-- A unitary matrix is its own unitary part. -/
theorem unitaryPart_of_mem_unitaryGroup {U : Matrix p p ℂ} (hU : U ∈ unitaryGroup p ℂ) :
    unitaryPart U = U := by
  rcases isEmpty_or_nonempty p with hp | hp
  · exact Subsingleton.elim _ _
  rw [unitaryPart, invSqrtGram, Unitary.star_mul_self_of_mem hU, cfc_congr (g := fun _ ↦ 1)
    (fun t ht ↦ ?_), cfc_const_one ℝ (1 : Matrix p p ℂ), Matrix.mul_one]
  rw [spectrum.one_eq] at ht
  simp [Set.mem_singleton_iff.mp ht]

/-- The inverse square root of the Gram matrix is the square root of the inverse
Gram matrix. -/
private theorem invSqrtGram_eq_sqrt {X : Matrix p p ℂ} (hX : IsUnit X) :
    invSqrtGram X = CFC.sqrt (star X * X)⁻¹ := by
  have hG : IsSelfAdjoint (star X * X) := IsSelfAdjoint.star_mul_self X
  have hc := continuousOn_inv_sqrt.mono fun t (ht : t ∈ spectrum ℝ (star X * X)) ↦
    spectrum_star_mul_self_pos hX ht
  have hpos : (star X * X).PosDef :=
    IsStrictlyPositive.posDef ((hX.star.mul hX).isStrictlyPositive (star_mul_self_nonneg X))
  have hnn : 0 ≤ invSqrtGram X := cfc_nonneg fun t ht ↦
    inv_nonneg.mpr (Real.sqrt_nonneg t)
  symm
  rw [CFC.sqrt_eq_iff _ _ hpos.inv.posSemidef.nonneg hnn, invSqrtGram,
    ← cfc_mul _ _ _ hc hc]
  obtain ⟨u, hu⟩ := hpos.isUnit
  rw [← hu, ← Matrix.coe_units_inv, ← cfc_inv_id (R := ℝ) u (hu ▸ hG)]
  refine cfc_congr fun t ht ↦ ?_
  have h0 := spectrum_star_mul_self_pos hX (hu ▸ ht)
  rw [← mul_inv, Real.mul_self_sqrt h0.le]

/-- **The unitary part of a Kronecker product.** For invertible `A` and `B`,
`Q(A ⊗ B) = Q(A) ⊗ Q(B)`. -/
theorem unitaryPart_kronecker {q : Type*} [Fintype q] [DecidableEq q]
    {A : Matrix p p ℂ} {B : Matrix q q ℂ} (hA : IsUnit A) (hB : IsUnit B) :
    unitaryPart (A ⊗ₖ B) = unitaryPart A ⊗ₖ unitaryPart B := by
  have hAB : IsUnit (A ⊗ₖ B) := by
    rw [isUnit_iff_isUnit_det, det_kronecker]
    exact ((isUnit_iff_isUnit_det A).mp hA).pow _ |>.mul (((isUnit_iff_isUnit_det B).mp hB).pow _)
  have hpA : (star A * A).PosDef :=
    IsStrictlyPositive.posDef ((hA.star.mul hA).isStrictlyPositive (star_mul_self_nonneg A))
  have hpB : (star B * B).PosDef :=
    IsStrictlyPositive.posDef ((hB.star.mul hB).isStrictlyPositive (star_mul_self_nonneg B))
  rw [unitaryPart, unitaryPart, unitaryPart, mul_kronecker_mul, invSqrtGram_eq_sqrt hAB,
    invSqrtGram_eq_sqrt hA, invSqrtGram_eq_sqrt hB]
  congr 1
  have hstar : star (A ⊗ₖ B) * (A ⊗ₖ B) = (star A * A) ⊗ₖ (star B * B) := by
    rw [star_eq_conjTranspose, conjTranspose_kronecker, ← mul_kronecker_mul,
      star_eq_conjTranspose, star_eq_conjTranspose]
  rw [hstar, inv_kronecker, CFC.sqrt_eq_iff _ _
    (hpA.inv.posSemidef.kronecker hpB.inv.posSemidef).nonneg
    ((nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).kronecker
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))).nonneg,
    ← mul_kronecker_mul, CFC.sqrt_mul_sqrt_self _ hpA.inv.posSemidef.nonneg,
    CFC.sqrt_mul_sqrt_self _ hpB.inv.posSemidef.nonneg]

end UnitaryPart

/-! ### The local section -/

section LocalSection

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable (a b : ℝ) (u₀ : Matrix (m × n) (m × n) ℂ)

/-- The local gauge `g(u) = Q(N(u u₀†))`.

Source: the gauge `g(u)` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def localGauge (u : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  unitaryPart (nearestKronecker a b (u * star u₀))

/-- The local section `σ(u) = g(u)† u`.

Source: the section `σ` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def localSection (u : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  star (localGauge a b u₀ u) * u

/-- The domain of the local section: `u u₀†` lies in the gap set of the nearest
Kronecker product, and `N(u u₀†)` is invertible.

Source: the open set `W` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
def localSectionDomain : Set (Matrix (m × n) (m × n) ℂ) :=
  {u | u * star u₀ ∈ kroneckerGapSet a b ∧ IsUnit (nearestKronecker a b (u * star u₀))}

theorem isOpen_localSectionDomain : IsOpen (localSectionDomain a b u₀) := by
  have hc : Continuous fun u : Matrix (m × n) (m × n) ℂ ↦ u * star u₀ :=
    continuous_id.mul continuous_const
  have hdet : Continuous fun u : Matrix (m × n) (m × n) ℂ ↦
      (nearestKronecker a b (u * star u₀)).det :=
    ((continuous_nearestKronecker a b).comp hc).matrix_det
  have hunit : {u : Matrix (m × n) (m × n) ℂ | IsUnit (nearestKronecker a b (u * star u₀))} =
      (fun u ↦ (nearestKronecker a b (u * star u₀)).det) ⁻¹' {0}ᶜ := by
    ext u
    simp [isUnit_iff_isUnit_det]
  change IsOpen ((fun u : Matrix (m × n) (m × n) ℂ ↦ u * star u₀) ⁻¹' kroneckerGapSet a b ∩
    {u | IsUnit (nearestKronecker a b (u * star u₀))})
  rw [hunit]
  exact ((isOpen_kroneckerGapSet a b).preimage hc).inter (isOpen_compl_singleton.preimage hdet)

theorem continuousOn_localSection :
    ContinuousOn (localSection a b u₀) (localSectionDomain a b u₀) := by
  have hc : Continuous fun u : Matrix (m × n) (m × n) ℂ ↦ nearestKronecker a b (u * star u₀) :=
    (continuous_nearestKronecker a b).comp (continuous_id.mul continuous_const)
  have hg : ContinuousOn (localGauge a b u₀) (localSectionDomain a b u₀) :=
    continuousOn_unitaryPart.comp hc.continuousOn fun _ hu ↦ hu.2
  exact (continuous_star.comp_continuousOn hg).mul continuousOn_id

variable (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ))

private theorem kronecker_mem_unitaryGroup :
    (x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ) ∈ unitaryGroup (m × n) ℂ :=
  kronecker_mem_unitary x.2 y.2

/-- **Invariance of the local section.** `σ((x ⊗ y) u) = σ(u)` for unitaries `x`
and `y`.

Source: the invariance of `σ` in step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
theorem localSection_kronecker_mul (u : Matrix (m × n) (m × n) ℂ) :
    localSection a b u₀ (((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u) =
      localSection a b u₀ u := by
  rw [localSection, localSection, localGauge, localGauge, Matrix.mul_assoc,
    nearestKronecker_kronecker_mul, unitaryPart_unitary_mul (kronecker_mem_unitaryGroup x y),
    star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star _) _ u,
    Unitary.star_mul_self_of_mem (kronecker_mem_unitaryGroup x y), Matrix.one_mul]

/-- The domain of the local section is invariant under the local unitaries. -/
theorem kronecker_mul_mem_localSectionDomain_iff (u : Matrix (m × n) (m × n) ℂ) :
    ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u ∈ localSectionDomain a b u₀ ↔
      u ∈ localSectionDomain a b u₀ := by
  have hU := kronecker_mem_unitaryGroup x y
  simp only [localSectionDomain, Set.mem_ofPred_eq, Matrix.mul_assoc,
    kronecker_mul_mem_kroneckerGapSet_iff, nearestKronecker_kronecker_mul]
  refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun h ↦ (Unitary.isUnit_coe (U := ⟨_, hU⟩)).mul h⟩
  have := (Unitary.isUnit_coe (U := ⟨_, Unitary.star_mem hU⟩)).mul h
  rwa [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.one_mul] at this

/-- **The local section stays in the orbit.** For `u` in the domain, `σ(u)` is
`(x ⊗ y) u` for some unitaries `x` and `y`, provided `0 < a < b`.

Source: step 3 of the cross-section construction for arXiv:1703.09188,
Corollary `coruvSF`, lines 942--947. -/
theorem exists_localSection_eq_kronecker_mul (ha : 0 < a) (hab : a < b)
    {u : Matrix (m × n) (m × n) ℂ} (hu : u ∈ localSectionDomain a b u₀) :
    ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
      localSection a b u₀ u = ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u := by
  rcases isEmpty_or_nonempty m with hm | hm
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  obtain ⟨A, B, -, -, hAB⟩ := exists_eq_kronecker_nearestKronecker ha hab hu.1
  have hunit := hu.2
  rw [hAB, isUnit_iff_isUnit_det, det_kronecker] at hunit
  have hA : IsUnit A := by
    rw [isUnit_iff_isUnit_det]
    exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_left hunit)
  have hB : IsUnit B := by
    rw [isUnit_iff_isUnit_det]
    exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hunit)
  refine ⟨⟨star (unitaryPart A), Unitary.star_mem (unitaryPart_mem_unitaryGroup hA)⟩,
    ⟨star (unitaryPart B), Unitary.star_mem (unitaryPart_mem_unitaryGroup hB)⟩, ?_⟩
  rw [localSection, localGauge, hAB, unitaryPart_kronecker hA hB, star_eq_conjTranspose,
    conjTranspose_kronecker]
  rfl

private theorem kronecker_mul_mul_star_eq {u₀ : Matrix (m × n) (m × n) ℂ}
    (hu₀ : u₀ ∈ unitaryGroup (m × n) ℂ) :
    ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u₀ * star u₀ =
      (x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ) := by
  rw [Matrix.mul_assoc, Unitary.mul_star_self_of_mem hu₀, Matrix.mul_one]

section Orbit

variable {a b} {u₀} (hapos : 0 < a) (hab : a < b) (hbc : b < Fintype.card m * Fintype.card n)
  (hu₀ : u₀ ∈ unitaryGroup (m × n) ℂ)
include hapos hab hbc hu₀

/-- **The orbit of the base point lies in the domain.** For a unitary `u₀`, every
`(x ⊗ y) u₀` lies in the domain of the local section, provided
`0 < a < b < |m| |n|`. -/
theorem kronecker_mul_mem_localSectionDomain :
    ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u₀ ∈ localSectionDomain a b u₀ := by
  rw [localSectionDomain, Set.mem_ofPred_eq, kronecker_mul_mul_star_eq x y hu₀,
    nearestKronecker_kronecker_of_unitary hapos hab hbc]
  exact ⟨kronecker_mem_kroneckerGapSet hapos hab hbc x y,
    Unitary.isUnit_coe (U := ⟨_, kronecker_mem_unitaryGroup x y⟩)⟩

/-- **The local section fixes the base point.** For a unitary `u₀`,
`σ((x ⊗ y) u₀) = u₀`, provided `0 < a < b < |m| |n|`. -/
theorem localSection_kronecker_mul_self :
    localSection a b u₀ (((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u₀) = u₀ := by
  rw [localSection_kronecker_mul, localSection, localGauge, Unitary.mul_star_self_of_mem hu₀,
    nearestKronecker_one hapos hab hbc, unitaryPart_of_mem_unitaryGroup (one_mem _), star_one,
    Matrix.one_mul]

end Orbit

end LocalSection

end Matrix
