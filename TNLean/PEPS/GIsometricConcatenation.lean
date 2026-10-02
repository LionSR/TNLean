/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TNLean.PEPS.BasisRepresentation
import TNLean.PEPS.GIsometric

/-!
# G-isometry under contraction of a two-dimensional link

The adjoint of a contracted tensor is obtained by contracting the adjoints of its two
constituents. All adjoints are taken in the product bases of the physical and virtual
systems. In particular, the basis of a contracted outgoing leg is dual to the basis
of the corresponding incoming leg. For the regular representation, the correction
in the left inverse is the identity, and the positive isometry factors multiply.

**Local fix (normalization):** the source omits scalar normalizations in diagrams.
As in `IsGIsometric`, the inner products are preserved up to a positive factor.
For one unnormalized link the resulting factor is the product of the two input
factors. Documented in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

**Scope restriction (one contracted bond):** The contracted-adjoint results and
`IsGIsometric.linkContraction` (including its four-leg specialization) contract one
regular bond between two tensors. Contraction of several shared bonds and the Gram
identity for regions containing closed virtual cycles remain separate steps.
Documented in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Lemma 6.2
(`lemma:iso:iso-stable-under-concat`), lines 1704–1716 of
`Papers/1001.3807/paper_v3.tex`, together with Lemma 5.2, lines 1319–1344.
-/

open Module LinearMap Representation TensorProduct
open scoped Matrix

namespace TNLean.PEPS

section Coordinates

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The adjoint in the inner products for which the specified bases are orthonormal.
Source: arXiv:1001.3807, lines 1668–1686: conjugate coefficients and reverse the
physical-to-virtual orientation. -/
noncomputable def basisAdjoint (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y) (T : X →ₗ[ℂ] Y) :
    Y →ₗ[ℂ] X :=
  Matrix.toLin bY bX (LinearMap.toMatrix bX bY T).conjTranspose

@[simp]
theorem toMatrix_basisAdjoint (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y) (T : X →ₗ[ℂ] Y) :
    LinearMap.toMatrix bY bX (basisAdjoint bX bY T) =
      (LinearMap.toMatrix bX bY T).conjTranspose := by
  simp [basisAdjoint]

end Coordinates

section CoordinateIsometry

variable {G ι κ : Type*} [Group G] [Fintype G] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
attribute [local instance] Representation.invertibleFintypeCardComplex
/-- The adjoint for the coordinate inner products. -/
noncomputable def coordinateAdjoint (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) :
    (κ → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  Matrix.toLin' (LinearMap.toMatrix' T).conjTranspose

/-- Source: arXiv:1001.3807, Definition 6.1, lines 1692–1700. For an orthogonal
averaging projector, isometry on the invariant subspace is equivalent to the
adjoint-projector identity on the whole virtual space. -/
theorem IsGIsometric.exists_coordinateAdjoint_comp
    {ρ : Representation ℂ G (ι → ℂ)} {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}
    (hT : IsGIsometric ρ T)
    (hAvg : ∀ x y, star (ρ.averageMap x) ⬝ᵥ y = star x ⬝ᵥ ρ.averageMap y) :
    ∃ c : ℝ, 0 < c ∧ coordinateAdjoint T ∘ₗ T = (c : ℂ) • ρ.averageMap := by
  obtain ⟨c, hc, hinner⟩ := hT.exists_inner_eq
  have hglobal (x y : ι → ℂ) :
      star (T x) ⬝ᵥ T y = (c : ℂ) * (star x ⬝ᵥ ρ.averageMap y) := by
    calc
      star (T x) ⬝ᵥ T y = star (T (ρ.averageMap x)) ⬝ᵥ T (ρ.averageMap y) := by
        rw [apply_averageMap_of_forall_comp_eq hT.invariant,
          apply_averageMap_of_forall_comp_eq hT.invariant]
      _ = (c : ℂ) * (star (ρ.averageMap x) ⬝ᵥ ρ.averageMap y) :=
        hinner _ (ρ.averageMap_invariant x) _ (ρ.averageMap_invariant y)
      _ = (c : ℂ) * (star x ⬝ᵥ ρ.averageMap y) := by
        rw [hAvg, ρ.averageMap_id _ (ρ.averageMap_invariant y)]
  refine ⟨c, hc, ?_⟩
  apply LinearMap.toMatrix'.injective
  apply Matrix.ext
  intro i j
  have hij := hglobal (Pi.single i 1) (Pi.single j 1)
  have hmul (x : ι → ℂ) : (LinearMap.toMatrix' T) *ᵥ x = T x := by
    simpa only [Matrix.toLin'_apply] using LinearMap.congr_fun (Matrix.toLin'_toMatrix' T) x
  rw [← hmul, ← hmul] at hij
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec] at hij
  simp only [coordinateAdjoint, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin', map_smul, Matrix.smul_apply, smul_eq_mul]
  simpa [Matrix.mulVec_single_one, Pi.single_apply,
    Matrix.star_eq_conjTranspose, LinearMap.toMatrix'_apply] using hij
end CoordinateIsometry

section CoordinateAverage
variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The normalized average of a unitary representation is self-adjoint. -/
theorem averageMap_dotProduct_of_unitary
    (ρ : Representation ℂ G (ι → ℂ))
    (hU : ∀ g x y, star (ρ g x) ⬝ᵥ ρ g y = star x ⬝ᵥ y) (x y : ι → ℂ) :
    star (ρ.averageMap x) ⬝ᵥ y = star x ⬝ᵥ ρ.averageMap y := by
  have hpair (g : G) : star (ρ g x) ⬝ᵥ y = star x ⬝ᵥ ρ g⁻¹ y := by
    have h := hU g x (ρ g⁻¹ y)
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h
    exact h
  rw [Representation.averageMap_apply_eq_sum, Representation.averageMap_apply_eq_sum]
  simp only [star_smul, star_sum, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, invOf_eq_inv, star_inv₀, star_natCast,
    hpair]
  congr 1
  simpa using Equiv.sum_comp (Equiv.inv G) (fun g : G => star x ⬝ᵥ ρ g y)
end CoordinateAverage


section CoordinateCriterion

variable {G ι κ : Type*} [Group G] [Fintype G] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The defining adjoint identity for the coordinate inner products. -/
theorem coordinateAdjoint_dotProduct (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
    (x : ι → ℂ) (y : κ → ℂ) :
    star x ⬝ᵥ coordinateAdjoint T y = star (T x) ⬝ᵥ y := by
  rw [coordinateAdjoint, Matrix.toLin'_apply, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
  congr 2
  simpa only [Matrix.toLin'_apply] using LinearMap.congr_fun (Matrix.toLin'_toMatrix' T) x

/-- Source: arXiv:1001.3807, Definition 6.1, lines 1692–1700. An invariant map
whose adjoint is a positive multiple of a left inverse is `G`-isometric. -/
theorem isGIsometric_of_coordinateAdjoint_comp
    {ρ : Representation ℂ G (ι → ℂ)} {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}
    (hinv : ∀ g, T ∘ₗ ρ g = T) {c : ℝ} (hc : 0 < c)
    (hT : coordinateAdjoint T ∘ₗ T = (c : ℂ) • ρ.averageMap) : IsGIsometric ρ T := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  refine ⟨(isGInjective_iff_exists_leftInverse ρ T).2 ⟨hinv,
    (c : ℂ)⁻¹ • coordinateAdjoint T, ?_⟩, c, hc, ?_⟩
  · rw [LinearMap.smul_comp, hT, smul_smul, inv_mul_cancel₀ hc', one_smul]
  · intro x hx y hy
    rw [← coordinateAdjoint_dotProduct, ← LinearMap.comp_apply, hT,
      LinearMap.smul_apply, ρ.averageMap_id y hy, dotProduct_smul, smul_eq_mul]

end CoordinateCriterion

section BasisCriterion

variable {G X Y ι κ : Type*} [Group G] [Fintype G]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
attribute [local instance] Representation.invertibleFintypeCardComplex

omit [DecidableEq ι] in
@[simp]
theorem basisCoordinates_averageMap (b : Basis ι ℂ X) (ρ : Representation ℂ G X) :
    basisCoordinates b b ρ.averageMap = (basisRepresentation b ρ).averageMap := by
  apply LinearMap.ext
  intro x
  change b.equivFun (ρ.averageMap (b.equivFun.symm x)) = _
  rw [Representation.averageMap_apply_eq_sum, Representation.averageMap_apply_eq_sum]
  simp only [map_smul, map_sum, basisRepresentation_apply]

omit [Fintype G] [DecidableEq ι] [DecidableEq κ] in
/-- Invariance is unchanged by passage to coordinates. -/
theorem basisCoordinates_invariant_iff (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y)
    (ρ : Representation ℂ G X) (T : X →ₗ[ℂ] Y) :
    (∀ g, basisCoordinates bX bY T ∘ₗ basisRepresentation bX ρ g =
      basisCoordinates bX bY T) ↔ ∀ g, T ∘ₗ ρ g = T := by
  constructor
  · intro h g
    ext x
    apply bY.equivFun.injective
    have hx := LinearMap.congr_fun (h g) (bX.equivFun x)
    simpa [basisCoordinates] using hx
  · intro h g
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun (h g) (bX.equivFun.symm x)
    simpa [basisCoordinates] using congrArg bY.equivFun hx

omit [DecidableEq ι] [DecidableEq κ] in
@[simp]
theorem basisCoordinates_smul (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y)
    (r : ℂ) (T : X →ₗ[ℂ] Y) :
    basisCoordinates bX bY (r • T) = r • basisCoordinates bX bY T := by
  apply LinearMap.ext
  intro x
  simp [basisCoordinates]

@[simp]
theorem basisCoordinates_basisAdjoint (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y)
    (T : X →ₗ[ℂ] Y) :
    basisCoordinates bY bX (basisAdjoint bX bY T) =
      coordinateAdjoint (basisCoordinates bX bY T) := by
  apply LinearMap.toMatrix'.injective
  simp only [toMatrix_basisCoordinates, toMatrix_basisAdjoint, coordinateAdjoint]
  exact (LinearMap.toMatrix'_toLin' _).symm

omit [DecidableEq ι] [DecidableEq κ] in
theorem basisCoordinates_injective (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y) :
    Function.Injective (basisCoordinates bX bY) := by
  classical
  intro S T h
  apply (LinearMap.toMatrix bX bY).injective
  simpa using congrArg LinearMap.toMatrix' h

/-- The adjoint-projector identity is independent of the coordinate realization. -/
theorem basisAdjoint_comp_iff (bX : Basis ι ℂ X) (bY : Basis κ ℂ Y)
    (ρ : Representation ℂ G X) (T : X →ₗ[ℂ] Y) (c : ℝ) :
    basisAdjoint bX bY T ∘ₗ T = (c : ℂ) • ρ.averageMap ↔
      coordinateAdjoint (basisCoordinates bX bY T) ∘ₗ basisCoordinates bX bY T =
        (c : ℂ) • (basisRepresentation bX ρ).averageMap := by
  rw [← basisCoordinates_averageMap bX ρ, ← basisCoordinates_smul,
    ← basisCoordinates_basisAdjoint, ← basisCoordinates_comp]
  exact (basisCoordinates_injective bX bX).eq_iff.symm

end BasisCriterion

section LinkBasis

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The maximally entangled link vector in any basis and its dual basis. -/
theorem linkVector_eq_sum (b : Basis ι ℂ E) :
    (linkVector : Module.Dual ℂ E ⊗[ℂ] E) = ∑ i, b.coord i ⊗ₜ[ℂ] b i := by
  apply (dualTensorHomEquiv ℂ E E).injective
  ext x
  simp only [linkVector, coevaluation_apply_one, map_sum, TensorProduct.comm_tmul,
    dualTensorHomEquiv_tmul, LinearMap.sum_apply, Basis.coord_apply]
  rw [Basis.sum_repr, Basis.sum_repr]

end LinkBasis

section LinkAdjoint

variable {E WA WB PA PB : Type*}
  [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
  [AddCommGroup WA] [Module ℂ WA] [AddCommGroup WB] [Module ℂ WB]
  [AddCommGroup PA] [Module ℂ PA] [AddCommGroup PB] [Module ℂ PB]
variable {ε α β π τ : Type*}
  [Fintype ε] [Fintype α] [Fintype β] [Fintype π] [Fintype τ]
  [DecidableEq ε] [DecidableEq α] [DecidableEq β] [DecidableEq π] [DecidableEq τ]

omit [Fintype π] [Fintype τ] [DecidableEq π] [DecidableEq τ] in
/-- Coefficients of a link contraction in the product bases. -/
theorem toMatrix_linkContraction [Finite π] [Finite τ] (bE : Basis ε ℂ E) (bWA : Basis α ℂ WA)
    (bWB : Basis β ℂ WB) (bPA : Basis π ℂ PA) (bPB : Basis τ ℂ PB)
    (TA : WA ⊗[ℂ] Module.Dual ℂ E →ₗ[ℂ] PA) (TB : E ⊗[ℂ] WB →ₗ[ℂ] PB)
    (p : π × τ) (q : α × β) :
    LinearMap.toMatrix (bWA.tensorProduct bWB) (bPA.tensorProduct bPB)
        (linkContraction TA TB) p q =
      ∑ i, LinearMap.toMatrix (bWA.tensorProduct bE.dualBasis) bPA TA p.1 (q.1, i) *
        LinearMap.toMatrix (bE.tensorProduct bWB) bPB TB p.2 (i, q.2) := by
  rcases p with ⟨pA, pB⟩
  simp only [LinearMap.toMatrix_apply, Basis.tensorProduct_apply', linkContraction_tmul,
    linkVector_eq_sum bE, map_sum, map_tmul, LinearMap.comp_apply, TensorProduct.mk_apply,
    LinearMap.flip_apply, Finsupp.finsetSum_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.coe_dualBasis, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [FiniteDimensional ℂ E] [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β] in
/-- Coefficients of the contraction of two physical-to-virtual maps. -/
theorem toMatrix_innerContraction_map [Finite α] [Finite β] (bE : Basis ε ℂ E) (bWA : Basis α ℂ WA)
    (bWB : Basis β ℂ WB) (bPA : Basis π ℂ PA) (bPB : Basis τ ℂ PB)
    (LA : PA →ₗ[ℂ] WA ⊗[ℂ] Module.Dual ℂ E) (LB : PB →ₗ[ℂ] E ⊗[ℂ] WB)
    (q : α × β) (p : π × τ) :
    LinearMap.toMatrix (bPA.tensorProduct bPB) (bWA.tensorProduct bWB)
        (innerContraction 1 ∘ₗ TensorProduct.map LA LB) q p =
      ∑ i, LinearMap.toMatrix bPA (bWA.tensorProduct bE.dualBasis) LA (q.1, i) p.1 *
        LinearMap.toMatrix bPB (bE.tensorProduct bWB) LB (i, q.2) p.2 := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rcases q with ⟨qA, qB⟩
  simp only [LinearMap.toMatrix_apply, Basis.tensorProduct_apply', LinearMap.comp_apply,
    map_tmul]
  conv_lhs =>
    rw [← (bWA.tensorProduct bE.dualBasis).sum_repr (LA (bPA p.1)),
      ← (bE.tensorProduct bWB).sum_repr (LB (bPB p.2))]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul',
    map_sum, map_smul, Basis.tensorProduct_apply',
    innerContraction_tmul, Module.End.one_apply, Basis.coe_dualBasis, Basis.coord_apply,
    Basis.repr_self_apply, smul_smul]
  simp only [Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
    Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  simp only [Basis.repr_self_apply, Fintype.sum_prod_type, mul_ite, ite_mul,
    mul_zero, zero_mul, mul_one, one_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Source: arXiv:1001.3807, Lemma 6.2, lines 1709–1713. The adjoint of a
contracted tensor contracts the adjoints of its two constituents. -/
theorem basisAdjoint_linkContraction (bE : Basis ε ℂ E) (bWA : Basis α ℂ WA)
    (bWB : Basis β ℂ WB) (bPA : Basis π ℂ PA) (bPB : Basis τ ℂ PB)
    (TA : WA ⊗[ℂ] Module.Dual ℂ E →ₗ[ℂ] PA) (TB : E ⊗[ℂ] WB →ₗ[ℂ] PB) :
    basisAdjoint (bWA.tensorProduct bWB) (bPA.tensorProduct bPB)
        (linkContraction TA TB) =
      innerContraction 1 ∘ₗ TensorProduct.map
        (basisAdjoint (bWA.tensorProduct bE.dualBasis) bPA TA)
        (basisAdjoint (bE.tensorProduct bWB) bPB TB) := by
  apply (LinearMap.toMatrix (bPA.tensorProduct bPB) (bWA.tensorProduct bWB)).injective
  ext (q : α × β) (p : π × τ)
  rw [toMatrix_basisAdjoint, Matrix.conjTranspose_apply,
    toMatrix_linkContraction bE bWA bWB bPA bPB,
    toMatrix_innerContraction_map bE bWA bWB bPA bPB]
  simp only [toMatrix_basisAdjoint, Matrix.conjTranspose_apply, star_sum, star_mul, mul_comm]

end LinkAdjoint

section RegularContraction

variable {G WA WB PA PB : Type*} [Group G] [Fintype G] [DecidableEq G]
  [AddCommGroup WA] [Module ℂ WA] [AddCommGroup WB] [Module ℂ WB]
  [AddCommGroup PA] [Module ℂ PA] [AddCommGroup PB] [Module ℂ PB]
variable {α β π τ : Type*} [Fintype α] [Fintype β] [Fintype π] [Fintype τ]
  [DecidableEq α] [DecidableEq β] [DecidableEq π] [DecidableEq τ]

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- Source: arXiv:1001.3807, Lemma 6.2, lines 1704–1716. With one unnormalized
regular link, the positive isometry factors multiply: `C† C = c_A c_B Π`.
The factor `|G|` of the concatenated left inverse cancels `Δ = |G|⁻¹ 𝟙`. -/
theorem basisAdjoint_linkContraction_comp
    (bWA : Basis α ℂ WA) (bWB : Basis β ℂ WB)
    (bPA : Basis π ℂ PA) (bPB : Basis τ ℂ PB)
    (σA : Representation ℂ G WA) (σB : Representation ℂ G WB)
    (TA : WA ⊗[ℂ] Module.Dual ℂ (MonoidAlgebra ℂ G) →ₗ[ℂ] PA)
    (TB : MonoidAlgebra ℂ G ⊗[ℂ] WB →ₗ[ℂ] PB)
    {cA cB : ℝ} (hcA : 0 < cA) (hcB : 0 < cB)
    (hA : basisAdjoint (bWA.tensorProduct (MonoidAlgebra.basis G ℂ).dualBasis) bPA TA ∘ₗ TA =
      (cA : ℂ) • (σA.tprod (leftRegular ℂ G).dual).averageMap)
    (hB : basisAdjoint ((MonoidAlgebra.basis G ℂ).tensorProduct bWB) bPB TB ∘ₗ TB =
      (cB : ℂ) • ((leftRegular ℂ G).tprod σB).averageMap) :
    basisAdjoint (bWA.tensorProduct bWB) (bPA.tensorProduct bPB)
        (linkContraction TA TB) ∘ₗ linkContraction TA TB =
      ((cA * cB : ℝ) : ℂ) • (σA.tprod σB).averageMap := by
  have hcA' : (cA : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcA.ne'
  have hcB' : (cB : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcB.ne'
  have hLA : ((cA : ℂ)⁻¹ • basisAdjoint
      (bWA.tensorProduct (MonoidAlgebra.basis G ℂ).dualBasis) bPA TA) ∘ₗ TA =
      (σA.tprod (leftRegular ℂ G).dual).averageMap := by
    rw [LinearMap.smul_comp, hA, smul_smul, inv_mul_cancel₀ hcA', one_smul]
  have hLB : ((cB : ℂ)⁻¹ • basisAdjoint
      ((MonoidAlgebra.basis G ℂ).tensorProduct bWB) bPB TB) ∘ₗ TB =
      ((leftRegular ℂ G).tprod σB).averageMap := by
    rw [LinearMap.smul_comp, hB, smul_smul, inv_mul_cancel₀ hcB', one_smul]
  have hC := linkContractionLeftInverse_comp (isSemiRegular_leftRegular (G := G)) hLA hLB
  rw [linkContractionLeftInverse_leftRegular, TensorProduct.map_smul_left,
    TensorProduct.map_smul_right, LinearMap.comp_smul, LinearMap.comp_smul, smul_smul,
    ← basisAdjoint_linkContraction (MonoidAlgebra.basis G ℂ) bWA bWB bPA bPB,
    LinearMap.smul_comp] at hC
  have hscale : ((cA * cB : ℝ) : ℂ) * ((cA : ℂ)⁻¹ * (cB : ℂ)⁻¹) = 1 := by
    rw [Complex.ofReal_mul, mul_mul_mul_comm, mul_inv_cancel₀ hcA',
      mul_inv_cancel₀ hcB', one_mul]
  have h := congrArg (fun L => ((cA * cB : ℝ) : ℂ) • L) hC
  simpa only [smul_smul, hscale, one_smul] using h

omit [DecidableEq α] [DecidableEq β] [DecidableEq π] [DecidableEq τ] in
private theorem isGIsometric_linkContraction_of_average
    (bWA : Basis α ℂ WA) (bWB : Basis β ℂ WB)
    (bPA : Basis π ℂ PA) (bPB : Basis τ ℂ PB)
    (σA : Representation ℂ G WA) (σB : Representation ℂ G WB)
    (TA : WA ⊗[ℂ] Module.Dual ℂ (MonoidAlgebra ℂ G) →ₗ[ℂ] PA)
    (TB : MonoidAlgebra ℂ G ⊗[ℂ] WB →ₗ[ℂ] PB)
    (hAvgA : ∀ x y,
      star ((basisRepresentation (bWA.tensorProduct (MonoidAlgebra.basis G ℂ).dualBasis)
        (σA.tprod (leftRegular ℂ G).dual)).averageMap x) ⬝ᵥ y =
      star x ⬝ᵥ (basisRepresentation (bWA.tensorProduct (MonoidAlgebra.basis G ℂ).dualBasis)
        (σA.tprod (leftRegular ℂ G).dual)).averageMap y)
    (hAvgB : ∀ x y,
      star ((basisRepresentation ((MonoidAlgebra.basis G ℂ).tensorProduct bWB)
        ((leftRegular ℂ G).tprod σB)).averageMap x) ⬝ᵥ y =
      star x ⬝ᵥ (basisRepresentation ((MonoidAlgebra.basis G ℂ).tensorProduct bWB)
        ((leftRegular ℂ G).tprod σB)).averageMap y)
    (hA : IsGIsometric
      (basisRepresentation (bWA.tensorProduct (MonoidAlgebra.basis G ℂ).dualBasis)
        (σA.tprod (leftRegular ℂ G).dual))
      (basisCoordinates (bWA.tensorProduct (MonoidAlgebra.basis G ℂ).dualBasis) bPA TA))
    (hB : IsGIsometric
      (basisRepresentation ((MonoidAlgebra.basis G ℂ).tensorProduct bWB)
        ((leftRegular ℂ G).tprod σB))
      (basisCoordinates ((MonoidAlgebra.basis G ℂ).tensorProduct bWB) bPB TB)) :
    IsGIsometric (basisRepresentation (bWA.tensorProduct bWB) (σA.tprod σB))
      (basisCoordinates (bWA.tensorProduct bWB) (bPA.tensorProduct bPB)
        (linkContraction TA TB)) := by
  classical
  obtain ⟨cA, hcA, hA'⟩ := hA.exists_coordinateAdjoint_comp hAvgA
  obtain ⟨cB, hcB, hB'⟩ := hB.exists_coordinateAdjoint_comp hAvgB
  have hAi := (basisCoordinates_invariant_iff _ _ _ _).1 hA.invariant
  have hBi := (basisCoordinates_invariant_iff _ _ _ _).1 hB.invariant
  refine isGIsometric_of_coordinateAdjoint_comp
    ((basisCoordinates_invariant_iff _ _ _ _).2 (linkContraction_comp_tprod hAi hBi))
    (mul_pos hcA hcB) ?_
  apply (basisAdjoint_comp_iff _ _ _ _ _).1
  exact basisAdjoint_linkContraction_comp bWA bWB bPA bPB σA σB TA TB hcA hcB
    ((basisAdjoint_comp_iff _ _ _ _ _).2 hA') ((basisAdjoint_comp_iff _ _ _ _ _).2 hB')

omit [DecidableEq α] [DecidableEq β] [DecidableEq π] [DecidableEq τ] in
/-- Source: arXiv:1001.3807, Lemma 6.2, lines 1704–1716. Contracting one
outgoing regular leg with one incoming regular leg preserves `G`-isometry.
The remaining virtual representations are unitary in the chosen bases, as are
products of regular actions on the uncontracted legs of the source's PEPS.
The coordinate inner products are those of the orthonormal product bases. -/
theorem IsGIsometric.linkContraction
    (bWA : Basis α ℂ WA) (bWB : Basis β ℂ WB)
    (bPA : Basis π ℂ PA) (bPB : Basis τ ℂ PB)
    (σA : Representation ℂ G WA) (σB : Representation ℂ G WB)
    (TA : WA ⊗[ℂ] Module.Dual ℂ (MonoidAlgebra ℂ G) →ₗ[ℂ] PA)
    (TB : MonoidAlgebra ℂ G ⊗[ℂ] WB →ₗ[ℂ] PB)
    (hσA : ∀ g x y, star (basisRepresentation bWA σA g x) ⬝ᵥ
      basisRepresentation bWA σA g y = star x ⬝ᵥ y)
    (hσB : ∀ g x y, star (basisRepresentation bWB σB g x) ⬝ᵥ
      basisRepresentation bWB σB g y = star x ⬝ᵥ y)
    (hA : IsGIsometric
      (basisRepresentation (bWA.tensorProduct (MonoidAlgebra.basis G ℂ).dualBasis)
        (σA.tprod (leftRegular ℂ G).dual))
      (basisCoordinates (bWA.tensorProduct (MonoidAlgebra.basis G ℂ).dualBasis) bPA TA))
    (hB : IsGIsometric
      (basisRepresentation ((MonoidAlgebra.basis G ℂ).tensorProduct bWB)
        ((leftRegular ℂ G).tprod σB))
      (basisCoordinates ((MonoidAlgebra.basis G ℂ).tensorProduct bWB) bPB TB)) :
    IsGIsometric (basisRepresentation (bWA.tensorProduct bWB) (σA.tprod σB))
      (basisCoordinates (bWA.tensorProduct bWB) (bPA.tensorProduct bPB)
        (PEPS.linkContraction TA TB)) := by
  classical
  have hreg := basisRepresentation_unitary_leftRegular (G := G)
  have hdual := basisRepresentation_unitary_dual (MonoidAlgebra.basis G ℂ)
    (leftRegular ℂ G) hreg
  exact isGIsometric_linkContraction_of_average bWA bWB bPA bPB σA σB TA TB
    (averageMap_dotProduct_of_unitary _
      (basisRepresentation_unitary_tensorProduct bWA _ σA _ hσA hdual))
    (averageMap_dotProduct_of_unitary _
      (basisRepresentation_unitary_tensorProduct _ bWB _ σB hreg hσB)) hA hB

local notation "ℂG" => MonoidAlgebra ℂ G
local notation "bG" => MonoidAlgebra.basis G ℂ
local notation "LG" => leftRegular ℂ G

omit [DecidableEq π] [DecidableEq τ] in
set_option maxSynthPendingDepth 8 in
/-- Source: arXiv:1001.3807, Lemma 6.2, lines 1704–1716, for two neighboring
four-leg PEPS tensors. Each tensor has two incoming regular legs and two
outgoing dual regular legs. Contracting the final outgoing leg of the first
with the first incoming leg of the second preserves `G`-isometry. All actions
on the remaining legs are explicitly regular or dual regular, so their
unitarity is a consequence rather than an additional hypothesis. -/
theorem IsGIsometric.linkContraction_fourLeg
    (bPA : Basis π ℂ PA) (bPB : Basis τ ℂ PB)
    (TA : ((ℂG ⊗[ℂ] ℂG) ⊗[ℂ] Module.Dual ℂ ℂG) ⊗[ℂ]
      Module.Dual ℂ ℂG →ₗ[ℂ] PA)
    (TB : ℂG ⊗[ℂ] (ℂG ⊗[ℂ]
      (Module.Dual ℂ ℂG ⊗[ℂ] Module.Dual ℂ ℂG)) →ₗ[ℂ] PB)
    (hA : IsGIsometric
      (basisRepresentation
        ((((bG).tensorProduct bG).tensorProduct (bG).dualBasis).tensorProduct (bG).dualBasis)
        ((((LG).tprod LG).tprod (LG).dual).tprod (LG).dual))
      (basisCoordinates
        ((((bG).tensorProduct bG).tensorProduct (bG).dualBasis).tensorProduct (bG).dualBasis)
        bPA TA))
    (hB : IsGIsometric
      (basisRepresentation
        ((bG).tensorProduct ((bG).tensorProduct ((bG).dualBasis.tensorProduct (bG).dualBasis)))
        ((LG).tprod ((LG).tprod ((LG).dual.tprod (LG).dual))))
      (basisCoordinates
        ((bG).tensorProduct ((bG).tensorProduct ((bG).dualBasis.tensorProduct (bG).dualBasis)))
        bPB TB)) :
    IsGIsometric
      (basisRepresentation
        ((((bG).tensorProduct bG).tensorProduct (bG).dualBasis).tensorProduct
          ((bG).tensorProduct ((bG).dualBasis.tensorProduct (bG).dualBasis)))
        ((((LG).tprod LG).tprod (LG).dual).tprod ((LG).tprod ((LG).dual.tprod (LG).dual))))
      (basisCoordinates
        (X := ((ℂG ⊗[ℂ] ℂG) ⊗[ℂ] Module.Dual ℂ ℂG) ⊗[ℂ]
          (ℂG ⊗[ℂ] (Module.Dual ℂ ℂG ⊗[ℂ] Module.Dual ℂ ℂG)))
        (Y := PA ⊗[ℂ] PB)
        ((((bG).tensorProduct bG).tensorProduct (bG).dualBasis).tensorProduct
          ((bG).tensorProduct ((bG).dualBasis.tensorProduct (bG).dualBasis)))
        (bPA.tensorProduct bPB)
        (PEPS.linkContraction
          (WA := (ℂG ⊗[ℂ] ℂG) ⊗[ℂ] Module.Dual ℂ ℂG)
          (WB := ℂG ⊗[ℂ] (Module.Dual ℂ ℂG ⊗[ℂ] Module.Dual ℂ ℂG)) TA TB)) := by
  classical
  have hreg := basisRepresentation_unitary_leftRegular (G := G)
  have hdual := basisRepresentation_unitary_dual bG LG hreg
  exact IsGIsometric.linkContraction _ _ bPA bPB _ _ TA TB
    (basisRepresentation_unitary_tensorProduct _ _ _ _
      (basisRepresentation_unitary_tensorProduct _ _ _ _ hreg hreg) hdual)
    (basisRepresentation_unitary_tensorProduct _ _ _ _ hreg
      (basisRepresentation_unitary_tensorProduct _ _ _ _ hdual hdual)) hA hB

end RegularContraction

end TNLean.PEPS
