/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.PEPS.GIsometric
import Mathlib.LinearAlgebra.Contraction

/-!
# Stability of G-isometry under the two-dimensional link contraction

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), `Papers/1001.3807/paper_v3.tex`:

* Definition 6.1 (`def:iso:isopeps`), lines 1692–1700: a `G`-injective PEPS is `G`-isometric if
  `U_g = L_g` is the left-regular representation, `L_g|h⟩ = |gh⟩`, and `𝒫(A)⁻¹ = 𝒫(A†)`;
* Lemma 6.2 (`lemma:iso:iso-stable-under-concat`), lines 1704–1716: `G`-isometry is stable under
  concatenation. The proof: for `U_g = L_g`, `Δ = |G|⁻¹ 𝟙`, so the left inverse of the
  concatenated tensor, built in equation `eq:noninj:linv` and, in two dimensions, in figure
  `figs3/ab-inv.pdf` of Lemma 5.2 (lines 1319–1344), is the contraction of the adjoints of the
  two factors, which is the adjoint of the contraction.

**Formalized here.** The two-dimensional concatenation is the contraction of one link of two
tensors (`TNLean.PEPS.linkContraction`, Lemma 5.2): the right leg of `A`, with virtual system
`W_A ⊗ ℂ[G]^*`, is contracted with the left leg of `B`, with virtual system `ℂ[G] ⊗ W_B`. In the
coordinates of the group elements on the link and of coordinate bases `ℂ^α`, `ℂ^β` of the
remaining legs and of the physical systems (`linkLeftCoord`, `linkRightCoord`, `pairCoord`,
`tensorCoord`), the contraction is `linkContractionCoord`,
`C_{(k, l), (a, b)} = ∑_g A_{k, (a, g)} B_{l, (g, b)}`
(`tensorCoord_comp_linkContraction_comp_pairCoord`). In these coordinates the representations
`σ_A ⊗ L^*` and `L ⊗ σ_B` of the two virtual systems are the Kronecker representations
`σ_A ⊗ L` and `L ⊗ σ_B` of `kroneckerRep`, with `L = leftRegularFun` the left-regular
representation on `ℂ^G` (`linkLeftCoord_comp_kroneckerRep`, `linkRightCoord_comp_kroneckerRep`,
`coeff_leftRegular`), and `G`-isometry is `TNLean.PEPS.IsGIsometric`, with its positive factor.

For a unitary representation, `G`-isometry is `𝒫(A)† 𝒫(A) = c_A Π`
(`conjTranspose_toMatrix'_mul_toMatrix'`). The Gram matrix of the contraction is the
contraction of the two Gram matrices; on the link the two group elements `g`, `h` of the two
projectors meet in `∑_{k, k'} (L_g)_{k k'} (L_h)_{k k'} = |G| δ_{g, h}`, which is the step
`Δ = |G|⁻¹ 𝟙` of the source, so `𝒫(C)† 𝒫(C) = c_A c_B Π`
(`conjTranspose_linkContractionMatrix_mul_eq`). Hence the left inverse of `𝒫(C)` is
`(c_A c_B)⁻¹ 𝒫(C)†` (`toLin'_conjTranspose_comp_linkContractionCoord`), and Lemma 6.2 in two
dimensions is `IsGIsometric.linkContraction`, with the factors multiplying.

The representations `σ_A`, `σ_B` of the remaining legs are required to be unitary. In the
source every leg of a `G`-isometric tensor carries the left-regular representation or its
contragredient, both unitary, so this is implied by the source's hypotheses; the theorem is
stated for any unitary representations on these legs.

## Main definitions

* `TNLean.PEPS.leftRegularFun`: the left-regular representation on `ℂ^G`.
* `TNLean.PEPS.kroneckerRep`: the tensor product of two representations on coordinate spaces.
* `TNLean.PEPS.linkContractionCoord`: the contraction of one link in coordinates.

## Main results

* `TNLean.PEPS.conjTranspose_toMatrix'_mul_toMatrix'`: `𝒫(A)† 𝒫(A) = c Π`.
* `TNLean.PEPS.conjTranspose_linkContractionMatrix_mul_eq`: `𝒫(C)† 𝒫(C) = c_A c_B Π`.
* `TNLean.PEPS.IsGIsometric.linkContractionCoord`, `TNLean.PEPS.IsGIsometric.linkContraction`:
  Lemma 6.2 in two dimensions.
* `TNLean.PEPS.tensorCoord_comp_linkContraction_comp_pairCoord`: the coordinate form of
  `linkContraction`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap Representation TensorProduct
open scoped Matrix Kronecker ComplexOrder

namespace TNLean
namespace PEPS

attribute [local instance] Representation.invertibleFintypeCardComplex

variable {G : Type*} [Group G]

section Regular

/-- The left-regular representation on the coordinate space `ℂ^G`, `(L_g f)(h) = f(g⁻¹ h)`. -/
noncomputable def leftRegularFun : Representation ℂ G (G → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun h => g⁻¹ * h
  map_one' := by
    refine LinearMap.ext fun f => funext fun h => ?_
    simp [LinearMap.funLeft]
  map_mul' g g' := by
    refine LinearMap.ext fun f => funext fun h => ?_
    simp [LinearMap.funLeft, mul_assoc]

@[simp]
theorem leftRegularFun_apply (g : G) (f : G → ℂ) (h : G) :
    leftRegularFun g f h = f (g⁻¹ * h) :=
  rfl

/-- Bridge: on coefficients, the representation `leftRegularFun` is Mathlib's left-regular
representation `leftRegular ℂ G` on `ℂ[G]`, `L_g |h⟩ = |gh⟩`. -/
theorem coeff_leftRegular (g : G) (f : MonoidAlgebra ℂ G) :
    (fun h => (leftRegular ℂ G g f).coeff h) = leftRegularFun g fun h => f.coeff h := by
  funext h
  simp [coeff_ofMulAction, smul_eq_mul]

variable [Fintype G] [DecidableEq G]

theorem toMatrix'_leftRegularFun (g h h' : G) :
    LinearMap.toMatrix' (leftRegularFun g) h h' = if g * h' = h then 1 else 0 := by
  rw [LinearMap.toMatrix'_apply, leftRegularFun_apply, Pi.single_apply]
  congr 1
  exact propext ⟨fun e => by rw [← e, mul_inv_cancel_left],
    fun e => by rw [← e, inv_mul_cancel_left]⟩

theorem toMatrix'_leftRegularFun_mem_unitaryGroup (g : G) :
    LinearMap.toMatrix' (leftRegularFun g) ∈ Matrix.unitaryGroup G ℂ := by
  refine mem_unitaryGroup_of_dotProduct fun x y => ?_
  simp only [Matrix.toLin'_toMatrix', ← Matrix.toLin'_apply]
  simp only [leftRegularFun_apply, dotProduct, Pi.star_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => rfl

end Regular

section Kronecker

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The tensor product `ρ ⊗ τ` of two representations on coordinate spaces, acting on
`ℂ^{ι × κ}` by the Kronecker product of their matrices. -/
noncomputable def kroneckerRep (ρ : Representation ℂ G (ι → ℂ))
    (τ : Representation ℂ G (κ → ℂ)) : Representation ℂ G (ι × κ → ℂ) where
  toFun g := Matrix.toLin' (LinearMap.toMatrix' (ρ g) ⊗ₖ LinearMap.toMatrix' (τ g))
  map_one' := by
    rw [ρ.map_one, τ.map_one, LinearMap.toMatrix'_one, LinearMap.toMatrix'_one,
      Matrix.one_kronecker_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [ρ.map_mul, τ.map_mul, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul,
      Matrix.mul_kronecker_mul, Matrix.toLin'_mul]
    rfl

theorem toMatrix'_kroneckerRep (ρ : Representation ℂ G (ι → ℂ))
    (τ : Representation ℂ G (κ → ℂ)) (g : G) :
    LinearMap.toMatrix' (kroneckerRep ρ τ g) =
      LinearMap.toMatrix' (ρ g) ⊗ₖ LinearMap.toMatrix' (τ g) :=
  LinearMap.toMatrix'_toLin' _

theorem toMatrix'_kroneckerRep_mem_unitaryGroup {ρ : Representation ℂ G (ι → ℂ)}
    {τ : Representation ℂ G (κ → ℂ)}
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup ι ℂ)
    (hτ : ∀ g, LinearMap.toMatrix' (τ g) ∈ Matrix.unitaryGroup κ ℂ) (g : G) :
    LinearMap.toMatrix' (kroneckerRep ρ τ g) ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  rw [toMatrix'_kroneckerRep]
  exact Matrix.kronecker_mem_unitary (hρ g) (hτ g)

end Kronecker

section Gram

variable [Fintype G] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- For a unitary representation the projector `Π` onto the invariant subspace is
self-adjoint: `⟪Π u, w⟫ = ⟪u, Π w⟫`. -/
theorem star_averageMap_dotProduct {ρ : Representation ℂ G (ι → ℂ)}
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup ι ℂ) (u w : ι → ℂ) :
    star (ρ.averageMap u) ⬝ᵥ w = star u ⬝ᵥ ρ.averageMap w := by
  have hg : ∀ g, star (ρ g u) ⬝ᵥ w = star u ⬝ᵥ ρ g⁻¹ w := fun g => by
    have h := Matrix.star_mulVec_dotProduct_mulVec_of_mem_unitary (hρ g) u (ρ g⁻¹ w)
    simp only [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix'] at h
    rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [averageMap_apply_eq_sum, averageMap_apply_eq_sum, star_smul, smul_dotProduct,
    dotProduct_smul, star_sum, sum_dotProduct, dotProduct_sum]
  simp only [hg]
  congr 1
  · simp [Invertible.invOf, star_inv₀]
  · exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl

/-- Source: arXiv:1001.3807, Definition 6.1, `Papers/1001.3807/paper_v3.tex` lines 1692–1700.
If `T` is invariant under a unitary representation and preserves inner products of invariant
vectors up to `c`, then `T†T = c Π`: the left inverse of `T` is `c⁻¹ T†`. -/
theorem conjTranspose_toMatrix'_mul_toMatrix' {ρ : Representation ℂ G (ι → ℂ)}
    {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup ι ℂ)
    (hinv : ∀ g, T ∘ₗ ρ g = T) {c : ℂ}
    (hc : ∀ x ∈ ρ.invariants, ∀ y ∈ ρ.invariants, star (T x) ⬝ᵥ T y = c * (star x ⬝ᵥ y)) :
    (LinearMap.toMatrix' T)ᴴ * LinearMap.toMatrix' T = c • LinearMap.toMatrix' ρ.averageMap := by
  ext i j
  have key : star (T (Pi.single i 1)) ⬝ᵥ T (Pi.single j 1) =
      c * ρ.averageMap (Pi.single j 1) i := by
    rw [← apply_averageMap_of_forall_comp_eq hinv,
      ← apply_averageMap_of_forall_comp_eq hinv (Pi.single j 1),
      hc _ (ρ.averageMap_invariant _) _ (ρ.averageMap_invariant _),
      star_averageMap_dotProduct hρ, averageMap_id _ _ (ρ.averageMap_invariant _)]
    simp [dotProduct, Pi.single_apply]
  rw [Matrix.mul_apply, Matrix.smul_apply, LinearMap.toMatrix'_apply, smul_eq_mul, ← key]
  simp [dotProduct, LinearMap.toMatrix'_apply, Matrix.conjTranspose_apply]

end Gram

section Link

variable [Fintype G] [DecidableEq G] {α β κA κB : Type*} [Fintype α] [Fintype β] [Fintype κA]
  [Fintype κB] [DecidableEq α] [DecidableEq β]

/-- The matrix of the contraction of the right leg of `A` with the left leg of `B` in
coordinates, `C_{(k, l), (a, b)} = ∑_g A_{k, (a, g)} B_{l, (g, b)}`. -/
noncomputable def linkContractionMatrix (MA : Matrix κA (α × G) ℂ) (MB : Matrix κB (G × β) ℂ) :
    Matrix (κA × κB) (α × β) ℂ :=
  Matrix.of fun k p => ∑ g, MA k.1 (p.1, g) * MB k.2 (g, p.2)

/-- The map `𝒫(C)` of the contracted tensor in coordinates. -/
noncomputable def linkContractionCoord (TA : (α × G → ℂ) →ₗ[ℂ] (κA → ℂ))
    (TB : (G × β → ℂ) →ₗ[ℂ] (κB → ℂ)) : (α × β → ℂ) →ₗ[ℂ] (κA × κB → ℂ) :=
  Matrix.toLin' (linkContractionMatrix (LinearMap.toMatrix' TA) (LinearMap.toMatrix' TB))

omit [Group G] [DecidableEq G] [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
/-- The Gram matrix of the contraction is the contraction of the two Gram matrices. -/
theorem conjTranspose_linkContractionMatrix_mul (MA : Matrix κA (α × G) ℂ)
    (MB : Matrix κB (G × β) ℂ) (p q : α × β) :
    ((linkContractionMatrix MA MB)ᴴ * linkContractionMatrix MA MB) p q =
      ∑ g, ∑ g', (MAᴴ * MA) (p.1, g) (q.1, g') * (MBᴴ * MB) (g, p.2) (g', q.2) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, linkContractionMatrix, Matrix.of_apply,
    star_sum, star_mul', Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_last_two_first_four, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun g' _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq G] [DecidableEq β] in
/-- The matrix of the projector onto the invariant subspace is the average of the matrices of
the representation. -/
theorem toMatrix'_averageMap (ρ : Representation ℂ G (α → ℂ)) :
    LinearMap.toMatrix' ρ.averageMap = ⅟(Fintype.card G : ℂ) • ∑ g, LinearMap.toMatrix' (ρ g) := by
  have h : ρ.averageMap = ⅟(Fintype.card G : ℂ) • ∑ g, ρ g :=
    LinearMap.ext fun v => by rw [averageMap_apply_eq_sum]; simp
  rw [h, map_smul, map_sum]

/-- Source: arXiv:1001.3807, proof of Lemma 6.2, `Papers/1001.3807/paper_v3.tex`
lines 1709–1713. If `A†A = c_A Π_{σ_A ⊗ L}` and `B†B = c_B Π_{L ⊗ σ_B}`, with the left-regular
representation `L` on the contracted link, then `C†C = c_A c_B Π_{σ_A ⊗ σ_B}`. The sum over the
link index pairs the two group elements reaching its ends, which is the step `Δ = |G|⁻¹ 𝟙`. -/
theorem conjTranspose_linkContractionMatrix_mul_eq {σA : Representation ℂ G (α → ℂ)}
    {σB : Representation ℂ G (β → ℂ)} {MA : Matrix κA (α × G) ℂ} {MB : Matrix κB (G × β) ℂ}
    {cA cB : ℂ}
    (hA : MAᴴ * MA = cA • LinearMap.toMatrix' (kroneckerRep σA leftRegularFun).averageMap)
    (hB : MBᴴ * MB = cB • LinearMap.toMatrix' (kroneckerRep leftRegularFun σB).averageMap) :
    (linkContractionMatrix MA MB)ᴴ * linkContractionMatrix MA MB =
      (cA * cB) • LinearMap.toMatrix' (kroneckerRep σA σB).averageMap := by
  have hn : (Fintype.card G : ℂ) * ⅟(Fintype.card G : ℂ) = 1 := mul_invOf_self _
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [conjTranspose_linkContractionMatrix_mul, hA, hB]
  simp only [toMatrix'_averageMap, toMatrix'_kroneckerRep, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, toMatrix'_leftRegularFun, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul]
  -- Collapse the indicator `h g' = g` to `h = g g'⁻¹`.
  have hcol : ∀ g g' : G, ∀ f : G → ℂ, (∑ h, if h * g' = g then f h else 0) = f (g * g'⁻¹) :=
    fun g g' f => by
      simp_rw [← eq_mul_inv_iff_mul_eq]
      simp
  simp only [hcol]
  have hre : ∀ g' : G, (∑ g, (cA * (⅟(Fintype.card G : ℂ) *
      (LinearMap.toMatrix' (σA (g * g'⁻¹)) a a'))) *
      (cB * (⅟(Fintype.card G : ℂ) * (LinearMap.toMatrix' (σB (g * g'⁻¹)) b b')))) =
      ∑ h, (cA * (⅟(Fintype.card G : ℂ) * (LinearMap.toMatrix' (σA h) a a'))) *
        (cB * (⅟(Fintype.card G : ℂ) * (LinearMap.toMatrix' (σB h) b b'))) := fun g' =>
    Fintype.sum_equiv (Equiv.mulRight g'⁻¹) _ _ fun g => rfl
  rw [Finset.sum_comm]
  simp only [hre, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  linear_combination (cA * cB * ⅟(Fintype.card G : ℂ) * (LinearMap.toMatrix' (σA h) a a') *
    (LinearMap.toMatrix' (σB h) b b')) * hn

omit [Fintype κA] [Fintype κB] in
/-- Source: arXiv:1001.3807, proof of Lemma 5.2, `Papers/1001.3807/paper_v3.tex`
lines 1336–1337. If `𝒫(A)` is invariant under `σ_A ⊗ L` and `𝒫(B)` under `L ⊗ σ_B`, then
`𝒫(C)` is invariant under `σ_A ⊗ σ_B`: the actions on the contracted link cancel. -/
theorem linkContractionCoord_comp_kroneckerRep {σA : Representation ℂ G (α → ℂ)}
    {σB : Representation ℂ G (β → ℂ)} {TA : (α × G → ℂ) →ₗ[ℂ] (κA → ℂ)}
    {TB : (G × β → ℂ) →ₗ[ℂ] (κB → ℂ)} (hA : ∀ g, TA ∘ₗ kroneckerRep σA leftRegularFun g = TA)
    (hB : ∀ g, TB ∘ₗ kroneckerRep leftRegularFun σB g = TB) (g : G) :
    linkContractionCoord TA TB ∘ₗ kroneckerRep σA σB g = linkContractionCoord TA TB := by
  have eA : ∀ k a' h', ∑ a, LinearMap.toMatrix' TA k (a, g * h') *
      LinearMap.toMatrix' (σA g) a a' = LinearMap.toMatrix' TA k (a', h') := by
    intro k a' h'
    have := congrFun (congrFun (congrArg LinearMap.toMatrix' (hA g)) k) (a', h')
    rw [LinearMap.toMatrix'_comp, toMatrix'_kroneckerRep, Matrix.mul_apply] at this
    simpa only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, toMatrix'_leftRegularFun,
      mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using this
  have eB : ∀ l b' h', ∑ b, LinearMap.toMatrix' TB l (g * h', b) *
      LinearMap.toMatrix' (σB g) b b' = LinearMap.toMatrix' TB l (h', b') := by
    intro l b' h'
    have := congrFun (congrFun (congrArg LinearMap.toMatrix' (hB g)) l) (h', b')
    rw [LinearMap.toMatrix'_comp, toMatrix'_kroneckerRep, Matrix.mul_apply] at this
    simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, toMatrix'_leftRegularFun,
      mul_ite, ite_mul, mul_zero, one_mul, zero_mul] at this
    rw [Finset.sum_comm] at this
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] using this
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_comp, linkContractionCoord, LinearMap.toMatrix'_toLin',
    toMatrix'_kroneckerRep]
  ext ⟨k, l⟩ ⟨a', b'⟩
  simp only [Matrix.mul_apply, linkContractionMatrix, Matrix.of_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  calc ∑ a, ∑ b, (∑ h, LinearMap.toMatrix' TA k (a, h) * LinearMap.toMatrix' TB l (h, b)) *
        (LinearMap.toMatrix' (σA g) a a' * LinearMap.toMatrix' (σB g) b b')
      = ∑ h, (∑ a, LinearMap.toMatrix' TA k (a, h) * LinearMap.toMatrix' (σA g) a a') *
          (∑ b, LinearMap.toMatrix' TB l (h, b) * LinearMap.toMatrix' (σB g) b b') := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Fintype.sum_reverse_three]
        refine Finset.sum_congr rfl fun h _ => ?_
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ h', (∑ a, LinearMap.toMatrix' TA k (a, g * h') * LinearMap.toMatrix' (σA g) a a') *
          (∑ b, LinearMap.toMatrix' TB l (g * h', b) * LinearMap.toMatrix' (σB g) b b') :=
        (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ => rfl).symm
    _ = _ := by simp only [eA, eB]
/-- Source: arXiv:1001.3807, proof of Lemma 6.2, `Papers/1001.3807/paper_v3.tex`
lines 1709–1713. With unitary representations `σ_A`, `σ_B` on the remaining legs and the
left-regular representation on the contracted link, if `⟪𝒫(A) u, 𝒫(A) v⟫ = c_A ⟪u, v⟫` and
`⟪𝒫(B) u, 𝒫(B) v⟫ = c_B ⟪u, v⟫` on invariant vectors, then
`⟪𝒫(C) x, 𝒫(C) y⟫ = c_A c_B ⟪x, Π y⟫` for all `x`, `y`. -/
theorem star_linkContractionCoord_dotProduct {σA : Representation ℂ G (α → ℂ)}
    {σB : Representation ℂ G (β → ℂ)}
    (hσA : ∀ g, LinearMap.toMatrix' (σA g) ∈ Matrix.unitaryGroup α ℂ)
    (hσB : ∀ g, LinearMap.toMatrix' (σB g) ∈ Matrix.unitaryGroup β ℂ)
    {TA : (α × G → ℂ) →ₗ[ℂ] (κA → ℂ)} {TB : (G × β → ℂ) →ₗ[ℂ] (κB → ℂ)}
    (hAinv : ∀ g, TA ∘ₗ kroneckerRep σA leftRegularFun g = TA)
    (hBinv : ∀ g, TB ∘ₗ kroneckerRep leftRegularFun σB g = TB) {cA cB : ℂ}
    (hcA : ∀ x ∈ (kroneckerRep σA leftRegularFun).invariants,
      ∀ y ∈ (kroneckerRep σA leftRegularFun).invariants, star (TA x) ⬝ᵥ TA y = cA * (star x ⬝ᵥ y))
    (hcB : ∀ x ∈ (kroneckerRep leftRegularFun σB).invariants,
      ∀ y ∈ (kroneckerRep leftRegularFun σB).invariants, star (TB x) ⬝ᵥ TB y = cB * (star x ⬝ᵥ y))
    (x y : α × β → ℂ) :
    star (linkContractionCoord TA TB x) ⬝ᵥ linkContractionCoord TA TB y =
      (cA * cB) * (star x ⬝ᵥ (kroneckerRep σA σB).averageMap y) := by
  have hGA := conjTranspose_toMatrix'_mul_toMatrix'
    (toMatrix'_kroneckerRep_mem_unitaryGroup hσA toMatrix'_leftRegularFun_mem_unitaryGroup)
    hAinv hcA
  have hGB := conjTranspose_toMatrix'_mul_toMatrix'
    (toMatrix'_kroneckerRep_mem_unitaryGroup toMatrix'_leftRegularFun_mem_unitaryGroup hσB)
    hBinv hcB
  have hG := conjTranspose_linkContractionMatrix_mul_eq hGA hGB
  rw [linkContractionCoord, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hG,
    Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec, dotProduct_smul, smul_eq_mul]

/-- Source: arXiv:1001.3807, proof of Lemma 6.2, `Papers/1001.3807/paper_v3.tex`
lines 1709–1713. Under the hypotheses of `star_linkContractionCoord_dotProduct`, the left inverse
of the contracted tensor is its adjoint: `𝒫(C)† 𝒫(C) = c_A c_B Π`, so
`𝒫(C)⁻¹ = (c_A c_B)⁻¹ 𝒫(C)†`, the adjoint of the contraction being the contraction of the
adjoints. -/
theorem toLin'_conjTranspose_comp_linkContractionCoord [DecidableEq κA] [DecidableEq κB]
    {σA : Representation ℂ G (α → ℂ)}
    {σB : Representation ℂ G (β → ℂ)}
    (hσA : ∀ g, LinearMap.toMatrix' (σA g) ∈ Matrix.unitaryGroup α ℂ)
    (hσB : ∀ g, LinearMap.toMatrix' (σB g) ∈ Matrix.unitaryGroup β ℂ)
    {TA : (α × G → ℂ) →ₗ[ℂ] (κA → ℂ)} {TB : (G × β → ℂ) →ₗ[ℂ] (κB → ℂ)}
    (hAinv : ∀ g, TA ∘ₗ kroneckerRep σA leftRegularFun g = TA)
    (hBinv : ∀ g, TB ∘ₗ kroneckerRep leftRegularFun σB g = TB) {cA cB : ℂ}
    (hcA : ∀ x ∈ (kroneckerRep σA leftRegularFun).invariants,
      ∀ y ∈ (kroneckerRep σA leftRegularFun).invariants, star (TA x) ⬝ᵥ TA y = cA * (star x ⬝ᵥ y))
    (hcB : ∀ x ∈ (kroneckerRep leftRegularFun σB).invariants,
      ∀ y ∈ (kroneckerRep leftRegularFun σB).invariants, star (TB x) ⬝ᵥ TB y = cB * (star x ⬝ᵥ y)) :
    Matrix.toLin' (linkContractionMatrix (LinearMap.toMatrix' TA) (LinearMap.toMatrix' TB))ᴴ ∘ₗ
        linkContractionCoord TA TB = (cA * cB) • (kroneckerRep σA σB).averageMap := by
  have hGA := conjTranspose_toMatrix'_mul_toMatrix'
    (toMatrix'_kroneckerRep_mem_unitaryGroup hσA toMatrix'_leftRegularFun_mem_unitaryGroup)
    hAinv hcA
  have hGB := conjTranspose_toMatrix'_mul_toMatrix'
    (toMatrix'_kroneckerRep_mem_unitaryGroup toMatrix'_leftRegularFun_mem_unitaryGroup hσB)
    hBinv hcB
  rw [linkContractionCoord, ← Matrix.toLin'_mul, conjTranspose_linkContractionMatrix_mul_eq hGA hGB,
    map_smul, Matrix.toLin'_toMatrix']

/-- Source: arXiv:1001.3807, Lemma 6.2 (stability of isometry under concatenation),
`Papers/1001.3807/paper_v3.tex` lines 1704–1716, for the contraction of one link of two PEPS
tensors. If `𝒫(A)` is `G`-isometric for `σ_A ⊗ L` and `𝒫(B)` for `L ⊗ σ_B`, with the
left-regular representation `L` on the contracted link and unitary representations on the
remaining legs, then the contracted tensor `C` is `G`-isometric for `σ_A ⊗ σ_B`, with the
factors multiplying, `⟪𝒫(C) x, 𝒫(C) y⟫ = c_A c_B ⟪x, y⟫` on invariant vectors. -/
theorem IsGIsometric.linkContractionCoord {σA : Representation ℂ G (α → ℂ)}
    {σB : Representation ℂ G (β → ℂ)}
    (hσA : ∀ g, LinearMap.toMatrix' (σA g) ∈ Matrix.unitaryGroup α ℂ)
    (hσB : ∀ g, LinearMap.toMatrix' (σB g) ∈ Matrix.unitaryGroup β ℂ)
    {TA : (α × G → ℂ) →ₗ[ℂ] (κA → ℂ)} {TB : (G × β → ℂ) →ₗ[ℂ] (κB → ℂ)}
    (hA : IsGIsometric (kroneckerRep σA leftRegularFun) TA)
    (hB : IsGIsometric (kroneckerRep leftRegularFun σB) TB) :
    IsGIsometric (kroneckerRep σA σB) (PEPS.linkContractionCoord TA TB) := by
  obtain ⟨cA, hcA, hA'⟩ := hA.exists_inner_eq
  obtain ⟨cB, hcB, hB'⟩ := hB.exists_inner_eq
  have key : ∀ x, ∀ y ∈ (kroneckerRep σA σB).invariants,
      star (PEPS.linkContractionCoord TA TB x) ⬝ᵥ PEPS.linkContractionCoord TA TB y =
        ((cA * cB : ℝ) : ℂ) * (star x ⬝ᵥ y) := fun x y hy => by
    rw [star_linkContractionCoord_dotProduct hσA hσB hA.invariant hB.invariant hA' hB',
      averageMap_id _ y hy, Complex.ofReal_mul]
  refine ⟨⟨linkContractionCoord_comp_kroneckerRep hA.invariant hB.invariant, fun x hx h0 => ?_⟩,
    cA * cB, mul_pos hcA hcB, fun x _ y hy => key x y hy⟩
  have hc : ((cA * cB : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (mul_pos hcA hcB).ne'
  have h := key x x hx
  rw [h0, star_zero, zero_dotProduct, eq_comm, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h hc
  · exact dotProduct_star_self_eq_zero.1 h

end Link

section Bridge

/-- The element `∑_i e_i^* ⊗ e_i` of `E^* ⊗ E` is the identity of `E`. -/
theorem dualTensorHom_sum_coord_tmul {E κ : Type*} [AddCommGroup E] [Module ℂ E] [Fintype κ]
    (d : Basis κ ℂ E) : dualTensorHom ℂ E E (∑ i, d.coord i ⊗ₜ d i) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [map_sum, LinearMap.sum_apply, dualTensorHom_apply, Basis.coord_apply,
    LinearMap.id_apply]
  exact d.sum_repr x

/-- The link vector in any finite basis: `∑_i e_i^* ⊗ e_i`. -/
theorem linkVector_eq_sum_basis {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [Fintype ι] (b : Basis ι ℂ E) :
    (linkVector : Module.Dual ℂ E ⊗[ℂ] E) = ∑ i, b.coord i ⊗ₜ b i := by
  classical
  apply (dualTensorHomEquivOfBasis (N := E) b).injective
  have hlv : (linkVector : Module.Dual ℂ E ⊗[ℂ] E) =
      ∑ i, (Basis.ofVectorSpace ℂ E).coord i ⊗ₜ (Basis.ofVectorSpace ℂ E) i := by
    rw [linkVector, coevaluation_apply_one, map_sum]
    rfl
  simp only [dualTensorHomEquivOfBasis_apply]
  rw [hlv, dualTensorHom_sum_coord_tmul, dualTensorHom_sum_coord_tmul]

variable [Fintype G] [DecidableEq G] {α β κA κB : Type*} [Fintype α] [Fintype β] [DecidableEq α]
  [DecidableEq β] [Fintype κA] [Fintype κB]

/-- Coordinates of the virtual system `W_A ⊗ ℂ[G]^*` of `A`, with `W_A = ℂ^α` and the dual
basis of the group elements on the outgoing link: `e_{(a, g)} ↦ e_a ⊗ ⟨g|`. -/
noncomputable def linkLeftCoord :
    (α × G → ℂ) →ₗ[ℂ] (α → ℂ) ⊗[ℂ] Module.Dual ℂ (MonoidAlgebra ℂ G) :=
  (Pi.basisFun ℂ (α × G)).constr ℂ fun p =>
    Pi.single p.1 1 ⊗ₜ (MonoidAlgebra.basis G ℂ).coord p.2

/-- Coordinates of the virtual system `ℂ[G] ⊗ W_B` of `B`: `e_{(g, b)} ↦ |g⟩ ⊗ e_b`. -/
noncomputable def linkRightCoord :
    (G × β → ℂ) →ₗ[ℂ] MonoidAlgebra ℂ G ⊗[ℂ] (β → ℂ) :=
  (Pi.basisFun ℂ (G × β)).constr ℂ fun p => MonoidAlgebra.basis G ℂ p.1 ⊗ₜ Pi.single p.2 1

/-- Coordinates of `W_A ⊗ W_B`: `e_{(a, b)} ↦ e_a ⊗ e_b`. -/
noncomputable def pairCoord : (α × β → ℂ) →ₗ[ℂ] (α → ℂ) ⊗[ℂ] (β → ℂ) :=
  (Pi.basisFun ℂ (α × β)).constr ℂ fun p => Pi.single p.1 1 ⊗ₜ Pi.single p.2 1

omit [Group G] in
@[simp]
theorem linkLeftCoord_single (p : α × G) :
    linkLeftCoord (Pi.single p 1) = Pi.single p.1 1 ⊗ₜ (MonoidAlgebra.basis G ℂ).coord p.2 := by
  rw [← Pi.basisFun_apply, linkLeftCoord, Basis.constr_basis]

omit [Group G] in
@[simp]
theorem linkRightCoord_single (p : G × β) :
    linkRightCoord (Pi.single p 1) = MonoidAlgebra.basis G ℂ p.1 ⊗ₜ Pi.single p.2 1 := by
  rw [← Pi.basisFun_apply, linkRightCoord, Basis.constr_basis]

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem pairCoord_single (p : α × β) :
    pairCoord (Pi.single p 1) = Pi.single p.1 1 ⊗ₜ Pi.single p.2 1 := by
  rw [← Pi.basisFun_apply, pairCoord, Basis.constr_basis]

/-- The coordinates of a product vector, `u ⊗ v ↦ (u_k v_l)_{(k, l)}`. -/
noncomputable def tensorCoord : (κA → ℂ) ⊗[ℂ] (κB → ℂ) →ₗ[ℂ] (κA × κB → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun u v p => u p.1 * v p.2)
    (fun _ _ _ => funext fun _ => by simp [add_mul])
    (fun _ _ _ => funext fun _ => by simp [mul_assoc])
    (fun _ _ _ => funext fun _ => by simp [mul_add])
    (fun _ _ _ => funext fun _ => by simp [mul_left_comm]))

omit [Fintype κA] [Fintype κB] in
@[simp]
theorem tensorCoord_tmul (u : κA → ℂ) (v : κB → ℂ) (p : κA × κB) :
    tensorCoord (u ⊗ₜ v) p = u p.1 * v p.2 :=
  rfl

omit [Group G] [Fintype κA] [Fintype κB] in
/-- Bridge: in the bases of group elements on the contracted link and the coordinate bases of
the remaining legs and the physical systems, the contraction `linkContraction` of Lemma 5.2 is
`linkContractionCoord`. -/
theorem tensorCoord_comp_linkContraction_comp_pairCoord
    (TA : (α → ℂ) ⊗[ℂ] Module.Dual ℂ (MonoidAlgebra ℂ G) →ₗ[ℂ] (κA → ℂ))
    (TB : MonoidAlgebra ℂ G ⊗[ℂ] (β → ℂ) →ₗ[ℂ] (κB → ℂ)) :
    tensorCoord ∘ₗ linkContraction TA TB ∘ₗ pairCoord =
      linkContractionCoord (TA ∘ₗ linkLeftCoord) (TB ∘ₗ linkRightCoord) := by
  refine (Pi.basisFun ℂ (α × β)).ext fun p => funext fun q => ?_
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, pairCoord_single, linkContraction_tmul,
    linkVector_eq_sum_basis (MonoidAlgebra.basis G ℂ), map_sum, TensorProduct.map_tmul,
    linkContractionCoord, Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    linkContractionMatrix, Matrix.of_apply, LinearMap.toMatrix'_apply, linkLeftCoord_single,
    linkRightCoord_single, Finset.sum_apply, tensorCoord_tmul, TensorProduct.mk_apply,
    LinearMap.flip_apply]

omit [Fintype κA] [Fintype κB] in
/-- Bridge: in the coordinates `linkLeftCoord`, the representation `σ_A ⊗ L^*` of the virtual
system `W_A ⊗ ℂ[G]^*` of `A` (`U_g⁻¹` leaving the contracted leg) is `σ_A ⊗ L`: the
contragredient of a permutation representation has the same matrices in the dual basis. -/
theorem linkLeftCoord_comp_kroneckerRep (σA : Representation ℂ G (α → ℂ)) (g : G) :
    linkLeftCoord ∘ₗ kroneckerRep σA leftRegularFun g =
      (σA.tprod (leftRegular ℂ G).dual) g ∘ₗ linkLeftCoord := by
  refine (Pi.basisFun ℂ (α × G)).ext fun p => ?_
  have h1 : kroneckerRep σA leftRegularFun g (Pi.single p 1) =
      ∑ a', LinearMap.toMatrix' (σA g) a' p.1 • Pi.single (a', g * p.2) (1 : ℂ) := by
    funext q
    rw [← LinearMap.toMatrix'_mulVec, toMatrix'_kroneckerRep, Matrix.mulVec_single_one,
      Finset.sum_apply]
    simp only [Matrix.col_apply, Matrix.kroneckerMap_apply, toMatrix'_leftRegularFun,
      Pi.smul_apply, Pi.single_apply, Prod.ext_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hq : g * p.2 = q.2
    · simp [hq, eq_comm]
    · simp [hq, Ne.symm hq]
  have h2 : (∑ a', LinearMap.toMatrix' (σA g) a' p.1 • Pi.single a' (1 : ℂ)) =
      σA g (Pi.single p.1 1) := by
    funext a''
    simp [Finset.sum_apply, Pi.single_apply, LinearMap.toMatrix'_apply]
  have h3 : (MonoidAlgebra.basis G ℂ).coord (g * p.2) =
      Dual.transpose (R := ℂ) (leftRegular ℂ G g⁻¹) ((MonoidAlgebra.basis G ℂ).coord p.2) := by
    refine (MonoidAlgebra.basis G ℂ).ext fun k => ?_
    simp only [Dual.transpose_apply, LinearMap.comp_apply, Basis.coord_apply,
      MonoidAlgebra.basis_apply]
    simp only [MonoidAlgebra.basis, MonoidAlgebra.coeffLinearEquiv_apply,
      ofMulAction_single, smul_eq_mul, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      inv_mul_eq_iff_eq_mul]
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, linkLeftCoord_single, tprod_apply,
    TensorProduct.map_tmul, dual_apply, h1, map_sum, map_smul, linkLeftCoord_single, ← h3, ← h2,
    TensorProduct.sum_tmul, TensorProduct.smul_tmul']

omit [Fintype κA] [Fintype κB] [DecidableEq α] in
/-- Bridge: in the coordinates `linkRightCoord`, the representation `L ⊗ σ_B` of the virtual
system `ℂ[G] ⊗ W_B` of `B` (`U_g` entering the contracted leg) is `L ⊗ σ_B`. -/
theorem linkRightCoord_comp_kroneckerRep (σB : Representation ℂ G (β → ℂ)) (g : G) :
    linkRightCoord ∘ₗ kroneckerRep leftRegularFun σB g =
      ((leftRegular ℂ G).tprod σB) g ∘ₗ linkRightCoord := by
  refine (Pi.basisFun ℂ (G × β)).ext fun p => ?_
  have h1 : kroneckerRep leftRegularFun σB g (Pi.single p 1) =
      ∑ b', LinearMap.toMatrix' (σB g) b' p.2 • Pi.single (g * p.1, b') (1 : ℂ) := by
    funext q
    rw [← LinearMap.toMatrix'_mulVec, toMatrix'_kroneckerRep, Matrix.mulVec_single_one,
      Finset.sum_apply]
    simp only [Matrix.col_apply, Matrix.kroneckerMap_apply, toMatrix'_leftRegularFun,
      Pi.smul_apply, Pi.single_apply, Prod.ext_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul]
    by_cases hq : g * p.1 = q.1
    · simp [hq, eq_comm]
    · simp [hq, Ne.symm hq]
  have h2 : (∑ b', LinearMap.toMatrix' (σB g) b' p.2 • Pi.single b' (1 : ℂ)) =
      σB g (Pi.single p.2 1) := by
    funext b''
    simp [Finset.sum_apply, Pi.single_apply, LinearMap.toMatrix'_apply]
  have h3 : MonoidAlgebra.basis G ℂ (g * p.1) =
      leftRegular ℂ G g (MonoidAlgebra.basis G ℂ p.1) := by
    simp [MonoidAlgebra.basis_apply, ofMulAction_single, smul_eq_mul]
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, linkRightCoord_single, tprod_apply,
    TensorProduct.map_tmul, h1, map_sum, map_smul, ← h3, ← h2, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul]

omit [Fintype G] [Fintype κA] [Fintype κB] [DecidableEq G] in
/-- Bridge: in the coordinates `pairCoord`, the representation `σ_A ⊗ σ_B` of the virtual system
`W_A ⊗ W_B` of the contracted tensor is the Kronecker representation. -/
theorem pairCoord_comp_kroneckerRep (σA : Representation ℂ G (α → ℂ))
    (σB : Representation ℂ G (β → ℂ)) (g : G) :
    pairCoord ∘ₗ kroneckerRep σA σB g = (σA.tprod σB) g ∘ₗ pairCoord := by
  refine (Pi.basisFun ℂ (α × β)).ext fun p => ?_
  have h1 : kroneckerRep σA σB g (Pi.single p 1) =
      ∑ a', ∑ b', (LinearMap.toMatrix' (σA g) a' p.1 * LinearMap.toMatrix' (σB g) b' p.2) •
        Pi.single (a', b') (1 : ℂ) := by
    funext q
    rw [← LinearMap.toMatrix'_mulVec, toMatrix'_kroneckerRep, Matrix.mulVec_single_one,
      Finset.sum_apply]
    simp only [Matrix.col_apply, Matrix.kroneckerMap_apply, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply, Prod.ext_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single q.1 (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have h2 : ∀ (ρ : Representation ℂ G (α → ℂ)) (a : α),
      (∑ a', LinearMap.toMatrix' (ρ g) a' a • Pi.single a' (1 : ℂ)) = ρ g (Pi.single a 1) :=
    fun ρ a => funext fun a'' => by
      simp [Finset.sum_apply, Pi.single_apply, LinearMap.toMatrix'_apply]
  have h2' : (∑ b', LinearMap.toMatrix' (σB g) b' p.2 • Pi.single b' (1 : ℂ)) =
      σB g (Pi.single p.2 1) :=
    funext fun b'' => by simp [Finset.sum_apply, Pi.single_apply, LinearMap.toMatrix'_apply]
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, pairCoord_single, tprod_apply,
    TensorProduct.map_tmul, h1, map_sum, map_smul, ← h2, ← h2', TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  simp only [Finset.smul_sum, ← TensorProduct.smul_tmul', smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-- Source: arXiv:1001.3807, Lemma 6.2 (stability of isometry under concatenation),
`Papers/1001.3807/paper_v3.tex` lines 1704–1716, for the two-dimensional contraction
`linkContraction` of Lemma 5.2 along one link carrying the left-regular representation. If
`𝒫(A)` is `G`-isometric for `σ_A ⊗ L` and `𝒫(B)` for `L ⊗ σ_B`, in the coordinates of the bases of
group elements on the link, with unitary representations on the remaining legs, then the
contracted tensor is `G`-isometric for `σ_A ⊗ σ_B`, with the factors multiplying. -/
theorem IsGIsometric.linkContraction {σA : Representation ℂ G (α → ℂ)}
    {σB : Representation ℂ G (β → ℂ)}
    (hσA : ∀ g, LinearMap.toMatrix' (σA g) ∈ Matrix.unitaryGroup α ℂ)
    (hσB : ∀ g, LinearMap.toMatrix' (σB g) ∈ Matrix.unitaryGroup β ℂ)
    {TA : (α → ℂ) ⊗[ℂ] Module.Dual ℂ (MonoidAlgebra ℂ G) →ₗ[ℂ] (κA → ℂ)}
    {TB : MonoidAlgebra ℂ G ⊗[ℂ] (β → ℂ) →ₗ[ℂ] (κB → ℂ)}
    (hA : IsGIsometric (kroneckerRep σA leftRegularFun) (TA ∘ₗ linkLeftCoord))
    (hB : IsGIsometric (kroneckerRep leftRegularFun σB) (TB ∘ₗ linkRightCoord)) :
    IsGIsometric (kroneckerRep σA σB) (tensorCoord ∘ₗ PEPS.linkContraction TA TB ∘ₗ pairCoord) := by
  rw [tensorCoord_comp_linkContraction_comp_pairCoord]
  exact IsGIsometric.linkContractionCoord hσA hσB hA hB

end Bridge

end PEPS
end TNLean
