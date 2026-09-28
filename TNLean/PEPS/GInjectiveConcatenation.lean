/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationTensorProduct
import TNLean.PEPS.GInjective

/-!
# Stability of two-dimensional G-injectivity under concatenation

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Section 5,
`Papers/1001.3807/paper_v3.tex`:

* Definition 5.1 (`def:2d-Ug-inj`), lines 1278–1295, figures `figs3/ug-sym.pdf` and
  `figs3/linv.pdf`: a PEPS tensor `A` is `G`-injective for a semi-regular representation `U_g`
  if it is invariant under `U_g` on the virtual level (`U_g` entering the left and upper legs,
  `U_g⁻¹` leaving the right and lower legs) and `𝒫(A)` has a left inverse with
  `𝒫(A)⁻¹ 𝒫(A) = Π_U`. Lines 1310–1316: every link may carry its own representation, provided the
  two tensors on a link act with the same one.
* Lemma 5.2 (stability under concatenation), lines 1319–1344: for `G`-injective `A` and `B`, the
  tensor `C` obtained by contracting the right leg of `A` with the left leg of `B`
  (figure `figs3/c-eq-ab.pdf`), with the up, down and physical indices blocked, is
  `G`-injective, with the left inverse of figure `figs3/ab-inv.pdf`: the left inverses of `A` and
  `B` joined through `Δ` along the contracted link. The proof (figure `figs3/apply-ab-linv.pdf`)
  uses that `U_g ⊗ V_g` is semi-regular, that the actions on the inner link cancel, and
  `tr[U_g† U_h Δ] = δ_{g,h}` (Lemma 4.6).
* Observation 5.3, lines 1345–1356: contracting two legs of one connected block, such as the up
  leg of `A` with the down leg of `B`, keeps `G`-injectivity; the left inverse contracts the
  corresponding legs of the left inverse with any operator of nonzero trace, for instance `Δ`.

**Formalized here.** A tensor is its map `𝒫(A)` from the virtual to the physical system, and
`G`-injectivity is `TNLean.PEPS.IsGInjective`. A leg entered by `U_g` (left and up in
figure `figs3/ug-sym.pdf`) is a space `E` carrying `τ = U`; a leg left by `U_g⁻¹` (right and down)
is its dual `E^*` carrying the contragredient `τ^*`. For Lemma 5.2 the virtual system of `A` is
`W_A ⊗ E^*`, with `W_A` collecting its left, up and down legs and `E^*` its right leg, and that of
`B` is `E ⊗ W_B`, with `W_B` collecting its up, right and down legs; the group acts by
`σ_A ⊗ τ^*` and `τ ⊗ σ_B`, the same representation `τ` on both ends of the link, as lines
1310–1316 require. The contraction along the link is the pairing against
`∑_i e_i^* ⊗ e_i` (`linkVector`, `linkContraction`). The tensor `C` has virtual system
`W_A ⊗ W_B` with the action `σ_A ⊗ σ_B`; regrouping `W_A ⊗ W_B` into left, blocked up, right and
blocked down legs is a reordering of tensor factors. The left inverse of `figs3/ab-inv.pdf` is
`linkContractionLeftInverse`, and `linkContractionLeftInverse_comp` is the computation of
`figs3/apply-ab-linv.pdf`; of the semi-regularity assumed in Definition 5.1 it uses that of the
link representation `τ`, through Lemma 4.6. That the representation `σ_A ⊗ σ_B` of `C` is again
semi-regular is `Representation.IsSemiRegular.tprod`. Observation 5.3 is
`IsGInjective.legContraction`, with the left inverse `legContractionLeftInverse` for any operator
`M` of nonzero trace; the corollary takes the source's example `M = Δ`, whose trace is `1` for a
semi-regular representation.

The source omits normalizations in diagrams (line 936), so its `Π_U` in figure `figs3/linv.pdf`
is the plain group sum; here `Π_U = |G|⁻¹ ∑_g U_g` is Mathlib's averaging map, and the left
inverse of `figs3/ab-inv.pdf` carries the compensating factor `|G|`.

## Main definitions

* `TNLean.PEPS.linkVector`, `TNLean.PEPS.linkPairing`: the contraction of a leg `E^*` with a
  leg `E`, and its pairing through an operator.
* `TNLean.PEPS.linkContraction`: the tensor `C` of `figs3/c-eq-ab.pdf`.
* `TNLean.PEPS.linkContractionLeftInverse`: the left inverse of `figs3/ab-inv.pdf`.
* `TNLean.PEPS.legContraction`, `TNLean.PEPS.legContractionLeftInverse`: the contraction of two
  legs of one block and its left inverse (Observation 5.3).

## Main results

* `TNLean.PEPS.linkPairing_deltaOperator_map`: Lemma 4.6 on a contracted link.
* `TNLean.PEPS.linkContraction_comp_tprod`: `C` is invariant.
* `TNLean.PEPS.linkContractionLeftInverse_comp`: the left inverse of `figs3/ab-inv.pdf`.
* `TNLean.PEPS.IsGInjective.linkContraction`: Lemma 5.2.
* `TNLean.PEPS.legContractionLeftInverse_comp`, `TNLean.PEPS.IsGInjective.legContraction`:
  Observation 5.3.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap TensorProduct Representation

namespace TNLean
namespace PEPS

variable {G : Type*} [Group G]
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

/-- The link vector `∑_i e_i^* ⊗ e_i` of `E^* ⊗ E`: contracting a leg `E^*` with a leg `E` is
pairing against it. -/
noncomputable def linkVector : Module.Dual ℂ E ⊗[ℂ] E :=
  TensorProduct.comm ℂ E (Module.Dual ℂ E) (coevaluation ℂ E 1)

omit [FiniteDimensional ℂ E] in
theorem map_comm_apply {F : Type*} [AddCommGroup F] [Module ℂ F] (N : Module.End ℂ E)
    (K : Module.End ℂ F) (c : E ⊗[ℂ] F) :
    TensorProduct.map K N (TensorProduct.comm ℂ E F c) =
      TensorProduct.comm ℂ E F (TensorProduct.map N K c) := by
  induction c with
  | tmul e f => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- Source: arXiv:1001.3807, proof of Lemma 5.2, `Papers/1001.3807/paper_v3.tex`
lines 1336–1337. The link vector is invariant under `τ^*(g) ⊗ τ(g)`: the action `U_g⁻¹` leaving
one end of a link and `U_g` entering the other (figure `figs3/ug-sym.pdf`) cancel. -/
theorem map_dual_linkVector (τ : Representation ℂ G E) (g : G) :
    TensorProduct.map (τ.dual g) (τ g) linkVector = linkVector := by
  rw [linkVector, map_comm_apply, map_dual_coevaluation]

/-- The pairing `f ⊗ e ↦ f(M e)` of the two ends of a link through an operator `M`. -/
noncomputable def linkPairing (M : Module.End ℂ E) : Module.Dual ℂ E ⊗[ℂ] E →ₗ[ℂ] ℂ :=
  contractLeft ℂ E ∘ₗ TensorProduct.map LinearMap.id M

omit [FiniteDimensional ℂ E] in
@[simp]
theorem linkPairing_tmul (M : Module.End ℂ E) (f : Module.Dual ℂ E) (e : E) :
    linkPairing M (f ⊗ₜ e) = f (M e) := by
  simp [linkPairing, contractLeft_apply]

omit [FiniteDimensional ℂ E] in
theorem linkPairing_comm (M : Module.End ℂ E) (c : E ⊗[ℂ] Module.Dual ℂ E) :
    linkPairing M (TensorProduct.comm ℂ E (Module.Dual ℂ E) c) =
      contractRight ℂ E (TensorProduct.map M LinearMap.id c) := by
  induction c with
  | tmul e f => simp [contractRight_apply]
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- The link vector paired through `M` gives `tr M`. -/
theorem linkPairing_linkVector (M : Module.End ℂ E) :
    linkPairing M linkVector = LinearMap.trace ℂ E M := by
  rw [linkVector, linkPairing_comm, contractRight_map_coevaluation]

open Classical in
/-- Source: arXiv:1001.3807, Lemma 4.6, `Papers/1001.3807/paper_v3.tex` lines 1015–1029, in the
form used in figure `figs3/apply-ab-linv.pdf`: after the actions `U_g⁻¹` and `U_h` reach the two
ends of the contracted link, pairing them through `Δ` gives `tr[U_g† Δ U_h] = δ_{g,h}`. -/
theorem linkPairing_deltaOperator_map [Fintype G] {τ : Representation ℂ G E}
    (hτ : IsSemiRegular τ) (g h : G) :
    linkPairing (deltaOperator τ) (TensorProduct.map (τ.dual g) (τ h) linkVector) =
      if g = h then 1 else 0 := by
  rw [linkVector, map_comm_apply, linkPairing_comm, ← LinearMap.comp_apply (TensorProduct.map _ _),
    ← TensorProduct.map_comp, LinearMap.id_comp, contractRight_map_dual,
    contractRight_map_coevaluation]
  have key := trace_inv_comp_comp_deltaOperator_of_isSemiRegular τ hτ h⁻¹ g⁻¹
  rw [inv_inv, inv_inj, eq_comm (a := h)] at key
  rw [← key]
  simp only [← Module.End.mul_eq_comp]
  rw [← mul_assoc, LinearMap.trace_mul_comm]

section Concatenation

variable {WA WB PA PB : Type*} [AddCommGroup WA] [Module ℂ WA] [AddCommGroup WB] [Module ℂ WB]
  [AddCommGroup PA] [Module ℂ PA] [AddCommGroup PB] [Module ℂ PB]

/-- Source: arXiv:1001.3807, Lemma 5.2, `Papers/1001.3807/paper_v3.tex` lines 1322–1328
(equation `eq:2d:c-is-ab`, figure `figs3/c-eq-ab.pdf`). The map `𝒫(C)` of the tensor `C`
obtained by contracting the right leg of `A` (the factor `E^*` of its virtual system `W_A ⊗ E^*`)
with the left leg of `B` (the factor `E` of `E ⊗ W_B`), with the remaining legs and the physical
indices blocked: `𝒫(C)(x ⊗ y) = ∑_i 𝒫(A)(x ⊗ e_i^*) ⊗ 𝒫(B)(e_i ⊗ y)`. -/
noncomputable def linkContraction (TA : WA ⊗[ℂ] Module.Dual ℂ E →ₗ[ℂ] PA)
    (TB : E ⊗[ℂ] WB →ₗ[ℂ] PB) : WA ⊗[ℂ] WB →ₗ[ℂ] PA ⊗[ℂ] PB :=
  TensorProduct.lift
    (((TensorProduct.mapBilinear (RingHom.id ℂ) (Module.Dual ℂ E) E PA PB).compl₁₂
      ((TensorProduct.mk ℂ WA (Module.Dual ℂ E)).compr₂ TA)
      ((TensorProduct.mk ℂ E WB).flip.compr₂ TB)).compr₂
      (LinearMap.applyₗ linkVector))

theorem linkContraction_tmul (TA : WA ⊗[ℂ] Module.Dual ℂ E →ₗ[ℂ] PA)
    (TB : E ⊗[ℂ] WB →ₗ[ℂ] PB) (x : WA) (y : WB) :
    linkContraction TA TB (x ⊗ₜ y) =
      TensorProduct.map (TA ∘ₗ TensorProduct.mk ℂ WA (Module.Dual ℂ E) x)
        (TB ∘ₗ (TensorProduct.mk ℂ E WB).flip y) linkVector :=
  rfl

/-- Source: arXiv:1001.3807, proof of Lemma 5.2, `Papers/1001.3807/paper_v3.tex`
lines 1336–1337. If `𝒫(A)` is invariant under `σ_A ⊗ τ^*` and `𝒫(B)` under `τ ⊗ σ_B`, then
`𝒫(C)` is invariant under `σ_A ⊗ σ_B`: the actions on the inner link cancel. -/
theorem linkContraction_comp_tprod {σA : Representation ℂ G WA} {σB : Representation ℂ G WB}
    {τ : Representation ℂ G E} {TA : WA ⊗[ℂ] Module.Dual ℂ E →ₗ[ℂ] PA}
    {TB : E ⊗[ℂ] WB →ₗ[ℂ] PB} (hA : ∀ g, TA ∘ₗ (σA.tprod τ.dual) g = TA)
    (hB : ∀ g, TB ∘ₗ (τ.tprod σB) g = TB) (g : G) :
    linkContraction TA TB ∘ₗ (σA.tprod σB) g = linkContraction TA TB := by
  refine TensorProduct.ext' fun x y => ?_
  have hA' : TA ∘ₗ TensorProduct.mk ℂ WA (Module.Dual ℂ E) (σA g x) =
      (TA ∘ₗ TensorProduct.mk ℂ WA (Module.Dual ℂ E) x) ∘ₗ τ.dual g⁻¹ := by
    refine LinearMap.ext fun f => ?_
    have := LinearMap.congr_fun (hA g) (x ⊗ₜ τ.dual g⁻¹ f)
    simp only [LinearMap.comp_apply, tprod_apply, map_tmul, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply] at this
    simpa using this
  have hB' : TB ∘ₗ (TensorProduct.mk ℂ E WB).flip (σB g y) =
      (TB ∘ₗ (TensorProduct.mk ℂ E WB).flip y) ∘ₗ τ g⁻¹ := by
    refine LinearMap.ext fun e => ?_
    have := LinearMap.congr_fun (hB g) (τ g⁻¹ e ⊗ₜ y)
    simp only [LinearMap.comp_apply, tprod_apply, map_tmul, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply] at this
    simpa using this
  rw [LinearMap.comp_apply, tprod_apply, map_tmul, linkContraction_tmul, linkContraction_tmul,
    hA', hB', TensorProduct.map_comp, LinearMap.comp_apply, map_dual_linkVector]

/-- The contraction of the two inner legs of `(W_A ⊗ E^*) ⊗ (E ⊗ W_B)` through an operator `M`:
`(x ⊗ f) ⊗ (e ⊗ y) ↦ f(M e) (x ⊗ y)`. -/
noncomputable def innerContraction (M : Module.End ℂ E) :
    (WA ⊗[ℂ] Module.Dual ℂ E) ⊗[ℂ] (E ⊗[ℂ] WB) →ₗ[ℂ] WA ⊗[ℂ] WB :=
  TensorProduct.map LinearMap.id
      ((TensorProduct.lid ℂ WB).toLinearMap ∘ₗ TensorProduct.map (linkPairing M) LinearMap.id ∘ₗ
        (TensorProduct.assoc ℂ (Module.Dual ℂ E) E WB).symm.toLinearMap) ∘ₗ
    (TensorProduct.assoc ℂ WA (Module.Dual ℂ E) (E ⊗[ℂ] WB)).toLinearMap

omit [FiniteDimensional ℂ E] in
@[simp]
theorem innerContraction_tmul (M : Module.End ℂ E) (x : WA) (f : Module.Dual ℂ E) (e : E)
    (y : WB) :
    innerContraction M ((x ⊗ₜ f) ⊗ₜ (e ⊗ₜ y)) = f (M e) • (x ⊗ₜ[ℂ] y) := by
  simp [innerContraction, tmul_smul]

omit [FiniteDimensional ℂ E] in
theorem innerContraction_map (M : Module.End ℂ E) (x : WA) (y : WB)
    (N : Module.End ℂ (Module.Dual ℂ E)) (K : Module.End ℂ E) (c : Module.Dual ℂ E ⊗[ℂ] E) :
    innerContraction M (TensorProduct.map (TensorProduct.mk ℂ WA (Module.Dual ℂ E) x ∘ₗ N)
        ((TensorProduct.mk ℂ E WB).flip y ∘ₗ K) c) =
      linkPairing M (TensorProduct.map N K c) • (x ⊗ₜ[ℂ] y) := by
  induction c with
  | tmul f e => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂, add_smul]

variable [Fintype G]

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- Source: arXiv:1001.3807, Lemma 5.2, `Papers/1001.3807/paper_v3.tex` lines 1329–1332
(equation `eq:2d:ab-inv`, figure `figs3/ab-inv.pdf`). The left inverse of `𝒫(C)`: apply the left
inverses `L_A` and `L_B` of `𝒫(A)` and `𝒫(B)` and contract the two ends of the inner link
through `Δ`. The factor `|G|` compensates the normalization of `Π_U`, which the source omits in
diagrams. -/
noncomputable def linkContractionLeftInverse (τ : Representation ℂ G E)
    (LA : PA →ₗ[ℂ] WA ⊗[ℂ] Module.Dual ℂ E) (LB : PB →ₗ[ℂ] E ⊗[ℂ] WB) :
    PA ⊗[ℂ] PB →ₗ[ℂ] WA ⊗[ℂ] WB :=
  (Fintype.card G : ℂ) • (innerContraction (deltaOperator τ) ∘ₗ TensorProduct.map LA LB)

/-- Source: arXiv:1001.3807, proof of Lemma 5.2, `Papers/1001.3807/paper_v3.tex`
lines 1337–1343 (equation `eq:2d:linv-application`, figure `figs3/apply-ab-linv.pdf`). If
`L_A 𝒫(A) = Π_{σ_A ⊗ τ^*}` and `L_B 𝒫(B) = Π_{τ ⊗ σ_B}` and `τ` is semi-regular, then the left
inverse of `figs3/ab-inv.pdf` satisfies `C⁻¹ 𝒫(C) = Π_{σ_A ⊗ σ_B}`. The group elements `g` and
`h` reaching the two ends of the inner link are identified by Lemma 4.6,
`tr[U_g† Δ U_h] = δ_{g,h}`. -/
theorem linkContractionLeftInverse_comp {σA : Representation ℂ G WA}
    {σB : Representation ℂ G WB} {τ : Representation ℂ G E} (hτ : IsSemiRegular τ)
    {TA : WA ⊗[ℂ] Module.Dual ℂ E →ₗ[ℂ] PA} {TB : E ⊗[ℂ] WB →ₗ[ℂ] PB}
    {LA : PA →ₗ[ℂ] WA ⊗[ℂ] Module.Dual ℂ E} {LB : PB →ₗ[ℂ] E ⊗[ℂ] WB}
    (hA : LA ∘ₗ TA = (σA.tprod τ.dual).averageMap) (hB : LB ∘ₗ TB = (τ.tprod σB).averageMap) :
    linkContractionLeftInverse τ LA LB ∘ₗ linkContraction TA TB = (σA.tprod σB).averageMap := by
  classical
  refine TensorProduct.ext' fun x y => ?_
  have hA' : LA ∘ₗ TA ∘ₗ TensorProduct.mk ℂ WA (Module.Dual ℂ E) x =
      ⅟(Fintype.card G : ℂ) •
        ∑ g, TensorProduct.mk ℂ WA (Module.Dual ℂ E) (σA g x) ∘ₗ τ.dual g := by
    refine LinearMap.ext fun f => ?_
    rw [← LinearMap.comp_assoc, hA, LinearMap.comp_apply, averageMap_apply_eq_sum]
    simp [tprod_apply]
  have hB' : LB ∘ₗ TB ∘ₗ (TensorProduct.mk ℂ E WB).flip y =
      ⅟(Fintype.card G : ℂ) • ∑ h, (TensorProduct.mk ℂ E WB).flip (σB h y) ∘ₗ τ h := by
    refine LinearMap.ext fun e => ?_
    rw [← LinearMap.comp_assoc, hB, LinearMap.comp_apply, averageMap_apply_eq_sum]
    simp [tprod_apply]
  have hG : (Fintype.card G : ℂ) * ⅟(Fintype.card G : ℂ) = 1 := mul_invOf_self _
  rw [LinearMap.comp_apply, linkContraction_tmul, linkContractionLeftInverse, LinearMap.smul_apply,
    LinearMap.comp_apply, ← LinearMap.comp_apply (TensorProduct.map LA LB),
    ← TensorProduct.map_comp, hA', hB', ← TensorProduct.mapBilinear_apply]
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    TensorProduct.mapBilinear_apply, innerContraction_map, linkPairing_deltaOperator_map hτ,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, averageMap_apply_eq_sum, tprod_apply, map_tmul, smul_smul]
  simp only [hG, one_smul, ← Finset.smul_sum]

omit [Fintype G] in
/-- Source: arXiv:1001.3807, Lemma 5.2 (stability under concatenation),
`Papers/1001.3807/paper_v3.tex` lines 1319–1344, figures `figs3/c-eq-ab.pdf`,
`figs3/ab-inv.pdf` and `figs3/apply-ab-linv.pdf`. If `𝒫(A)` is `G`-injective for `σ_A ⊗ τ^*` and
`𝒫(B)` for `τ ⊗ σ_B`, with the representation `τ` of the contracted link semi-regular, then the
tensor `C` obtained by contracting the link is `G`-injective for `σ_A ⊗ σ_B`. When `σ_A` and `σ_B`
are semi-regular, so is `σ_A ⊗ σ_B` (`Representation.IsSemiRegular.tprod`), as Definition 5.1
requires. -/
theorem IsGInjective.linkContraction [Finite G] {σA : Representation ℂ G WA}
    {σB : Representation ℂ G WB} {τ : Representation ℂ G E} (hτ : IsSemiRegular τ)
    {TA : WA ⊗[ℂ] Module.Dual ℂ E →ₗ[ℂ] PA} {TB : E ⊗[ℂ] WB →ₗ[ℂ] PB}
    (hA : IsGInjective (σA.tprod τ.dual) TA) (hB : IsGInjective (τ.tprod σB) TB) :
    IsGInjective (σA.tprod σB) (PEPS.linkContraction TA TB) := by
  have := Fintype.ofFinite G
  obtain ⟨hAi, LA, hLA⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hA
  obtain ⟨hBi, LB, hLB⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hB
  exact (isGInjective_iff_exists_leftInverse _ _).2
    ⟨linkContraction_comp_tprod hAi hBi,
      linkContractionLeftInverse τ LA LB, linkContractionLeftInverse_comp hτ hLA hLB⟩

end Concatenation

section LegContraction

variable {W P : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]

/-- Source: arXiv:1001.3807, Observation 5.3, `Papers/1001.3807/paper_v3.tex` lines 1345–1350.
The map `𝒫` of a block whose virtual system is `W ⊗ (E^* ⊗ E)`, after contracting an outgoing
leg `E^*` with an incoming leg `E`: `x ↦ ∑_i 𝒫(x ⊗ e_i^* ⊗ e_i)`. -/
noncomputable def legContraction (T : W ⊗[ℂ] (Module.Dual ℂ E ⊗[ℂ] E) →ₗ[ℂ] P) : W →ₗ[ℂ] P :=
  T ∘ₗ (TensorProduct.mk ℂ W (Module.Dual ℂ E ⊗[ℂ] E)).flip linkVector

/-- Source: arXiv:1001.3807, Observation 5.3, `Papers/1001.3807/paper_v3.tex` lines 1350–1354.
The left inverse after contracting two legs: contract the corresponding legs of the left inverse
`L` with an operator `M`, normalized by `tr M`. -/
noncomputable def legContractionLeftInverse (M : Module.End ℂ E)
    (L : P →ₗ[ℂ] W ⊗[ℂ] (Module.Dual ℂ E ⊗[ℂ] E)) : P →ₗ[ℂ] W :=
  (LinearMap.trace ℂ E M)⁻¹ •
    ((TensorProduct.rid ℂ W).toLinearMap ∘ₗ TensorProduct.map LinearMap.id (linkPairing M) ∘ₗ L)

/-- Source: arXiv:1001.3807, Observation 5.3, `Papers/1001.3807/paper_v3.tex` lines 1345–1356.
Contracting two legs `E^*` and `E` of one block keeps invariance: the group elements attached to
the two legs cancel, as they belong to the same tensor. -/
theorem legContraction_comp {σ : Representation ℂ G W} {τ : Representation ℂ G E}
    {T : W ⊗[ℂ] (Module.Dual ℂ E ⊗[ℂ] E) →ₗ[ℂ] P}
    (hT : ∀ g, T ∘ₗ (σ.tprod (τ.dual.tprod τ)) g = T) (g : G) :
    legContraction T ∘ₗ σ g = legContraction T := by
  refine LinearMap.ext fun x => ?_
  have := LinearMap.congr_fun (hT g) (x ⊗ₜ linkVector)
  simp only [LinearMap.comp_apply, tprod_apply, map_tmul, map_dual_linkVector] at this
  simpa [legContraction] using this

/-- Source: arXiv:1001.3807, Observation 5.3, `Papers/1001.3807/paper_v3.tex` lines 1350–1356.
If `L 𝒫 = Π_{σ ⊗ τ^* ⊗ τ}` and `tr M ≠ 0`, then contracting the corresponding legs of `L` with `M`
gives a left inverse of the contracted block, `L' 𝒫' = Π_σ`. -/
theorem legContractionLeftInverse_comp [Fintype G] [Invertible (Fintype.card G : ℂ)]
    {σ : Representation ℂ G W} {τ : Representation ℂ G E}
    {T : W ⊗[ℂ] (Module.Dual ℂ E ⊗[ℂ] E) →ₗ[ℂ] P}
    {L : P →ₗ[ℂ] W ⊗[ℂ] (Module.Dual ℂ E ⊗[ℂ] E)}
    (hL : L ∘ₗ T = (σ.tprod (τ.dual.tprod τ)).averageMap) {M : Module.End ℂ E}
    (hM : LinearMap.trace ℂ E M ≠ 0) :
    legContractionLeftInverse M L ∘ₗ legContraction T = σ.averageMap := by
  refine LinearMap.ext fun x => ?_
  have h := LinearMap.congr_fun hL (x ⊗ₜ linkVector)
  simp only [LinearMap.comp_apply] at h
  simp only [legContractionLeftInverse, legContraction, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, h,
    averageMap_apply_eq_sum, tprod_apply, map_tmul, map_dual_linkVector, map_smul, map_sum,
    LinearMap.id_apply, linkPairing_linkVector, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    smul_smul]
  rw [← Finset.smul_sum, smul_smul, mul_right_comm, inv_mul_cancel₀ hM, one_mul]

attribute [local instance] Representation.invertibleFintypeCardComplex in
/-- Source: arXiv:1001.3807, Observation 5.3, `Papers/1001.3807/paper_v3.tex` lines 1345–1356.
If a block is `G`-injective for `σ ⊗ τ^* ⊗ τ`, with `τ` semi-regular as in Definition 5.1, then
contracting the two legs `E^*` and `E` gives a map that is `G`-injective for `σ`. The left inverse
contracts the corresponding legs of the left inverse of the block with `Δ`, whose trace is `1`
by Lemma 4.6. -/
theorem IsGInjective.legContraction [Finite G] {σ : Representation ℂ G W}
    {τ : Representation ℂ G E} (hτ : IsSemiRegular τ)
    {T : W ⊗[ℂ] (Module.Dual ℂ E ⊗[ℂ] E) →ₗ[ℂ] P}
    (hT : IsGInjective (σ.tprod (τ.dual.tprod τ)) T) :
    IsGInjective σ (PEPS.legContraction T) := by
  have := Fintype.ofFinite G
  obtain ⟨hTi, L, hL⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hT
  have hΔ : LinearMap.trace ℂ E (deltaOperator τ) = 1 := by
    have h := trace_inv_comp_comp_deltaOperator_of_isSemiRegular τ hτ 1 1
    rw [inv_one, map_one, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, one_mul,
      one_mul] at h
    simpa using h
  exact (isGInjective_iff_exists_leftInverse _ _).2
    ⟨legContraction_comp hTi, legContractionLeftInverse (deltaOperator τ) L,
      legContractionLeftInverse_comp hL (by rw [hΔ]; exact one_ne_zero)⟩

end LegContraction

end PEPS
end TNLean
