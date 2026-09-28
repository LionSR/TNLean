/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Coevaluation
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.SimpleModule.Rank
import TNLean.Algebra.RepresentationDelta

/-!
# Tensor products of semi-regular representations and the invariant link vector

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), proof of Lemma 5.2,
`Papers/1001.3807/paper_v3.tex` lines 1334–1343: for semi-regular representations `U_g` and
`V_g` (Definition 4.5, lines 1010–1013), `W_g = U_g ⊗ V_g` is again semi-regular, and when two
tensors share a link, the actions `U_g` and `U_g⁻¹` of the two ends of the link cancel
(figures `figs3/ug-sym.pdf` and `figs3/apply-ab-linv.pdf`).

**Formalized here.** A semi-regular representation contains the trivial representation, so it
has a nonzero invariant vector `v'`; for an irreducible `σ` occurring in `ρ` through `f`, the map
`x ↦ f x ⊗ v'` exhibits `σ` inside `ρ ⊗ ρ'` (`Representation.IsSemiRegular.tprod`). The source
suggests no proof; this argument uses only intertwining maps. A link joining two tensors is the
coevaluation vector `∑_i e_i ⊗ e_i^*` of `E ⊗ E^*`; it is invariant under `τ ⊗ τ^*`
(`Representation.map_dual_coevaluation`), which is the cancellation of the two actions on the
link, and pairing it through an operator `M` gives `tr M`
(`contractRight_map_coevaluation`).

## Main results

* `Representation.averageMap_apply_eq_sum`: `Π v = |G|⁻¹ ∑_g ρ(g) v`.
* `Representation.isIrreducible_of_finrank_eq_one`: a one-dimensional representation is
  irreducible.
* `Representation.IsSemiRegular.exists_mem_invariants_ne_zero`: a semi-regular representation
  has a nonzero invariant vector.
* `Representation.IsSemiRegular.tprod`: the tensor product of semi-regular representations is
  semi-regular.
* `Representation.map_dual_coevaluation`: the link vector is invariant under `τ ⊗ τ^*`.
* `contractRight_map_coevaluation`: `⟨e_i^*, M e_i⟩` summed over a basis is `tr M`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

universe u

open Module LinearMap TensorProduct

section Coevaluation

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

/-- The trace of an operator through the link vector:
`∑_i e_i^*(M e_i) = tr M`, for the coevaluation vector `∑_i e_i ⊗ e_i^*`. -/
theorem contractRight_map_coevaluation (M : Module.End ℂ E) :
    contractRight ℂ E (TensorProduct.map M LinearMap.id (coevaluation ℂ E 1)) =
      LinearMap.trace ℂ E M := by
  classical
  rw [coevaluation_apply_one, LinearMap.trace_eq_matrix_trace ℂ (Basis.ofVectorSpace ℂ E),
    Matrix.trace]
  simp [map_sum, contractRight_apply, LinearMap.toMatrix_apply, Basis.coord_apply]

variable {G : Type*} [Group G]

omit [FiniteDimensional ℂ E] in
/-- Moving a contragredient action across the pairing:
`⟨τ^*(h) f, N e⟩ = ⟨f, τ(h⁻¹) N e⟩`. -/
theorem contractRight_map_dual (τ : Representation ℂ G E) (N : Module.End ℂ E) (h : G)
    (c : E ⊗[ℂ] Module.Dual ℂ E) :
    contractRight ℂ E (TensorProduct.map N (τ.dual h) c) =
      contractRight ℂ E (TensorProduct.map (τ h⁻¹ ∘ₗ N) LinearMap.id c) := by
  induction c with
  | tmul e f => simp [contractRight_apply, Representation.dual_apply, Module.Dual.transpose_apply]
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- Source: arXiv:1001.3807, proof of Lemma 5.2, `Papers/1001.3807/paper_v3.tex`
lines 1336–1337 ("the action of the `U_g` on the inner link cancels"). The link vector
`∑_i e_i ⊗ e_i^*` is invariant under `τ(g) ⊗ τ^*(g)`: the action `U_g` entering one end of a
link and `U_g⁻¹` leaving the other end (figure `figs3/ug-sym.pdf`) cancel. -/
theorem Representation.map_dual_coevaluation (τ : Representation ℂ G E) (g : G) :
    TensorProduct.map (τ g) (τ.dual g) (coevaluation ℂ E 1) = coevaluation ℂ E 1 := by
  classical
  rw [coevaluation_apply_one]
  set b := Basis.ofVectorSpace ℂ E
  have hdual : ∀ i, τ.dual g (b.coord i) = ∑ j, b.coord i (τ g⁻¹ (b j)) • b.coord j := by
    intro i
    conv_lhs => rw [← b.sum_dual_apply_smul_coord (τ.dual g (b.coord i))]
    simp [Representation.dual_apply, Module.Dual.transpose_apply, Basis.coord_apply]
  have hcol : ∀ j, ∑ i, b.coord i (τ g⁻¹ (b j)) • τ g (b i) = b j := by
    intro j
    simp_rw [← map_smul, ← map_sum, Basis.coord_apply, b.sum_repr, ← Module.End.mul_apply,
      ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simp only [map_sum, map_tmul, hdual, tmul_sum, tmul_smul]
  rw [Finset.sum_comm]
  simp_rw [TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, hcol]

end Coevaluation

namespace Representation

/-- The averaging map as a group sum: `Π v = |G|⁻¹ ∑_g ρ(g) v`. -/
theorem averageMap_apply_eq_sum {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [Invertible (Fintype.card G : ℂ)] (ρ : Representation ℂ G V) (v : V) :
    ρ.averageMap v = ⅟(Fintype.card G : ℂ) • ∑ g, ρ g v := by
  simp [averageMap, GroupAlgebra.average, map_sum, Finset.smul_sum]

/-- A one-dimensional representation is irreducible. -/
theorem isIrreducible_of_finrank_eq_one {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (hV : finrank k V = 1) : ρ.IsIrreducible := by
  have : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.2 hV
  have hsub : ∀ S : Subrepresentation ρ, S.toSubmodule = ⊥ ∨ S.toSubmodule = ⊤ := fun S =>
    IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · rcases hsub S with h | h
    · exact Or.inl (Subrepresentation.ext h)
    · exact Or.inr (Subrepresentation.ext h)

section SemiRegular

variable {G : Type u} [Group G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Source: arXiv:1001.3807, Definition 4.5, `Papers/1001.3807/paper_v3.tex` lines 1010–1013.
A semi-regular representation contains the trivial representation, so it has a nonzero invariant
vector. -/
theorem IsSemiRegular.exists_mem_invariants_ne_zero {ρ : Representation ℂ G V}
    (hρ : IsSemiRegular ρ) : ∃ v ∈ ρ.invariants, v ≠ 0 := by
  have hdim : finrank ℂ (ULift.{u} ℂ) = 1 := by
    rw [ULift.moduleEquiv.finrank_eq, finrank_self]
  have : FiniteDimensional ℂ (ULift.{u} ℂ) := Module.finite_of_finrank_eq_succ hdim
  obtain ⟨f, hf⟩ := hρ (ULift.{u} ℂ) (trivial ℂ G (ULift.{u} ℂ))
    (isIrreducible_of_finrank_eq_one _ hdim)
  refine ⟨f ⟨1⟩, fun g => ?_, fun h0 => hf ?_⟩
  · have := LinearMap.congr_fun (f.isIntertwining' g) ⟨1⟩
    simpa using this.symm
  · ext ⟨c⟩
    have : (⟨c⟩ : ULift.{u} ℂ) = c • ⟨1⟩ := by ext; simp
    rw [this, map_smul]
    simp [h0]

/-- An irreducible representation occurring in `ρ` occurs in `ρ ⊗ ρ'` whenever `ρ'` has a nonzero
invariant vector `v'`: `x ↦ f x ⊗ v'` is a nonzero intertwining map. -/
theorem IsSemiRegular.tprod_of_mem_invariants {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G W} (hρ : IsSemiRegular ρ) {v' : W} (hv' : v' ∈ ρ'.invariants)
    (hv'0 : v' ≠ 0) : IsSemiRegular (ρ.tprod ρ') := by
  intro U _ _ _ σ hσ
  obtain ⟨f, hf⟩ := hρ U σ hσ
  refine ⟨⟨(TensorProduct.mk ℂ V W).flip v' ∘ₗ f.toLinearMap, fun g => ?_⟩, fun h0 => hf ?_⟩
  · refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun (f.isIntertwining' g) x
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, tprod_apply, TensorProduct.mk_apply, LinearMap.flip_apply,
      map_tmul, hv' g]
    exact congrArg (fun z => z ⊗ₜ[ℂ] v') this
  · obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ v' ≠ 0 := by
      by_contra! h
      exact hv'0 ((Module.forall_dual_apply_eq_zero_iff ℂ v').1 h)
    ext x
    have := congrArg (fun F : IntertwiningMap σ (ρ.tprod ρ') =>
      _root_.TensorProduct.rid ℂ V (_root_.TensorProduct.map LinearMap.id φ (F.toLinearMap x))) h0
    simpa [hφ] using this

/-- Source: arXiv:1001.3807, proof of Lemma 5.2, `Papers/1001.3807/paper_v3.tex`
lines 1334–1336. For semi-regular representations `U_g` and `V_g`, the tensor product
`W_g = U_g ⊗ V_g` is semi-regular. -/
theorem IsSemiRegular.tprod {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G W} (hρ : IsSemiRegular ρ) (hρ' : IsSemiRegular ρ') :
    IsSemiRegular (ρ.tprod ρ') := by
  obtain ⟨v', hv', hv'0⟩ := hρ'.exists_mem_invariants_ne_zero
  exact hρ.tprod_of_mem_invariants hv' hv'0

end SemiRegular

end Representation
