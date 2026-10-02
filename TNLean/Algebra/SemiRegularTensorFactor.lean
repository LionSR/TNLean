/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SemiRegularGroupAlgebra
import TNLean.Algebra.SemiRegularEquiv
import TNLean.Algebra.RepresentationTensorProduct

/-!
# Nonzero tensor factors of semi-regular representations

A semi-regular representation stays semi-regular after tensoring with any nonzero
finite-dimensional representation. The trace-dual functional of its first factor
extracts each group coefficient separately; the corresponding operator on the second
factor is invertible and therefore nonzero. Mathlib's equivalence between tensor
products of endomorphisms and endomorphisms of tensor products connects this
coefficient argument to the actual tensor-product representation.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 5.2,
`Papers/1001.3807/paper_v3.tex`, lines 1334–1336, and Lemma 4.6, lines 1015–1029.
The conclusion strengthens the source's tensor-product observation, which assumes
both factors semi-regular. It does not assert a graph contraction theorem.
-/

open Module LinearMap

open scoped TensorProduct
namespace Representation
variable {G V W : Type*} [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]

/-- Tensoring a semi-regular representation with any nonzero finite-dimensional
representation preserves semi-regularity. Unlike the invariant-vector argument, the
second factor need not contain the trivial representation. Source: algebraic extension
of the tensor-product step in SCP10, Lemma 5.2, lines 1334–1336, using the trace-dual
identity of Lemma 4.6, lines 1015–1029. -/
theorem IsSemiRegular.tprod_of_nontrivial {ρ : Representation ℂ G V} (hρ : ρ.IsSemiRegular)
    (σ : Representation ℂ G W) : (ρ.tprod σ).IsSemiRegular := by
  let _ := Fintype.ofFinite G
  classical
  apply isSemiRegular_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  let e := homTensorHomEquiv ℂ V W V W
  have ht : ∑ h : G, c h • (ρ h ⊗ₜ[ℂ] σ h) = 0 := by
    apply e.injective
    simpa only [map_sum, map_smul, map_zero, e, homTensorHomEquiv_apply,
      TensorProduct.homTensorHomMap_apply, tprod_apply] using hc
  let F : (Module.End ℂ V ⊗[ℂ] Module.End ℂ W) →ₗ[ℂ] Module.End ℂ W :=
    (_root_.TensorProduct.lid ℂ (Module.End ℂ W)).toLinearMap ∘ₗ
      TensorProduct.map (deltaPairing ρ g) LinearMap.id
  have hd := congrArg F ht
  simp only [map_sum, map_smul, map_zero, F, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    deltaPairing_rep_of_isSemiRegular ρ hρ, ite_smul, one_smul, zero_smul, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hd
  apply (smul_eq_zero.mp hd).resolve_right
  intro hzero
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  apply hw
  apply (σ.apply_bijective g).injective
  simp [hzero]
/-- A nonzero tensor factor may also be placed on the left. Source: the same
algebraic extension of the tensor-product step in SCP10, Lemma 5.2, lines 1334–1336. -/
theorem IsSemiRegular.tprod_left_of_nontrivial {ρ : Representation ℂ G V}
    (hρ : ρ.IsSemiRegular) (σ : Representation ℂ G W) :
    (σ.tprod ρ).IsSemiRegular :=
  (hρ.tprod_of_nontrivial σ).of_equiv (TensorProduct.comm ρ σ)

end Representation
