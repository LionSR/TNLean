/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PreBialgebra
import TNLean.MPS.MPDO.CompleteZipperFusionCoproduct
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# The fusion coproduct as a pre-bialgebra

The pair space $\bigoplus_{a,b}M_{\chi_a}\otimes M_{\chi_b}$, on which the fusion coproduct of
a complete zipper fusion family takes values, is the tensor square of the boundary space
$\mathcal B=\bigoplus_cM_{\chi_c}$: the tensor product distributes over the two finite direct
sums, and $M_{\chi_a}\otimes M_{\chi_b}\cong M_{\chi_a\chi_b}$ by the Kronecker product.  Read
through this identification, the fusion coproduct is a comultiplication
$\Delta:\mathcal B\to\mathcal B\otimes\mathcal B$ with
\[
  \Delta\big((T_c^{ik})_c\big)=\sum_j(T_c^{ij})_c\otimes(T_c^{jk})_c.
\]
It is multiplicative and coassociative, but it has no counit and $\Delta(1)$ is only the
support projector of the fusion tensors.  This is a pre-bialgebra in the sense of
arXiv:2204.05940, `mpo.tex`, lines 1409--1419, realized on the dual algebra.

The source starts from a coassociative coproduct and derives the associativity of the fusion
trees (`mpo.tex`, lines 1732--1787, equation `eq:associative`).  Here the direction is
reversed.  The coproduct is built from the fusion tensors and its coassociativity is proved
without the $F$-move: both iterated coproducts are linear, both send a letter to
$\sum_{j,k}T^{ij}\otimes T^{jk}\otimes T^{kl}$, and the letters span the boundary space.  This
is the argument of `mpo.tex`, lines 940--945 and 2001--2003, run backwards.

## Main definitions

* `CompleteZipperFusionFamily.tensorPairEquiv`: the algebra equivalence
  $\mathcal B\otimes\mathcal B\cong\bigoplus_{a,b}M_{\chi_a\chi_b}$.
* `CompleteZipperFusionFamily.comul`: the fusion coproduct with values in
  $\mathcal B\otimes\mathcal B$, a non-unital algebra homomorphism.
* `CompleteZipperFusionFamily.toPreBialgebra`: the resulting pre-bialgebra structure.

## Main statements

* `comul_letter`: $\Delta(T^{ik})=\sum_jT^{ij}\otimes T^{jk}$.
* `comul_coassoc`: coassociativity of the fusion coproduct.

## References

* arXiv:2204.05940, `mpo.tex`, lines 866--875, 1409--1419, 1655, 1732--1787, and 2003--2006.
* arXiv:2509.03600, section "MPO representations of bialgebras".
-/

open scoped Matrix BigOperators Kronecker TensorProduct
open Matrix

namespace MPOTensor

namespace CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

/-- The tensor square of the boundary space is the pair space:
$\big(\bigoplus_aM_{\chi_a}\big)\otimes\big(\bigoplus_bM_{\chi_b}\big)\cong
\bigoplus_{a,b}M_{\chi_a}\otimes M_{\chi_b}$, with each summand written through the Kronecker
product.  This identifies the codomain of the coproduct of arXiv:2204.05940, `mpo.tex`,
line 1655, with $\mathcal A^*\otimes\mathcal A^*$. -/
noncomputable def tensorPairEquiv :
    Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace ≃ₐ[ℂ] Fus.PairSpace :=
  (Algebra.TensorProduct.comm ℂ _ _).trans <|
    (Algebra.TensorProduct.piRight ℂ ℂ Fus.BoundarySpace
      fun a => Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ).trans <|
    AlgEquiv.piCongrRight fun _ => (Algebra.TensorProduct.comm ℂ _ _).trans <|
      (Algebra.TensorProduct.piRight ℂ ℂ _
        fun b => Matrix (Fin (Fus.bondDim b)) (Fin (Fus.bondDim b)) ℂ).trans <|
      AlgEquiv.piCongrRight fun _ => Matrix.kroneckerAlgEquiv _ _ ℂ

@[simp]
theorem tensorPairEquiv_tmul (X Y : Fus.BoundarySpace) (a b : Λ) :
    Fus.tensorPairEquiv (X ⊗ₜ Y) a b = X a ⊗ₖ Y b := by
  simp [tensorPairEquiv, Algebra.TensorProduct.piRight_tmul]

/-- **The fusion coproduct on the tensor square.**  The coproduct
$\Delta(X)_{ab}=\sum_{c,\mu}X^c_{ab,\mu}X_cX^{c+}_{ab,\mu}$ of `coproduct`, read in
$\mathcal B\otimes\mathcal B$ through `tensorPairEquiv`.  It is multiplicative but not unital.

Source: arXiv:2204.05940, `mpo.tex`, lines 1409--1419 and 1655 (equation
`eq:splitting_algebraic`). -/
noncomputable def comul :
    Fus.BoundarySpace →ₙₐ[ℂ] Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace where
  toFun X := Fus.tensorPairEquiv.symm (Fus.coproduct X)
  map_smul' r X := by simp
  map_zero' := by simp
  map_add' X Y := by simp
  map_mul' X Y := by simp [coproduct_mul]

@[simp]
theorem tensorPairEquiv_comul (X : Fus.BoundarySpace) :
    Fus.tensorPairEquiv (Fus.comul X) = Fus.coproduct X :=
  Fus.tensorPairEquiv.apply_symm_apply _

/-- **Letter formula.**  $\Delta(T^{ik})=\sum_jT^{ij}\otimes T^{jk}$ in
$\mathcal B\otimes\mathcal B$.

Source: arXiv:2204.05940, `mpo.tex`, lines 2003--2006 (equation `eq:MPO_tensor_product`). -/
theorem comul_letter (i k : Fin p) :
    Fus.comul (Fus.letter i k) = ∑ j, Fus.letter i j ⊗ₜ[ℂ] Fus.letter j k := by
  apply Fus.tensorPairEquiv.injective
  funext a b
  rw [tensorPairEquiv_comul, coproduct_letter, map_sum]
  simp [Finset.sum_apply, letter]

/-- **Coassociativity of the fusion coproduct.**
$(\Delta\otimes\mathrm{id})\circ\Delta=(\mathrm{id}\otimes\Delta)\circ\Delta$ on the boundary
space of a complete zipper fusion family, after reassociating the triple tensor product.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875 (coassociativity of a coalgebra), with the
coproduct of line 1655 and the letter identity of lines 2003--2006. -/
theorem comul_coassoc :
    TensorProduct.assoc ℂ Fus.BoundarySpace Fus.BoundarySpace Fus.BoundarySpace ∘ₗ
        (Fus.comul : Fus.BoundarySpace →ₗ[ℂ] Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace).rTensor
          Fus.BoundarySpace ∘ₗ
        (Fus.comul : Fus.BoundarySpace →ₗ[ℂ] Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace) =
      (Fus.comul : Fus.BoundarySpace →ₗ[ℂ] Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace).lTensor
          Fus.BoundarySpace ∘ₗ
        (Fus.comul : Fus.BoundarySpace →ₗ[ℂ] Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace) := by
  refine LinearMap.ext_on_range Fus.span_letter_eq_top fun ⟨i, l⟩ => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_ofClass,
    comul_letter, map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  exact Finset.sum_comm

/-- **The fusion pre-bialgebra.**  The boundary space of a complete zipper fusion family with
the fusion coproduct is a pre-bialgebra: the coproduct is multiplicative and coassociative,
while `coproduct_one` shows that it is not unital in general.

Source: arXiv:2204.05940, `mpo.tex`, lines 1409--1419, 1655 and 1708. -/
@[instance_reducible]
noncomputable def toPreBialgebra : PreBialgebra ℂ Fus.BoundarySpace where
  comul := Fus.comul
  coassoc := Fus.comul_coassoc

end CompleteZipperFusionFamily

end MPOTensor
