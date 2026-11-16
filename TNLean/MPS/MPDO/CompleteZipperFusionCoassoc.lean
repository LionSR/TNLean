/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PreBialgebra
import TNLean.MPS.MPDO.CompleteZipperFusionCoproduct
import QICLean.Algebra.TraceFormDuality
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
It is multiplicative and coassociative, and $\Delta(1)$ is only the support projector of the
fusion tensors.

The source's pre-bialgebra (arXiv:2204.05940, `mpo.tex`, Definition 4.1, lines 1409--1414) is
also a coalgebra with a counit (Definition 3.1, lines 866--875).  In the source the boundary
space is the dual algebra $\mathcal A^*$, whose counit is evaluation at the unit of
$\mathcal A$ (lines 880 and 1419), and the letters are the images of the matrix coefficients
$x\mapsto\phi(x)_{ik}$ of the physical representation $\phi$, which is a representation of the
unital algebra $\mathcal A$, so $\phi(1)=1$ (line 1421).  The counit is therefore the
functional with $\varepsilon(T^{ik})=\phi(1)_{ik}=\delta_{ik}$, and both counit laws follow
from the letter formula.  Any such functional is unique, since the letters span the boundary
space.  Every functional on the boundary space is a trace pairing
$X\mapsto\sum_c\operatorname{tr}(Y_cX_c)$, so the functional exists exactly when the identity
operator on one site is a one-site operator of the family,
$\sum_c\operatorname{tr}(Y_cT_c^{ik})=\delta_{ik}$; this holds when one block is the identity
operator, as for a bialgebra.  It also exists for every family whose letters are the images
$\psi(\phi_{ik})$ of the matrix coefficients of a unital representation $\phi$ under an
injective linear map $\psi$ from the dual algebra, and it is then $\psi(f)\mapsto f(1)$.

**Scope restriction (counit existence):** a complete zipper fusion family records the tensors
of arXiv:1511.08090, not the unital algebra $\mathcal A$, and its fields do not force the
functional $\varepsilon(T^{ik})=\delta_{ik}$ to be well defined; for instance, one block of
bond dimension one whose letters form a nonzero matrix $(T^{ik})_{ik}$ of square zero, with no
fusion channel, satisfies every field and has zero coproduct, which admits no counit.  The
pre-bialgebra structures `toPreBialgebra`, `toPreBialgebraOfUnitWitness` and
`toPreBialgebraOfDualRepresentation` therefore take, respectively, the functional, a one-site
identity witness, or a unital representation realizing the letters as arguments.  The source's
construction of the family from a pre-bialgebra, which would supply the last of these, is not
formalized.  Documented in `docs/paper-gaps/mrgscp22_pre_bialgebra_counit_scope.tex`.

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
* `CompleteZipperFusionFamily.identityBlockCounit`: the normalized trace of one block, a counit
  when that block is the identity operator.
* `CompleteZipperFusionFamily.toPreBialgebra`: the resulting pre-bialgebra structure, given a
  functional with $\varepsilon(T^{ik})=\delta_{ik}$.
* `CompleteZipperFusionFamily.tracePairing`: the functional
  $X\mapsto\sum_c\operatorname{tr}(Y_cX_c)$.
* `CompleteZipperFusionFamily.dualRepresentationCounit`: the counit $\psi(f)\mapsto f(1)$ of a
  family whose letters come from a unital representation.

## Main statements

* `comul_letter`: $\Delta(T^{ik})=\sum_jT^{ij}\otimes T^{jk}$.
* `comul_coassoc`: coassociativity of the fusion coproduct.
* `rTensor_counit_comp_comul`, `lTensor_counit_comp_comul`: the two counit laws for a functional
  with $\varepsilon(T^{ik})=\delta_{ik}$.
* `counit_unique`: such a functional is unique.
* `exists_tracePairing_eq`: every functional on the boundary space is a trace pairing.
* `exists_counit_iff`: a functional with $\varepsilon(T^{ik})=\delta_{ik}$ exists if and only if
  the identity operator on one site is a one-site operator of the family.
* `dualRepresentationCounit_letter`: the counit $\psi(f)\mapsto f(1)$ takes the values
  $\delta_{ik}$ on the letters.

## References

* arXiv:2204.05940, `mpo.tex`, lines 866--875, 880, 1070, 1084, 1409--1421, 1655,
  1732--1787, and 2003--2006.
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

Source: arXiv:2204.05940, `mpo.tex`, lines 1409--1414 and 1655 (equation
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

/-- **Left counit law.**  If a linear functional $\varepsilon$ on the boundary space takes the
values $\varepsilon(T^{ik})=\delta_{ik}$ on the letters, then
$(\varepsilon\otimes\mathrm{id})\circ\Delta=\mathrm{id}$.

In the source the boundary space is the dual algebra $\mathcal A^*$, its counit is
$f\mapsto f(1)$, and the letters are the matrix coefficients of the unital physical
representation, so this functional is the source's counit.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875 (Definition 3.1), 880 and 1419 (the counit
of $\mathcal A^*$ is evaluation at the unit), and 2003--2006 (equation
`eq:MPO_tensor_product`). -/
theorem rTensor_counit_comp_comul (ε : Fus.BoundarySpace →ₗ[ℂ] ℂ)
    (hε : ∀ i k : Fin p, ε (Fus.letter i k) = if i = k then 1 else 0) :
    ε.rTensor Fus.BoundarySpace ∘ₗ
        (Fus.comul : Fus.BoundarySpace →ₗ[ℂ] Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace) =
      TensorProduct.mk ℂ ℂ Fus.BoundarySpace 1 := by
  refine LinearMap.ext_on_range Fus.span_letter_eq_top fun ⟨i, k⟩ => ?_
  simp [comul_letter, hε, TensorProduct.ite_tmul]

/-- **Right counit law.**  If a linear functional $\varepsilon$ on the boundary space takes the
values $\varepsilon(T^{ik})=\delta_{ik}$ on the letters, then
$(\mathrm{id}\otimes\varepsilon)\circ\Delta=\mathrm{id}$.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875 (Definition 3.1), 880 and 1419, and
2003--2006 (equation `eq:MPO_tensor_product`). -/
theorem lTensor_counit_comp_comul (ε : Fus.BoundarySpace →ₗ[ℂ] ℂ)
    (hε : ∀ i k : Fin p, ε (Fus.letter i k) = if i = k then 1 else 0) :
    ε.lTensor Fus.BoundarySpace ∘ₗ
        (Fus.comul : Fus.BoundarySpace →ₗ[ℂ] Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace) =
      (TensorProduct.mk ℂ Fus.BoundarySpace ℂ).flip 1 := by
  refine LinearMap.ext_on_range Fus.span_letter_eq_top fun ⟨i, k⟩ => ?_
  simp [comul_letter, hε, TensorProduct.tmul_ite]

/-- **Uniqueness of the counit.**  A linear functional on the boundary space is determined by
its values on the letters; in particular there is at most one functional with
$\varepsilon(T^{ik})=\delta_{ik}$.

Source: arXiv:2204.05940, `mpo.tex`, lines 1182 (injectivity of the physical representation)
and 1419. -/
theorem counit_unique (ε ε' : Fus.BoundarySpace →ₗ[ℂ] ℂ)
    (hε : ∀ i k : Fin p, ε (Fus.letter i k) = if i = k then 1 else 0)
    (hε' : ∀ i k : Fin p, ε' (Fus.letter i k) = if i = k then 1 else 0) :
    ε = ε' :=
  LinearMap.ext_on_range Fus.span_letter_eq_top fun ⟨i, k⟩ => by
    simp only [hε, hε']

/-- The normalized trace $X\mapsto\chi_{c_0}^{-1}\operatorname{tr}X_{c_0}$ of the block with
label $c_0$. -/
noncomputable def identityBlockCounit (c₀ : Λ) : Fus.BoundarySpace →ₗ[ℂ] ℂ where
  toFun X := (Fus.bondDim c₀ : ℂ)⁻¹ * (X c₀).trace
  map_add' X Y := by simp [Matrix.trace_add, mul_add]
  map_smul' r X := by
    simp only [Pi.smul_apply, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    ring

/-- **A counit from an identity block.**  If the block with label $c_0$ is the identity operator,
$T_{c_0}^{ik}=\delta_{ik}\mathbb 1$, then its normalized trace takes the values
$\delta_{ik}$ on the letters.  For a bialgebra, the evaluation at the unit is a one-dimensional
representation of the dual algebra, and its block is such an identity block.

Source: arXiv:2204.05940, `mpo.tex`, lines 880 and 1419. -/
theorem identityBlockCounit_letter (c₀ : Λ)
    (h : ∀ i k : Fin p, Fus.tensor c₀ i k = if i = k then 1 else 0) (i k : Fin p) :
    Fus.identityBlockCounit c₀ (Fus.letter i k) = if i = k then 1 else 0 := by
  have hD : (Fus.bondDim c₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fus.bondDim_pos c₀).ne'
  change (Fus.bondDim c₀ : ℂ)⁻¹ * (Fus.tensor c₀ i k).trace = _
  rw [h]
  split_ifs <;> simp [hD]

/-- **The fusion pre-bialgebra.**  The boundary space of a complete zipper fusion family, with
the fusion coproduct and a linear functional $\varepsilon$ taking the values
$\varepsilon(T^{ik})=\delta_{ik}$ on the letters as counit, is a pre-bialgebra: the coproduct is
coassociative and multiplicative and $\varepsilon$ satisfies both counit laws, while
`coproduct_one` shows that the coproduct is not unital in general.  By `counit_unique` the
counit is determined by the family.  The functional is an argument, because the fields of the
family do not force it to exist, as the module docstring records; in the source it is
evaluation at the unit of $\mathcal A$.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875, 1409--1421, 1655 and 1708. -/
@[instance_reducible]
noncomputable def toPreBialgebra (ε : Fus.BoundarySpace →ₗ[ℂ] ℂ)
    (hε : ∀ i k : Fin p, ε (Fus.letter i k) = if i = k then 1 else 0) :
    PreBialgebra ℂ Fus.BoundarySpace where
  comul := (Fus.comul : Fus.BoundarySpace →ₗ[ℂ] Fus.BoundarySpace ⊗[ℂ] Fus.BoundarySpace)
  counit := ε
  coassoc := Fus.comul_coassoc
  rTensor_counit_comp_comul := Fus.rTensor_counit_comp_comul ε hε
  lTensor_counit_comp_comul := Fus.lTensor_counit_comp_comul ε hε
  comul_mul := map_mul Fus.comul

/-! ### Existence of the counit -/

/-- The trace pairing $X\mapsto\sum_c\operatorname{tr}(Y_cX_c)$ of the boundary space with a
fixed boundary element $Y=(Y_c)_c$.  On a letter it is the one-site operator
$\sum_c\operatorname{tr}(Y_cT_c^{ik})$ of the family with boundary $Y$. -/
noncomputable def tracePairing (Y : Fus.BoundarySpace) : Fus.BoundarySpace →ₗ[ℂ] ℂ where
  toFun X := ∑ c, (Y c * X c).trace
  map_add' X X' := by simp [Matrix.mul_add, Matrix.trace_add, Finset.sum_add_distrib]
  map_smul' r X := by simp [Matrix.trace_smul, Finset.mul_sum]

theorem tracePairing_apply (Y X : Fus.BoundarySpace) :
    Fus.tracePairing Y X = ∑ c, (Y c * X c).trace :=
  rfl

/-- **Every functional on the boundary space is a trace pairing.**  For a linear functional
$\varepsilon$ on $\mathcal B=\bigoplus_cM_{\chi_c}$ there is a boundary element $Y$ with
$\varepsilon(X)=\sum_c\operatorname{tr}(Y_cX_c)$, because the block-indexed trace pairing is
nondegenerate. -/
theorem exists_tracePairing_eq (ε : Fus.BoundarySpace →ₗ[ℂ] ℂ) :
    ∃ Y : Fus.BoundarySpace, Fus.tracePairing Y = ε := by
  have hB := Matrix.piTraceForm_nondegenerate (n := fun c => Fin (Fus.bondDim c))
  refine ⟨((Matrix.piTraceForm _).toDual hB).symm ε, LinearMap.ext fun X => ?_⟩
  rw [tracePairing_apply, ← Matrix.piTraceForm_apply (n := fun c => Fin (Fus.bondDim c)),
    ← LinearMap.BilinForm.toDual_def hB, LinearEquiv.apply_symm_apply]

/-- **Existence criterion for the counit.**  A linear functional $\varepsilon$ on the boundary
space with $\varepsilon(T^{ik})=\delta_{ik}$ exists if and only if the identity operator on one
site is a one-site operator of the family: $\sum_c\operatorname{tr}(Y_cT_c^{ik})=\delta_{ik}$
for some boundary element $Y$.  The functional is then the trace pairing with $Y$.

In the source, $Y$ represents evaluation at the unit of $\mathcal A$ on the boundary algebra
$\mathcal A^*$, and the condition is $\phi(1)=\mathbb 1$ for the physical representation.

Source: arXiv:2204.05940, `mpo.tex`, lines 880, 1419 and 1421. -/
theorem exists_counit_iff :
    (∃ ε : Fus.BoundarySpace →ₗ[ℂ] ℂ,
        ∀ i k : Fin p, ε (Fus.letter i k) = if i = k then 1 else 0) ↔
      ∃ Y : Fus.BoundarySpace, ∀ i k : Fin p,
        ∑ c, (Y c * Fus.tensor c i k).trace = if i = k then 1 else 0 := by
  constructor
  · rintro ⟨ε, hε⟩
    obtain ⟨Y, rfl⟩ := Fus.exists_tracePairing_eq ε
    exact ⟨Y, hε⟩
  · rintro ⟨Y, hY⟩
    exact ⟨Fus.tracePairing Y, hY⟩

/-- **The fusion pre-bialgebra from a one-site identity.**  If the identity operator on one site
is the one-site operator of the family with boundary $Y$,
$\sum_c\operatorname{tr}(Y_cT_c^{ik})=\delta_{ik}$, then the trace pairing with $Y$ is the counit
of the fusion coproduct.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875, 1409--1421 and 1655. -/
@[instance_reducible]
noncomputable def toPreBialgebraOfUnitWitness (Y : Fus.BoundarySpace)
    (hY : ∀ i k : Fin p, ∑ c, (Y c * Fus.tensor c i k).trace = if i = k then 1 else 0) :
    PreBialgebra ℂ Fus.BoundarySpace :=
  Fus.toPreBialgebra (Fus.tracePairing Y) hY

section DualRepresentation

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- If the letters lie in the range of a linear map, that map is onto the boundary space, since
the letters span. -/
theorem surjective_of_forall_letter_mem_range {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : V →ₗ[ℂ] Fus.BoundarySpace) (h : ∀ i k : Fin p, Fus.letter i k ∈ LinearMap.range ψ) :
    Function.Surjective ψ := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← Fus.span_letter_eq_top, Submodule.span_le]
  rintro _ ⟨⟨i, k⟩, rfl⟩
  exact h i k

/-- **The source's counit.**  Let $\phi$ be a unital representation of the algebra
$\mathcal A$ on the physical space and let $\psi:\mathcal A^*\to\mathcal B$ be an injective
linear map sending each matrix coefficient $\phi_{ik}:x\mapsto\phi(x)_{ik}$ to the letter
$T^{ik}$.  Since the letters span, $\psi$ is a linear isomorphism, and the counit is evaluation
at the unit read through it, $\psi(f)\mapsto f(1)$.

Source: arXiv:2204.05940, `mpo.tex`, lines 880 and 1419 (the counit of $\mathcal A^*$ is
$f\mapsto f(1)$), 1070 and 1084 (the boundary algebra is $\mathcal A^*$ through the direct sum
$\psi$ of its irreducible representations), and 1421 (representations are unital). -/
noncomputable def dualRepresentationCounit (φ : A →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (ψ : Module.Dual ℂ A →ₗ[ℂ] Fus.BoundarySpace) (hψ : Function.Injective ψ)
    (hletter : ∀ i k : Fin p,
      ψ (Matrix.entryLinearMap ℂ ℂ i k ∘ₗ φ.toLinearMap) = Fus.letter i k) :
    Fus.BoundarySpace →ₗ[ℂ] ℂ :=
  Module.Dual.eval ℂ A 1 ∘ₗ
    (LinearEquiv.ofBijective ψ ⟨hψ, Fus.surjective_of_forall_letter_mem_range ψ
      fun i k => LinearMap.mem_range.2 ⟨_, hletter i k⟩⟩).symm.toLinearMap

/-- The counit of `dualRepresentationCounit` is evaluation at the unit: $\psi(f)\mapsto f(1)$.

Source: arXiv:2204.05940, `mpo.tex`, lines 880 and 1419. -/
theorem dualRepresentationCounit_apply (φ : A →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (ψ : Module.Dual ℂ A →ₗ[ℂ] Fus.BoundarySpace) (hψ : Function.Injective ψ)
    (hletter : ∀ i k : Fin p,
      ψ (Matrix.entryLinearMap ℂ ℂ i k ∘ₗ φ.toLinearMap) = Fus.letter i k)
    (f : Module.Dual ℂ A) :
    Fus.dualRepresentationCounit φ ψ hψ hletter (ψ f) = f 1 :=
  congrArg (Module.Dual.eval ℂ A 1) ((LinearEquiv.ofBijective ψ _).symm_apply_apply f)

/-- **Letter values of the source's counit.**  The counit $\psi(f)\mapsto f(1)$ takes the value
$\phi(1)_{ik}=\delta_{ik}$ on the letter $T^{ik}=\psi(\phi_{ik})$, because the physical
representation is unital.

Source: arXiv:2204.05940, `mpo.tex`, lines 1419 and 1421. -/
theorem dualRepresentationCounit_letter (φ : A →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (ψ : Module.Dual ℂ A →ₗ[ℂ] Fus.BoundarySpace) (hψ : Function.Injective ψ)
    (hletter : ∀ i k : Fin p,
      ψ (Matrix.entryLinearMap ℂ ℂ i k ∘ₗ φ.toLinearMap) = Fus.letter i k) (i k : Fin p) :
    Fus.dualRepresentationCounit φ ψ hψ hletter (Fus.letter i k) =
      if i = k then 1 else 0 := by
  rw [← hletter i k, dualRepresentationCounit_apply]
  simp [Matrix.one_apply]

/-- **The fusion pre-bialgebra of a family arising from a unital representation.**  If the
letters are the images $T^{ik}=\psi(\phi_{ik})$ of the matrix coefficients of a unital
representation $\phi$ of an algebra $\mathcal A$ under an injective linear map
$\psi:\mathcal A^*\to\mathcal B$, then the boundary space is a pre-bialgebra with the fusion
coproduct and the counit $\psi(f)\mapsto f(1)$, with no further argument.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875, 880, 1070, 1084, 1409--1421 and 1655. -/
@[instance_reducible]
noncomputable def toPreBialgebraOfDualRepresentation
    (φ : A →ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (ψ : Module.Dual ℂ A →ₗ[ℂ] Fus.BoundarySpace) (hψ : Function.Injective ψ)
    (hletter : ∀ i k : Fin p,
      ψ (Matrix.entryLinearMap ℂ ℂ i k ∘ₗ φ.toLinearMap) = Fus.letter i k) :
    PreBialgebra ℂ Fus.BoundarySpace :=
  Fus.toPreBialgebra (Fus.dualRepresentationCounit φ ψ hψ hletter)
    (Fus.dualRepresentationCounit_letter φ ψ hψ hletter)

end DualRepresentation

end CompleteZipperFusionFamily

end MPOTensor
