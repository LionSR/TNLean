import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Two-injective-tensor comparison for PEPS

This file records the source-facing finite-dimensional statement of the
two-tensor comparison used in the proof of the injective PEPS Fundamental
Theorem.

The statement is Lemma inj_equal_tensors_2 in
Molnár--Schuch--Verstraete--Cirac, arXiv:1804.04964, Section 3, lines
1068--1203 of Papers/1804.04964/paper_normal.tex: if two pairs of
injective tensors agree after inserting an arbitrary matrix on each shared
virtual bond, then the corresponding tensors differ by reciprocal nonzero
scalars.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {Bond : Type*} [Fintype Bond]
variable {bondDim : Bond → Type*} [∀ b, Fintype (bondDim b)]

/-! ### Abstract two-block tensors -/

/-- A configuration of the shared virtual bonds between two injective tensors.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, displayed
equation eq:lem_inj_eq_ten_2. The family `bondDim` indexes the virtual
spaces carried by the parallel shared bonds in that diagram. -/
abbrev SharedBondConfig (bondDim : Bond → Type*) : Type _ :=
  (b : Bond) → bondDim b

/-- A finite-dimensional tensor block with an external virtual boundary, a
shared virtual boundary, and a physical index.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, where each
of A_1,A_2,B_1,B_2 is an injective tensor. -/
abbrev TwoBlockTensor (bondDim : Bond → Type*) (External Physical : Type*) : Type _ :=
  External → SharedBondConfig bondDim → Physical → ℂ

/-- Two shared-bond configurations agree away from the distinguished bond.

Source: arXiv:1804.04964, Section 3, equation eq:lem_inj_eq_ten_2: inserting
a matrix `X` on one shared edge leaves all other shared virtual bonds
contracted by the identity. -/
def SameAwayFromBond (b : Bond)
    (η θ : SharedBondConfig bondDim) : Prop :=
  ∀ c : Bond, c ≠ b → η c = θ c

/-- The two-tensor coefficient obtained by inserting a matrix on one shared
virtual bond.

The summation has two shared-bond configurations, one on each side of the
inserted matrix. The factor `SameAwayFromBond b η θ` imposes identity
contraction on every other shared bond.

Source: arXiv:1804.04964, Section 3, equation eq:lem_inj_eq_ten_2. -/
noncomputable def twoBlockInsertedCoeff
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (b : Bond) (X : Matrix (bondDim b) (bondDim b) ℂ)
    (η₁ : External₁) (η₂ : External₂)
    (σ₁ : Physical₁) (σ₂ : Physical₂) : ℂ := by
  classical
  exact
    ∑ μ : SharedBondConfig bondDim,
      ∑ ν : SharedBondConfig bondDim,
        (if SameAwayFromBond b μ ν then X (μ b) (ν b) else 0) *
          A₁ η₁ μ σ₁ * A₂ η₂ ν σ₂

/-- Injectivity of a two-block tensor, expressed as linear independence of the
physical vectors indexed by all virtual boundary configurations.

This is the abstract form of injectivity used in arXiv:1804.04964, Section 3,
Lemma inj_equal_tensors_2. -/
def IsTwoBlockInjective
    {External Physical : Type*}
    (A : TwoBlockTensor bondDim External Physical) : Prop :=
  LinearIndependent ℂ
    (fun η : External × SharedBondConfig bondDim => fun σ : Physical => A η.1 η.2 σ)

/-- Equality of all one-bond matrix insertions for two pairs of injective
tensors.

Source: arXiv:1804.04964, Section 3, equation eq:lem_inj_eq_ten_2: for every
shared virtual bond and every matrix inserted on that bond, the two-tensor
contractions for the `A`-pair and the `B`-pair coincide. -/
def SameTwoBlockInsertions
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂) : Prop :=
  ∀ (b : Bond) (X : Matrix (bondDim b) (bondDim b) ℂ)
    (η₁ : External₁) (η₂ : External₂)
    (σ₁ : Physical₁) (σ₂ : Physical₂),
      twoBlockInsertedCoeff A₁ A₂ b X η₁ η₂ σ₁ σ₂ =
        twoBlockInsertedCoeff B₁ B₂ b X η₁ η₂ σ₁ σ₂

/-- Scalar proportionality of two tensor blocks with the same boundary spaces.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, conclusion
A_1 = λ B_1 and A_2 = λ^{-1} B_2. -/
def TwoBlockScalarProportional
    {External Physical : Type*}
    (A B : TwoBlockTensor bondDim External Physical) (c : ℂ) : Prop :=
  ∀ (η : External) (μ : SharedBondConfig bondDim) (σ : Physical),
    A η μ σ = c * B η μ σ

/-- Reciprocal scalar proportionality of the two tensor pairs in
Lemma inj_equal_tensors_2.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2. -/
def TwoBlockReciprocalScalarProportional
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂) : Prop :=
  ∃ c : ℂ,
    c ≠ 0 ∧
      TwoBlockScalarProportional A₁ B₁ c ∧
        TwoBlockScalarProportional A₂ B₂ c⁻¹

/-! ### Product cancellation after coefficient separation -/

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- Reciprocal scalar proportionality from separated pointwise products.

This auxiliary cancellation closes the comparison once the two pairs of blocks
satisfy the separated equality
$A_1(\eta_1,\mu,\sigma_1)A_2(\eta_2,\nu,\sigma_2)
= B_1(\eta_1,\mu,\sigma_1)B_2(\eta_2,\nu,\sigma_2)$ for all indices
independently.

**Scope restriction (separated product):** that separated equality is stronger
than the source hypothesis of Lemma inj_equal_tensors_2, which assumes equality
of one-bond insertions only. It follows from the conclusion
$A_1=\lambda B_1$, $A_2=\lambda^{-1}B_2$, so this lemma lies on the source path
only in the single-shared-bond case, where a matrix-unit insertion extracts the
separated product directly
(`two_injective_tensor_insertion_comparison_singletonBond`). In the
many-shared-bond case the source does not separate the product; it follows the
$Z,U,W$ gauge-consistency route via `threeLeg_residual_forms_scalar`. Documented
in `docs/paper-gaps/peps_injective_ft_section3_route.tex` (arXiv:1804.04964,
Section 3, lines 1157--1204 of `Papers/1804.04964/paper_normal.tex`).
-/
theorem twoBlockReciprocalScalarProportional_of_pointwise_mul_eq
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty (SharedBondConfig bondDim)] [Nonempty External₁] [Nonempty External₂]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hA₁ : IsTwoBlockInjective A₁) (hA₂ : IsTwoBlockInjective A₂)
    (hmul : ∀ (η₁ : External₁) (η₂ : External₂)
      (μ ν : SharedBondConfig bondDim) (σ₁ : Physical₁) (σ₂ : Physical₂),
        A₁ η₁ μ σ₁ * A₂ η₂ ν σ₂ = B₁ η₁ μ σ₁ * B₂ η₂ ν σ₂) :
    TwoBlockReciprocalScalarProportional A₁ B₁ A₂ B₂ := by
  classical
  let η₁₀ : External₁ := Classical.choice ‹Nonempty External₁›
  let η₂₀ : External₂ := Classical.choice ‹Nonempty External₂›
  let μ₀ : SharedBondConfig bondDim := Classical.choice ‹Nonempty (SharedBondConfig bondDim)›
  let ν₀ : SharedBondConfig bondDim := μ₀
  have hA₁_vec_ne : (fun σ₁ : Physical₁ => A₁ η₁₀ μ₀ σ₁) ≠ 0 :=
    hA₁.ne_zero (η₁₀, μ₀)
  obtain ⟨σ₁₀, hA₁_ne⟩ :=
    Function.ne_iff.mp hA₁_vec_ne
  have hA₂_vec_ne : (fun σ₂ : Physical₂ => A₂ η₂₀ ν₀ σ₂) ≠ 0 :=
    hA₂.ne_zero (η₂₀, ν₀)
  obtain ⟨σ₂₀, hA₂_ne⟩ :=
    Function.ne_iff.mp hA₂_vec_ne
  have hprod₀ :
      B₁ η₁₀ μ₀ σ₁₀ * B₂ η₂₀ ν₀ σ₂₀ ≠ 0 := by
    rw [← hmul η₁₀ η₂₀ μ₀ ν₀ σ₁₀ σ₂₀]
    exact mul_ne_zero hA₁_ne hA₂_ne
  have hB₁_ne : B₁ η₁₀ μ₀ σ₁₀ ≠ 0 :=
    (mul_ne_zero_iff.mp hprod₀).1
  have hB₂_ne : B₂ η₂₀ ν₀ σ₂₀ ≠ 0 :=
    (mul_ne_zero_iff.mp hprod₀).2
  let c : ℂ := B₂ η₂₀ ν₀ σ₂₀ / A₂ η₂₀ ν₀ σ₂₀
  have hc_ne : c ≠ 0 := div_ne_zero hB₂_ne hA₂_ne
  have hA₁_scalar : TwoBlockScalarProportional A₁ B₁ c := by
    intro η₁ μ σ₁
    have h := hmul η₁ η₂₀ μ ν₀ σ₁ σ₂₀
    have hB₂_eq : B₂ η₂₀ ν₀ σ₂₀ = A₂ η₂₀ ν₀ σ₂₀ * c := by
      change B₂ η₂₀ ν₀ σ₂₀ =
        A₂ η₂₀ ν₀ σ₂₀ * (B₂ η₂₀ ν₀ σ₂₀ / A₂ η₂₀ ν₀ σ₂₀)
      exact (mul_div_cancel₀ (B₂ η₂₀ ν₀ σ₂₀) hA₂_ne).symm
    change A₁ η₁ μ σ₁ = c * B₁ η₁ μ σ₁
    rw [mul_comm c (B₁ η₁ μ σ₁)]
    rw [← mul_right_inj' hA₂_ne]
    calc
      A₂ η₂₀ ν₀ σ₂₀ * A₁ η₁ μ σ₁ =
          A₁ η₁ μ σ₁ * A₂ η₂₀ ν₀ σ₂₀ := by
        simp [mul_comm]
      _ = B₁ η₁ μ σ₁ * B₂ η₂₀ ν₀ σ₂₀ := h
      _ = A₂ η₂₀ ν₀ σ₂₀ * (B₁ η₁ μ σ₁ * c) := by
        rw [hB₂_eq]
        simp [mul_left_comm]
  have hA₂_scalar : TwoBlockScalarProportional A₂ B₂ c⁻¹ := by
    intro η₂ ν σ₂
    have h := hmul η₁₀ η₂ μ₀ ν σ₁₀ σ₂
    have hA₁₀ : A₁ η₁₀ μ₀ σ₁₀ = c * B₁ η₁₀ μ₀ σ₁₀ :=
      hA₁_scalar η₁₀ μ₀ σ₁₀
    change A₂ η₂ ν σ₂ = c⁻¹ * B₂ η₂ ν σ₂
    rw [hA₁₀] at h
    rw [← mul_left_inj' (mul_ne_zero hc_ne hB₁_ne)]
    calc
      A₂ η₂ ν σ₂ * (c * B₁ η₁₀ μ₀ σ₁₀) =
          (c * B₁ η₁₀ μ₀ σ₁₀) * A₂ η₂ ν σ₂ := by
        simp [mul_comm]
      _ =
          B₁ η₁₀ μ₀ σ₁₀ * B₂ η₂ ν σ₂ := h
      _ = (c⁻¹ * B₂ η₂ ν σ₂) * (c * B₁ η₁₀ μ₀ σ₁₀) := by
        simp [hc_ne, mul_comm, mul_left_comm]
  exact ⟨c, hc_ne, hA₁_scalar, hA₂_scalar⟩

/-! ### The one-shared-bond case -/

/-- The usual elementary matrix with a single nonzero entry equal to `1` at
position `(i, j)`. -/
noncomputable def matrixUnit {ι κ : Type*} (i : ι) (j : κ) :
    Matrix ι κ ℂ := by
  classical
  exact Matrix.single i j (1 : ℂ)

open scoped Classical in
/-- Inserting the matrix unit `E_{p,q}` on the shared bond `b` extracts the
open-bond contraction: every other shared bond is contracted by the identity,
while the distinguished bond carries the row index `p` on the `A₁`-side and the
column index `q` on the `A₂`-side.

This is the open-leg form of the matrix insertion used in
arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2: a one-bond matrix
insertion frees the chosen bond and traces the others. It generalizes
`twoBlockInsertedCoeff_singletonBond_single` to an arbitrary finite shared-bond
family. -/
theorem twoBlockInsertedCoeff_matrixUnit
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (b : Bond) (p q : bondDim b)
    (η₁ : External₁) (η₂ : External₂) (σ₁ : Physical₁) (σ₂ : Physical₂) :
    twoBlockInsertedCoeff A₁ A₂ b (matrixUnit p q) η₁ η₂ σ₁ σ₂ =
      ∑ μ : SharedBondConfig bondDim,
        (if μ b = p then
          A₁ η₁ μ σ₁ * A₂ η₂ (Function.update μ b q) σ₂ else 0) := by
  classical
  unfold twoBlockInsertedCoeff
  refine Finset.sum_congr rfl ?_
  intro μ _
  by_cases hμ : μ b = p
  · rw [if_pos hμ]
    rw [Finset.sum_eq_single (Function.update μ b q)]
    · have hsame : SameAwayFromBond b μ (Function.update μ b q) := by
        intro c hc
        rw [Function.update_of_ne hc]
      rw [if_pos hsame]
      simp [matrixUnit, Matrix.single, hμ, Function.update_self]
    · intro ν' _ hν'
      by_cases hsame : SameAwayFromBond b μ ν'
      · rw [if_pos hsame]
        have hνb : ν' b ≠ q := by
          intro hb
          apply hν'
          funext c
          by_cases hcb : c = b
          · subst hcb; rw [Function.update_self, hb]
          · rw [Function.update_of_ne hcb]; exact (hsame c hcb).symm
        have hz : matrixUnit p q (μ b) (ν' b) = 0 := by
          simp only [matrixUnit, Matrix.single]
          rw [Matrix.of_apply, if_neg]
          rintro ⟨-, hq⟩; exact hνb hq.symm
        rw [hz]; ring
      · rw [if_neg hsame]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hμ]
    apply Finset.sum_eq_zero
    intro ν' _
    by_cases hsame : SameAwayFromBond b μ ν'
    · rw [if_pos hsame]
      have hz : matrixUnit p q (μ b) (ν' b) = 0 := by
        simp only [matrixUnit, Matrix.single]
        rw [Matrix.of_apply, if_neg]
        rintro ⟨hp, -⟩; exact hμ hp.symm
      rw [hz]; ring
    · rw [if_neg hsame]; ring

/-- If there is only one shared bond, then a matrix insertion supported at one
matrix entry extracts the corresponding pointwise product.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2. This is the
one-shared-bond specialization, where no residual two-leg operators appear. -/
theorem twoBlockInsertedCoeff_singletonBond_single
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Subsingleton Bond] (b : Bond)
    (A₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (η₁ : External₁) (η₂ : External₂)
    (μ ν : SharedBondConfig bondDim) (σ₁ : Physical₁) (σ₂ : Physical₂) :
    twoBlockInsertedCoeff A₁ A₂ b (matrixUnit (μ b) (ν b))
        η₁ η₂ σ₁ σ₂ =
      A₁ η₁ μ σ₁ * A₂ η₂ ν σ₂ := by
  classical
  unfold twoBlockInsertedCoeff
  rw [Finset.sum_eq_single μ]
  · rw [Finset.sum_eq_single ν]
    · have hsame : SameAwayFromBond b μ ν := by
        intro c hc
        exact (hc (Subsingleton.elim c b)).elim
      simp [matrixUnit, Matrix.single, hsame]
    · intro ν' _ hν'
      have hν'_ne : ν' b ≠ ν b := by
        intro hb
        apply hν'
        funext c
        have hc : c = b := Subsingleton.elim c b
        rw [hc]
        exact hb
      have hν_ne' : ν b ≠ ν' b := hν'_ne.symm
      simp [matrixUnit, Matrix.single, hν_ne']
    · intro hν
      simp at hν
  · intro μ' _ hμ'
    have hμ'_ne : μ' b ≠ μ b := by
      intro hb
      apply hμ'
      funext c
      have hc : c = b := Subsingleton.elim c b
      rw [hc]
      exact hb
    have hμ_ne' : μ b ≠ μ' b := hμ'_ne.symm
    apply Finset.sum_eq_zero
    intro ν' _
    simp [matrixUnit, Matrix.single, hμ_ne']
  · intro hμ
    simp at hμ

/-- The generalized two-injective comparison in the case of a single shared
virtual bond.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2. This proves
the coefficient-separation subcase where the shared-boundary family has one
bond, so equality of all matrix insertions gives pointwise product equality
directly. The many-bond case still requires the residual-operator argument. -/
theorem two_injective_tensor_insertion_comparison_singletonBond
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty Bond] [Subsingleton Bond] [Nonempty External₁] [Nonempty External₂]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hA₁ : IsTwoBlockInjective A₁) (hA₂ : IsTwoBlockInjective A₂)
    (hinsert : SameTwoBlockInsertions A₁ B₁ A₂ B₂) :
    TwoBlockReciprocalScalarProportional A₁ B₁ A₂ B₂ := by
  classical
  by_cases hcfg : Nonempty (SharedBondConfig bondDim)
  · letI : Nonempty (SharedBondConfig bondDim) := hcfg
    refine
      twoBlockReciprocalScalarProportional_of_pointwise_mul_eq A₁ B₁ A₂ B₂ hA₁ hA₂ ?_
    intro η₁ η₂ μ ν σ₁ σ₂
    let b : Bond := Classical.choice ‹Nonempty Bond›
    have hcoeff := hinsert b (matrixUnit (μ b) (ν b)) η₁ η₂ σ₁ σ₂
    rw [twoBlockInsertedCoeff_singletonBond_single b A₁ A₂,
      twoBlockInsertedCoeff_singletonBond_single b B₁ B₂] at hcoeff
    exact hcoeff
  · refine ⟨1, one_ne_zero, ?_, ?_⟩
    · intro η μ σ
      exact (hcfg ⟨μ⟩).elim
    · intro η μ σ
      exact (hcfg ⟨μ⟩).elim

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- If some shared virtual bond carries an empty index space, then the family of
shared-bond configurations is empty and reciprocal scalar proportionality holds
vacuously.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2. The source works
with nonzero-dimensional virtual bonds; the empty-bond situation does not occur
there, but the abstract statement carries no positivity hypothesis, so this
boundary case is discharged directly. -/
theorem twoBlockReciprocalScalarProportional_of_isEmpty_config
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hcfg : IsEmpty (SharedBondConfig bondDim)) :
    TwoBlockReciprocalScalarProportional A₁ B₁ A₂ B₂ := by
  refine ⟨1, one_ne_zero, ?_, ?_⟩
  · intro _ μ _
    exact (hcfg.false μ).elim
  · intro _ μ _
    exact (hcfg.false μ).elim

/-! ### One-leg-open equalities -/

open scoped Classical in
/-- The per-bond insertion hypothesis is equivalent to equality of all one-leg-open
contractions: for every shared bond `b` and every pair of bond endpoints `(p, q)`,
opening bond `b` (and contracting every other shared bond by the identity) gives
the same value for the `A`-pair and the `B`-pair.

This is the first reduction in arXiv:1804.04964, Section 3, Lemma
inj_equal_tensors_2: "if the insertion equality holds for all `X`, then" the
displayed open-leg equalities hold. It is obtained from `SameTwoBlockInsertions`
by inserting matrix units and applying `twoBlockInsertedCoeff_matrixUnit`. -/
theorem sameOpenBondContraction
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hinsert : SameTwoBlockInsertions A₁ B₁ A₂ B₂)
    (b : Bond) (p q : bondDim b)
    (η₁ : External₁) (η₂ : External₂) (σ₁ : Physical₁) (σ₂ : Physical₂) :
    (∑ μ : SharedBondConfig bondDim,
        (if μ b = p then A₁ η₁ μ σ₁ * A₂ η₂ (Function.update μ b q) σ₂ else 0)) =
      ∑ μ : SharedBondConfig bondDim,
        (if μ b = p then B₁ η₁ μ σ₁ * B₂ η₂ (Function.update μ b q) σ₂ else 0) := by
  have h := hinsert b (matrixUnit p q) η₁ η₂ σ₁ σ₂
  rwa [twoBlockInsertedCoeff_matrixUnit A₁ A₂, twoBlockInsertedCoeff_matrixUnit B₁ B₂] at h

/-! ### Identity insertion and the fully contracted identity -/

open scoped Classical in
/-- Inserting the identity matrix on a bond contracts that bond by the identity,
so all shared bonds are contracted diagonally: the two-tensor coefficient becomes
the sum over the single diagonal configuration `μ = ν`.

This is the identity-insertion specialization of `twoBlockInsertedCoeff` used as
the starting reduction in arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2:
before opening any bond, the all-identity contraction equates the two states. -/
theorem twoBlockInsertedCoeff_one
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (b : Bond)
    (η₁ : External₁) (η₂ : External₂) (σ₁ : Physical₁) (σ₂ : Physical₂) :
    twoBlockInsertedCoeff A₁ A₂ b (1 : Matrix (bondDim b) (bondDim b) ℂ) η₁ η₂ σ₁ σ₂ =
      ∑ μ : SharedBondConfig bondDim, A₁ η₁ μ σ₁ * A₂ η₂ μ σ₂ := by
  classical
  unfold twoBlockInsertedCoeff
  refine Finset.sum_congr rfl ?_
  intro μ _
  rw [Finset.sum_eq_single μ]
  · have hsame : SameAwayFromBond b μ μ := fun c _ => rfl
    simp [hsame]
  · intro ν' _ hν'
    by_cases hsame : SameAwayFromBond b μ ν'
    · rw [if_pos hsame]
      have hb : μ b ≠ ν' b := by
        intro hb
        apply hν'
        funext c
        by_cases hcb : c = b
        · subst hcb; exact hb.symm
        · exact (hsame c hcb).symm
      simp [hb]
    · rw [if_neg hsame]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped Classical in
/-- The fully contracted identity: contracting all shared bonds diagonally gives
the same value for the `A`-pair and the `B`-pair.

This is obtained from `SameTwoBlockInsertions` by inserting the identity matrix on
any shared bond and using `twoBlockInsertedCoeff_one`. It is the all-identity
contraction equality in arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2. -/
theorem fullContraction_eq
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty Bond]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hinsert : SameTwoBlockInsertions A₁ B₁ A₂ B₂)
    (η₁ : External₁) (η₂ : External₂) (σ₁ : Physical₁) (σ₂ : Physical₂) :
    (∑ μ : SharedBondConfig bondDim, A₁ η₁ μ σ₁ * A₂ η₂ μ σ₂) =
      ∑ μ : SharedBondConfig bondDim, B₁ η₁ μ σ₁ * B₂ η₂ μ σ₂ := by
  classical
  let b : Bond := Classical.arbitrary Bond
  have h := hinsert b (1 : Matrix (bondDim b) (bondDim b) ℂ) η₁ η₂ σ₁ σ₂
  rwa [twoBlockInsertedCoeff_one A₁ A₂, twoBlockInsertedCoeff_one B₁ B₂] at h

/-! ### Left inverse of an injective two-block tensor -/

/-- The linear combination map of the physical vectors of a two-block tensor,
indexed by the external and shared-bond boundary configurations.

Injectivity of this map is exactly `IsTwoBlockInjective` (rephrased through
`Finsupp.linearCombination`). -/
noncomputable def twoBlockComb
    {External Physical : Type*}
    (A : TwoBlockTensor bondDim External Physical) :
    ((External × SharedBondConfig bondDim) →₀ ℂ) →ₗ[ℂ] (Physical → ℂ) :=
  Finsupp.linearCombination ℂ
    (fun η : External × SharedBondConfig bondDim => fun σ : Physical => A η.1 η.2 σ)

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
theorem twoBlockComb_injective
    {External Physical : Type*}
    {A : TwoBlockTensor bondDim External Physical}
    (hA : IsTwoBlockInjective A) :
    Function.Injective (twoBlockComb A) :=
  hA.finsuppLinearCombination_injective

/-- A chosen left inverse of `twoBlockComb A`, available because injectivity makes
that linear combination map injective. This is the abstract "inverse of an
injective tensor" used in arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2
("applying the inverse of `A₂`"). -/
noncomputable def twoBlockLeftInverse
    {External Physical : Type*}
    (A : TwoBlockTensor bondDim External Physical)
    (hA : IsTwoBlockInjective A) :
    (Physical → ℂ) →ₗ[ℂ] ((External × SharedBondConfig bondDim) →₀ ℂ) :=
  ((twoBlockComb A).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (twoBlockComb_injective hA))).choose

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
@[simp] theorem twoBlockLeftInverse_comp
    {External Physical : Type*}
    (A : TwoBlockTensor bondDim External Physical)
    (hA : IsTwoBlockInjective A) :
    (twoBlockLeftInverse A hA).comp (twoBlockComb A) = LinearMap.id :=
  ((twoBlockComb A).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (twoBlockComb_injective hA))).choose_spec

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
@[simp] theorem twoBlockLeftInverse_apply
    {External Physical : Type*}
    (A : TwoBlockTensor bondDim External Physical)
    (hA : IsTwoBlockInjective A)
    (c : (External × SharedBondConfig bondDim) →₀ ℂ) :
    twoBlockLeftInverse A hA (twoBlockComb A c) = c := by
  change ((twoBlockLeftInverse A hA).comp (twoBlockComb A)) c = c
  rw [twoBlockLeftInverse_comp]; rfl

/-! ### Operator-Schmidt uniqueness: the bond gauge -/

-- The shared-bond `Fintype` instances are used in the proof (to sum over
-- `SharedBondConfig bondDim`) but not reflected in the statement, so the
-- `unusedFintypeInType` linter cannot see them.
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- Config-indexed linear independence from joint injectivity.

`IsTwoBlockInjective A` is linear independence of the physical vectors indexed
by the *joint* boundary configuration `(η, μ)`. Reading the external coordinate
as part of the vector, the family indexed by the shared-bond configuration `μ`
alone is then linearly independent in the space `External × Physical → ℂ`,
provided the external boundary is nonempty.

This is the bridge to the config-indexed independence used in the
operator-Schmidt uniqueness argument of arXiv:1804.04964, Section 3, Lemma
inj_equal_tensors_2 (lines 1157--1204 of `Papers/1804.04964/paper_normal.tex`),
where the two contracted tensors are compared as bipartite operators. -/
theorem IsTwoBlockInjective.config_linearIndependent
    {External Physical : Type*} [Nonempty External]
    {A : TwoBlockTensor bondDim External Physical}
    (hA : IsTwoBlockInjective A) :
    LinearIndependent ℂ
      (fun μ : SharedBondConfig bondDim => fun p : External × Physical => A p.1 μ p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc μ₀
  let η₀ : External := Classical.arbitrary External
  have hjoint := (linearIndependent_iff'.1 hA)
  set s : Finset (External × SharedBondConfig bondDim) :=
    {η₀} ×ˢ (Finset.univ : Finset (SharedBondConfig bondDim)) with hs
  have hzero : (∑ q ∈ s, (fun q : External × SharedBondConfig bondDim => c q.2) q •
        (fun σ : Physical => A q.1 q.2 σ)) = 0 := by
    funext σ
    rw [Finset.sum_apply]
    have hcσ := congrFun hc (η₀, σ)
    rw [Finset.sum_apply] at hcσ
    simp only [Pi.smul_apply, smul_eq_mul] at hcσ ⊢
    rw [hs, Finset.sum_product]
    simp only [Finset.sum_singleton]
    simp only [Pi.zero_apply] at hcσ ⊢
    rw [← hcσ]
  have hmem : (η₀, μ₀) ∈ s := by rw [hs]; simp
  have hfinal := hjoint s (fun q => c q.2) hzero (η₀, μ₀) hmem
  simpa using hfinal

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- A linearly independent finite family in a complex vector space admits a dual
functional isolating each index: for every index `μ₀` there is a linear
functional vanishing on the other family members and equal to `1` on the
`μ₀`-th one. This is the coordinate functional of the family, extended from its
span to the whole space.

This is the dual-vector ingredient of operator-Schmidt uniqueness used in
arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2 ("applying the inverse of
the injective tensor"): isolating one Schmidt vector reads off a single gauge
column. -/
theorem exists_dual_isolating
    {K W : Type*} [DecidableEq K]
    [AddCommGroup W] [Module ℂ W]
    {f : K → W} (hf : LinearIndependent ℂ f) (μ₀ : K) :
    ∃ ψ : W →ₗ[ℂ] ℂ, ∀ μ : K, ψ (f μ) = if μ = μ₀ then 1 else 0 := by
  classical
  set φ : (Submodule.span ℂ (Set.range f)) →ₗ[ℂ] ℂ :=
    (Finsupp.lapply μ₀ : (K →₀ ℂ) →ₗ[ℂ] ℂ).comp (hf.repr) with hφ
  obtain ⟨ψ, hψ⟩ := φ.exists_extend
  refine ⟨ψ, fun μ => ?_⟩
  have hmem : f μ ∈ Submodule.span ℂ (Set.range f) :=
    Submodule.subset_span ⟨μ, rfl⟩
  have key : ψ (f μ) = φ ⟨f μ, hmem⟩ := by
    have := congrArg (fun L => L ⟨f μ, hmem⟩) hψ
    simpa using this
  rw [key, hφ]
  simp only [LinearMap.comp_apply, Finsupp.lapply_apply]
  rw [hf.repr_eq_single μ ⟨f μ, hmem⟩ rfl]
  simp [Finsupp.single_apply, eq_comm]

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- First gauge equation of operator-Schmidt uniqueness. If two bipartite tensors
`∑_μ a_μ ⊗ a'_μ` and `∑_ν b_ν ⊗ b'_ν` agree and the right Schmidt family `a'`
is linearly independent, then each left vector `a_μ` lies in the span of the
left vectors `b_ν`, with the coefficient matrix `g μ ν` given by the dual
functional of `a'_μ` evaluated on `b'_ν`.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. -/
theorem gauge_eq1
    {K V1 V2 : Type*} [Fintype K]
    {a b : K → V1 → ℂ} {a' b' : K → V2 → ℂ}
    (ha' : LinearIndependent ℂ (fun μ : K => (a' μ : V2 → ℂ)))
    (hcontr : ∀ (p1 : V1) (p2 : V2),
      (∑ μ : K, a μ p1 * a' μ p2) = ∑ ν : K, b ν p1 * b' ν p2) :
    ∃ g : K → K → ℂ, ∀ (μ : K) (p1 : V1),
      a μ p1 = ∑ ν : K, g μ ν * b ν p1 := by
  classical
  choose ψ hψ using fun μ₀ : K => exists_dual_isolating ha' μ₀
  refine ⟨fun μ ν => ψ μ (b' ν), fun μ₀ p1 => ?_⟩
  have hvec : (∑ μ : K, a μ p1 • (a' μ : V2 → ℂ))
      = ∑ ν : K, b ν p1 • (b' ν : V2 → ℂ) := by
    funext p2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hcontr p1 p2
  have happ := congrArg (ψ μ₀) hvec
  rw [map_sum, map_sum] at happ
  simp only [map_smul, smul_eq_mul] at happ
  rw [Finset.sum_congr rfl (fun μ _ => by rw [hψ μ₀ μ])] at happ
  simp only [mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq' Finset.univ μ₀ (fun μ => a μ p1), Finset.mem_univ, if_true] at happ
  rw [happ]
  refine Finset.sum_congr rfl ?_
  intro ν _
  ring

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- Second gauge equation of operator-Schmidt uniqueness. Continuing from
`gauge_eq1`, substituting `a_μ = ∑_ν g μ ν • b_ν` into the bipartite identity
and using linear independence of the left family `b` forces the right vector
`b'_ν` to equal `∑_μ g μ ν • a'_μ` with the *same* gauge matrix `g`.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. -/
theorem gauge_eq2
    {K V1 V2 : Type*} [Fintype K]
    {a b : K → V1 → ℂ} {a' b' : K → V2 → ℂ} {g : K → K → ℂ}
    (hb : LinearIndependent ℂ (fun ν : K => (b ν : V1 → ℂ)))
    (hcontr : ∀ (p1 : V1) (p2 : V2),
      (∑ μ : K, a μ p1 * a' μ p2) = ∑ ν : K, b ν p1 * b' ν p2)
    (hg1 : ∀ (μ : K) (p1 : V1), a μ p1 = ∑ ν : K, g μ ν * b ν p1) :
    ∀ (ν : K) (p2 : V2), b' ν p2 = ∑ μ : K, g μ ν * a' μ p2 := by
  classical
  choose χ hχ using fun ν₀ : K => exists_dual_isolating hb ν₀
  intro ν₀ p2
  have hvec : (∑ μ : K, a' μ p2 • (a μ : V1 → ℂ))
      = ∑ ν : K, b' ν p2 • (b ν : V1 → ℂ) := by
    funext p1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have := hcontr p1 p2
    rw [Finset.sum_congr rfl (fun μ _ => mul_comm (a μ p1) (a' μ p2))] at this
    rw [Finset.sum_congr rfl (fun ν _ => mul_comm (b ν p1) (b' ν p2))] at this
    exact this
  have hsubst : (∑ μ : K, a' μ p2 • (a μ : V1 → ℂ))
      = ∑ ν : K, (∑ μ : K, g μ ν * a' μ p2) • (b ν : V1 → ℂ) := by
    funext p1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun μ _ => by rw [hg1 μ p1])]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro ν _
    refine Finset.sum_congr rfl ?_
    intro μ _
    ring
  have hcomb : (∑ ν : K, (∑ μ : K, g μ ν * a' μ p2) • (b ν : V1 → ℂ))
      = ∑ ν : K, b' ν p2 • (b ν : V1 → ℂ) := by rw [← hsubst, hvec]
  have happ := congrArg (χ ν₀) hcomb
  rw [map_sum, map_sum] at happ
  simp only [map_smul, smul_eq_mul, hχ ν₀, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq' Finset.univ ν₀, Finset.mem_univ, if_true] at happ
  rw [happ]

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- Invertibility of the gauge. If `a = g·b` and `b = g'·a` with the family `a`
linearly independent, then the gauge matrices are mutually inverse: as matrices
indexed by the common index, `∑_ν g μ ν * g' ν κ = δ_{μκ}`.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. -/
theorem gauge_inv
    {K V1 : Type*} [Fintype K] [DecidableEq K]
    {a b : K → V1 → ℂ} {g g' : K → K → ℂ}
    (ha : LinearIndependent ℂ (fun μ : K => (a μ : V1 → ℂ)))
    (hg1 : ∀ (μ : K) (p1 : V1), a μ p1 = ∑ ν : K, g μ ν * b ν p1)
    (hg1' : ∀ (ν : K) (p1 : V1), b ν p1 = ∑ κ : K, g' ν κ * a κ p1) :
    ∀ μ κ : K, (∑ ν : K, g μ ν * g' ν κ) = if μ = κ then 1 else 0 := by
  classical
  intro μ₀
  have hrep : ∀ p1 : V1,
      a μ₀ p1 = ∑ κ : K, (∑ ν : K, g μ₀ ν * g' ν κ) * a κ p1 := by
    intro p1
    rw [hg1 μ₀ p1]
    rw [Finset.sum_congr rfl (fun ν _ => by rw [hg1' ν p1])]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro κ _
    refine Finset.sum_congr rfl ?_
    intro ν _
    ring
  have hcoeff : (fun p1 : V1 => a μ₀ p1) =
      ∑ κ : K, (∑ ν : K, g μ₀ ν * g' ν κ) • (a κ : V1 → ℂ) := by
    funext p1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hrep p1
  have hself : (fun p1 : V1 => a μ₀ p1) =
      ∑ κ : K, (if κ = μ₀ then (1:ℂ) else 0) • (a κ : V1 → ℂ) := by
    funext p1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq' Finset.univ μ₀, Finset.mem_univ, if_true]
  have hdiff : (∑ κ : K,
      ((∑ ν : K, g μ₀ ν * g' ν κ) - (if κ = μ₀ then (1:ℂ) else 0)) •
        (a κ : V1 → ℂ)) = 0 := by
    funext p1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, sub_mul, Pi.zero_apply]
    rw [Finset.sum_sub_distrib]
    have h1 := congrFun hcoeff p1
    have h2 := congrFun hself p1
    rw [Finset.sum_apply] at h1 h2
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
    ring
  have hzero := (Fintype.linearIndependent_iff.1 ha) _ hdiff
  intro κ₀
  have := hzero κ₀
  rw [sub_eq_zero] at this
  rw [this]
  by_cases h : μ₀ = κ₀
  · subst h; simp
  · rw [if_neg (fun hk => h hk.symm), if_neg h]

set_option maxHeartbeats 400000 in
-- The `Classical`-derived `Fintype (SharedBondConfig bondDim)` instance is
-- noncomputable, so unifying it across the four gauge-extraction calls below
-- exceeds the default heartbeat budget; a modest raise keeps the proof robust.
open scoped Classical in
/-- **Bond gauge from the full contraction (operator-Schmidt uniqueness).**

Given the fully contracted identity `fullContraction_eq` — that contracting all
shared bonds diagonally gives the same value for the `A`-pair and the `B`-pair —
and injectivity of all four tensors, there is an invertible gauge matrix `g` on
the shared-bond configurations such that `A₁ = g · B₁` (contracted on the shared
index) and `B₂ = gᵀ · A₂`. The matrix `g'` is the explicit inverse with
`g * g' = 1`.

This is the operator-Schmidt uniqueness step at the heart of arXiv:1804.04964,
Section 3, Lemma inj_equal_tensors_2, lines 1157--1204 of
`Papers/1804.04964/paper_normal.tex`: writing the contracted state as a bipartite
operator with two injective (hence linearly independent) Schmidt families on each
side forces the two decompositions to differ by an invertible change of the
shared-bond basis. -/
theorem exists_bondGauge_of_fullContraction
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty External₁] [Nonempty External₂]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hA₁ : IsTwoBlockInjective A₁) (hA₂ : IsTwoBlockInjective A₂)
    (hB₁ : IsTwoBlockInjective B₁) (hB₂ : IsTwoBlockInjective B₂)
    (hfull : ∀ (η₁ : External₁) (η₂ : External₂) (σ₁ : Physical₁) (σ₂ : Physical₂),
      (∑ μ : SharedBondConfig bondDim, A₁ η₁ μ σ₁ * A₂ η₂ μ σ₂) =
        ∑ ν : SharedBondConfig bondDim, B₁ η₁ ν σ₁ * B₂ η₂ ν σ₂) :
    ∃ (g g' : Matrix (SharedBondConfig bondDim) (SharedBondConfig bondDim) ℂ),
      g * g' = 1 ∧
      (∀ (η₁ : External₁) (μ : SharedBondConfig bondDim) (σ₁ : Physical₁),
        A₁ η₁ μ σ₁ = ∑ ν, g μ ν * B₁ η₁ ν σ₁) ∧
      (∀ (η₂ : External₂) (ν : SharedBondConfig bondDim) (σ₂ : Physical₂),
        B₂ η₂ ν σ₂ = ∑ μ, g μ ν * A₂ η₂ μ σ₂) := by
  classical
  have hA₁c := hA₁.config_linearIndependent
  have hA₂c := hA₂.config_linearIndependent
  have hB₁c := hB₁.config_linearIndependent
  have hB₂c := hB₂.config_linearIndependent
  have hcontr : ∀ (p1 : External₁ × Physical₁) (p2 : External₂ × Physical₂),
      (∑ μ : SharedBondConfig bondDim, A₁ p1.1 μ p1.2 * A₂ p2.1 μ p2.2) =
        ∑ ν : SharedBondConfig bondDim, B₁ p1.1 ν p1.2 * B₂ p2.1 ν p2.2 := by
    intro p1 p2
    exact hfull p1.1 p2.1 p1.2 p2.2
  obtain ⟨g, hg1⟩ := gauge_eq1
    (V1 := External₁ × Physical₁) (V2 := External₂ × Physical₂)
    (a := fun μ p => A₁ p.1 μ p.2)
    (b := fun ν p => B₁ p.1 ν p.2) (a' := fun μ p => A₂ p.1 μ p.2)
    (b' := fun ν p => B₂ p.1 ν p.2) hA₂c hcontr
  have hg2 := gauge_eq2
    (V1 := External₁ × Physical₁) (V2 := External₂ × Physical₂)
    (a := fun μ p => A₁ p.1 μ p.2)
    (b := fun ν p => B₁ p.1 ν p.2) (a' := fun μ p => A₂ p.1 μ p.2)
    (b' := fun ν p => B₂ p.1 ν p.2) (g := g) hB₁c hcontr hg1
  have hcontr' : ∀ (p1 : External₁ × Physical₁) (p2 : External₂ × Physical₂),
      (∑ μ : SharedBondConfig bondDim, B₁ p1.1 μ p1.2 * B₂ p2.1 μ p2.2) =
        ∑ ν : SharedBondConfig bondDim, A₁ p1.1 ν p1.2 * A₂ p2.1 ν p2.2 := by
    intro p1 p2
    exact (hcontr p1 p2).symm
  obtain ⟨g', hg1'⟩ := gauge_eq1
    (V1 := External₁ × Physical₁) (V2 := External₂ × Physical₂)
    (a := fun ν p => B₁ p.1 ν p.2)
    (b := fun μ p => A₁ p.1 μ p.2) (a' := fun ν p => B₂ p.1 ν p.2)
    (b' := fun μ p => A₂ p.1 μ p.2) hB₂c hcontr'
  have hinv := gauge_inv
    (V1 := External₁ × Physical₁)
    (a := fun μ p => A₁ p.1 μ p.2)
    (b := fun ν p => B₁ p.1 ν p.2) (g := g) (g' := g') hA₁c hg1 hg1'
  refine ⟨g, g', ?_, ?_, ?_⟩
  · ext μ κ
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hinv μ κ
  · intro η₁ μ σ₁
    have := hg1 μ (η₁, σ₁)
    simpa using this
  · intro η₂ ν σ₂
    have := hg2 ν (η₂, σ₂)
    simpa using this

/-! ### From the bond gauge to scalar proportionality -/

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- Coefficient matching for a bilinear form over two linearly independent
families. If the bilinear form `∑_{k,l} c k l · u k · w l` vanishes for every
pair of test vectors and the families `u`, `w` are linearly independent, then
all coefficients `c k l` vanish.

This is the elementary bilinear separation used to read off the gauge
constraints from the one-leg-open contraction identities of arXiv:1804.04964,
Section 3, Lemma inj_equal_tensors_2. -/
theorem bilinear_coeff_zero {K L V1 V2 : Type*} [Fintype K] [Fintype L]
    {u : K → V1 → ℂ} {w : L → V2 → ℂ}
    (hu : LinearIndependent ℂ u) (hw : LinearIndependent ℂ w)
    (c : K → L → ℂ)
    (h : ∀ (p1 : V1) (p2 : V2), (∑ k, ∑ l, c k l * u k p1 * w l p2) = 0) :
    ∀ k l, c k l = 0 := by
  classical
  have step : ∀ (p1 : V1) (l : L), (∑ k, c k l * u k p1) = 0 := by
    intro p1
    have hzero : (∑ l, (∑ k, c k l * u k p1) • w l) = 0 := by
      funext p2
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hrw : (∑ l, (∑ k, c k l * u k p1) * w l p2)
            = ∑ k, ∑ l, c k l * u k p1 * w l p2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [Finset.sum_mul]
      rw [hrw]
      exact h p1 p2
    exact (Fintype.linearIndependent_iff.1 hw) _ hzero
  intro k₀ l₀
  have hzero : (∑ k, c k l₀ • u k) = 0 := by
    funext p1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact step p1 l₀
  exact (Fintype.linearIndependent_iff.1 hu) _ hzero k₀

open scoped Classical in
/-- Reindexing a one-bond-open sum by the bond update `μ ↦ update μ b q`, which
bijects the configurations valued `p` at bond `b` onto those valued `q`.

This is the change of summation variable that turns the `A`-side of a one-leg-open
contraction into a sum over the configurations on the `A₂`-leg, used in
arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2. -/
theorem reindex_update {M : Type*} [AddCommMonoid M]
    (b : Bond) (p q : bondDim b) (f : SharedBondConfig bondDim → M) :
    (∑ μ : SharedBondConfig bondDim, if μ b = p then f (Function.update μ b q) else 0)
      = ∑ ρ : SharedBondConfig bondDim, if ρ b = q then f ρ else 0 := by
  classical
  rw [← Finset.sum_filter (fun μ : SharedBondConfig bondDim => μ b = p),
    ← Finset.sum_filter (fun ρ : SharedBondConfig bondDim => ρ b = q)]
  refine Finset.sum_bij' (fun μ _ => Function.update μ b q) (fun ρ _ => Function.update ρ b p)
    ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ ⊢
    rw [Function.update_self]
  · intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    rw [Function.update_self]
  · intro μ hμ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ
    change Function.update (Function.update μ b q) b p = μ
    rw [Function.update_idem, ← hμ, Function.update_eq_self]
  · intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    change Function.update (Function.update ρ b p) b q = ρ
    rw [Function.update_idem, ← hρ, Function.update_eq_self]
  · intro μ hμ
    rfl

open scoped Classical in
/-- The master per-bond constraint on the bond gauge `g`. Substituting the two
gauge equations `A₁ = g · B₁` and `B₂ = g · A₂` into the one-leg-open contraction
identity (`sameOpenBondContraction`) and separating the two injective families
`B₁` and `A₂` forces, for every shared bond `b` and every pair of endpoints
`p, q`, the identity

`[ρ b = q] · g (update ρ b p) ν = [ν b = p] · g ρ (update ν b q)`

for all configurations `ν, ρ`.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. -/
theorem bondGauge_master_constraint
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (g : Matrix (SharedBondConfig bondDim) (SharedBondConfig bondDim) ℂ)
    (hg1 : ∀ (η₁ : External₁) (μ : SharedBondConfig bondDim) (σ₁ : Physical₁),
      A₁ η₁ μ σ₁ = ∑ ν, g μ ν * B₁ η₁ ν σ₁)
    (hg2 : ∀ (η₂ : External₂) (ν : SharedBondConfig bondDim) (σ₂ : Physical₂),
      B₂ η₂ ν σ₂ = ∑ μ, g μ ν * A₂ η₂ μ σ₂)
    (hB₁c : LinearIndependent ℂ
      (fun ν : SharedBondConfig bondDim => fun p : External₁ × Physical₁ => B₁ p.1 ν p.2))
    (hA₂c : LinearIndependent ℂ
      (fun ρ : SharedBondConfig bondDim => fun p : External₂ × Physical₂ => A₂ p.1 ρ p.2))
    (hopen : SameTwoBlockInsertions A₁ B₁ A₂ B₂) :
    ∀ (b : Bond) (p q : bondDim b) (ν ρ : SharedBondConfig bondDim),
      (if ρ b = q then g (Function.update ρ b p) ν else 0) =
        (if ν b = p then g ρ (Function.update ν b q) else 0) := by
  classical
  intro b p q
  have key := bilinear_coeff_zero (K := SharedBondConfig bondDim) (L := SharedBondConfig bondDim)
    (V1 := External₁ × Physical₁) (V2 := External₂ × Physical₂)
    (u := fun ν p => B₁ p.1 ν p.2) (w := fun ρ p => A₂ p.1 ρ p.2)
    hB₁c hA₂c
    (fun ν ρ => (if ρ b = q then g (Function.update ρ b p) ν else 0)
                 - (if ν b = p then g ρ (Function.update ν b q) else 0))
    ?_
  · intro ν ρ
    have := key ν ρ
    rwa [sub_eq_zero] at this
  · rintro ⟨η₁, σ₁⟩ ⟨η₂, σ₂⟩
    have hO := sameOpenBondContraction A₁ B₁ A₂ B₂ hopen b p q η₁ η₂ σ₁ σ₂
    -- Rewrite the `A`-side as a bilinear form with coefficient `cLHS`.
    have hLHS : (∑ μ : SharedBondConfig bondDim,
          (if μ b = p then A₁ η₁ μ σ₁ * A₂ η₂ (Function.update μ b q) σ₂ else 0))
        = ∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
            (if ρ b = q then g (Function.update ρ b p) ν else 0)
              * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂ := by
      have stepA : (∑ μ : SharedBondConfig bondDim,
            (if μ b = p then A₁ η₁ μ σ₁ * A₂ η₂ (Function.update μ b q) σ₂ else 0))
          = ∑ μ : SharedBondConfig bondDim,
            (if μ b = p then
              (fun ρ : SharedBondConfig bondDim =>
                (∑ ν, g (Function.update ρ b p) ν * B₁ η₁ ν σ₁) * A₂ η₂ ρ σ₂)
                (Function.update μ b q)
              else 0) := by
        refine Finset.sum_congr rfl ?_
        intro μ _
        by_cases hμ : μ b = p
        · rw [if_pos hμ, if_pos hμ]
          simp only [Function.update_idem]
          rw [hg1 η₁ μ σ₁, ← hμ, Function.update_eq_self]
        · rw [if_neg hμ, if_neg hμ]
      rw [stepA, reindex_update b p q
        (fun ρ : SharedBondConfig bondDim =>
          (∑ ν, g (Function.update ρ b p) ν * B₁ η₁ ν σ₁) * A₂ η₂ ρ σ₂)]
      have stepB : (∑ ρ : SharedBondConfig bondDim,
            (if ρ b = q then
              (∑ ν, g (Function.update ρ b p) ν * B₁ η₁ ν σ₁) * A₂ η₂ ρ σ₂ else 0))
          = ∑ ρ : SharedBondConfig bondDim, ∑ ν : SharedBondConfig bondDim,
              (if ρ b = q then g (Function.update ρ b p) ν else 0)
                * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂ := by
        refine Finset.sum_congr rfl ?_
        intro ρ _
        by_cases hρ : ρ b = q
        · simp only [if_pos hρ]
          rw [Finset.sum_mul]
        · simp [if_neg hρ]
      rw [stepB]
      exact Finset.sum_comm
    -- Rewrite the `B`-side as a bilinear form with coefficient `cRHS`.
    have hRHS : (∑ μ : SharedBondConfig bondDim,
          (if μ b = p then B₁ η₁ μ σ₁ * B₂ η₂ (Function.update μ b q) σ₂ else 0))
        = ∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
            (if ν b = p then g ρ (Function.update ν b q) else 0)
              * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂ := by
      refine Finset.sum_congr rfl ?_
      intro ν _
      by_cases hν : ν b = p
      · simp only [if_pos hν]
        rw [hg2 η₂ (Function.update ν b q) σ₂, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro ρ _; ring
      · simp only [if_neg hν]
        rw [eq_comm, Finset.sum_eq_zero]
        intro ρ _; ring
    -- Combine: the difference of the two bilinear forms vanishes.
    rw [hLHS, hRHS] at hO
    -- Rewrite the target difference-of-coefficients sum as the bilinear difference.
    rw [show (∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
          ((if ρ b = q then g (Function.update ρ b p) ν else 0)
            - (if ν b = p then g ρ (Function.update ν b q) else 0))
            * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂)
        = (∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
            (if ρ b = q then g (Function.update ρ b p) ν else 0)
              * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂)
          - ∑ ν : SharedBondConfig bondDim, ∑ ρ : SharedBondConfig bondDim,
            (if ν b = p then g ρ (Function.update ν b q) else 0)
              * B₁ η₁ ν σ₁ * A₂ η₂ ρ σ₂ from ?_]
    · rw [hO, sub_self]
    · rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro ν _
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro ρ _
      ring

open scoped Classical in
/-- The bond gauge is a nonzero scalar multiple of the identity. Iterating the
master per-bond constraint over all shared bonds forces `g` to vanish off the
diagonal and to be constant along it; invertibility (`g * g' = 1`) makes the
constant nonzero.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. The paper packages this as
the statement that the residual gauges `Z`, `U`, `W` on three leg pairs are each
scalar. -/
theorem bondGauge_scalar_of_master
    [Nonempty (SharedBondConfig bondDim)]
    (g g' : Matrix (SharedBondConfig bondDim) (SharedBondConfig bondDim) ℂ)
    (hgg' : g * g' = 1)
    (hmaster : ∀ (b : Bond) (p q : bondDim b) (ν ρ : SharedBondConfig bondDim),
      (if ρ b = q then g (Function.update ρ b p) ν else 0) =
        (if ν b = p then g ρ (Function.update ν b q) else 0)) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ μ ν : SharedBondConfig bondDim,
      g μ ν = lam * (if μ = ν then 1 else 0) := by
  classical
  -- `g` vanishes whenever the configurations differ at some bond.
  have hoffdiag : ∀ (b : Bond) (μ ν : SharedBondConfig bondDim),
      μ b ≠ ν b → g μ ν = 0 := by
    intro b μ ν hne
    have h := hmaster b (μ b) (μ b) ν μ
    rw [if_pos rfl, Function.update_eq_self] at h
    rw [if_neg (fun hh => hne hh.symm)] at h
    exact h
  have hdiag : ∀ μ ν : SharedBondConfig bondDim, μ ≠ ν → g μ ν = 0 := by
    intro μ ν hne
    obtain ⟨b, hb⟩ := Function.ne_iff.1 hne
    exact hoffdiag b μ ν hb
  -- The diagonal value is invariant under changing a single bond coordinate.
  have hconst1 : ∀ (b : Bond) (q : bondDim b) (ν : SharedBondConfig bondDim),
      g ν ν = g (Function.update ν b q) (Function.update ν b q) := by
    intro b q ν
    have h := hmaster b (ν b) q ν (Function.update ν b q)
    rw [Function.update_self, if_pos rfl] at h
    rw [Function.update_idem, Function.update_eq_self] at h
    rw [if_pos rfl] at h
    exact h
  -- Diagonal values agree whenever configurations agree off a finite bond set.
  have hagree : ∀ (s : Finset Bond) (μ ν : SharedBondConfig bondDim),
      (∀ b, b ∉ s → μ b = ν b) → g μ μ = g ν ν := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro μ ν hagree
        have : μ = ν := by
          funext b; exact hagree b (Finset.notMem_empty b)
        rw [this]
    | insert b s hbs ih =>
        intro μ ν hagree
        have hstep : g ν ν = g (Function.update ν b (μ b)) (Function.update ν b (μ b)) :=
          hconst1 b (μ b) ν
        have hrest : ∀ c, c ∉ s → μ c = (Function.update ν b (μ b)) c := by
          intro c hc
          by_cases hcb : c = b
          · subst hcb; rw [Function.update_self]
          · rw [Function.update_of_ne hcb]
            exact hagree c (by simp [Finset.mem_insert, hcb, hc])
        rw [hstep]
        exact ih μ (Function.update ν b (μ b)) hrest
  let μ₀ : SharedBondConfig bondDim := Classical.arbitrary (SharedBondConfig bondDim)
  let lam : ℂ := g μ₀ μ₀
  have hdiagconst : ∀ μ : SharedBondConfig bondDim, g μ μ = lam :=
    fun μ => hagree Finset.univ μ μ₀ (fun b hb => absurd (Finset.mem_univ b) hb)
  -- `g` is `lam` on the diagonal and `0` off it.
  have hform : ∀ μ ν : SharedBondConfig bondDim, g μ ν = lam * (if μ = ν then 1 else 0) := by
    intro μ ν
    by_cases h : μ = ν
    · subst h; rw [if_pos rfl, mul_one]; exact hdiagconst μ
    · rw [if_neg h, mul_zero]; exact hdiag μ ν h
  -- Invertibility forces `lam ≠ 0`.
  have hlam : lam ≠ 0 := by
    intro hlam0
    have hone : (g * g') μ₀ μ₀ = 1 := by rw [hgg']; simp
    rw [Matrix.mul_apply] at hone
    have hzero : (∑ ν, g μ₀ ν * g' ν μ₀) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro ν _
      rw [hform μ₀ ν, hlam0, zero_mul, zero_mul]
    rw [hzero] at hone
    exact one_ne_zero hone.symm
  exact ⟨lam, hlam, hform⟩

/-! ### Main comparison theorem -/

/-- The substantive case of the generalized two-injective comparison, where every
shared virtual bond carries a nonempty index space (so the configuration family
is nonempty).

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`.

The fully contracted identity supplies a bond gauge `g` with `A₁ = g · B₁` and
`B₂ = g · A₂` (`exists_bondGauge_of_fullContraction`). Substituting both gauge
equations into each one-leg-open contraction (`sameOpenBondContraction`) and
separating the two injective families `B₁` and `A₂` yields the master per-bond
constraint `bondGauge_master_constraint`. Iterating that constraint over all
shared bonds forces `g` to be a nonzero scalar multiple of the identity
(`bondGauge_scalar_of_master`), which is exactly the source statement that the
residual gauges on the freed leg groups are scalar. Reinserting `g = lam · 1`
into the gauge equations gives `A₁ = lam · B₁` and `A₂ = lam⁻¹ · B₂`. -/
theorem two_injective_tensor_insertion_comparison_core
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty Bond] [Nonempty External₁] [Nonempty External₂]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hA₁ : IsTwoBlockInjective A₁) (hA₂ : IsTwoBlockInjective A₂)
    (hB₁ : IsTwoBlockInjective B₁) (hB₂ : IsTwoBlockInjective B₂)
    (hinsert : SameTwoBlockInsertions A₁ B₁ A₂ B₂)
    (hbond : ∀ b, Nonempty (bondDim b)) :
    TwoBlockReciprocalScalarProportional A₁ B₁ A₂ B₂ := by
  classical
  haveI : Nonempty (SharedBondConfig bondDim) := Classical.nonempty_pi.mpr hbond
  -- The bond gauge from operator-Schmidt uniqueness.
  obtain ⟨g, g', hgg', hg1, hg2⟩ :=
    exists_bondGauge_of_fullContraction A₁ B₁ A₂ B₂ hA₁ hA₂ hB₁ hB₂
      (fullContraction_eq A₁ B₁ A₂ B₂ hinsert)
  -- Config-indexed independence of the inner families.
  have hB₁c := hB₁.config_linearIndependent
  have hA₂c := hA₂.config_linearIndependent
  -- The master per-bond constraint, then scalar-diagonality of the gauge.
  have hmaster := bondGauge_master_constraint A₁ B₁ A₂ B₂ g hg1 hg2 hB₁c hA₂c hinsert
  obtain ⟨lam, hlam, hform⟩ := bondGauge_scalar_of_master g g' hgg' hmaster
  refine ⟨lam, hlam, ?_, ?_⟩
  · -- A₁ = lam • B₁.
    intro η₁ μ σ₁
    rw [hg1 η₁ μ σ₁]
    rw [Finset.sum_congr rfl (fun ν _ => by rw [hform μ ν])]
    rw [Finset.sum_eq_single μ]
    · rw [if_pos rfl, mul_one]
    · intro ν _ hν
      rw [if_neg (fun hh => hν hh.symm), mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- A₂ = lam⁻¹ • B₂, equivalently B₂ = lam • A₂.
    intro η₂ ν σ₂
    have hB₂eq : B₂ η₂ ν σ₂ = lam * A₂ η₂ ν σ₂ := by
      rw [hg2 η₂ ν σ₂]
      rw [Finset.sum_congr rfl (fun μ _ => by rw [hform μ ν])]
      rw [Finset.sum_eq_single ν]
      · rw [if_pos rfl, mul_one]
      · intro μ _ hμ
        rw [if_neg hμ, mul_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hlam, mul_comm]
    rw [mul_comm] at hB₂eq
    exact hB₂eq

/-- **Generalized two-injective-tensor comparison.**

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1068--1203 of Papers/1804.04964/paper_normal.tex.

This is the source comparison theorem in an abstract form with nonempty
spectator external boundary spaces; the statement in the paper is recovered by
taking these spaces to be one-point spaces. If `A₁,A₂,B₁,B₂` are injective
tensors joined by a finite nonempty family of shared virtual bonds, and
inserting an arbitrary matrix on any shared bond gives the same two-tensor
coefficient for the `A`-pair and the `B`-pair, then there is a nonzero scalar
`λ` such that `A₁ = λ B₁` and `A₂ = λ⁻¹ B₂`.

When the shared-bond configuration family is nonempty the result is the
substantive case `two_injective_tensor_insertion_comparison_core`: the fully
contracted identity yields a bond gauge that the one-leg-open contractions force
to be a nonzero scalar multiple of the identity, giving $A_1=\lambda B_1$ and
$A_2=\lambda^{-1}B_2$ (arXiv:1804.04964, Section 3, lines 1157--1204). The
single-shared-bond specialization is `two_injective_tensor_insertion_comparison_singletonBond`.
When some shared bond carries an empty index space the configuration family is
empty and the conclusion holds vacuously
(`twoBlockReciprocalScalarProportional_of_isEmpty_config`). -/
theorem two_injective_tensor_insertion_comparison
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty Bond] [Nonempty External₁] [Nonempty External₂]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hA₁ : IsTwoBlockInjective A₁) (hA₂ : IsTwoBlockInjective A₂)
    (hB₁ : IsTwoBlockInjective B₁) (hB₂ : IsTwoBlockInjective B₂)
    (hinsert : SameTwoBlockInsertions A₁ B₁ A₂ B₂) :
    TwoBlockReciprocalScalarProportional A₁ B₁ A₂ B₂ := by
  classical
  -- If some shared bond is empty, the configuration family is empty and the
  -- conclusion is vacuous (the source uses nonzero-dimensional bonds).
  by_cases hcfg : Nonempty (SharedBondConfig bondDim)
  · -- All bonds are nonempty; this is the substantive case.
    have hbond : ∀ b, Nonempty (bondDim b) := Classical.nonempty_pi.mp hcfg
    exact two_injective_tensor_insertion_comparison_core
      A₁ B₁ A₂ B₂ hA₁ hA₂ hB₁ hB₂ hinsert hbond
  · exact twoBlockReciprocalScalarProportional_of_isEmpty_config A₁ B₁ A₂ B₂
      (not_nonempty_iff.mp hcfg)

/-! ### One vertex against its complement -/

/-- **One-vertex versus complement comparison.**

Source: arXiv:1804.04964, Section 3, immediately after Lemma
inj_equal_tensors_2, lines 1205--1210 of
Papers/1804.04964/paper_normal.tex.

After the edge gauges have been absorbed into the second PEPS tensor family,
the source blocks one vertex against its complement. The post-absorption
insertion equality arXiv:1804.04964, eq:inj_equal_edge, supplies equality of
all one-bond insertions for this two-block pair. Applying Lemma
inj_equal_tensors_2 then gives scalar proportionality of the selected vertex
tensor with its modified counterpart.

This theorem records precisely that final local use of the generalized
two-injective comparison in an abstract form with nonempty spectator external
boundary spaces: the selected vertex is the first block and its complement is
the second block. -/
theorem one_vertex_complement_comparison
    {ExternalVertex ExternalComplement PhysicalVertex PhysicalComplement : Type*}
    [Nonempty Bond] [Nonempty ExternalVertex] [Nonempty ExternalComplement]
    (Avertex Bvertex : TwoBlockTensor bondDim ExternalVertex PhysicalVertex)
    (Acomplement Bcomplement :
      TwoBlockTensor bondDim ExternalComplement PhysicalComplement)
    (hAvertex : IsTwoBlockInjective Avertex)
    (hAcomplement : IsTwoBlockInjective Acomplement)
    (hBvertex : IsTwoBlockInjective Bvertex)
    (hBcomplement : IsTwoBlockInjective Bcomplement)
    (hinsert :
      SameTwoBlockInsertions Avertex Bvertex Acomplement Bcomplement) :
    ∃ c : ℂ, c ≠ 0 ∧ TwoBlockScalarProportional Avertex Bvertex c := by
  rcases two_injective_tensor_insertion_comparison
      Avertex Bvertex Acomplement Bcomplement
      hAvertex hAcomplement hBvertex hBcomplement hinsert with
    ⟨c, hc_ne, hvertex, _hcomplement⟩
  exact ⟨c, hc_ne, hvertex⟩

end PEPS
end TNLean
