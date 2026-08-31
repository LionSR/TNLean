/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Basis
import TNLean.Algebra.OperatorSchmidt

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

The module also gives the operator-Schmidt comparison used in Lemma 5,
lines 2213--2252 of the same source: equality of the two end contractions and
linear independence of the two genuine families determine one unique matrix
on their common bond.
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
    twoBlockInsertedCoeff A₁ A₂ b (Matrix.single p q (1 : ℂ)) η₁ η₂ σ₁ σ₂ =
      ∑ μ : SharedBondConfig bondDim,
        (if μ b = p then
          A₁ η₁ μ σ₁ * A₂ η₂ (Function.update μ b q) σ₂ else 0) := by
  classical
  unfold twoBlockInsertedCoeff
  refine Finset.sum_congr rfl ?_
  intro μ _
  by_cases hμ : μ b = p
  · rw [ite_eq_left hμ]
    rw [Finset.sum_eq_single (Function.update μ b q)]
    · have hsame : SameAwayFromBond b μ (Function.update μ b q) := by
        intro c hc
        rw [Function.update_of_ne hc]
      rw [ite_eq_left hsame]
      simp [Matrix.single, hμ, Function.update_self]
    · intro ν' _ hν'
      by_cases hsame : SameAwayFromBond b μ ν'
      · rw [ite_eq_left hsame]
        have hνb : ν' b ≠ q := by
          intro hb
          apply hν'
          funext c
          by_cases hcb : c = b
          · subst hcb; rw [Function.update_self, hb]
          · rw [Function.update_of_ne hcb]; exact (hsame c hcb).symm
        have hz : Matrix.single p q (1 : ℂ) (μ b) (ν' b) = 0 := by
          simp only [Matrix.single]
          rw [Matrix.of_apply, ite_eq_right]
          rintro ⟨-, hq⟩; exact hνb hq.symm
        rw [hz]; ring
      · rw [ite_eq_right hsame]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hμ]
    apply Finset.sum_eq_zero
    intro ν' _
    by_cases hsame : SameAwayFromBond b μ ν'
    · rw [ite_eq_left hsame]
      have hz : Matrix.single p q (1 : ℂ) (μ b) (ν' b) = 0 := by
        simp only [Matrix.single]
        rw [Matrix.of_apply, ite_eq_right]
        rintro ⟨hp, -⟩; exact hμ hp.symm
      rw [hz]; ring
    · rw [ite_eq_right hsame]; ring

open scoped Classical in
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
    twoBlockInsertedCoeff A₁ A₂ b (Matrix.single (μ b) (ν b) (1 : ℂ))
        η₁ η₂ σ₁ σ₂ =
      A₁ η₁ μ σ₁ * A₂ η₂ ν σ₂ := by
  classical
  unfold twoBlockInsertedCoeff
  rw [Finset.sum_eq_single μ]
  · rw [Finset.sum_eq_single ν]
    · have hsame : SameAwayFromBond b μ ν := by
        intro c hc
        exact (hc (Subsingleton.elim c b)).elim
      simp [Matrix.single, hsame]
    · intro ν' _ hν'
      have hν'_ne : ν' b ≠ ν b := by
        intro hb
        apply hν'
        funext c
        have hc : c = b := Subsingleton.elim c b
        rw [hc]
        exact hb
      have hν_ne' : ν b ≠ ν' b := hν'_ne.symm
      simp [Matrix.single, hν_ne']
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
    simp [Matrix.single, hμ_ne']
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
  · let : Nonempty (SharedBondConfig bondDim) := hcfg
    refine
      twoBlockReciprocalScalarProportional_of_pointwise_mul_eq A₁ B₁ A₂ B₂ hA₁ hA₂ ?_
    intro η₁ η₂ μ ν σ₁ σ₂
    let b : Bond := Classical.choice ‹Nonempty Bond›
    have hcoeff := hinsert b (Matrix.single (μ b) (ν b) (1 : ℂ)) η₁ η₂ σ₁ σ₂
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
/-- The per-bond insertion hypothesis implies equality of all one-leg-open
contractions: for every shared bond `b` and every pair of bond endpoints `(p, q)`,
opening bond `b` (and contracting every other shared bond by the identity) gives
the same value for the `A`-pair and the `B`-pair.

This is the first reduction in arXiv:1804.04964, Section 3, Lemma
inj_equal_tensors_2: "if the insertion equality holds for all `X`, then" the
displayed open-leg equalities hold. It is obtained from `SameTwoBlockInsertions`
by inserting matrix units and applying `twoBlockInsertedCoeff_matrixUnit`. -/
theorem openBondContraction_of_sameInsertions
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
  have h := hinsert b (Matrix.single p q (1 : ℂ)) η₁ η₂ σ₁ σ₂
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
    · rw [ite_eq_left hsame]
      have hb : μ b ≠ ν' b := by
        intro hb
        apply hν'
        funext c
        by_cases hcb : c = b
        · subst hcb; exact hb.symm
        · exact (hsame c hcb).symm
      simp [hb]
    · rw [ite_eq_right hsame]; ring
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

/-! ### Operator-Schmidt uniqueness: the bond gauge -/

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
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
    [Finite Bond] [∀ b, Finite (bondDim b)]
    {External Physical : Type*} [Nonempty External]
    {A : TwoBlockTensor bondDim External Physical}
    (hA : IsTwoBlockInjective A) :
    LinearIndependent ℂ
      (fun μ : SharedBondConfig bondDim => fun p : External × Physical => A p.1 μ p.2) := by
  classical
  let := Fintype.ofFinite Bond
  let (b : Bond) := Fintype.ofFinite (bondDim b)
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

/-! ### Lemma 5 end-pair operation -/

omit [Fintype Bond] [(b : Bond) → Fintype (bondDim b)] in
/-- **The virtual operation obtained by comparing the two end blocks.**

Let `A₁` and `A₂` be the two genuine injective blocks on the ends of a
tensor-network segment, and let `C₁` and `C₂` be the corresponding blocks
after applying the two end physical operations.  If the two resulting open
contractions agree, then there is a unique matrix `X` on the bond between the
blocks such that `C₁` is obtained from `A₁` by inserting `X`, while `C₂` is
obtained from `A₂` by inserting the transpose action of the same `X`.

Only the two genuine blocks are required to be injective.  In particular, no
injectivity assumption is made on the physically modified blocks.  This is the
operator-Schmidt uniqueness argument used in the converse of Lemma 5 of
arXiv:1804.04964: after inverting the genuine regions `45` and `51`, comparing
the two ends produces `X` and `Y`, and equality of the common state forces
`X = Y`.

Source: arXiv:1804.04964, Lemma 5 and its proof, lines 2044--2250 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem existsUnique_virtualOperation_of_endPair
    {K V₁ V₂ : Type*} [Fintype K]
    (A₁ C₁ : K → V₁ → ℂ) (A₂ C₂ : K → V₂ → ℂ)
    (hA₁ : LinearIndependent ℂ (fun μ : K ↦ (A₁ μ : V₁ → ℂ)))
    (hA₂ : LinearIndependent ℂ (fun μ : K ↦ (A₂ μ : V₂ → ℂ)))
    (hcontract : ∀ (p₁ : V₁) (p₂ : V₂),
      (∑ μ : K, C₁ μ p₁ * A₂ μ p₂) = ∑ ν : K, A₁ ν p₁ * C₂ ν p₂) :
    ∃! X : Matrix K K ℂ,
      (∀ (ν : K) (p₁ : V₁), C₁ ν p₁ = ∑ μ : K, A₁ μ p₁ * X μ ν) ∧
        ∀ (μ : K) (p₂ : V₂), C₂ μ p₂ = ∑ ν : K, X μ ν * A₂ ν p₂ := by
  classical
  obtain ⟨g, hleft⟩ := gauge_eq1
    (a := C₁) (b := A₁) (a' := A₂) (b' := C₂) hA₂ hcontract
  have hright := gauge_eq2
    (a := C₁) (b := A₁) (a' := A₂) (b' := C₂) (g := g) hA₁ hcontract hleft
  let X : Matrix K K ℂ := fun μ ν ↦ g ν μ
  have hleftX : ∀ (ν : K) (p₁ : V₁), C₁ ν p₁ = ∑ μ : K, A₁ μ p₁ * X μ ν := by
    intro ν p₁
    simpa [X, mul_comm] using hleft ν p₁
  have hrightX : ∀ (μ : K) (p₂ : V₂), C₂ μ p₂ = ∑ ν : K, X μ ν * A₂ ν p₂ := by
    intro μ p₂
    simpa [X] using hright μ p₂
  refine ⟨X, ⟨hleftX, hrightX⟩, ?_⟩
  intro Y hY
  apply Matrix.ext
  intro μ ν
  have hzero :
      (∑ κ : K, (X κ ν - Y κ ν) • (A₁ κ : V₁ → ℂ)) = 0 := by
    funext p₁
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    calc
      (∑ κ : K, (X κ ν - Y κ ν) * A₁ κ p₁) =
          (∑ κ : K, A₁ κ p₁ * X κ ν) - ∑ κ : K, A₁ κ p₁ * Y κ ν := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro κ _
        ring
      _ = C₁ ν p₁ - C₁ ν p₁ := by rw [← hleftX ν p₁, ← hY.1 ν p₁]
      _ = 0 := sub_self _
  have hcoeff := (Fintype.linearIndependent_iff.mp hA₁)
    (fun κ : K ↦ X κ ν - Y κ ν) hzero μ
  exact (sub_eq_zero.mp hcoeff).symm

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
  · apply Matrix.ext
    intro μ κ
    change (∑ ν, g μ ν * g' ν κ) = if μ = κ then 1 else 0
    exact hinv μ κ
  · intro η₁ μ σ₁
    have := hg1 μ (η₁, σ₁)
    simpa using this
  · intro η₂ ν σ₂
    have := hg2 ν (η₂, σ₂)
    simpa using this


end PEPS
end TNLean
