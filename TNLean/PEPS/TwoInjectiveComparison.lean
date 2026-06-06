import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.LinearIndependent.Basic

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

/-! ### Main comparison theorem -/

/-- The substantive case of the generalized two-injective comparison, where every
shared virtual bond carries a nonempty index space (so the configuration family
is nonempty).

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204. This is the residual-operator route: invert `A₂` and free three leg
groups to obtain gauges `Z`, `U`, `W`, whose identity-form compatibility forces
each to be a scalar by `threeLeg_residual_forms_scalar`. -/
theorem two_injective_tensor_insertion_comparison_core
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    [Nonempty External₁] [Nonempty External₂]
    (A₁ B₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ B₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (hA₁ : IsTwoBlockInjective A₁) (hA₂ : IsTwoBlockInjective A₂)
    (hB₁ : IsTwoBlockInjective B₁) (hB₂ : IsTwoBlockInjective B₂)
    (hinsert : SameTwoBlockInsertions A₁ B₁ A₂ B₂)
    (hbond : ∀ b, Nonempty (bondDim b)) :
    TwoBlockReciprocalScalarProportional A₁ B₁ A₂ B₂ := by
  sorry

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

**Proof status:** open (`sorry`). The source route, which this proof should
follow, groups the shared bonds into three nonzero legs, inverts `A₂`, and
reads off the gauges $Z$, $U$, $W$ on the three leg pairs; their identity-form
compatibility forces each to be a scalar by `threeLeg_residual_forms_scalar`
(already proved), giving $A_1=\lambda B_1$ and $A_2=\lambda^{-1}B_2$
(arXiv:1804.04964, Section 3, lines 1157--1204). The single-shared-bond case is
closed by `two_injective_tensor_insertion_comparison_singletonBond`. The
remaining work, the inversion and leg-regrouping that produce $Z$, $U$, $W$ from
the one-bond insertions, is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations"; tracked by issue #1361. -/
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
