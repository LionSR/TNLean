/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionLMatrixGauge
import TNLean.MPS.MPDO.BoundarySourceMixedPentagon

/-!
# Injective matrix product states cannot be invariant under non-trivial MPOs

Let a matrix product state have a single injective block `x`, and suppose
that every operator block acts on it without multiplicity, `M_{a,x}^x = 1`.
GLM23, Section `nonuniqueGS` (lines 607--636), concludes that the exact
fusion-then-action and sequential-action trees are proportional, with
constants `λ_{a,b}^{c,μ}` (the inverse L-symbols), and that the coupled
pentagon then writes every F-symbol as

`F^{d,μν}_{f,χη} = λ_{ab}^{dμ} λ_{dc}^{eν} / (λ_{bc}^{fχ} λ_{af}^{eη})`,

so the F-symbols are gauge equivalent to one.

This file formalizes that argument for the exact fusion and action maps.
The L matrix of a pair `a, b` then has a single row; because it is
invertible, it also has a single column. Hence `∑_c N_{ab}^c = 1`: the
fusion multiplicities are those of a group-like fusion rule. The constant
`λ_{a,b}^{c,μ}` is the single entry of the inverse L matrix. The coupled
pentagon for the actual coefficients gives the displayed formula, and
rescaling the fusion maps by these constants makes every F coefficient one.

The hypotheses are those of the formalized coupled pentagon: individually
injective, positive-dimensional operator blocks without scalar-gauge
duplicates, and an injective positive-dimensional state block. The source's
statement uses these standing assumptions; the separation of state blocks
is vacuous for a single block.

## Main results

* `MPOTensor.sum_fusionMultiplicity_eq_one_of_singleBlock`: `∑_c N_{ab}^c = 1`.
* `MPOTensor.singleBlockLambda`: the constants `λ_{a,b}^{c,μ}`.
* `MPOTensor.actionLMatrix_mul_singleBlockLambda`: `L λ = 1`.
* `MPOTensor.fusionFMatrix_eq_singleBlockLambda`: the source's formula for
  the F-symbols.
* `MPOTensor.exists_fusionFMatrix_eq_one_of_singleBlock`: rescaled exact
  fusion maps have every F coefficient equal to one.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
  subsection `nonuniqueGS`, lines 607--636, using `rawrels` and
  `coupledpent`, lines 491--562.
-/

open scoped Matrix BigOperators

namespace MPSTensor.IsBiorthogonalDecomposition

variable {ι : Type*} [Fintype ι] {d D : ℕ} {δ : ι → ℕ}
  {B : MPSTensor d D} {A : ∀ c : ι, MPSTensor d (δ c)}
  {V : ∀ c : ι, Matrix (Fin (δ c)) (Fin D) ℂ}
  {W : ∀ c : ι, Matrix (Fin D) (Fin (δ c)) ℂ}

/-- Rescaling each analysis map by `t⁻¹` and each synthesis map by `t`
preserves an exact biorthogonal decomposition. This is the scalar case of
the fusion- and action-tensor gauge freedom, GLM23 lines 415--424 and
595--602. -/
theorem inv_smul_smul (h : IsBiorthogonalDecomposition B A V W) (t : ι → ℂ)
    (ht : ∀ c, t c ≠ 0) :
    IsBiorthogonalDecomposition B A (fun c ↦ (t c)⁻¹ • V c) (fun c ↦ t c • W c) where
  retract c := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (ht c), one_smul,
      h.retract]
  orthogonal c b hcb := by
    rw [Matrix.smul_mul, Matrix.mul_smul, h.orthogonal c b hcb, smul_zero, smul_zero]
  letter i := by
    rw [h.letter i]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ (ht c),
      one_smul]

end MPSTensor.IsBiorthogonalDecomposition

namespace MPOTensor

variable {d r : ℕ} {χ : Fin r → ℕ} {D : Fin 1 → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin 1 → Fin 1 → ℕ}

section

variable (hM : ∀ a, M a 0 0 = 1)

include hM in
/-- The action multiplicity spaces of the single block are singletons. -/
theorem subsingleton_fin_of_singleBlock (a : Fin r) (x y : Fin 1) :
    Subsingleton (Fin (M a x y)) := by
  rw [Subsingleton.elim x 0, Subsingleton.elim y 0, hM]
  infer_instance

/-- The unique index of the action multiplicity space `M_{a,x}^x = 1`. -/
def singleBlockIndex (a : Fin r) : Fin (M a 0 0) :=
  ⟨0, by rw [hM]; exact Nat.one_pos⟩

/-- The unique row `(x,0,0)` of the L matrix of a pair `a, b`. -/
def singleBlockRow (a b : Fin r) : SequentialActionMultiplicity M a b 0 0 :=
  ⟨0, singleBlockIndex hM a, singleBlockIndex hM b⟩

include hM in
theorem card_sequentialActionMultiplicity_of_singleBlock (a b : Fin r) :
    Fintype.card (SequentialActionMultiplicity M a b 0 0) = 1 := by
  simp [SequentialActionMultiplicity, Fintype.card_sigma, hM]

end

variable {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x : Fin 1, MPSTensor d (D x)}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
      (fun q : (y : Fin 1) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
  (hInjA : ∀ x, Kraus.IsInjective (A x)) (hD : ∀ x, 0 < D x)
  (hM : ∀ a, M a 0 0 = 1)

/-- A single block is trivially separated from the other blocks. -/
private theorem blocksNotGaugePhaseEquiv_fin_one :
    MPSTensor.BlocksNotGaugePhaseEquiv A :=
  fun j k hjk ↦ absurd (Subsingleton.elim j k) hjk

include hF hA hInjA hD hM in
/-- **Group-like fusion multiplicities.** If a single injective state block
is acted on by every operator block without multiplicity, then
`∑_c N_{ab}^c = 1` for every pair `a, b`. The L matrix has one row and is
invertible, so it has one column. Source: GLM23, lines 607--614, where the
proportionality constants `λ_{a,b}^{c,μ}` presuppose this count. -/
theorem sum_fusionMultiplicity_eq_one_of_singleBlock (a b : Fin r) :
    ∑ c, N a b c = 1 := by
  obtain ⟨h₁, h₂⟩ := actionLMatrix_inverse_of_isInjective VF WF VA WA hF hA hD hInjA
    blocksNotGaugePhaseEquiv_fin_one a b 0 0
  have hcard : (Fintype.card (FusionActionMultiplicity N M a b 0 0) : ℂ) =
      Fintype.card (SequentialActionMultiplicity M a b 0 0) := by
    rw [← Matrix.trace_one, ← h₂, Matrix.trace_mul_comm, h₁, Matrix.trace_one]
  rw [card_sequentialActionMultiplicity_of_singleBlock hM] at hcard
  have hQ : Fintype.card (FusionActionMultiplicity N M a b 0 0) = ∑ c, N a b c := by
    simp [FusionActionMultiplicity, Fintype.card_sigma, hM]
  exact_mod_cast hQ ▸ hcard

include hF hA hInjA hD hM in
/-- The fusion channels of a pair `a, b` form a singleton. -/
theorem subsingleton_fusionChannel_of_singleBlock (a b : Fin r) :
    Subsingleton ((c : Fin r) × Fin (N a b c)) := by
  rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_sigma]
  simp [sum_fusionMultiplicity_eq_one_of_singleBlock VF WF VA WA hF hA hInjA hD hM a b]

include hF hA hInjA hD hM in
/-- Every fusion multiplicity space is a singleton or empty. -/
theorem subsingleton_fin_fusionMultiplicity_of_singleBlock (a b c : Fin r) :
    Subsingleton (Fin (N a b c)) := by
  rw [Fin.subsingleton_iff_le_one,
    ← sum_fusionMultiplicity_eq_one_of_singleBlock VF WF VA WA hF hA hInjA hD hM a b]
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c)

/-- **The proportionality constants** `λ_{a,b}^{c,μ} = (L̂^x_{abx})^x_{c,μ}`
of GLM23, line 611: the single entry of the inverse L matrix in the
column `(c,0,μ)`. -/
noncomputable def singleBlockLambda (a b c : Fin r) (μ : Fin (N a b c)) : ℂ :=
  inverseActionLMatrix VF VA WA a b 0 0 ⟨c, singleBlockIndex hM c, μ⟩ (singleBlockRow hM a b)

include hF hA hInjA hD in
/-- The L entries and the constants `λ` are mutually inverse: `L λ = 1`.
Source: GLM23, lines 607--614. -/
theorem actionLMatrix_mul_singleBlockLambda (a b c : Fin r) (μ : Fin (N a b c)) :
    actionLMatrix WF VA WA a b 0 0 (singleBlockRow hM a b) ⟨c, singleBlockIndex hM c, μ⟩ *
      singleBlockLambda VF VA WA hM a b c μ = 1 := by
  obtain ⟨h₁, -⟩ := actionLMatrix_inverse_of_isInjective VF WF VA WA hF hA hD hInjA
    blocksNotGaugePhaseEquiv_fin_one a b 0 0
  have : Subsingleton (FusionActionMultiplicity N M a b 0 0) := by
    rw [← Fintype.card_le_one_iff_subsingleton]
    simp [FusionActionMultiplicity, Fintype.card_sigma, hM,
      sum_fusionMultiplicity_eq_one_of_singleBlock VF WF VA WA hF hA hInjA hD hM a b]
  have h := congrArg (fun Z ↦ Z (singleBlockRow hM a b) (singleBlockRow hM a b)) h₁
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rwa [Fintype.sum_subsingleton _ ⟨c, singleBlockIndex hM c, μ⟩] at h

include hF hA hInjA hD in
/-- The constants `λ` do not vanish. -/
theorem singleBlockLambda_ne_zero (a b c : Fin r) (μ : Fin (N a b c)) :
    singleBlockLambda VF VA WA hM a b c μ ≠ 0 :=
  right_ne_zero_of_mul_eq_one
    (actionLMatrix_mul_singleBlockLambda VF WF VA WA hF hA hInjA hD hM a b c μ)

variable (O A) in
include hF hA hInjA hD in
/-- **The F-symbols of an MPO leaving an injective state invariant are
trivial.** For a single injective state block acted on without
multiplicity, every F coefficient of the exact fusion maps is

`F[(d,η,χ),(f,μ,ν)] = λ_{ab}^{dη} λ_{dc}^{eχ} / (λ_{bc}^{fμ} λ_{af}^{eν})`.

Source: GLM23, lines 615--626. The orientation of the multiplicity indices
of `F` is the corrected one of `docs/paper-gaps/glm23_multiplicity_l_indices.tex`;
there the source's labels `μ, ν` and `χ, η` of this display are exchanged. -/
theorem fusionFMatrix_eq_singleBlockLambda
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (a b c d e f : Fin r) (η : Fin (N a b d)) (χ' : Fin (N d c e))
    (μ : Fin (N b c f)) (ν : Fin (N a f e)) :
    fusionFMatrix VF WF a b c e ⟨d, η, χ'⟩ ⟨f, μ, ν⟩ =
      singleBlockLambda VF VA WA hM a b d η * singleBlockLambda VF VA WA hM d c e χ' /
        (singleBlockLambda VF VA WA hM b c f μ * singleBlockLambda VF VA WA hM a f e ν) := by
  classical
  have hsub := subsingleton_fin_of_singleBlock hM
  have hchan := subsingleton_fusionChannel_of_singleBlock VF WF VA WA hF hA hInjA hD hM
  have hfin := subsingleton_fin_fusionMultiplicity_of_singleBlock VF WF VA WA hF hA hInjA hD hM
  have hp := actionLMatrix_mixed_pentagon O A hInjO hInjA hχ hD hneO
    blocksNotGaugePhaseEquiv_fin_one VF WF VA WA hF hA a b c e f 0 0 0 0
    (singleBlockIndex hM a) (singleBlockIndex hM b) (singleBlockIndex hM c)
    (singleBlockIndex hM e) μ ν
  rw [Finset.sum_eq_single d (fun v _ hv ↦ Finset.sum_eq_zero fun _ _ ↦
      Finset.sum_eq_zero fun η' _ ↦ absurd
        (congrArg Sigma.fst (Subsingleton.elim (⟨v, η'⟩ : (c : Fin r) × Fin (N a b c)) ⟨d, η⟩))
        hv) (fun h ↦ absurd (Finset.mem_univ d) h),
    Fintype.sum_subsingleton _ (singleBlockIndex hM d), Fintype.sum_subsingleton _ η,
    Fintype.sum_subsingleton _ χ', Fintype.sum_subsingleton _ (singleBlockIndex hM f)] at hp
  have hL : ∀ (a b c : Fin r) (μ : Fin (N a b c)),
      actionLMatrix WF VA WA a b 0 0 (singleBlockRow hM a b) ⟨c, singleBlockIndex hM c, μ⟩ =
        (singleBlockLambda VF VA WA hM a b c μ)⁻¹ := fun a b c μ ↦
    eq_inv_of_mul_eq_one_left
      (actionLMatrix_mul_singleBlockLambda VF WF VA WA hF hA hInjA hD hM a b c μ)
  have hne := singleBlockLambda_ne_zero VF WF VA WA hF hA hInjA hD hM
  change actionLMatrix WF VA WA a b 0 0 (singleBlockRow hM a b) ⟨d, _, η⟩ *
      actionLMatrix WF VA WA d c 0 0 (singleBlockRow hM d c) ⟨e, _, χ'⟩ *
        fusionFMatrix VF WF a b c e ⟨d, η, χ'⟩ ⟨f, μ, ν⟩ =
      actionLMatrix WF VA WA b c 0 0 (singleBlockRow hM b c) ⟨f, _, μ⟩ *
        actionLMatrix WF VA WA a f 0 0 (singleBlockRow hM a f) ⟨e, _, ν⟩ at hp
  rw [hL, hL, hL, hL] at hp
  have h1 := hne a b d η
  have h2 := hne d c e χ'
  have h3 := hne b c f μ
  have h4 := hne a f e ν
  field_simp at hp ⊢
  linear_combination hp

variable (O A) in
include hF hA hInjA hD hM in
/-- **The F-symbols are gauge equivalent to one.** Rescaling the exact
fusion maps by the constants `λ`, analysis by `λ⁻¹` and synthesis by `λ`,
gives exact fusion maps all of whose F coefficients equal one. Source:
GLM23, lines 626--630: "the F-symbols of the MPO belong to the trivial
class, i.e. they are gauge equivalent to 1". -/
theorem exists_fusionFMatrix_eq_one_of_singleBlock
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor)) :
    ∃ (VF' : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
      (WF' : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ),
      (∀ a b, MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF' a b q.1 q.2) (fun q ↦ WF' a b q.1 q.2)) ∧
      ∀ a b c e p q, fusionFMatrix VF' WF' a b c e p q = 1 := by
  classical
  let lam := singleBlockLambda VF VA WA hM
  have ht := singleBlockLambda_ne_zero VF WF VA WA hF hA hInjA hD hM
  refine ⟨fun a b c μ ↦ (lam a b c μ)⁻¹ • VF a b c μ, fun a b c μ ↦ lam a b c μ • WF a b c μ,
    fun a b ↦ (hF a b).inv_smul_smul (fun q ↦ lam a b q.1 q.2) (fun q ↦ ht a b q.1 q.2), ?_⟩
  rintro a b c e ⟨d, η, χ'⟩ ⟨f, μ, ν⟩
  have hfin := subsingleton_fin_fusionMultiplicity_of_singleBlock VF WF VA WA hF hA hInjA hD hM
  rw [fusionFMatrix_regauge (Y := fun a b c μ _ ↦ (lam a b c μ)⁻¹)
      (Yh := fun a b c μ _ ↦ lam a b c μ)
      (fun a b c μ ↦ by rw [Fintype.sum_subsingleton _ μ])
      (fun a b c μ ↦ by rw [Fintype.sum_subsingleton _ μ]),
    Fintype.sum_subsingleton _ η, Fintype.sum_subsingleton _ χ', Fintype.sum_subsingleton _ μ,
    Fintype.sum_subsingleton _ ν,
    fusionFMatrix_eq_singleBlockLambda O A VF WF VA WA hF hA hInjA hD hM hInjO hχ hneO]
  have h1 := ht a b d η
  have h2 := ht d c e χ'
  have h3 := ht b c f μ
  have h4 := ht a f e ν
  simp only [lam]
  field_simp

end MPOTensor
