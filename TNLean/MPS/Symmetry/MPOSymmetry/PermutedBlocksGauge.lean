/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.StabilizerBlockIndependenceCircle
import TNLean.Algebra.StabilizerCocycleReconstruction
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorCohomology
import TNLean.MPS.Symmetry.MPOSymmetry.PermutedBlocks

/-!
# Gauge law of the L-symbols of permuted blocks and the stabilizer form

Let `g ↦ O_g` be a group of matrix product operators with normal tensors and let `x ↦ A_x` be
normal blocks permuted by it, as in `TNLean.MPS.Symmetry.MPOSymmetry.PermutedBlocks`. Fusion
tensors `F^<_{g,h} = V_{g,h}`, `F^>_{g,h} = W_{g,h}` and action tensors `A^Γ_{g,x} = V_{g,x}`,
`A^{refΓ}_{g,x} = W_{g,x}` carry the scalar gauge freedoms of arXiv:2502.20257,
`eq:scalar_fus_ten` (`main.tex` lines 1500--1504) and `eq:scalar_act_ten` (lines 1871--1873):
the right tensors are multiplied by `β_{g,h}` and `γ_{g,x}` and the left ones by their inverses.

Two choices of fusion and of action tensors are compared against long words by nonzero
scalars `β_{g,h}` and `γ_{g,x}`, and the L-symbols of the two choices satisfy the gauge law
`eq:Lsymbgauge` (line 1918):
`L'ˣ_{g,h} = γ_{gh,x} β_{g,h} / (γ_{g,hx} γ_{h,x}) Lˣ_{g,h}`.
Conversely every pair of scalar gauges is realized by rescaling the tensors.

With this law, the scalar classification of L-symbols for a transitive action
(arXiv:2203.12563, Section 4.1) applies to the L-symbols of actual tensors. For a nonanomalous
family, some fusion and action gauge has `ω = 1` and `Lˣ_{g₁,g₂} = ψ(h₁,h₂)` for a stabilizer
two-cocycle `ψ` (arXiv:2502.20257, Lemma `lemma:h1h2`, lines 7028--7042), with the corrected
transition elements `h₂ = k_{g₂x}⁻¹ g₂ k_x` and `h₁ = k_{g₁g₂x}⁻¹ g₁ k_{g₂x}`. For a finite group
the cocycle can be taken with values in `U(1)`, and block independence of the L-symbols holds
exactly when the class `[ψ] ∈ H²(H, U(1))` extends to `G` (Proposition `prop:BI_psi`,
lines 7042--7064).

**Local fix (boundary-dressed scalars):** the source defines `β`, `γ` and the L-symbols as bare
scalars relating the tensors themselves. The available uniqueness of reductions onto a normal
tensor (arXiv:1706.07329v2, Theorem 22) relates two reductions only against long words, so all
three are defined here by comparison against long words, and the gauge law is proved in that
form. See `docs/paper-gaps/fbc25_boundary_dressed_l_symbols.tex`. The transition-element index
correction is recorded in `docs/paper-gaps/fbc25_stabilizer_transition_index_typo.tex`.

## Main definitions

* `MPOTensor.GroupFamily.FusionData.rescale`: reciprocal rescaling of fusion tensors.
* `MPOTensor.GroupFamily.BlockActionData.relativeScalar`: the scalars comparing two choices of
  action tensors.
* `MPOTensor.GroupFamily.BlockActionData.rescale`: reciprocal rescaling of action tensors.

## Main results

* `MPOTensor.GroupFamily.BlockActionData.lSymbol_eq_gauge`: the gauge law `eq:Lsymbgauge`.
* `MPOTensor.GroupFamily.BlockActionData.lSymbol_rescale`: rescaled tensors realize every
  joint scalar gauge.
* `MPOTensor.GroupFamily.BlockActionData.exists_rescale_omega_eq_one_lSymbol_eq_one`: for a
  single block, some gauge has `ω = 1` and `L = 1` (arXiv:2502.20257, lines 1925--1926).
* `MPOTensor.GroupFamily.BlockActionData.exists_rescale_lSymbol_eq_inducedLSymbol`:
  `lemma:h1h2`, with `exists_rescale_lSymbol_eq_inducedLSymbol_of_finite` for `U(1)`-valued
  cocycles.
* `MPOTensor.GroupFamily.BlockActionData.isBlockIndependent_lSymbol_iff_circle`: `prop:BI_psi`.
-/

open scoped Matrix Kronecker
open TNLean.Algebra

open scoped TNLean.Algebra.ScalarCohomology

namespace MPOTensor

namespace GroupFamily

universe v

variable {d : ℕ} {G : Type} [Group G] {F : GroupFamily G d}
  {X : Type v} [MulAction G X] {D : X → ℕ} {A : (x : X) → MPSTensor d (D x)}

/-! ### Rescaling of fusion tensors -/

namespace FusionData

/-- **Reciprocal rescaling of fusion tensors** (arXiv:2502.20257, `eq:scalar_fus_ten`, `main.tex`
lines 1500--1504): `F^>_{g,h} ↦ β_{g,h} F^>_{g,h}` and `F^<_{g,h} ↦ β_{g,h}⁻¹ F^<_{g,h}`. -/
noncomputable def rescale (fd : FusionData F) (β : ScalarCocycle G) : FusionData F where
  V g h := ((β (g, h) : ℂ))⁻¹ • fd.V g h
  W g h := (β (g, h) : ℂ) • fd.W g h
  isReduction g h := (fd.isReduction g h).reciprocal_smul (β (g, h)).ne_zero

/-- The left fusion tensors before and after rescaling by `β` differ by `β`. -/
theorem isDressedProportional_rescale (fd : FusionData F) (β : ScalarCocycle G) (g h : G) :
    MPSTensor.IsDressedProportional (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
      (fd.V g h) ((fd.rescale β).V g h) (β (g, h)) :=
  ⟨0, fun w _ ↦ by simp [rescale, Matrix.smul_mul, smul_smul, (β (g, h)).ne_zero]⟩

/-- Rescaling the fusion tensors by `β` is compared to the original choice by `β`. -/
theorem relativeScalar_rescale (hF : F.IsNormalRepresentation) (fd : FusionData F)
    (β : ScalarCocycle G) : fd.relativeScalar (fd.rescale β) = β := by
  funext ⟨g, h⟩
  apply Units.ext
  exact (isDressedProportional_relativeScalar hF fd (fd.rescale β) g h).eq_of_forall_exists_ne_zero
    (isDressedProportional_rescale fd β g h)
    ((fd.isReduction g h).exists_mul_evalWord_ne_zero (hF.isNormal _) (F.bondDim_pos _))

/-- Rescaling the fusion tensors by `β` changes `ω` by the coboundary of `β`
(arXiv:2502.20257, `eq:omegagauge`, `main.tex` lines 1541--1545). -/
theorem omega_rescale (hF : F.IsNormalRepresentation) (fd : FusionData F)
    (β : ScalarCocycle G) :
    (fd.rescale β).omega = ScalarThreeCochain.fusionGauge β fd.omega := by
  rw [omega_eq_fusionGauge hF fd (fd.rescale β), relativeScalar_rescale hF]

end FusionData

/-! ### Comparison and rescaling of action tensors -/

namespace BlockActionData

/-- The scalars comparing two choices of action tensors: `γ_{g,x}` is the nonzero scalar with
`V_{g,x} B^w = γ_{g,x} V'_{g,x} B^w` for all long words `w` of `B = O_g · A_x`
(`MPOTensor.GroupFamily.BlockActionData.isDressedProportional_relativeScalar`), set to one if no
such scalar exists.

Source: the scalar gauge freedom of the action tensors, arXiv:2502.20257, `eq:scalar_act_ten`,
`main.tex` lines 1871--1873, under which `A^{refΓ}_{g,x} ↦ γ_{g,x} A^{refΓ}_{g,x}` and
`A^Γ_{g,x} ↦ γ_{g,x}⁻¹ A^Γ_{g,x}`. -/
noncomputable def relativeScalar (ad ad' : BlockActionData F A) : ActionTensorGauge G X :=
  fun g x ↦ MPSTensor.dressedScalar (actTensor (F.tensor g) (A x)) (ad.V g x) (ad'.V g x)

/-- Two choices of action tensors differ, against long words, by `relativeScalar`. -/
theorem isDressedProportional_relativeScalar (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (ad ad' : BlockActionData F A)
    (g : G) (x : X) :
    MPSTensor.IsDressedProportional (actTensor (F.tensor g) (A x)) (ad.V g x) (ad'.V g x)
      (ad.relativeScalar ad' g x) := by
  have hex : ∃ z : ℂ, z ≠ 0 ∧ MPSTensor.IsDressedProportional
      (actTensor (F.tensor g) (A x)) (ad.V g x) (ad'.V g x) z :=
    (ad.isReduction g x).exists_isDressedProportional (ad'.isReduction g x) (hA _)
      ((hperm g x).sameMPV₂Pos_actTensor (MPSTensor.SameMPV₂Pos.refl (A x)))
  exact MPSTensor.isDressedProportional_dressedScalar hex

/-- **Reciprocal rescaling of action tensors** (arXiv:2502.20257, `eq:scalar_act_ten`,
`main.tex` lines 1871--1873): `A^{refΓ}_{g,x} ↦ γ_{g,x} A^{refΓ}_{g,x}` and
`A^Γ_{g,x} ↦ γ_{g,x}⁻¹ A^Γ_{g,x}`.

`BlockActionData.smul` in `TNLean/MPS/MPU/ActionCommonBlocking.lean` performs the same
rescaling with a complex scalar and a separate nonvanishing hypothesis. It is not reused here
because that module belongs to the matrix product unitary layer, which imports this symmetry
layer rather than the reverse; the unit-valued gauge here is the form the gauge law uses. -/
noncomputable def rescale (ad : BlockActionData F A) (γ : ActionTensorGauge G X) :
    BlockActionData F A where
  V g x := ((γ g x : ℂ))⁻¹ • ad.V g x
  W g x := (γ g x : ℂ) • ad.W g x
  isReduction g x := (ad.isReduction g x).reciprocal_smul (γ g x).ne_zero

/-- Rescaling the action tensors by `γ` is compared to the original choice by `γ`. -/
theorem relativeScalar_rescale (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (ad : BlockActionData F A)
    (γ : ActionTensorGauge G X) : ad.relativeScalar (ad.rescale γ) = γ := by
  funext g x
  apply Units.ext
  exact (isDressedProportional_relativeScalar hA hperm ad (ad.rescale γ) g x)
    |>.eq_of_forall_exists_ne_zero
      ⟨0, fun w _ ↦ by simp [rescale, Matrix.smul_mul, smul_smul, (γ g x).ne_zero]⟩
    ((ad.isReduction g x).exists_mul_evalWord_ne_zero (hA _) (hD _))

/-! ### The gauge law -/

/-- **The gauge law of the L-symbols of permuted blocks** (arXiv:2502.20257, `eq:Lsymbgauge`,
`main.tex` lines 1915--1918): if `β` compares two choices of fusion tensors and `γ` two choices
of action tensors, the L-symbols of the two choices are related by
`L'ˣ_{g,h} = γ_{gh,x} β_{g,h} / (γ_{g,hx} γ_{h,x}) Lˣ_{g,h}`.

All three scalars are boundary-dressed, as recorded in the module docstring. -/
theorem lSymbol_eq_gauge (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x))
    (hD : ∀ x, 0 < D x) (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (fd fd' : FusionData F) (ad ad' : BlockActionData F A) :
    ad'.lSymbol fd' =
      LSymbol.gauge (fd.relativeScalar fd') (ad.relativeScalar ad') (ad.lSymbol fd) := by
  funext x g h
  have hγ := isDressedProportional_relativeScalar hA hperm ad ad'
  have hSame : ∀ (a : G) {n : ℕ} (C : MPSTensor d n) (y : X),
      MPSTensor.SameMPV₂Pos C (A y) →
        MPSTensor.SameMPV₂Pos (actTensor (F.tensor a) C) (A (a • y)) :=
    fun a _ C y hC ↦ (hperm a y).sameMPV₂Pos_actTensor hC
  -- the tree acting with `h` and then `g`
  have hact : MPSTensor.IsDressedProportional
      (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x))
      (ad.actV g h x) (ad'.actV g h x) (ad.relativeScalar ad' h x *
        ad.relativeScalar ad' g (h • x)) := by
    have h₁ := ((hγ h x).actTensor_idKron (F.tensor g)).mul_left (ad.V g (h • x))
    have h₂ := (hγ g (h • x)).pullback ((ad'.isReduction h x).actTensor_idKron (F.tensor g))
      ((hSame g _ (h • x) (hSame h _ x (MPSTensor.SameMPV₂Pos.refl (A x)))).trans
        (hSame g _ (h • x) (MPSTensor.SameMPV₂Pos.refl _)).symm)
    exact (h₁.trans h₂).of_intertwine (mulTensorAssocMatrix_mul_invMatrix _ _ _)
      (mulTensorAssocInvMatrix_mul_matrix _ _ _)
      (actTensor_mulTensor_mul_assocMatrix (F.tensor g) (F.tensor h) (A x))
  -- the tree fusing `g` with `h` and then acting
  have hfuse : MPSTensor.IsDressedProportional
      (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x))
      (ad.fuseV fd g h x) (ad'.fuseV fd' g h x) (fd.relativeScalar fd' (g, h) *
        ad.relativeScalar ad' (g * h) x) := by
    have hSameB : MPSTensor.SameMPV₂Pos
        (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x))
        (actTensor (F.tensor (g * h)) (A x)) := by
      intro N hN σ
      rw [(((hperm g _).mulTensor (hperm h x)).sameMPV₂Pos_actTensor
          (MPSTensor.SameMPV₂Pos.refl (A x))) N hN σ,
        (hSame (g * h) _ x (MPSTensor.SameMPV₂Pos.refl (A x))) N hN σ, mul_smul]
    have h₁ := ((FusionData.isDressedProportional_relativeScalar hF fd fd' g h).actTensor_kronId
      (A x)).mul_left (ad.V (g * h) x)
    have h₂ := (hγ (g * h) x).pullback ((fd'.isReduction g h).actTensor_kronId (A x)) hSameB
    exact (h₁.trans h₂).mul_left (castIndex D (mul_smul g h x))
  have key := (hact.trans (isDressedProportional_lSymbol (fd := fd') (ad := ad') hA hperm x g h))
    |>.eq_of_forall_exists_ne_zero
      ((isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hperm x g h).trans hfuse)
      (by
        obtain ⟨W, hW⟩ := ad.exists_isReduction_actV g h x
        exact hW.exists_mul_evalWord_ne_zero (hA _) (hD _))
  apply Units.ext
  simp only [LSymbol.gauge, Units.val_mul, Units.val_div_eq_div_val] at key ⊢
  have h₁ := (ad.relativeScalar ad' g (h • x)).ne_zero
  have h₂ := (ad.relativeScalar ad' h x).ne_zero
  field_simp
  linear_combination key

/-- **Rescaled tensors realize every joint scalar gauge.** Rescaling the fusion tensors by `β`
and the action tensors by `γ` changes the L-symbols by the joint scalar gauge of
arXiv:2502.20257, `eq:Lsymbgauge`. -/
theorem lSymbol_rescale (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x))
    (hD : ∀ x, 0 < D x) (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (fd : FusionData F) (ad : BlockActionData F A) (β : ScalarCocycle G)
    (γ : ActionTensorGauge G X) :
    (ad.rescale γ).lSymbol (fd.rescale β) = LSymbol.gauge β γ (ad.lSymbol fd) := by
  rw [lSymbol_eq_gauge hF hA hD hperm fd (fd.rescale β) ad (ad.rescale γ),
    FusionData.relativeScalar_rescale hF, relativeScalar_rescale hA hD hperm]

/-! ### A single block -/

/-- **A single block: `ω = 1` and `L = 1` in some gauge.** If there is exactly one block, some
rescaling of the fusion and action tensors makes both the anomaly three-cochain and the
L-symbols identically one.

Source: arXiv:2502.20257, `main.tex` lines 1925--1926 ("whenever `|X| = 1` ... there is a choice
of gauge such that `ω(g,h,k) = L_{g,h} = 1`"). The gauge rescales the fusion tensors by the
inverse L-symbols and leaves the action tensors unchanged. -/
theorem exists_rescale_omega_eq_one_lSymbol_eq_one [Unique X] (hF : F.IsNormalRepresentation)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (fd : FusionData F)
    (ad : BlockActionData F A) :
    ∃ (β : ScalarCocycle G) (γ : ActionTensorGauge G X),
      (fd.rescale β).omega = 1 ∧ (ad.rescale γ).lSymbol (fd.rescale β) = 1 := by
  refine ⟨fun p ↦ (ad.lSymbol fd default p.1 p.2)⁻¹, 1, ?_⟩
  have hL : (ad.rescale 1).lSymbol (fd.rescale fun p ↦ (ad.lSymbol fd default p.1 p.2)⁻¹) = 1 := by
    rw [lSymbol_rescale hF hA hD hperm]
    funext x g h
    rw [Subsingleton.elim x default]
    simp [LSymbol.gauge]
  refine ⟨?_, hL⟩
  have hc := isCompatible_lSymbol (fd := fd.rescale fun p ↦ (ad.lSymbol fd default p.1 p.2)⁻¹)
    (ad := ad.rescale 1) hF hA hD hperm
  rw [hL] at hc
  funext g h k
  simpa using (hc default g h k).symm

/-! ### The stabilizer form of nonanomalous L-symbols -/

variable {x₀ : X}

/-- **Nonanomalous L-symbols in stabilizer-cocycle form** (arXiv:2502.20257, Lemma `lemma:h1h2`,
`main.tex` lines 7028--7042). Let the group act on the blocks with basepoint `x₀`, stabilizer
`H`, and representatives `k_x` with `k_x x₀ = x` and `k_{x₀} = e`. If the anomaly class
vanishes, some rescaling of the fusion and action tensors gives `ω = 1` and
`Lˣ_{g₁,g₂} = ψ(h₁,h₂)` for a two-cocycle `ψ` on `H`, where `h₂ = k_{g₂x}⁻¹ g₂ k_x` and
`h₁ = k_{g₁g₂x}⁻¹ g₁ k_{g₂x}`.

The two-cocycle is a representative, not a cohomology class. The first factor uses the corrected
representative index recorded in `docs/paper-gaps/fbc25_stabilizer_transition_index_typo.tex`.
The gauge `ω = 1` is derived from the vanishing of the anomaly class. -/
theorem exists_rescale_lSymbol_eq_inducedLSymbol (hF : F.IsNormalRepresentation)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hω : hF.anomalyClass = 0) (K : StabilizerRepresentatives G X x₀) (fd : FusionData F)
    (ad : BlockActionData F A) :
    ∃ (β : ScalarCocycle G) (γ : ActionTensorGauge G X),
      (fd.rescale β).omega = 1 ∧
        ∃ ψ : ScalarCocycle (MulAction.stabilizer G x₀), groupCohomology.IsMulCocycle₂ ψ ∧
          (ad.rescale γ).lSymbol (fd.rescale β) = K.inducedLSymbol ψ := by
  obtain ⟨β, hβ⟩ := ((FusionData.isTrivialGaugeClass_omega_iff hF fd).2 hω).symm
  have hω₁ : (fd.rescale β).omega = 1 := by
    rw [FusionData.omega_rescale hF, hβ]
    rfl
  have hR : LSymbol.IsCompatible (LSymbol.gauge β (fun _ _ ↦ 1) (ad.lSymbol fd))
      (fun _ _ _ ↦ 1) := by
    simpa only [hβ] using (isCompatible_lSymbol (fd := fd) (ad := ad) hF hA hD hperm).gauge β
      (fun _ _ ↦ 1)
  obtain ⟨γ, hγ⟩ := K.exists_actionGauge_eq_inducedLSymbol hR
  refine ⟨β, γ⁻¹, hω₁, _, hR.isCocycle_restrict x₀, ?_⟩
  rw [lSymbol_rescale hF hA hD hperm]
  calc LSymbol.gauge β γ⁻¹ (ad.lSymbol fd)
      = LSymbol.gauge (fun _ ↦ 1) γ⁻¹ (LSymbol.gauge β (fun _ _ ↦ 1) (ad.lSymbol fd)) := by
        rw [LSymbol.gauge_comp]
        congr 1
        exacts [(mul_one β).symm, (one_mul γ⁻¹).symm]
    _ = LSymbol.gauge (fun _ ↦ 1) γ⁻¹ (LSymbol.gauge (fun _ ↦ 1) γ (K.inducedLSymbol _)) :=
        congrArg _ hγ
    _ = _ := by
        rw [LSymbol.gauge_comp]
        conv_rhs => rw [← LSymbol.gauge_one (K.inducedLSymbol _)]
        congr 1
        exacts [mul_one _, mul_inv_cancel γ]

/-- **Nonanomalous L-symbols in stabilizer-cocycle form with `U(1)` values.** For a finite
group, the two-cocycle of `exists_rescale_lSymbol_eq_inducedLSymbol` can be chosen with values
of modulus one, as in arXiv:2502.20257, Lemma `lemma:h1h2` (`main.tex` lines 7028--7042), where
`ψ` is valued in `U(1)`. The unit phase of the cocycle is cohomologous to it, by the
finite-group comparison of `docs/paper-gaps/fbc25_circle_complex_units_cohomology.tex`, and the
coboundary is absorbed into the action gauge. -/
theorem exists_rescale_lSymbol_eq_inducedLSymbol_of_finite [Finite G]
    (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hω : hF.anomalyClass = 0) (K : StabilizerRepresentatives G X x₀) (fd : FusionData F)
    (ad : BlockActionData F A) :
    ∃ (β : ScalarCocycle G) (γ : ActionTensorGauge G X),
      (fd.rescale β).omega = 1 ∧
        ∃ ψ : ScalarCocycle (MulAction.stabilizer G x₀), groupCohomology.IsMulCocycle₂ ψ ∧
          (∀ p, ‖(ψ p : ℂ)‖ = 1) ∧
          (ad.rescale γ).lSymbol (fd.rescale β) = K.inducedLSymbol ψ := by
  obtain ⟨β, γ, hω₁, ψ, hψ, hL⟩ :=
    exists_rescale_lSymbol_eq_inducedLSymbol hF hA hD hperm hω K fd ad
  have hψ₁ := ScalarCocycle.circlePhaseInclusion_isMulCocycle₂ hψ
  obtain ⟨γ', hγ'⟩ := (K.isMulCoboundary₂_div_iff_exists_actionGauge_inducedLSymbol_eq ψ
    ψ.circlePhaseInclusion).1
    ((H2π_eq_iff_isMulCoboundary₂_div hψ hψ₁).1 (ScalarCocycle.H2π_circlePhaseInclusion hψ))
  refine ⟨β, γ * γ'⁻¹, hω₁, _, hψ₁, fun p ↦ by
    simp [ScalarCocycle.circlePhaseInclusion], ?_⟩
  rw [lSymbol_rescale hF hA hD hperm] at hL ⊢
  calc LSymbol.gauge β (γ * γ'⁻¹) (ad.lSymbol fd)
      = LSymbol.gauge (fun _ ↦ 1) γ'⁻¹ (LSymbol.gauge β γ (ad.lSymbol fd)) := by
        rw [LSymbol.gauge_comp]
        congr 1
        exact (mul_one β).symm
    _ = _ := by
        rw [hL, hγ', LSymbol.gauge_comp]
        conv_rhs => rw [← LSymbol.gauge_one (K.inducedLSymbol _)]
        congr 1
        exacts [mul_one _, mul_inv_cancel γ']

/-! ### Block independence and extension of the stabilizer class -/

/-- **Block independence of the L-symbols of actual tensors, with `ℂˣ` coefficients.** If some
rescaling of the tensors puts the L-symbols in the stabilizer form `Lˣ_{g₁,g₂} = ψ(h₁,h₂)`, the
L-symbols are block independent exactly when the class `[ψ] ∈ H²(H, ℂˣ)` lies in the image of
restriction from `H²(G, ℂˣ)`.

Source: arXiv:2502.20257, Proposition `prop:BI_psi`, `main.tex` lines 7042--7064, with the
coefficients `ℂˣ` of lines 1927--1931. -/
theorem isBlockIndependent_lSymbol_iff (hF : F.IsNormalRepresentation)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (K : StabilizerRepresentatives G X x₀) (fd : FusionData F) (ad : BlockActionData F A)
    {β : ScalarCocycle G} {γ : ActionTensorGauge G X}
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)} (hψ : groupCohomology.IsMulCocycle₂ ψ)
    (hL : (ad.rescale γ).lSymbol (fd.rescale β) = K.inducedLSymbol ψ) :
    LSymbol.IsBlockIndependent (ad.lSymbol fd) ↔
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hψ) ∈
        Set.range (groupCohomology.map (MulAction.stabilizer G x₀).subtype
          (scalarRepresentationRes (MulAction.stabilizer G x₀).subtype) 2) := by
  rw [← LSymbol.isBlockIndependent_gauge_iff β γ, ← lSymbol_rescale hF hA hD hperm, hL]
  exact K.inducedLSymbol_isBlockIndependent_iff_H2π_mem_range_map_subtype hψ

/-- **Block independence and extension of the stabilizer class** (arXiv:2502.20257,
Proposition `prop:BI_psi`, `main.tex` lines 7042--7064). Let a finite group act on the blocks of
a nonanomalous family, with basepoint `x₀`, stabilizer `H`, and representatives `k_x`. Some
rescaling of the fusion and action tensors gives `ω = 1` and `Lˣ_{g₁,g₂} = ψ(h₁,h₂)` for a
`U(1)`-valued two-cocycle `ψ` on `H`, and for every such choice the L-symbols are block
independent exactly when the class `[ψ] ∈ H²(H, U(1))` lies in the image of the restriction
map `H²(G, U(1)) → H²(H, U(1))`.

The class is the class of the unit phase of `ψ`, which is `ψ` itself. The representative-level
form of the criterion is
`TNLean.Algebra.StabilizerRepresentatives.inducedLSymbol_isBlockIndependent_iff_exists_extension`.
The stabilizer need not be normal. -/
theorem isBlockIndependent_lSymbol_iff_circle [Finite G] (hF : F.IsNormalRepresentation)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (K : StabilizerRepresentatives G X x₀) (fd : FusionData F) (ad : BlockActionData F A)
    {β : ScalarCocycle G} {γ : ActionTensorGauge G X}
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)} (hψ : groupCohomology.IsMulCocycle₂ ψ)
    (hL : (ad.rescale γ).lSymbol (fd.rescale β) = K.inducedLSymbol ψ) :
    LSymbol.IsBlockIndependent (ad.lSymbol fd) ↔
      groupCohomology.H2π _
          (ScalarCocycle.circlePhaseMathlibCocycle
            (groupCohomology.cocyclesOfIsMulCocycle₂ hψ)) ∈
        Set.range (groupCohomology.map (MulAction.stabilizer G x₀).subtype
          (circleRepresentationRes (MulAction.stabilizer G x₀).subtype) 2) := by
  rw [← LSymbol.isBlockIndependent_gauge_iff β γ, ← lSymbol_rescale hF hA hD hperm, hL]
  exact K.inducedLSymbol_isBlockIndependent_iff_circle hψ

end BlockActionData

end GroupFamily

end MPOTensor
