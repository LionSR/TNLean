/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommonFixedSubmodule
import TNLean.Algebra.UnitaryCompletionClass
import TNLean.MPS.MPDO.GaussProjectorPlacement

/-!
# The gauge-invariant subspace of a completion and its universal vector

For a completion `R` of prescribed defect maps, the local Gauss projectors are
placed on the periodic two-site windows of a chain of length `N`, and their
common `+1` eigenspace is the gauge-invariant subspace. The projectors average
the modified Gauss laws of FBC25 (arXiv:2502.20257, lines 4325--4335), whose
gauge block at the window `(j, j + 1)` compares the completion at the two
labels adjacent to that window.

A chain site carries one matter index and one gauge label. Matter defect
states `Ψ α` indexed by gauge-label configurations `α` assemble into the
gauged vector whose component at a configuration is the component of `Ψ α` at
the matter part of that configuration, `α` being its gauge-label part; this is
`∑_α Ψ_α ⊗ |α⟩`. Under two hypotheses on the matter defect states -- the
matter support inside every window lies in the defect subspace of the two
labels adjacent to it, and the prescribed defect maps are exactly covariant
under moving those two labels -- the gauged vector is fixed by every placed
Gauss operator, hence by every placed projector, of every completion. It
therefore lies in the gauge-invariant subspace, whose dimension is at least one
whenever the gauged vector does not vanish. This is the invariance statement
following the modified Gauss laws of FBC25 (arXiv:2502.20257, lines
4325--4335); the question of the size of this subspace (arXiv:2502.20257,
line 5198) is untouched.

**Scope restriction (abstract defect covariance):** FBC25 derives the local
support and covariance from locally orthogonal MPS blocks and its modified
fusion maps. This module assumes those two properties. The remaining
specialization is documented in
`docs/paper-gaps/fbc25_state_level_gauging_covariance.tex` and tracked by #7569.

Commutativity of the placed projectors on neighbouring windows, a spectral
gap, and any bound on the subspace beyond dimension at least one are not
treated here.
-/

noncomputable section

open scoped BigOperators Matrix

namespace MPOTensor

/-! ### The label action at one window -/

section LabelAction

variable {G : Type*} [Group G] {N : ℕ}

/-- The gauge-label configuration obtained by moving the two labels adjacent to
the window `(j, j + 1)` by the Gauss leg action `T_g(a, b) = (a g⁻¹, g b)` and
leaving every other label unchanged.

This is the label configuration `T_{j,g} α` of FBC25
(arXiv:2502.20257, lines 4325--4335). -/
def chainLabelAction (hN : 2 ≤ N) (j : Fin N) (g : G) (α : Fin N → G) :
    Fin N → G :=
  MPSTensor.replaceWindow 2 hN j α
    ![MPSTensor.extractWindow 2 j α 0 * g⁻¹, g * MPSTensor.extractWindow 2 j α 1]

@[simp]
theorem extractWindow_chainLabelAction_zero (hN : 2 ≤ N) (j : Fin N) (g : G)
    (α : Fin N → G) :
    MPSTensor.extractWindow 2 j (chainLabelAction hN j g α) 0 =
      MPSTensor.extractWindow 2 j α 0 * g⁻¹ := by
  rw [chainLabelAction, MPSTensor.extractWindow_replaceWindow]
  rfl

@[simp]
theorem extractWindow_chainLabelAction_one (hN : 2 ≤ N) (j : Fin N) (g : G)
    (α : Fin N → G) :
    MPSTensor.extractWindow 2 j (chainLabelAction hN j g α) 1 =
      g * MPSTensor.extractWindow 2 j α 1 := by
  rw [chainLabelAction, MPSTensor.extractWindow_replaceWindow]
  rfl

@[simp]
theorem chainLabelAction_one (hN : 2 ≤ N) (j : Fin N) (α : Fin N → G) :
    chainLabelAction hN j (1 : G) α = α := by
  have hvec : (![MPSTensor.extractWindow 2 j α 0 * (1 : G)⁻¹,
      (1 : G) * MPSTensor.extractWindow 2 j α 1] : Fin 2 → G) =
      MPSTensor.extractWindow 2 j α := by
    funext k
    fin_cases k <;> simp
  rw [chainLabelAction, hvec, MPSTensor.replaceWindow_extractWindow]

/-- The label actions at one window compose according to the group law, as the
Gauss leg actions do. -/
theorem chainLabelAction_chainLabelAction (hN : 2 ≤ N) (j : Fin N) (g h : G)
    (α : Fin N → G) :
    chainLabelAction hN j g (chainLabelAction hN j h α) =
      chainLabelAction hN j (g * h) α := by
  have hvec : (![MPSTensor.extractWindow 2 j (chainLabelAction hN j h α) 0 * g⁻¹,
      g * MPSTensor.extractWindow 2 j (chainLabelAction hN j h α) 1] : Fin 2 → G) =
      ![MPSTensor.extractWindow 2 j α 0 * (g * h)⁻¹,
        g * h * MPSTensor.extractWindow 2 j α 1] := by
    funext k
    fin_cases k <;>
      simp [extractWindow_chainLabelAction_zero, extractWindow_chainLabelAction_one,
        mul_assoc, mul_inv_rev]
  rw [chainLabelAction, hvec, chainLabelAction,
    MPSTensor.replaceWindow_replaceWindow_same, chainLabelAction]

/-- Moving the two labels adjacent to one window is a bijection of gauge-label
configurations, with inverse the move by the inverse group element. This is the
bijection `T_{j,g}` used to reindex the sum over gauge-label configurations in
FBC25 (arXiv:2502.20257, lines 4325--4335). -/
def chainLabelActionEquiv (hN : 2 ≤ N) (j : Fin N) (g : G) :
    (Fin N → G) ≃ (Fin N → G) where
  toFun := chainLabelAction hN j g
  invFun := chainLabelAction hN j g⁻¹
  left_inv α := by
    rw [chainLabelAction_chainLabelAction, inv_mul_cancel, chainLabelAction_one]
  right_inv α := by
    rw [chainLabelAction_chainLabelAction, mul_inv_cancel, chainLabelAction_one]

@[simp]
theorem chainLabelActionEquiv_apply (hN : 2 ≤ N) (j : Fin N) (g : G)
    (α : Fin N → G) :
    chainLabelActionEquiv hN j g α = chainLabelAction hN j g α :=
  rfl

end LabelAction

/-! ### Matter and gauge parts of a chain configuration -/

section Configurations

variable (d : ℕ) (G : Type*) [Fintype G]

/-- The matter part of a configuration of sites, each carrying one matter index
and one gauge label. -/
def gaugedMatter {ι : Type*} (σ : ι → Fin (Fintype.card (Fin d × G))) : ι → Fin d :=
  fun k ↦ ((Fintype.equivFin (Fin d × G)).symm (σ k)).1

/-- The gauge-label part of a configuration of sites, each carrying one matter
index and one gauge label. -/
def gaugedLabel {ι : Type*} (σ : ι → Fin (Fintype.card (Fin d × G))) : ι → G :=
  fun k ↦ ((Fintype.equivFin (Fin d × G)).symm (σ k)).2

theorem gaugedMatter_extractWindow (L : ℕ) {M : ℕ} (i : Fin M)
    (σ : Fin M → Fin (Fintype.card (Fin d × G))) :
    gaugedMatter d G (MPSTensor.extractWindow L i σ) =
      MPSTensor.extractWindow L i (gaugedMatter d G σ) :=
  rfl

theorem gaugedLabel_extractWindow (L : ℕ) {M : ℕ} (i : Fin M)
    (σ : Fin M → Fin (Fintype.card (Fin d × G))) :
    gaugedLabel d G (MPSTensor.extractWindow L i σ) =
      MPSTensor.extractWindow L i (gaugedLabel d G σ) :=
  rfl

private theorem comp_replaceWindow {α β : Type*} (f : α → β) (L : ℕ) {M : ℕ}
    (hLM : L ≤ M) (i : Fin M) (σ : Fin M → α) (τ : Fin L → α) :
    (fun k ↦ f (MPSTensor.replaceWindow L hLM i σ τ k)) =
      MPSTensor.replaceWindow L hLM i (fun k ↦ f (σ k)) (fun k ↦ f (τ k)) := by
  funext k
  unfold MPSTensor.replaceWindow
  by_cases h : (k.val + M - i.val) % M < L <;> simp [h]

theorem gaugedMatter_replaceWindow (L : ℕ) {M : ℕ} (hLM : L ≤ M) (i : Fin M)
    (σ : Fin M → Fin (Fintype.card (Fin d × G)))
    (τ : Fin L → Fin (Fintype.card (Fin d × G))) :
    gaugedMatter d G (MPSTensor.replaceWindow L hLM i σ τ) =
      MPSTensor.replaceWindow L hLM i (gaugedMatter d G σ) (gaugedMatter d G τ) :=
  comp_replaceWindow (fun s ↦ ((Fintype.equivFin (Fin d × G)).symm s).1) L hLM i σ τ

theorem gaugedLabel_replaceWindow (L : ℕ) {M : ℕ} (hLM : L ≤ M) (i : Fin M)
    (σ : Fin M → Fin (Fintype.card (Fin d × G)))
    (τ : Fin L → Fin (Fintype.card (Fin d × G))) :
    gaugedLabel d G (MPSTensor.replaceWindow L hLM i σ τ) =
      MPSTensor.replaceWindow L hLM i (gaugedLabel d G σ) (gaugedLabel d G τ) :=
  comp_replaceWindow (fun s ↦ ((Fintype.equivFin (Fin d × G)).symm s).2) L hLM i σ τ

end Configurations

section GaugedVector

variable (d : ℕ) (G : Type*) [Group G] [Fintype G] [DecidableEq G] {N : ℕ}

omit [Group G] [DecidableEq G] in
/-- A two-site configuration is determined by its matter and gauge-label
parts. -/
theorem gaussLocalCoordinateEquiv_symm_apply
    (τ : Fin 2 → Fin (Fintype.card (Fin d × G))) :
    (gaussLocalCoordinateEquiv d G).symm τ =
      (gaugedMatter d G τ, (gaugedLabel d G τ 0, gaugedLabel d G τ 1)) := by
  rw [Equiv.symm_apply_eq]
  funext k
  fin_cases k <;> simp [gaugedMatter, gaugedLabel]

omit [Group G] [DecidableEq G] in
@[simp]
theorem gaugedMatter_gaussLocalCoordinateEquiv
    (y : (Fin 2 → Fin d) × (G × G)) :
    gaugedMatter d G (gaussLocalCoordinateEquiv d G y) = y.1 := by
  funext k
  fin_cases k <;> simp [gaugedMatter]

omit [Group G] [DecidableEq G] in
@[simp]
theorem gaugedLabel_gaussLocalCoordinateEquiv
    (y : (Fin 2 → Fin d) × (G × G)) :
    gaugedLabel d G (gaussLocalCoordinateEquiv d G y) = ![y.2.1, y.2.2] := by
  funext k
  fin_cases k <;> simp [gaugedLabel]

/-- The local Gauss operator reindexed into two-site chain-window
coordinates. -/
def gaussWindowOperator
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) (g : G) :
    Matrix (Fin 2 → Fin (Fintype.card (Fin d × G)))
      (Fin 2 → Fin (Fintype.card (Fin d × G))) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (gaussLocalCoordinateEquiv d G)
    (TNLean.Algebra.gaussOperator R g)

theorem gaussWindowOperator_apply
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) (g : G)
    (u y : (Fin 2 → Fin d) × (G × G)) :
    gaussWindowOperator d G R g (gaussLocalCoordinateEquiv d G u)
        (gaussLocalCoordinateEquiv d G y) =
      TNLean.Algebra.gaussOperator R g u y := by
  simp only [gaussWindowOperator, Matrix.coe_reindexAlgEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

/-- The local Gauss operator of a completion placed on the periodic two-site
window beginning at `j`. This is the modified (tilded) Gauss law `𝒢^{j,j+1}_g(R)` of
FBC25 (arXiv:2502.20257, lines 4325--4335). -/
def placedGaussOperator (N : ℕ) (hN : 2 ≤ N) (j : Fin N)
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) (g : G) :
    MPOTensor.ChainOperator (Fintype.card (Fin d × G)) N :=
  MPOTensor.embedLocalOperator 2 N hN j (gaussWindowOperator d G R g)

/-- The gauged vector `∑_α Ψ_α ⊗ |α⟩` assembled from matter defect states
indexed by gauge-label configurations, as in FBC25
(arXiv:2502.20257, lines 4325--4335). -/
def gaugedVector (Ψ : (Fin N → G) → (Fin N → Fin d) → ℂ) :
    (Fin N → Fin (Fintype.card (Fin d × G))) → ℂ :=
  fun σ ↦ Ψ (gaugedLabel d G σ) (gaugedMatter d G σ)

omit [Group G] [DecidableEq G] in
@[simp]
theorem gaugedVector_apply (Ψ : (Fin N → G) → (Fin N → Fin d) → ℂ)
    (σ : Fin N → Fin (Fintype.card (Fin d × G))) :
    gaugedVector d G Ψ σ = Ψ (gaugedLabel d G σ) (gaugedMatter d G σ) :=
  rfl

/-- The matter support of every defect state inside the window `(j, j + 1)`
lies in the defect subspace of the two labels adjacent to that window. This is
the local support hypothesis on the matter defect states of FBC25
(arXiv:2502.20257, lines 4325--4335). -/
def HasDefectSupport (hN : 2 ≤ N)
    (Dd : TNLean.Algebra.DefectMaps G (Fin 2 → Fin d))
    (Ψ : (Fin N → G) → (Fin N → Fin d) → ℂ) : Prop :=
  ∀ (α : Fin N → G) (j : Fin N) (x : Fin N → Fin d),
    (fun m ↦ Ψ α (MPSTensor.replaceWindow 2 hN j x m)) ∈
      Dd.domain (MPSTensor.extractWindow 2 j α 0)
        (MPSTensor.extractWindow 2 j α 1)

/-- Exact covariance of the prescribed defect maps on the matter defect states:
applying the prescribed map of the two labels adjacent to a window gives the
same vector as applying the prescribed map of the moved labels to the defect
state of the moved label configuration. This is the exact defect-fusion
covariance underlying the modified Gauss laws of FBC25
(arXiv:2502.20257, lines 4325--4335). -/
def HasPrescribedDefectCovariance (hN : 2 ≤ N)
    (Dd : TNLean.Algebra.DefectMaps G (Fin 2 → Fin d))
    (Ψ : (Fin N → G) → (Fin N → Fin d) → ℂ) : Prop :=
  ∀ (α : Fin N → G) (j : Fin N) (g : G),
    MPOTensor.embedLocalOperator 2 N hN j
        (Dd.prescribed (MPSTensor.extractWindow 2 j α 0)
          (MPSTensor.extractWindow 2 j α 1)) *ᵥ Ψ α =
      MPOTensor.embedLocalOperator 2 N hN j
        (Dd.prescribed (MPSTensor.extractWindow 2 j α 0 * g⁻¹)
          (g * MPSTensor.extractWindow 2 j α 1)) *ᵥ
        Ψ (chainLabelAction hN j g α)

end GaugedVector

/-- A placed operator applied to a vector, evaluated at a configuration whose
window has been replaced, is the local operator applied to the matter slice of
that vector over the same window. -/
theorem embedLocalOperator_mulVec_replaceWindow {D' : ℕ} (L : ℕ) (M : ℕ)
    (hLM : L ≤ M) (i : Fin M)
    (B : Matrix (Fin L → Fin D') (Fin L → Fin D') ℂ)
    (v : (Fin M → Fin D') → ℂ) (x : Fin M → Fin D') (r : Fin L → Fin D') :
    (MPOTensor.embedLocalOperator L M hLM i B *ᵥ v)
        (MPSTensor.replaceWindow L hLM i x r) =
      (B *ᵥ fun m ↦ v (MPSTensor.replaceWindow L hLM i x m)) r := by
  rw [MPOTensor.embedLocalOperator_mulVec_apply]
  simp only [MPSTensor.extractWindow_replaceWindow,
    MPSTensor.replaceWindow_replaceWindow_same, Matrix.mulVec, dotProduct]

section Invariance

variable {d : ℕ} {G : Type*} [Group G] [Fintype G] [DecidableEq G] {N : ℕ}

/-- Every placed Gauss operator of every completion fixes the gauged vector.

This is the invariance of the gauged state under the modified Gauss laws of
FBC25 (arXiv:2502.20257, lines 4325--4335). The proof uses the exact covariance
of the prescribed defect maps before any adjoint is applied. -/
theorem placedGaussOperator_mulVec_gaugedVector (hN : 2 ≤ N)
    {Dd : TNLean.Algebra.DefectMaps G (Fin 2 → Fin d)}
    {R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ}
    (hR : Dd.IsCompletion R) {Ψ : (Fin N → G) → (Fin N → Fin d) → ℂ}
    (hsupp : HasDefectSupport d G hN Dd Ψ)
    (hcov : HasPrescribedDefectCovariance d G hN Dd Ψ) (j : Fin N) (g : G) :
    placedGaussOperator d G N hN j R g *ᵥ gaugedVector d G Ψ =
      gaugedVector d G Ψ := by
  classical
  funext σ
  set x : Fin N → Fin d := gaugedMatter d G σ with hxdef
  set α : Fin N → G := gaugedLabel d G σ with hαdef
  set a : G := MPSTensor.extractWindow 2 j α 0 with hadef
  set b : G := MPSTensor.extractWindow 2 j α 1 with hbdef
  set β : Fin N → G := chainLabelAction hN j g⁻¹ α with hβdef
  have hβ0 : MPSTensor.extractWindow 2 j β 0 = a * g := by
    rw [hβdef, extractWindow_chainLabelAction_zero, inv_inv]
  have hβ1 : MPSTensor.extractWindow 2 j β 1 = g⁻¹ * b := by
    rw [hβdef, extractWindow_chainLabelAction_one]
  have hβα : chainLabelAction hN j g β = α := by
    rw [hβdef, chainLabelAction_chainLabelAction, mul_inv_cancel,
      chainLabelAction_one]
  set ξ : (Fin 2 → Fin d) → ℂ :=
    fun m ↦ Ψ β (MPSTensor.replaceWindow 2 hN j x m) with hξdef
  set η : (Fin 2 → Fin d) → ℂ :=
    fun m ↦ Ψ α (MPSTensor.replaceWindow 2 hN j x m) with hηdef
  have hmemξ : ξ ∈ Dd.domain (a * g) (g⁻¹ * b) := by
    have h := hsupp β j x
    rwa [hβ0, hβ1] at h
  have hmemη : η ∈ Dd.domain a b := hsupp α j x
  have hcovslice :
      Dd.prescribed (a * g) (g⁻¹ * b) *ᵥ ξ = Dd.prescribed a b *ᵥ η := by
    have h := hcov β j g
    rw [hβα, hβ0, hβ1] at h
    have hleft : a * g * g⁻¹ = a := by group
    have hright : g * (g⁻¹ * b) = b := by group
    rw [hleft, hright] at h
    funext r
    have hr := congrFun h (MPSTensor.replaceWindow 2 hN j x r)
    rw [embedLocalOperator_mulVec_replaceWindow,
      embedLocalOperator_mulVec_replaceWindow] at hr
    exact hr
  have htransport :
      (Matrix.unitaryFactorizationComparison R (a * g) (g⁻¹ * b) a b :
        Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) *ᵥ ξ = η :=
    hR.unitaryFactorizationComparison_mulVec hmemξ hmemη hcovslice
  have hextract : MPSTensor.extractWindow 2 j σ =
      gaussLocalCoordinateEquiv d G
        (MPSTensor.extractWindow 2 j x, (a, b)) := by
    have h := gaussLocalCoordinateEquiv_symm_apply d G
      (MPSTensor.extractWindow 2 j σ)
    rw [Equiv.symm_apply_eq] at h
    rw [h, hxdef, hadef, hbdef, hαdef, gaugedMatter_extractWindow,
      gaugedLabel_extractWindow]
  have hmove : TNLean.Algebra.gaussLegAction g ((a * g, g⁻¹ * b) : G × G) =
      (a, b) := by
    rw [TNLean.Algebra.gaussLegAction_apply]
    simp
  have hterm : ∀ (m : Fin 2 → Fin d) (pq : G × G),
      gaussWindowOperator d G R g (MPSTensor.extractWindow 2 j σ)
          (gaussLocalCoordinateEquiv d G (m, pq)) *
        gaugedVector d G Ψ
          (MPSTensor.replaceWindow 2 hN j σ
            (gaussLocalCoordinateEquiv d G (m, pq))) =
      if pq = (a * g, g⁻¹ * b) then
        (Matrix.unitaryFactorizationComparison R (a * g) (g⁻¹ * b) a b :
          Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
            (MPSTensor.extractWindow 2 j x) m * ξ m
      else 0 := by
    intro m pq
    rw [hextract, gaussWindowOperator_apply]
    by_cases hpq : pq = (a * g, g⁻¹ * b)
    · subst hpq
      have hentry :
          TNLean.Algebra.gaussOperator R g
              (MPSTensor.extractWindow 2 j x, (a, b))
              (m, ((a * g, g⁻¹ * b) : G × G)) =
            (Matrix.unitaryFactorizationComparison R (a * g) (g⁻¹ * b) a b :
              Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
              (MPSTensor.extractWindow 2 j x) m := by
        rw [← hmove, TNLean.Algebra.gaussOperator_apply_target]
        have hleft : a * g * g⁻¹ = a := by group
        have hright : g * (g⁻¹ * b) = b := by group
        rw [hleft, hright]
      rw [hentry, ite_eq_left rfl]
      congr 1
      have hmatter : gaugedMatter d G
          (MPSTensor.replaceWindow 2 hN j σ
            (gaussLocalCoordinateEquiv d G (m, ((a * g, g⁻¹ * b) : G × G)))) =
          MPSTensor.replaceWindow 2 hN j x m := by
        rw [gaugedMatter_replaceWindow, gaugedMatter_gaussLocalCoordinateEquiv]
      have hlabel : gaugedLabel d G
          (MPSTensor.replaceWindow 2 hN j σ
            (gaussLocalCoordinateEquiv d G (m, ((a * g, g⁻¹ * b) : G × G)))) =
          β := by
        rw [gaugedLabel_replaceWindow, gaugedLabel_gaussLocalCoordinateEquiv,
          hβdef, chainLabelAction, inv_inv]
      rw [gaugedVector_apply, hmatter, hlabel]
    · have hne : ((MPSTensor.extractWindow 2 j x, (a, b)) :
          (Fin 2 → Fin d) × (G × G)).2 ≠
          TNLean.Algebra.gaussLegAction g
            ((m, pq) : (Fin 2 → Fin d) × (G × G)).2 := by
        intro hEq
        exact hpq
          (((TNLean.Algebra.gaussLegAction g).injective (hmove.trans hEq)).symm)
      rw [TNLean.Algebra.gaussOperator_apply_of_ne R g _ _ hne]
      simp [hpq]
  rw [placedGaussOperator, MPOTensor.embedLocalOperator_mulVec_apply,
    ← Equiv.sum_comp (gaussLocalCoordinateEquiv d G)
      (fun τ ↦ gaussWindowOperator d G R g (MPSTensor.extractWindow 2 j σ) τ *
        gaugedVector d G Ψ (MPSTensor.replaceWindow 2 hN j σ τ)),
    Fintype.sum_prod_type]
  simp only [hterm, Fintype.sum_ite_eq']
  have hsum : ∑ m : Fin 2 → Fin d,
      (Matrix.unitaryFactorizationComparison R (a * g) (g⁻¹ * b) a b :
        Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
          (MPSTensor.extractWindow 2 j x) m * ξ m =
      ((Matrix.unitaryFactorizationComparison R (a * g) (g⁻¹ * b) a b :
        Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) *ᵥ ξ)
        (MPSTensor.extractWindow 2 j x) := rfl
  rw [hsum, htransport]
  have hvalue : η (MPSTensor.extractWindow 2 j x) = Ψ α x := by
    rw [hηdef]
    simp only [MPSTensor.replaceWindow_extractWindow]
  rw [hvalue, gaugedVector_apply, hxdef, hαdef]

/-- The placed Gauss projector is the normalized sum over the group of the
placed Gauss operators. -/
theorem placedGaussProjector_eq_average (hN : 2 ≤ N) (j : Fin N)
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) :
    placedGaussProjector d G N hN j R =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, placedGaussOperator d G N hN j R g := by
  classical
  have hwindow : gaussWindowProjector d G R =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, gaussWindowOperator d G R g := by
    ext u v
    simp [gaussWindowProjector, gaussWindowOperator, Matrix.reindex_apply,
      TNLean.Algebra.gaussProjector_eq_average]
  ext σ τ
  by_cases hagree : MPOTensor.AgreesOutsideWindow
      (d := Fintype.card (Fin d × G)) 2 hN j σ τ <;>
    simp [placedGaussProjector, placedGaussOperator, hwindow, hagree,
      Matrix.sum_apply, embedLocalOperator_apply]

/-- The gauged vector is fixed by every placed Gauss projector of every
completion. -/
theorem placedGaussProjector_mulVec_gaugedVector (hN : 2 ≤ N)
    {Dd : TNLean.Algebra.DefectMaps G (Fin 2 → Fin d)}
    {R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ}
    (hR : Dd.IsCompletion R) {Ψ : (Fin N → G) → (Fin N → Fin d) → ℂ}
    (hsupp : HasDefectSupport d G hN Dd Ψ)
    (hcov : HasPrescribedDefectCovariance d G hN Dd Ψ) (j : Fin N) :
    placedGaussProjector d G N hN j R *ᵥ gaugedVector d G Ψ =
      gaugedVector d G Ψ := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero (α := G)]
  rw [placedGaussProjector_eq_average, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [placedGaussOperator_mulVec_gaugedVector hN hR hsupp hcov j,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

variable (d G)

/-- The gauge-invariant subspace of a completion: the common `+1` eigenspace of
the placed Gauss projectors at every window. This is the subspace `𝒱_N(R)` of
FBC25 (arXiv:2502.20257, lines 4325--4335 and line 5198). No commutativity of
the projectors on neighbouring windows is assumed. -/
def gaugeInvariantSubspace (N : ℕ) (hN : 2 ≤ N)
    (R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ) :
    Submodule ℂ ((Fin N → Fin (Fintype.card (Fin d × G))) → ℂ) :=
  LinearMap.commonFixedSubmodule fun j : Fin N ↦
    (placedGaussProjector d G N hN j R).mulVecLin

variable {d G}

/-- The gauged vector lies in the gauge-invariant subspace of every
completion. -/
theorem gaugedVector_mem_gaugeInvariantSubspace (hN : 2 ≤ N)
    {Dd : TNLean.Algebra.DefectMaps G (Fin 2 → Fin d)}
    {R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ}
    (hR : Dd.IsCompletion R) {Ψ : (Fin N → G) → (Fin N → Fin d) → ℂ}
    (hsupp : HasDefectSupport d G hN Dd Ψ)
    (hcov : HasPrescribedDefectCovariance d G hN Dd Ψ) :
    gaugedVector d G Ψ ∈ gaugeInvariantSubspace d G N hN R := by
  rw [gaugeInvariantSubspace, LinearMap.mem_commonFixedSubmodule_iff]
  intro j
  exact placedGaussProjector_mulVec_gaugedVector hN hR hsupp hcov j

/-- A nonvanishing gauged vector forces the gauge-invariant subspace of every
completion to have dimension at least one. No upper bound and no bound
independent of the completion follows from this. -/
theorem one_le_finrank_gaugeInvariantSubspace (hN : 2 ≤ N)
    {Dd : TNLean.Algebra.DefectMaps G (Fin 2 → Fin d)}
    {R : G → G → Matrix.unitaryGroup (Fin 2 → Fin d) ℂ}
    (hR : Dd.IsCompletion R) {Ψ : (Fin N → G) → (Fin N → Fin d) → ℂ}
    (hsupp : HasDefectSupport d G hN Dd Ψ)
    (hcov : HasPrescribedDefectCovariance d G hN Dd Ψ)
    (hne : gaugedVector d G Ψ ≠ 0) :
    1 ≤ Module.finrank ℂ (gaugeInvariantSubspace d G N hN R) :=
  LinearMap.one_le_finrank_commonFixedSubmodule _
    (gaugedVector_mem_gaugeInvariantSubspace hN hR hsupp hcov) hne

end Invariance

end MPOTensor
