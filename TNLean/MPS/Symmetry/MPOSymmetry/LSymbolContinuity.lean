/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpaceMapContinuity
import TNLean.MPS.Symmetry.MPOSymmetry.LSymbolComputation

/-!
# Continuity of scalar comparisons between actual reductions

The source bond dimension gives a common long-word threshold for comparing reductions.
A nonzero entry of one dressed boundary then extracts their scalar by a quotient near
each parameter. Consequently continuous tensors and continuous left reduction caps give
continuous comparison scalars. No continuity of the right caps is needed.

This is the scalar continuity step in arXiv:2203.12563, Section 4, lines 1361--1390.
Existence of continuous action caps from a physical Hamiltonian path is a separate step.
-/

open scoped Matrix

namespace MPSTensor

variable {d D E : ℕ}

/-- The selected reduction scalar compares every word longer than twice the source bond
dimension. The bound is uniform over the reductions and target tensor. This combines
MGSC18, Theorem 22, with the derived residual bond-dimension bound. -/
theorem IsReduction.mul_evalWord_eq_dressedScalar_smul
    {B : MPSTensor d E} {A : MPSTensor d D}
    {V V' : Matrix (Fin D) (Fin E) ℂ} {W W' : Matrix (Fin E) (Fin D) ℂ}
    (h : IsReduction B A V W) (h' : IsReduction B A V' W')
    (hA : Kraus.IsNormal A) (hD : 0 < D) (hSame : SameMPV₂Pos B A)
    (w : List (Fin d)) (hw : 2 * E < w.length) :
    V * Kraus.evalWord B w =
      (dressedScalar B V V' : ℂ) • (V' * Kraus.evalWord B w) := by
  obtain ⟨z, hz, hwords⟩ := h.exists_boundary_dressed_proportional h' hA
    (h.bondDim_isReductionResidualNilpotencyBound hSame)
    (h'.bondDim_isReductionResidualNilpotencyBound hSame)
  have hrel : IsDressedProportional B V V' z :=
    ⟨2 * E + 1, fun u hu ↦ (hwords u (by omega)).1⟩
  have heq : z = dressedScalar B V V' :=
    hrel.eq_of_forall_exists_ne_zero
      (isDressedProportional_dressedScalar ⟨z, hz, hrel⟩)
      (h.exists_mul_evalWord_ne_zero hA hD)
  simpa only [heq] using (hwords w hw).1

/-- Continuous source tensors and left reduction caps give a continuous selected scalar
when both reductions have the same normal positive-dimensional target and the same
positive-length periodic vectors. Right caps and target tensors need not be continuous.
Source context: arXiv:2203.12563, Section 4, lines 1361--1390. -/
theorem continuous_dressedScalar_of_reductions
    {X : Type*} [TopologicalSpace X]
    (B : X → MPSTensor d E) (A : X → MPSTensor d D)
    (V V' : X → Matrix (Fin D) (Fin E) ℂ)
    (W W' : X → Matrix (Fin E) (Fin D) ℂ)
    (hB : Continuous B) (hV : Continuous V) (hV' : Continuous V')
    (h : ∀ x, IsReduction (B x) (A x) (V x) (W x))
    (h' : ∀ x, IsReduction (B x) (A x) (V' x) (W' x))
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : 0 < D)
    (hSame : ∀ x, SameMPV₂Pos (B x) (A x)) :
    Continuous fun x ↦ (dressedScalar (B x) (V x) (V' x) : ℂ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨w, hw, hne⟩ := (h' x₀).exists_mul_evalWord_ne_zero (hA x₀) hD (2 * E + 1)
  obtain ⟨i, j, hij⟩ : ∃ i j, (V' x₀ * Kraus.evalWord (B x₀) w) i j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Matrix.ext fun i j ↦ hall i j)
  have hnum := (hV.matrix_mul (continuous_evalWord_family B hB w)).matrix_elem i j
  have hden := (hV'.matrix_mul (continuous_evalWord_family B hB w)).matrix_elem i j
  apply (hnum.continuousAt.div hden.continuousAt hij).congr
  filter_upwards [hden.continuousAt.eventually_ne hij] with x hx
  simp only [Pi.div_apply]
  have heq := congrArg (fun M ↦ M i j)
    ((h x).mul_evalWord_eq_dressedScalar_smul (h' x) (hA x) hD (hSame x) w (by omega))
  simpa only [Matrix.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx] using
    congrArg (fun z : ℂ ↦ z / (V' x * Kraus.evalWord (B x) w) i j) heq

end MPSTensor

namespace MPOTensor

/-- Acting by a fixed MPO tensor preserves continuity of a fixed-dimensional state
tensor family, since each output letter is a finite sum of Kronecker products. -/
theorem continuous_actTensor_family
    {X : Type*} [TopologicalSpace X] {d D E : ℕ}
    (T : MPOTensor d E) (A : X → MPSTensor d D) (hA : Continuous A) :
    Continuous fun x ↦ actTensor T (A x) := by
  apply continuous_pi
  intro i
  exact (continuous_finsetSum _ fun j _ ↦
    (continuous_const.matrix_kronecker ((continuous_apply j).comp hA))).matrix_submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm

namespace GroupFamily.ActionData

variable {G : Type} [Group G] {d D : ℕ} {F : GroupFamily G d}

omit [Group G] in
/-- Continuous left action caps give continuous successive-action trees. -/
theorem continuous_actV
    {X : Type*} [TopologicalSpace X] {A : X → MPSTensor d D}
    (ad : ∀ x, ActionData F (A x)) (hc : ∀ g, Continuous fun x ↦ (ad x).V g)
    (g h : G) : Continuous fun x ↦ (ad x).actV g h := by
  have hi : Continuous fun x ↦ idKron (F.bondDim g) ((ad x).V h) :=
    (continuous_const.matrix_kronecker (hc h)).matrix_submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm
  exact ((hc g).matrix_mul hi).matrix_mul continuous_const

/-- Continuous left action caps give continuous fusion-then-action trees for fixed
fusion reductions. -/
theorem continuous_fuseV
    {X : Type*} [TopologicalSpace X] {A : X → MPSTensor d D}
    (fd : FusionData F) (ad : ∀ x, ActionData F (A x))
    (hc : ∀ g, Continuous fun x ↦ (ad x).V g) (g h : G) :
    Continuous fun x ↦ (ad x).fuseV fd g h :=
  (hc (g * h)).matrix_mul continuous_const

/-- The actual single-block action L-symbol varies continuously with the state tensor
and left action caps, for a fixed symmetry and fixed fusion reductions. Normality,
positive fixed bond dimension and periodic invariance ensure that the scalar is the
one selected by actual reductions. Source context: arXiv:2203.12563, Section 4,
lines 1361--1390. Constructing continuous action caps from a physical path remains separate. -/
theorem continuous_lSymbol
    {X : Type*} [TopologicalSpace X]
    (fd : FusionData F) (A : X → MPSTensor d D) (ad : ∀ x, ActionData F (A x))
    (hc : Continuous A) (hV : ∀ g, Continuous fun x ↦ (ad x).V g)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : 0 < D)
    (hinv : ∀ x g, FixesMPV (F.tensor g) (A x)) (g h : G) :
    Continuous fun x ↦ ((ad x).lSymbol fd () g h : ℂ) := by
  choose W hW using fun x ↦ (ad x).exists_isReduction_actV g h
  choose W' hW' using fun x ↦ (ad x).exists_isReduction_fuseV fd g h
  exact MPSTensor.continuous_dressedScalar_of_reductions
    (fun x ↦ actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) A
    (fun x ↦ (ad x).actV g h) (fun x ↦ (ad x).fuseV fd g h) W W'
    (continuous_actTensor_family _ A hc) (continuous_actV ad hV g h)
    (continuous_fuseV fd ad hV g h) hW hW' hA hD
    (fun x ↦ ((hinv x g).mulTensor (hinv x h)).sameMPV₂Pos_actTensor
      (MPSTensor.SameMPV₂Pos.refl (A x)))

end GroupFamily.ActionData

end MPOTensor
