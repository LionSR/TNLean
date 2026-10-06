/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.ToricCodePauliGroundProjector

/-!
# Exact preparation of the literal toric-code tensor state

The unnormalized elementary T contraction is exactly 2^(2wh) times the
corrected joint ground projector applied to the all-zero physical product
state. This fixes the full preparation scalar, not just ground-state
membership. The proof uses the already derived K coloring sum, physical
regrouping, and gauge invariance of the ground projector's columns.

Source: SCP10, arXiv:1001.3807v3, Section 7.1, lines 2664–2748.
**Local fix (normalization):** the joint projector uses I−h, retaining the
penalties h=(I−S)/2. Extra source half-factors only rescale an unnormalized
prepared state. See `docs/paper-gaps/scp10_toric_code_projector_normalization.tex`.
**Scope restriction (native even torus):** fine periods are 2w,2h with w,h≥3,
as in the complete native K kernel theorem. The same note records this scope.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "E" => Edge (torusGraph width height)
local notation "C" => (F → ToricCodeGroup)
local notation "K" => QuantumDoubleKLatticeConfig width height ToricCodeGroup
local notation "block" => quantumDoublePhysicalBlockingEquiv
  (G := ToricCodeGroup) (width := width) (height := height)
local notation "Q" => toricCodePauliGroundProjector (width := width) (height := height)
local notation "T" => (fun σ : C => torusBondNetwork
  (quantumDoublePeriodicElementarySite σ) 1 1)

/-- Original physical spins produced by one assignment of the actual shared
K bond colors. No independent copies of a shared bond are introduced. -/
def toricCodePhysicalColorConfig (c : E → ToricCodeGroup) : C :=
  (block).symm (quantumDoubleKLatticeSpins c)

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The all-zero physical product vector is killed by every A penalty,
as used at the start of the source preparation. -/
theorem toricCodeATerm_zero (j : V ⊕ V) :
    toricCodeATerm j *ᵥ Pi.single (1 : C) 1 = 0 := by
  apply (toricCodeATerm_mulVec_eq_zero_iff j _).mpr
  intro σ hσ
  have hne : σ ≠ 1 := by
    intro h
    subst σ
    simp at hσ
  simp [hne]

omit [Fact (2 < width)] [Fact (2 < height)] in
private theorem A_projector_product_zero (l : List (V ⊕ V)) :
    (l.map (fun j => 1 - toricCodeATerm j)).prod *ᵥ Pi.single (1 : C) 1 =
      Pi.single (1 : C) 1 := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, Matrix.one_mulVec]
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih,
      Matrix.sub_mulVec, Matrix.one_mulVec, toricCodeATerm_zero, sub_zero]

/-- The A ground projectors I−h_A fix the initial zero product state,
so the joint projector prepares exactly the sequential B projection. -/
theorem toricCodePauliGroundProjector_zero_eq_B_product :
    Q *ᵥ Pi.single (1 : C) 1 =
      ((Finset.univ : Finset E).toList.map (fun e => 1 - toricCodeBTerm e)).prod *ᵥ
        Pi.single (1 : C) 1 := by
  rw [toricCodePauliGroundProjector_eq_B_prod_A, ← Matrix.mulVec_mulVec,
    A_projector_product_zero]

/-- The literal T contraction is the unnormalized sum of the physical basis
vectors produced by every actual shared-bond coloring. -/
theorem toricCodeCheckerboard_eq_sum_colorBasis :
    T = ∑ c : E → ToricCodeGroup, Pi.single (toricCodePhysicalColorConfig c) 1 := by
  funext σ
  rw [torusBondNetwork_quantumDoublePeriodicElementarySite_eq_KNetwork]
  change torusBondNetwork (fun v c => quantumDoubleKTensor ToricCodeGroup
    c.1 c.2.1 c.2.2.1 c.2.2.2 (block σ v)) 1 1 = _
  rw [← quantumDoubleKLatticeContraction_eq_torusBondNetwork,
    quantumDoubleKLatticeContraction_eq]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Pi.single_apply, toricCodePhysicalColorConfig, Equiv.eq_symm_apply]

private theorem groundProjector_color_column (c : E → ToricCodeGroup) :
    Q *ᵥ Pi.single (toricCodePhysicalColorConfig c) 1 = Q *ᵥ Pi.single (1 : C) 1 := by
  funext σ
  have hcol : toricCodePauliHamiltonian *ᵥ (Q *ᵥ Pi.single σ 1) = 0 := by
    have hm : Q *ᵥ Pi.single σ 1 ∈ (Matrix.mulVecLin Q).range := ⟨Pi.single σ 1, rfl⟩
    rw [range_toricCodePauliGroundProjector] at hm
    exact hm
  rw [toricCodePauliHamiltonian_eq_unblocked, quantumDoubleKLatticeUnblockedHamiltonian,
    quantumDoubleUnblockOperator_mulVec_eq_zero_iff] at hcol
  have hinv := ((quantumDoubleKLatticeHamiltonian_mulVec_eq_zero_iff_flat_invariant _).mp
    hcol).2 c (1 : K)
  rw [← toricCodeBlockingLinearEquiv_apply] at hinv
  have hg : quantumDoubleKLatticeGauge c (1 : K) = quantumDoubleKLatticeSpins c := by
    funext v
    simp [quantumDoubleKLatticeGauge, quantumDoubleKLatticeSpins, quantumDoubleKSpins]
  have hzero : (block).symm (1 : K) = (1 : C) :=
    (block).symm_apply_apply (1 : C)
  simp only [toricCodeBlockingLinearEquiv, LinearEquiv.piCongrLeft'_apply,
    hg, hzero, Matrix.mulVec_single_one, Matrix.col_apply] at hinv
  have hself : Qᴴ = Q := toricCodePauliGroundProjector_isStarProjection.isSelfAdjoint
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply,
    ← Matrix.conjTranspose_apply, hself, toricCodePhysicalColorConfig] using congrArg star hinv

/-- Every assignment of binary B-plaquette controls contributes one coloring;
there are exactly 2^(2wh) assignments. -/
theorem card_toricCodePhysicalColorings :
    Fintype.card (E → ToricCodeGroup) = 2 ^ (2 * (width * height)) := by
  rw [Fintype.card_fun, ← Fintype.card_congr
    (torusEdgeEquiv (width := width) (height := height)), Fintype.card_sum]
  simp [ToricCodeGroup, TorusVertex, two_mul]

/-- The exact source preparation identity on the original physical qubits.
The scalar counts all B-plaquette controls, while the tensor T is retained
with its printed unnormalized entries. -/
theorem toricCodeCheckerboard_eq_groundProjector_zero :
    T = (2 : ℂ) ^ (2 * (width * height)) • (Q *ᵥ Pi.single (1 : C) 1) := by
  have hfix : Q *ᵥ T = T :=
    (toricCodePauliGroundProjector_mulVec_eq_self_iff T).mpr
      toricCodePauliHamiltonian_checkerboard
  calc
    T = Q *ᵥ T := hfix.symm
    _ = ∑ c : E → ToricCodeGroup,
        Q *ᵥ Pi.single (toricCodePhysicalColorConfig c) 1 := by
      rw [toricCodeCheckerboard_eq_sum_colorBasis, Matrix.mulVec_sum]
    _ = (Fintype.card (E → ToricCodeGroup) : ℂ) • (Q *ᵥ Pi.single (1 : C) 1) := by
      simp only [groundProjector_color_column, Finset.sum_const, Finset.card_univ,
        Nat.cast_smul_eq_nsmul]
    _ = (2 : ℂ) ^ (2 * (width * height)) • (Q *ᵥ Pi.single (1 : C) 1) := by
      rw [card_toricCodePhysicalColorings]
      norm_cast

/-- The actual binary T network has the same exact preparation scalar,
with additive bits and zero interpreted as the group identity. -/
theorem toricCodeBinaryCheckerboard_eq_groundProjector_zero :
    (fun σ : C => torusBondNetwork (kitaevPeriodicElementarySite
      (width := width) (height := height) (fun p => Multiplicative.toAdd (σ p))) 1 1) =
        (2 : ℂ) ^ (2 * (width * height)) • (Q *ᵥ Pi.single (1 : C) 1) := by
  simp_rw [← torusBondNetwork_quantumDoubleElementary_toricCode]
  exact toricCodeCheckerboard_eq_groundProjector_zero

/-- The exact sequential construction in SCP10: apply all correctly
normalized B ground projectors to the all-zero physical product state. -/
theorem toricCodeCheckerboard_eq_B_product_zero :
    T = (2 : ℂ) ^ (2 * (width * height)) •
      (((Finset.univ : Finset E).toList.map (fun e => 1 - toricCodeBTerm e)).prod *ᵥ
        Pi.single (1 : C) 1) := by
  rw [toricCodeCheckerboard_eq_groundProjector_zero,
    toricCodePauliGroundProjector_zero_eq_B_product]

/-- Projecting the all-zero physical product state does not give the zero vector. -/
theorem toricCodePauliGroundProjector_zero_ne_zero : Q *ᵥ Pi.single (1 : C) 1 ≠ 0 := by
  intro h
  have ht := toricCodeCheckerboard_eq_groundProjector_zero (width := width) (height := height)
  rw [h, smul_zero] at ht
  exact toricCodeCheckerboard_ne_zero ht

end TNLean.PEPS
