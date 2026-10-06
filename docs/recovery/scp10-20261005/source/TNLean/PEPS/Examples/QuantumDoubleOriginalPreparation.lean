/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleOriginalGroundProjector

/-!
# Exact finite-group preparation on the original spin lattice

SCP10, arXiv:1001.3807v3, Section 7.2, lines 2876–2895: the literal
unnormalized elementary T contraction is |G|^(2wh) times the correctly
normalized ground projector applied to the all-identity product state.
Equivalently, only the B averages need be applied, since the A projectors
already fix that input. The scalar counts B controls, not distinct physical
color configurations; stabilizer multiplicities are retained.

**Local fix (normalization):** B averages use |G|⁻¹. The nonzero overall
state scalar does not justify omitting this factor in a projector.
See `docs/paper-gaps/scp10_quantum_double_local_hamiltonian.tex`.
**Scope restriction (native even torus):** fine periods are 2w,2h with w,h≥3.
See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "E" => Edge (torusGraph width height)
local notation "C" => (F → G)
local notation "K" => QuantumDoubleKLatticeConfig width height G
local notation "block" => quantumDoublePhysicalBlockingEquiv
  (G := G) (width := width) (height := height)
local notation "Q" => quantumDoubleOriginalGroundProjector
  (width := width) (height := height) (G := G)
local notation "T" => (fun σ : C => torusBondNetwork
  (quantumDoublePeriodicElementarySite σ) 1 1)

/-- Original physical spins produced by one assignment of the actual shared
K bond colors. No independent copies of a shared bond are introduced. -/
def quantumDoubleOriginalPhysicalColorConfig (c : E → G) : C :=
  (block).symm (quantumDoubleKLatticeSpins c)

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The all-identity physical product vector is killed by every A penalty,
as used at the start of the source preparation. -/
theorem quantumDoubleOriginalATerm_one (j : V ⊕ V) :
    quantumDoubleOriginalATerm j *ᵥ Pi.single (1 : C) 1 = 0 := by
  apply (quantumDoubleOriginalATerm_mulVec_eq_zero_iff j _).mpr
  intro σ hσ
  have hne : σ ≠ 1 := by
    intro h
    subst σ
    cases j <;> simp [quantumDoubleOriginalAHolonomy] at hσ
  simp [hne]

omit [Fact (2 < width)] [Fact (2 < height)] in
private theorem A_projector_product_one (l : List (V ⊕ V)) :
    (l.map (fun j => 1 - quantumDoubleOriginalATerm j)).prod *ᵥ Pi.single (1 : C) 1 =
      Pi.single (1 : C) 1 := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, Matrix.one_mulVec]
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih,
      Matrix.sub_mulVec, Matrix.one_mulVec, quantumDoubleOriginalATerm_one, sub_zero]

/-- The A ground projectors I−h_A fix the initial identity product state,
so the joint projector prepares exactly the sequential B projection. -/
theorem quantumDoubleOriginalGroundProjector_one_eq_B_product :
    Q *ᵥ Pi.single (1 : C) 1 =
      ((Finset.univ : Finset E).toList.map (fun e => 1 - quantumDoubleOriginalBTerm e)).prod *ᵥ
        Pi.single (1 : C) 1 := by
  rw [quantumDoubleOriginalGroundProjector_eq_B_prod_A, ← Matrix.mulVec_mulVec,
    A_projector_product_one]

/-- The literal T contraction is the unnormalized sum of the physical basis
vectors produced by every actual shared-bond coloring. -/
theorem quantumDoubleOriginalCheckerboard_eq_sum_colorBasis :
    T = ∑ c : E → G, Pi.single (quantumDoubleOriginalPhysicalColorConfig c) 1 := by
  funext σ
  rw [torusBondNetwork_quantumDoublePeriodicElementarySite_eq_KNetwork]
  change torusBondNetwork (fun v c => quantumDoubleKTensor G
    c.1 c.2.1 c.2.2.1 c.2.2.2 (block σ v)) 1 1 = _
  rw [← quantumDoubleKLatticeContraction_eq_torusBondNetwork,
    quantumDoubleKLatticeContraction_eq]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Pi.single_apply, quantumDoubleOriginalPhysicalColorConfig, Equiv.eq_symm_apply]

private theorem groundProjector_color_column (c : E → G) :
    Q *ᵥ Pi.single (quantumDoubleOriginalPhysicalColorConfig c) 1 = Q *ᵥ Pi.single (1 : C) 1 := by
  funext σ
  have hcol : quantumDoubleOriginalHamiltonian *ᵥ (Q *ᵥ Pi.single σ 1) = 0 := by
    have hm : Q *ᵥ Pi.single σ 1 ∈ (Matrix.mulVecLin Q).range := ⟨Pi.single σ 1, rfl⟩
    rw [range_quantumDoubleOriginalGroundProjector] at hm
    exact hm
  rw [quantumDoubleOriginalHamiltonian_eq_unblocked, quantumDoubleKLatticeUnblockedHamiltonian,
    quantumDoubleUnblockOperator_mulVec_eq_zero_iff] at hcol
  have hinv := ((quantumDoubleKLatticeHamiltonian_mulVec_eq_zero_iff_flat_invariant _).mp
    hcol).2 c (1 : K)
  rw [← quantumDoubleOriginalBlockingLinearEquiv_apply] at hinv
  have hg : quantumDoubleKLatticeGauge c (1 : K) = quantumDoubleKLatticeSpins c := by
    funext v
    simp [quantumDoubleKLatticeGauge, quantumDoubleKLatticeSpins, quantumDoubleKSpins]
  have hzero : (block).symm (1 : K) = (1 : C) :=
    (block).symm_apply_apply (1 : C)
  simp only [quantumDoubleOriginalBlockingLinearEquiv, LinearEquiv.piCongrLeft'_apply,
    hg, hzero, Matrix.mulVec_single_one, Matrix.col_apply] at hinv
  have hself : Qᴴ = Q := quantumDoubleOriginalGroundProjector_isStarProjection.isSelfAdjoint
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply,
    ← Matrix.conjTranspose_apply, hself, quantumDoubleOriginalPhysicalColorConfig] using
      congrArg star hinv

omit [Group G] [DecidableEq G] in
/-- Every assignment of group-valued B-plaquette controls contributes one coloring;
there are exactly |G|^(2wh) assignments. -/
theorem card_quantumDoubleOriginalPhysicalColorings :
    Fintype.card (E → G) = Fintype.card G ^ (2 * (width * height)) := by
  rw [Fintype.card_fun, ← Fintype.card_congr
    (torusEdgeEquiv (width := width) (height := height)), Fintype.card_sum]
  simp [TorusVertex, two_mul]

/-- The exact source preparation identity on the original physical spins.
The scalar counts all B-plaquette controls, while the tensor T is retained
with its printed unnormalized entries. -/
theorem quantumDoubleOriginalCheckerboard_eq_groundProjector_one :
    T = (Fintype.card G : ℂ) ^ (2 * (width * height)) • (Q *ᵥ Pi.single (1 : C) 1) := by
  have hfix : Q *ᵥ T = T :=
    (quantumDoubleOriginalGroundProjector_mulVec_eq_self_iff T).mpr
      quantumDoubleOriginalHamiltonian_checkerboard
  calc
    T = Q *ᵥ T := hfix.symm
    _ = ∑ c : E → G,
        Q *ᵥ Pi.single (quantumDoubleOriginalPhysicalColorConfig c) 1 := by
      rw [quantumDoubleOriginalCheckerboard_eq_sum_colorBasis, Matrix.mulVec_sum]
    _ = (Fintype.card (E → G) : ℂ) • (Q *ᵥ Pi.single (1 : C) 1) := by
      simp only [groundProjector_color_column, Finset.sum_const, Finset.card_univ,
        Nat.cast_smul_eq_nsmul]
    _ = (Fintype.card G : ℂ) ^ (2 * (width * height)) • (Q *ᵥ Pi.single (1 : C) 1) := by
      rw [card_quantumDoubleOriginalPhysicalColorings]
      norm_cast

/-- The exact sequential construction in SCP10: apply all correctly
normalized B ground projectors to the all-identity physical product state. -/
theorem quantumDoubleOriginalCheckerboard_eq_B_product_one :
    T = (Fintype.card G : ℂ) ^ (2 * (width * height)) •
      (((Finset.univ : Finset E).toList.map (fun e => 1 - quantumDoubleOriginalBTerm e)).prod *ᵥ
        Pi.single (1 : C) 1) := by
  rw [quantumDoubleOriginalCheckerboard_eq_groundProjector_one,
    quantumDoubleOriginalGroundProjector_one_eq_B_product]

/-- Projecting the all-identity physical product state does not give the zero vector. -/
theorem quantumDoubleOriginalGroundProjector_one_ne_zero : Q *ᵥ Pi.single (1 : C) 1 ≠ 0 := by
  intro h
  have ht := quantumDoubleOriginalCheckerboard_eq_groundProjector_one
    (width := width) (height := height) (G := G)
  rw [h, smul_zero] at ht
  exact quantumDoubleOriginalCheckerboard_ne_zero ht

end TNLean.PEPS
