/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularBoundaryDecomposition
import TNLean.MPS.MPDO.TriangularBoundaryBlocked

/-!
# Exact triangular boundary family regressions

The source constructor accepts individual injectivity, positive dimensions,
within-kind scalar-gauge separation, and the exact original fusion/action
maps. Its positive blocking and simultaneous inverse are conclusions.
These tests retain the disjoint-union labels and check the original maps
without an equality cast or an additional comparison assumption.
-/

set_option linter.hashCommand false

open scoped Matrix BigOperators

namespace TriangularBoundaryTest

open MPOTensor

section ExactFamily

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hAct : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))

example (a : Fin r) : triangularBondDim χ D (.inl a) = χ a := rfl

example (x : Fin s) : triangularBondDim χ D (.inr x) = D x := rfl

example (a : Fin r) : triangularTensor O A (.inl a) = operatorPhysicalPadding (O a) := rfl

example (x : Fin s) : triangularTensor O A (.inr x) = statePhysicalPadding (A x) := rfl

example (a b c : Fin r) : triangularFusionMultiplicity N M (.inl a) (.inl b) (.inl c) =
    N a b c := rfl

example (a : Fin r) (x y : Fin s) :
    triangularFusionMultiplicity N M (.inl a) (.inr x) (.inr y) = M a x y := rfl

-- Every state-left multiplicity is zero, independently of its other labels.
example (x : Fin s) (b c : Fin r ⊕ Fin s) :
    triangularFusionMultiplicity N M (.inr x) b c = 0 := rfl

example (a b c : Fin r) :
    triangularFusionAnalysis VF VA (.inl a) (.inl b) (.inl c) = VF a b c := rfl

example (a : Fin r) (x y : Fin s) :
    triangularFusionAnalysis VF VA (.inl a) (.inr x) (.inr y) = VA a x y := rfl

example (a b c : Fin r) :
    triangularFusionSynthesis WF WA (.inl a) (.inl b) (.inl c) = WF a b c := rfl

example (a : Fin r) (x y : Fin s) :
    triangularFusionSynthesis WF WA (.inl a) (.inr x) (.inr y) = WA a x y := rfl

include hF hAct in
example (a b : Fin r ⊕ Fin s) :
    MPSTensor.IsBiorthogonalDecomposition
      (mulTensor (triangularTensor O A a) (triangularTensor O A b)).toMPSTensor
      (fun q : (c : Fin r ⊕ Fin s) × Fin (triangularFusionMultiplicity N M a b c) ↦
        (triangularTensor O A q.1).toMPSTensor)
      (fun q ↦ triangularFusionAnalysis VF VA a b q.1 q.2)
      (fun q ↦ triangularFusionSynthesis WF WA a b q.1 q.2) :=
  isBiorthogonalDecomposition_triangularTensor VF WF VA WA O A hF hAct a b

variable (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor)
  (hInjA : ∀ x, Kraus.IsInjective (A x))
  (hχ : ∀ a, 0 < χ a) (hD : ∀ x, 0 < D x)
  (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
  (hneA : MPSTensor.BlocksNotGaugePhaseEquiv A)

include hInjO hInjA hχ hD hneO hneA in
example :
    ∃ L : ℕ, 0 < L ∧
      (∀ c, Kraus.IsInjective (blockTensor (triangularTensor O A c) L).toMPSTensor) ∧
      ∃ K : Matrix ((c : Fin r ⊕ Fin s) ×
          (Fin (triangularBondDim χ D c) × Fin (triangularBondDim χ D c)))
          (Fin (MPSTensor.blockPhysDim (d + 1) L) ×
            Fin (MPSTensor.blockPhysDim (d + 1) L)) ℂ,
        ∀ (a b : Fin r ⊕ Fin s) (x y : Fin (triangularBondDim χ D a))
          (x' y' : Fin (triangularBondDim χ D b)),
          (∑ i, ∑ j, K ⟨a, x, y⟩ (i, j) *
            blockTensor (triangularTensor O A b) L i j x' y') =
            if he : a = b then
              if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
            else 0 :=
  exists_triangular_blockTensor_leftInverse O A hInjO hInjA hχ hD hneO hneA

example : 0 < triangularBlockLength O A hInjO hInjA hχ hD hneO hneA :=
  triangularBlockLength_pos O A hInjO hInjA hχ hD hneO hneA

local notation "F" =>
  CompleteZipperFusionFamily.ofTriangularBiorthogonalBlocked O A hInjO hInjA hχ hD
    hneO hneA VF WF VA WA hF hAct

-- This construction has no joint-span, joint-inverse, or coherence input.
include hF hAct in
example : CompleteZipperFusionFamily (Fin r ⊕ Fin s)
    (MPSTensor.blockPhysDim (d + 1)
      (triangularBlockLength O A hInjO hInjA hχ hD hneO hneA)) := F

example : (F).bondDim = triangularBondDim χ D := rfl

example : (F).fusionMultiplicity = triangularFusionMultiplicity N M := rfl

example (c : Fin r ⊕ Fin s) :
    (F).tensor c = blockTensor (triangularTensor O A c)
      (triangularBlockLength O A hInjO hInjA hχ hD hneO hneA) :=
  CompleteZipperFusionFamily.ofTriangularBiorthogonalBlocked_tensor O A hInjO hInjA
    hχ hD hneO hneA VF WF VA WA hF hAct c

example (a b : Fin r ⊕ Fin s) :
    (F).fusionSynthesis a b =
      CompleteZipperFusionFamily.biorthogonalSynthesis
        (triangularFusionSynthesis WF WA a b) :=
  CompleteZipperFusionFamily.ofTriangularBiorthogonalBlocked_fusionSynthesis O A hInjO hInjA
    hχ hD hneO hneA VF WF VA WA hF hAct a b

example (a b : Fin r ⊕ Fin s) :
    (F).fusionAnalysis a b =
      CompleteZipperFusionFamily.biorthogonalAnalysis (triangularFusionAnalysis VF VA a b) :=
  CompleteZipperFusionFamily.ofTriangularBiorthogonalBlocked_fusionAnalysis O A hInjO hInjA
    hχ hD hneO hneA VF WF VA WA hF hAct a b

-- The retained state-action entries are literally the original W and V.
example (a : Fin r) (x y : Fin s) (μ : Fin (M a x y))
    (ij : Fin (χ a) × Fin (D x)) (z : Fin (D y)) :
    (F).fusionSynthesis (.inl a) (.inr x) ij ⟨.inr y, μ, z⟩ =
      WA a x y μ (finProdFinEquiv ij) z := rfl

example (a : Fin r) (x y : Fin s) (μ : Fin (M a x y))
    (z : Fin (D y)) (ij : Fin (χ a) × Fin (D x)) :
    (F).fusionAnalysis (.inl a) (.inr x) ⟨.inr y, μ, z⟩ ij =
      VA a x y μ z (finProdFinEquiv ij) := rfl

end ExactFamily

-- No ordinal label assumption is needed to transport an exact pair through blocking.
example {Λ : Type*} [Fintype Λ] {p : ℕ} {D : Λ → ℕ}
    {T : ∀ c, MPOTensor p (D c)} {N : Λ → ℕ} {a b : Λ}
    {V : ∀ c, Fin (N c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ}
    {W : ∀ c, Fin (N c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ}
    (h : MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Λ) × Fin (N c) ↦ (T q.1).toMPSTensor)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2))
    {L : ℕ} (hL : 0 < L) :
    MPSTensor.IsBiorthogonalDecomposition
      (mulTensor (blockTensor (T a) L) (blockTensor (T b) L)).toMPSTensor
      (fun q : (c : Λ) × Fin (N c) ↦ (blockTensor (T q.1) L).toMPSTensor)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := h.blockMPO_fintype hL

example {Λ : Type*} [DecidableEq Λ] {p g : ℕ} {D : Λ → ℕ}
    (e : Λ ≃ Fin g) (T : ∀ c, MPOTensor p (D c))
    (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor) (hD : ∀ c, 0 < D c)
    (hne : ∀ a b : Λ, a ≠ b → ∀ h : D a = D b,
      ¬ MPSTensor.GaugePhaseEquiv
        (cast (congrArg (MPSTensor (p * p)) h) (T a).toMPSTensor) (T b).toMPSTensor) :
    ∃ L : ℕ, 0 < L ∧ (∀ c, Kraus.IsInjective (blockTensor (T c) L).toMPSTensor) ∧
      ∃ K : Matrix ((c : Λ) × (Fin (D c) × Fin (D c)))
          (Fin (MPSTensor.blockPhysDim p L) × Fin (MPSTensor.blockPhysDim p L)) ℂ,
        ∀ (a b : Λ) (x y : Fin (D a)) (x' y' : Fin (D b)),
          (∑ i, ∑ j, K ⟨a, x, y⟩ (i, j) * blockTensor (T b) L i j x' y') =
            if he : a = b then
              if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
            else 0 := exists_blockTensor_leftInverse_of_labelEquiv e T hT hD hne

/--
info: 'MPOTensor.isBiorthogonalDecomposition_triangularTensor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.isBiorthogonalDecomposition_triangularTensor
/--
info: 'MPSTensor.IsBiorthogonalDecomposition.blockMPO_fintype'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBiorthogonalDecomposition.blockMPO_fintype
/--
info: 'MPOTensor.exists_blockTensor_leftInverse_of_labelEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.exists_blockTensor_leftInverse_of_labelEquiv
/--
info: 'MPOTensor.exists_triangular_blockTensor_leftInverse'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.exists_triangular_blockTensor_leftInverse
/--
info: 'MPOTensor.triangularBlockLength_pos'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.triangularBlockLength_pos
/--
info: 'MPOTensor.CompleteZipperFusionFamily.ofTriangularBiorthogonalBlocked'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.CompleteZipperFusionFamily.ofTriangularBiorthogonalBlocked

end TriangularBoundaryTest
