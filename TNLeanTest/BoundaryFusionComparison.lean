/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryFusionFMatrix
import TNLean.MPS.MPDO.TriangularActionLIdentification

/-!
# Exact fusion/action comparison regressions

The examples pin all multiplicity orders and the actual normalized-trace
contractions. The guarded reports reject any additional axiom dependency.
-/

set_option linter.hashCommand false

open MPOTensor
open scoped Matrix BigOperators Kronecker

namespace BoundaryFusionComparisonTest

universe u

section Generic

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
  (Fus : CompleteZipperFusionFamily Λ p)

example
    (a b c d : Λ) (q : Fus.RightTripleMultiplicity a b c d)
    (t : Fus.LeftTripleMultiplicity a b c d) :
    (Fus.rightTripleAnalysis a b c d).submatrix (fun z ↦ (q, z)) id *
        (Fus.leftTripleSynthesis a b c d).submatrix id (fun z ↦ (t, z)) =
      Fus.printedFMatrix a b c d q t •
        (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) :=
  MPOTensor.CompleteZipperFusionFamily.rightTripleAnalysis_mul_leftTripleSynthesis_eq_smul_one
    Fus a b c d q t

example
    (a b c d : Λ) (q : Fus.RightTripleMultiplicity a b c d)
    (t : Fus.LeftTripleMultiplicity a b c d) :
    Fus.printedFMatrix a b c d q t = (Fus.bondDim d : ℂ)⁻¹ *
      Matrix.trace ((Fus.rightTripleAnalysis a b c d).submatrix (fun z ↦ (q, z)) id *
        (Fus.leftTripleSynthesis a b c d).submatrix id (fun z ↦ (t, z))) :=
  MPOTensor.CompleteZipperFusionFamily.printedFMatrix_eq_inv_dim_mul_trace Fus a b c d q t

example
    (a b c d : Λ) (t : Fus.LeftTripleMultiplicity a b c d)
    (q : Fus.RightTripleMultiplicity a b c d) :
    (Fus.leftTripleAnalysis a b c d).submatrix (fun z ↦ (t, z)) id *
        (Fus.rightTripleSynthesis a b c d).submatrix id (fun z ↦ (q, z)) =
      Fus.inversePrintedFMatrix a b c d t q •
        (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) :=
  MPOTensor.CompleteZipperFusionFamily.leftTripleAnalysis_mul_rightTripleSynthesis_eq_smul_one
    Fus a b c d t q

example
    (a b c d : Λ) (t : Fus.LeftTripleMultiplicity a b c d)
    (q : Fus.RightTripleMultiplicity a b c d) :
    Fus.inversePrintedFMatrix a b c d t q = (Fus.bondDim d : ℂ)⁻¹ *
      Matrix.trace ((Fus.leftTripleAnalysis a b c d).submatrix (fun z ↦ (t, z)) id *
        (Fus.rightTripleSynthesis a b c d).submatrix id (fun z ↦ (q, z))) :=
  MPOTensor.CompleteZipperFusionFamily.inversePrintedFMatrix_eq_inv_dim_mul_trace Fus a b c d t q

end Generic

section ActionTrees

variable {r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)

example
    (a b c : Fin r) (x y : Fin s) (mu : Fin (N a b c)) (k : Fin (M c x y))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (z : Fin (D y)) :
    fusionThenActionSynthesis WF WA a b x ⟨⟨c, mu⟩, y, k⟩
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) z =
      ∑ v : Fin (χ c),
        WF a b c mu (finProdFinEquiv (xa, xb)) v *
          WA c x y k (finProdFinEquiv (v, xx)) z :=
  MPOTensor.fusionThenActionSynthesis_apply WF WA a b c x y mu k xa xb xx z

example
    (a b : Fin r) (x y t : Fin s) (i : Fin (M a t y)) (j : Fin (M b x t))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (z : Fin (D y)) :
    sequentialActionAnalysis VA a b x ⟨⟨t, j⟩, y, i⟩ z
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) =
      ∑ v : Fin (D t),
        VA a t y i z (finProdFinEquiv (xa, v)) *
          VA b x t j v (finProdFinEquiv (xb, xx)) :=
  MPOTensor.sequentialActionAnalysis_apply VA a b x y t i j xa xb xx z

example
    (a b c : Fin r) (x y : Fin s) (mu : Fin (N a b c)) (k : Fin (M c x y))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (z : Fin (D y)) :
    fusionThenActionAnalysis VF VA a b x ⟨⟨c, mu⟩, y, k⟩ z
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) =
      ∑ v : Fin (χ c),
        VA c x y k z (finProdFinEquiv (v, xx)) *
          VF a b c mu v (finProdFinEquiv (xa, xb)) :=
  MPOTensor.fusionThenActionAnalysis_apply VF VA a b c x y mu k xa xb xx z

example
    (a b : Fin r) (x y t : Fin s) (i : Fin (M a t y)) (j : Fin (M b x t))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (z : Fin (D y)) :
    sequentialActionSynthesis WA a b x ⟨⟨t, j⟩, y, i⟩
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) z =
      ∑ v : Fin (D t),
        WA b x t j (finProdFinEquiv (xb, xx)) v *
          WA a t y i (finProdFinEquiv (xa, v)) z :=
  MPOTensor.sequentialActionSynthesis_apply WA a b x y t i j xa xb xx z

end ActionTrees

section SourceFusion

variable {p r : ℕ} {χ : Fin r → ℕ} {N : Fin r → Fin r → Fin r → ℕ}

example (a b c d : Fin r) :
    FusionLeftMultiplicity N a b c d =
      ((e : Fin r) × (Fin (N a b e) × Fin (N e c d))) := rfl

example (a b c d : Fin r) :
    FusionRightMultiplicity N a b c d =
      ((f : Fin r) × (Fin (N b c f) × Fin (N a f d))) := rfl

variable
  (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)

example (a b c d : Fin r) : fusionFMatrix V W a b c d =
  fun ⟨e, mu, nu⟩ ⟨f, lambda, sigma⟩ ↦
    let H : Matrix (Fin (χ d)) ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) ℂ :=
      fun z v ↦
        ∑ t : Fin (χ e),
          V e c d nu z (finProdFinEquiv (t, v.2)) *
            V a b e mu t (finProdFinEquiv v.1)
    let S : Matrix ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) (Fin (χ d)) ℂ :=
      fun v z ↦
        ∑ t : Fin (χ f),
          W b c f lambda (finProdFinEquiv (v.1.2, v.2)) t *
            W a f d sigma (finProdFinEquiv (v.1.1, t)) z
    (χ d : ℂ)⁻¹ * Matrix.trace (H * S) := by
  rfl

variable {T : ∀ a, MPOTensor p (χ a)}
  (hD : ∀ a, 0 < χ a) (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor)
  (hVW : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (T q.1).toMPSTensor)
      (fun q ↦ V a b q.1 q.2) (fun q ↦ W a b q.1 q.2))
  (K : Matrix ((c : Fin r) × (Fin (χ c) × Fin (χ c))) (Fin p × Fin p) ℂ)
  (hK : ∀ (c d : Fin r) (x y : Fin (χ c)) (x' y' : Fin (χ d)),
    (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
      if he : c = d then
        if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
      else 0)

example
    (a b c d : Fin r) (q : FusionLeftMultiplicity N a b c d)
    (t : FusionRightMultiplicity N a b c d) :
    (CompleteZipperFusionFamily.ofBiorthogonal hD hT V W hVW K hK).inversePrintedFMatrix
      a b c d q t = fusionFMatrix V W a b c d q t :=
  MPOTensor.ofBiorthogonal_inversePrintedFMatrix_eq_fusionFMatrix V W hD hT hVW K hK a b c d q t

end SourceFusion

section AuxiliaryAction

variable {p r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  {T : ∀ q : Fin r ⊕ Fin s, MPOTensor p (triangularBondDim χ D q)}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  (hD : ∀ q, 0 < triangularBondDim χ D q)
  (hT : ∀ q, Kraus.IsInjective (T q).toMPSTensor)
  (hVW : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin r ⊕ Fin s) × Fin (triangularFusionMultiplicity N M a b c) ↦
        (T q.1).toMPSTensor)
      (fun q ↦ triangularFusionAnalysis VF VA a b q.1 q.2)
      (fun q ↦ triangularFusionSynthesis WF WA a b q.1 q.2))
  (K : Matrix ((c : Fin r ⊕ Fin s) ×
    (Fin (triangularBondDim χ D c) × Fin (triangularBondDim χ D c)))
      (Fin p × Fin p) ℂ)
  (hK : ∀ (c d : Fin r ⊕ Fin s)
    (x y : Fin (triangularBondDim χ D c)) (x' y' : Fin (triangularBondDim χ D d)),
    (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
      if he : c = d then
        if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
      else 0)

local notation "F" => CompleteZipperFusionFamily.ofBiorthogonal hD hT
  (triangularFusionAnalysis VF VA) (triangularFusionSynthesis WF WA) hVW K hK

example
    (a b c : Fin r) (x y z : Fin s)
    (i : Fin (M a z y)) (j : Fin (M b x z))
    (k : Fin (M c x y)) (mu : Fin (N a b c)) :
    (F).printedFMatrix (.inl a) (.inl b) (.inr x) (.inr y)
        ⟨.inr z, j, i⟩ ⟨.inl c, mu, k⟩ =
      actionLMatrix WF VA WA a b x y ⟨z, i, j⟩ ⟨c, k, mu⟩ :=
  MPOTensor.triangular_printedFMatrix_eq_actionLMatrix
    VF WF VA WA hD hT hVW K hK a b c x y z i j k mu

end AuxiliaryAction

/-- info:
'MPOTensor.CompleteZipperFusionFamily.rightTripleAnalysis_mul_leftTripleSynthesis_eq_smul_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.CompleteZipperFusionFamily.rightTripleAnalysis_mul_leftTripleSynthesis_eq_smul_one

/-- info:
'MPOTensor.CompleteZipperFusionFamily.printedFMatrix_eq_inv_dim_mul_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.CompleteZipperFusionFamily.printedFMatrix_eq_inv_dim_mul_trace

/-- info:
'MPOTensor.CompleteZipperFusionFamily.leftTripleAnalysis_mul_rightTripleSynthesis_eq_smul_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.CompleteZipperFusionFamily.leftTripleAnalysis_mul_rightTripleSynthesis_eq_smul_one

/-- info:
'MPOTensor.CompleteZipperFusionFamily.inversePrintedFMatrix_eq_inv_dim_mul_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.CompleteZipperFusionFamily.inversePrintedFMatrix_eq_inv_dim_mul_trace

/-- info:
'MPOTensor.fusionThenActionSynthesis_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.fusionThenActionSynthesis_apply

/-- info:
'MPOTensor.sequentialActionAnalysis_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.sequentialActionAnalysis_apply

/-- info:
'MPOTensor.fusionThenActionAnalysis_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.fusionThenActionAnalysis_apply

/-- info:
'MPOTensor.sequentialActionSynthesis_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.sequentialActionSynthesis_apply

/-- info:
'MPOTensor.ofBiorthogonal_inversePrintedFMatrix_eq_fusionFMatrix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.ofBiorthogonal_inversePrintedFMatrix_eq_fusionFMatrix

/-- info:
'MPOTensor.triangular_printedFMatrix_eq_actionLMatrix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.triangular_printedFMatrix_eq_actionLMatrix

end BoundaryFusionComparisonTest
