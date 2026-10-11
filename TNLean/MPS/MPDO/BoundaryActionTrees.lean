/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryDecompositionOperations
import TNLean.MPS.MPDO.BoundaryDecompositionComparison

/-!
# The two exact double-action decompositions

The fusion-then-action and sequential-action trees are built from the actual
exact fusion and action matrices. Their incoming bond coordinates are aligned
by the existing tensor-product associator. Both reconstruct the same original
unblocked tensor, and a simultaneous target-word span identifies their support
idempotents. No L-matrix or mixed pentagon is assumed.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
  `eq:F_symbol2`, and `1Fsymbol`, lines 491--552.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- A fusion channel followed by an action channel, retaining its final
state label. Source: GLM23 `rawrels`, left side. -/
abbrev FusionActionPath (N : Fin r → Fin r → Fin r → ℕ)
    (M : Fin r → Fin s → Fin s → ℕ) (a b : Fin r) (x : Fin s) :=
  (q : (c : Fin r) × Fin (N a b c)) × ((y : Fin s) × Fin (M q.1 x y))

/-- Two successive action channels, retaining the intermediate and final
state labels. Source: GLM23 `rawrels`, right side. -/
abbrev SequentialActionPath (M : Fin r → Fin s → Fin s → ℕ)
    (a b : Fin r) (x : Fin s) :=
  (q : (z : Fin s) × Fin (M b x z)) × ((y : Fin s) × Fin (M a q.1 y))

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)

/-- Analysis along the fusion-then-action tree. -/
noncomputable def fusionThenActionAnalysis (a b : Fin r) (x : Fin s)
    (q : FusionActionPath N M a b x) :
    Matrix (Fin (D q.2.1)) (Fin (χ a * χ b * D x)) ℂ :=
  VA q.1.1 x q.2.1 q.2.2 * kronId (VF a b q.1.1 q.1.2) (D x)

/-- Synthesis along the fusion-then-action tree. -/
noncomputable def fusionThenActionSynthesis (a b : Fin r) (x : Fin s)
    (q : FusionActionPath N M a b x) :
    Matrix (Fin (χ a * χ b * D x)) (Fin (D q.2.1)) ℂ :=
  kronId (WF a b q.1.1 q.1.2) (D x) * WA q.1.1 x q.2.1 q.2.2

/-- Analysis along the sequential-action tree, transported to the
fusion-then-action incoming bond coordinates. -/
noncomputable def sequentialActionAnalysis (a b : Fin r) (x : Fin s)
    (q : SequentialActionPath M a b x) :
    Matrix (Fin (D q.2.1)) (Fin (χ a * χ b * D x)) ℂ :=
  (VA a q.1.1 q.2.1 q.2.2 * idKron (χ a) (VA b x q.1.1 q.1.2)) *
    mulTensorAssocInvMatrix (χ a) (χ b) (D x)

/-- Synthesis along the sequential-action tree in the common incoming
coordinates. -/
noncomputable def sequentialActionSynthesis (a b : Fin r) (x : Fin s)
    (q : SequentialActionPath M a b x) :
    Matrix (Fin (χ a * χ b * D x)) (Fin (D q.2.1)) ℂ :=
  mulTensorAssocMatrix (χ a) (χ b) (D x) *
    (idKron (χ a) (WA b x q.1.1 q.1.2) * WA a q.1.1 q.2.1 q.2.2)

variable {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))

include hF hA in
/-- The actual fusion-then-action maps give an exact biorthogonal
decomposition of the double action. Source: GLM23 `rawrels`, left side. -/
theorem fusionThenAction_isBiorthogonal (a b : Fin r) (x : Fin s) :
    MPSTensor.IsBiorthogonalDecomposition (actTensor (mulTensor (O a) (O b)) (A x))
      (fun q : FusionActionPath N M a b x ↦ A q.2.1)
      (fusionThenActionAnalysis VF VA a b x) (fusionThenActionSynthesis WF WA a b x) := by
  have hLift := MPSTensor.IsBiorthogonalDecomposition.actTensor_kronId
    (S := fun q : (c : Fin r) × Fin (N a b c) ↦ O q.1) (hF a b) (A x)
  exact hLift.comp
    (κ := fun q : (c : Fin r) × Fin (N a b c) ↦ (y : Fin s) × Fin (M q.1 x y))
    (fun _ q ↦ A q.1)
    (fun q t ↦ VA q.1 x t.1 t.2)
    (fun q t ↦ WA q.1 x t.1 t.2) (fun q ↦ hA q.1 x)

include hA in
/-- The actual sequential-action maps give an exact biorthogonal
decomposition of the same double action. Source: GLM23 `rawrels`, right side. -/
theorem sequentialAction_isBiorthogonal (a b : Fin r) (x : Fin s) :
    MPSTensor.IsBiorthogonalDecomposition (actTensor (mulTensor (O a) (O b)) (A x))
      (fun q : SequentialActionPath M a b x ↦ A q.2.1)
      (sequentialActionAnalysis VA a b x) (sequentialActionSynthesis WA a b x) := by
  have hSequential := ((hA b x).actTensor_idKron (O a)).comp
    (κ := fun q : (z : Fin s) × Fin (M b x z) ↦ (y : Fin s) × Fin (M a q.1 y))
    (E := fun _ q ↦ D q.1)
    (fun _ q ↦ A q.1)
    (fun q t ↦ VA a q.1 t.1 t.2)
    (fun q t ↦ WA a q.1 t.1 t.2) (fun q ↦ hA a q.1)
  have hTransport := hSequential.sandwich
    (mulTensorAssocMatrix (χ a) (χ b) (D x))
    (mulTensorAssocInvMatrix (χ a) (χ b) (D x))
    (mulTensorAssocInvMatrix_mul_matrix (χ a) (χ b) (D x))
  have hTensor :
      (fun i ↦ mulTensorAssocMatrix (χ a) (χ b) (D x) *
        actTensor (O a) (actTensor (O b) (A x)) i *
        mulTensorAssocInvMatrix (χ a) (χ b) (D x)) =
          actTensor (mulTensor (O a) (O b)) (A x) := by
    funext i
    rw [← actTensor_mulTensor_mul_assocMatrix, Matrix.mul_assoc,
      mulTensorAssocMatrix_mul_invMatrix, Matrix.mul_one]
  rw [hTensor] at hTransport
  exact hTransport

include hF hA in
/-- Simultaneous target-word spanning derives equality of the two actual
double-action supports. Source: GLM23 `rawrels`; support equality is a
conclusion here, not an input to the L-symbol construction. -/
theorem fusionThenAction_support_eq_sequentialAction (a b : Fin r) (x : Fin s)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    (∑ q : FusionActionPath N M a b x,
      fusionThenActionSynthesis WF WA a b x q * fusionThenActionAnalysis VF VA a b x q) =
    ∑ q : SequentialActionPath M a b x,
      sequentialActionSynthesis WA a b x q * sequentialActionAnalysis VA a b x q := by
  exact MPSTensor.IsBiorthogonalDecomposition.support_eq_of_wordTupleSpanTop
    (A := A)
    (f := fun q : FusionActionPath N M a b x ↦ q.2.1)
    (g := fun q : SequentialActionPath M a b x ↦ q.2.1)
    (fusionThenAction_isBiorthogonal VF WF VA WA hF hA a b x)
    (sequentialAction_isBiorthogonal VA WA hA a b x) hL hSpan

end MPOTensor
